module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpILemma
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceFour
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpZLemma

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

variable {F : Type} [Field F] {X : Type} [Group X]

theorem mul_self_mem_center_of_lift' {K : Type*} [Group K] (hperf : Group.IsPerfect K)
    (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K) {f : X} (hf : f * f = 1) {x : K}
    (hx : ∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) : x * x ∈ Subgroup.center K := by
  have hcomm : ∀ y : K, (x * x) * y * (x * x)⁻¹ * y⁻¹ ∈ Subgroup.center K := by
    intro y
    refine hker ?_
    have h1 : ψ ((x * x) * y * (x * x)⁻¹) = ψ y := by
      have e : (x * x) * y * (x * x)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by group
      rw [e, ← hx, ← hx]
      calc f * (f * ψ y * f⁻¹) * f⁻¹ = (f * f) * ψ y * (f * f)⁻¹ := by group
        _ = ψ y := by rw [hf]; group
    simp only [MonoidHom.mem_ker, map_mul, map_inv] at h1 ⊢
    rw [h1]
    group
  have hR : (⊤ : Subgroup K) ≤ ⁅(⊤ : Subgroup K), ⊤⁆ := by
    have := hperf.commutator_eq_top
    rw [commutator_def] at this
    exact this.ge
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  exact (commute_of_perfect_of_commutator_mem_center hR (fun s _ => hcomm s) y
    (Subgroup.mem_top y)).symm

theorem perfect_statedSp [Finite F] (h4 : 4 ≤ Nat.card F) : Group.IsPerfect (StatedSp 2 F) :=
  (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num) (Or.inl (Or.inr h4))).1

theorem conj_eq_self_of_eq_one_or_negOne {x : StatedSp 2 F} (hx : x = 1 ∨ x = negOne)
    (y : StatedSp 2 F) : x * y * x⁻¹ = y := by
  have hc := Subgroup.mem_center_iff.mp (mem_center_iff.mpr hx : x ∈ Subgroup.center (StatedSp 2 F))
    y
  rw [mul_inv_eq_iff_eq_mul]
  exact hc.symm


theorem strongConclusion_sp_two [Finite F] [Finite X] (hodd : ringChar F ≠ 2)
    (h4 : 4 ≤ Nat.card F) (ψ : StatedSp 2 F →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) (hnorm : ψ.range.Normal)
    {Fo : Subgroup X} (hcard : Nat.card Fo = 4) (hF2 : ∀ f ∈ Fo, f * f = 1)
    (hfaith : ∀ f ∈ Fo, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (htoral : ToralActionFour ψ Fo) : StrongConclusion ψ.range Fo := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have hperf := perfect_statedSp h4
  obtain ⟨P, hP, hact⟩ := htoral
  have hlift : ∀ f ∈ Fo, ∃ x ∈ P, ∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹) := fun f hf => by
    obtain ⟨x, hx, -, hxa⟩ := hact f hf
    exact ⟨x, hx, hxa⟩
  have htype : ∀ f ∈ Fo, f ≠ 1 → ∀ x : StatedSp 2 F,
      (∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) →
        x ≠ 1 ∧ x ≠ negOne ∧ (x * x = 1 ∨ x * x = negOne) := by
    intro f hf hf1 x hxa
    have hcen : ¬ (x = 1 ∨ x = negOne) := by
      intro hx
      refine hfaith f hf hf1 ?_
      rintro _ ⟨y, rfl⟩
      have := hxa y
      rw [conj_eq_self_of_eq_one_or_negOne hx y, mul_inv_eq_iff_eq_mul] at this
      exact this
    refine ⟨fun h => hcen (Or.inl h), fun h => hcen (Or.inr h), ?_⟩
    exact mem_center_iff.mp (mul_self_mem_center_of_lift' hperf ψ hker (hF2 f hf) hxa)
  have hz : ∀ f ∈ Fo, f ≠ 1 → ∀ x : StatedSp 2 F, (∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) →
      x * x = 1 → ∀ d ∈ involutionOddCore f, ∀ y, d * ψ y * d⁻¹ = ψ y :=
    fun f hf hf1 x hxa hxx d hd =>
      zLemma h2 h4 hodd ψ hker hnorm hxx (htype f hf hf1 x hxa).1 (htype f hf hf1 x hxa).2.1 hxa
        (hF2 f hf) (hfaith f hf hf1) hd
  have hzex : ∃ f ∈ Fo, f ≠ 1 ∧ ∃ x : StatedSp 2 F,
      (∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) ∧ x * x = 1 := by
    obtain ⟨f₁, f₂, hf₁, hf₂, h1, h1', h12⟩ : ∃ f₁ f₂, f₁ ∈ Fo ∧ f₂ ∈ Fo ∧ f₁ ≠ 1 ∧ f₂ ≠ 1 ∧
        f₁ ≠ f₂ := by
      have h : 2 < (Fo : Set X).ncard := by
        rw [← Nat.card_coe_set_eq]
        have : Nat.card (Fo : Set X) = Nat.card Fo := rfl
        omega
      obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp h
      by_cases h1 : a = 1
      · exact ⟨b, c, hb, hc, fun h => hab (h1.trans h.symm), fun h => hac (h1.trans h.symm), hbc⟩
      by_cases h2 : b = 1
      · exact ⟨a, c, ha, hc, h1, fun h => hbc (h2.trans h.symm), hac⟩
      exact ⟨a, b, ha, hb, h1, h2, hab⟩
    obtain ⟨x₁, hx₁P, hx₁⟩ := hlift f₁ hf₁
    obtain ⟨x₂, hx₂P, hx₂⟩ := hlift f₂ hf₂
    rcases (htype f₁ hf₁ h1 x₁ hx₁).2.2 with hs₁ | hs₁
    · exact ⟨f₁, hf₁, h1, x₁, hx₁, hs₁⟩
    rcases (htype f₂ hf₂ h1' x₂ hx₂).2.2 with hs₂ | hs₂
    · exact ⟨f₂, hf₂, h1', x₂, hx₂, hs₂⟩
    refine ⟨f₁ * f₂, Fo.mul_mem hf₁ hf₂, ?_, x₁ * x₂, ?_, ?_⟩
    · intro h
      apply h12
      have e2 : f₂⁻¹ = f₂ := inv_eq_of_mul_eq_one_right (hF2 f₂ hf₂)
      rw [mul_eq_one_iff_eq_inv, e2] at h
      exact h
    · intro y
      calc f₁ * f₂ * ψ y * (f₁ * f₂)⁻¹ = f₁ * (f₂ * ψ y * f₂⁻¹) * f₁⁻¹ := by group
        _ = f₁ * ψ (x₂ * y * x₂⁻¹) * f₁⁻¹ := by rw [hx₂ y]
        _ = ψ (x₁ * (x₂ * y * x₂⁻¹) * x₁⁻¹) := hx₁ _
        _ = ψ (x₁ * x₂ * y * (x₁ * x₂)⁻¹) := by congr 1; group
    · have hc : x₂ * x₁ = x₁ * x₂ := (hP x₁ hx₁P x₂ hx₂P).symm
      calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
        _ = x₁ * (x₁ * x₂) * x₂ := by rw [hc]
        _ = (x₁ * x₁) * (x₂ * x₂) := by group
        _ = 1 := by rw [hs₁, hs₂, negOne_mul_self]
  refine ⟨fun d hd w hw => ?_, fun f hf hf1 d hd g hg w hw => ?_⟩
  · obtain ⟨f₀, hf₀, hf₀1, x₀, hx₀, hxx₀⟩ := hzex
    have hd' : d ∈ involutionOddCore f₀ := deltaCore_le_involutionOddCore hf₀ hf₀1 hd
    obtain ⟨y, rfl⟩ := hw
    have := hz f₀ hf₀ hf₀1 x₀ hx₀ hxx₀ d hd' y
    rwa [mul_inv_eq_iff_eq_mul] at this
  · obtain ⟨x_f, hxfP, hxf⟩ := hlift f hf
    obtain ⟨y, rfl⟩ := hw
    obtain ⟨s, hsP, hs⟩ := hlift g hg
    rcases (htype f hf hf1 x_f hxf).2.2 with hxx | hxx
    · have hdc := hz f hf hf1 x_f hxf hxx d hd
      calc d * g * ψ y * (d * g)⁻¹ = d * (g * ψ y * g⁻¹) * d⁻¹ := by group
        _ = d * ψ (s * y * s⁻¹) * d⁻¹ := by rw [hs y]
        _ = ψ (s * y * s⁻¹) := hdc _
        _ = g * ψ y * g⁻¹ := (hs y).symm
        _ = g * (d * ψ y * d⁻¹) * g⁻¹ := by rw [hdc y]
        _ = g * d * ψ y * (g * d)⁻¹ := by group
    · have key := iLemma hodd h4 ψ hker hnorm hxx hxf hd s (hP s hsP x_f hxfP) y
      obtain ⟨y', hy'⟩ : d * ψ y * d⁻¹ ∈ ψ.range := hnorm.conj_mem _ ⟨y, rfl⟩ d
      calc d * g * ψ y * (d * g)⁻¹ = d * (g * ψ y * g⁻¹) * d⁻¹ := by group
        _ = d * ψ (s * y * s⁻¹) * d⁻¹ := by rw [hs y]
        _ = ψ s * (d * ψ y * d⁻¹) * (ψ s)⁻¹ := key
        _ = ψ s * ψ y' * (ψ s)⁻¹ := by rw [hy']
        _ = ψ (s * y' * s⁻¹) := by simp only [map_mul, map_inv]
        _ = g * ψ y' * g⁻¹ := (hs y').symm
        _ = g * (d * ψ y * d⁻¹) * g⁻¹ := by rw [hy']
        _ = g * d * ψ y * (g * d)⁻¹ := by group

theorem strongLocalTwoBalanceToralFourOn_PSp_two :
    StrongLocalTwoBalanceToralFourOn .PSp (fun n _ _ => n = 2) := by
  intro n p e hp hn hfund hadm hp2 h5 X _ _ ψ hker hnorm Fo hcard hF2 hfaith htoral
  subst hn
  have : Fact p.Prime := ⟨hp⟩
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  have hodd : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp2
  exact strongConclusion_sp_two hodd h4 ψ hker hnorm hcard hF2 hfaith htoral

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
