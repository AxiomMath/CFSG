module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpMain
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Balance (deltaCore)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjSp multiplier ker_multiplier
  coe_conjSp)

variable {F : Type} [Field F] {X : Type} [Group X]

theorem multiplier_eq_one_or_neg_one {n : ℕ} [NeZero n] {x : gsp n F} (hx : x ^ 2 = 1) :
    (multiplier n F x : F) = 1 ∨ (multiplier n F x : F) = -1 := by
  have h : ((multiplier n F x : Fˣ) : F) * ((multiplier n F x : Fˣ) : F) = 1 := by
    have := congrArg (fun z : Fˣ => (z : F)) (by rw [← map_pow, hx, map_one] :
      (multiplier n F x) ^ 2 = 1)
    simpa [pow_two] using this
  exact mul_self_eq_one_iff.mp h

theorem deltaCore_trivial_gsp [Finite F] [Finite X] (hodd : ringChar F ≠ 2)
    (h4 : 4 ≤ Nat.card F) (ψ : StatedSp 2 F →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) (hnorm : ψ.range.Normal)
    {Fo : Subgroup X} (hcard : Nat.card Fo = 4) (hF2 : ∀ f ∈ Fo, f * f = 1)
    (hfaith : ∀ f ∈ Fo, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (htoral : ToralDiagGSp 2 ψ Fo) {d : X} (hd : d ∈ deltaCore Fo) {w : X} (hw : w ∈ ψ.range) :
    d * w = w * d := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  obtain ⟨P, hP, hact⟩ := htoral
  obtain ⟨a, haF, b, hbF, ha1, hb1, hab1⟩ := Linear.exists_pair_of_card_four hcard hF2
  obtain ⟨xa, hxaP, hxa2, hxa⟩ := hact a haF
  obtain ⟨xb, hxbP, hxb2, hxb⟩ := hact b hbF
  have hex : ∃ f₀ ∈ Fo, f₀ ≠ 1 ∧ ∃ x₀ : gsp 2 F, (multiplier 2 F x₀ : F) = 1 ∧ x₀ ^ 2 = 1 ∧
      ∀ y, f₀ * ψ y * f₀⁻¹ = ψ (conjSp 2 F x₀ y) := by
    rcases multiplier_eq_one_or_neg_one hxa2 with h₁ | h₁
    · exact ⟨a, haF, ha1, xa, h₁, hxa2, hxa⟩
    rcases multiplier_eq_one_or_neg_one hxb2 with h₂ | h₂
    · exact ⟨b, hbF, hb1, xb, h₂, hxb2, hxb⟩
    refine ⟨a * b, Fo.mul_mem haF hbF, hab1, xa * xb, ?_, ?_, fun y => ?_⟩
    · rw [map_mul, Units.val_mul, h₁, h₂]
      norm_num
    · have hc : Commute xa xb := hP xa hxaP xb hxbP
      rw [hc.mul_pow, hxa2, hxb2, one_mul]
    · have e : (a * b) * ψ y * (a * b)⁻¹ = a * (b * ψ y * b⁻¹) * a⁻¹ := by group
      rw [e, hxb y, hxa (conjSp 2 F xb y), map_mul]
      rfl
  obtain ⟨f₀, hf₀, hf₀1, x₀, hμ₀, hx₀2, hx₀⟩ := hex
  have hmem : (x₀ : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F := by
    have : x₀ ∈ (multiplier 2 F).ker := by
      rw [MonoidHom.mem_ker]
      exact Units.ext hμ₀
    rw [ker_multiplier, Subgroup.mem_subgroupOf] at this
    exact this
  set s : StatedSp 2 F := ⟨(x₀ : GL (Fin 2 ⊕ Fin 2) F), hmem⟩ with hs
  have hss : s * s = 1 := by
    apply Subtype.ext
    have := congrArg (fun z : gsp 2 F => (z : GL (Fin 2 ⊕ Fin 2) F)) (by
      rwa [pow_two] at hx₀2 : x₀ * x₀ = 1)
    simpa using this
  have hsy : ∀ y, conjSp 2 F x₀ y = s * y * s⁻¹ := fun y => Subtype.ext (coe_conjSp x₀ y)
  have hf : ∀ y, f₀ * ψ y * f₀⁻¹ = ψ (s * y * s⁻¹) := fun y => by rw [hx₀ y, hsy]
  have hcen : ¬ (s = 1 ∨ s = negOne) := by
    intro hs'
    refine hfaith f₀ hf₀ hf₀1 ?_
    rintro _ ⟨y, rfl⟩
    have := hf y
    rw [conj_eq_self_of_eq_one_or_negOne hs' y, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hd' : d ∈ involutionOddCore f₀ :=
    CFSG.ClassicalInvolution.Balance.mem_deltaCore_iff.mp hd f₀ hf₀ hf₀1
  have hkey := zLemma h2 h4 hodd ψ hker hnorm hss (fun h => hcen (Or.inl h))
    (fun h => hcen (Or.inr h)) hf (hF2 f₀ hf₀) (hfaith f₀ hf₀ hf₀1) hd'
  obtain ⟨y, rfl⟩ := hw
  have := hkey y
  rwa [mul_inv_eq_iff_eq_mul] at this

theorem deltaCore_trivial_psp_two {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    [Finite X] (ψ : StatedSp 2 (GaloisField p e) →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField p e))) (hnorm : ψ.range.Normal)
    {Fo : Subgroup X} (hcard : Nat.card Fo = 4) (hF2 : ∀ f ∈ Fo, f * f = 1)
    (hfaith : ∀ f ∈ Fo, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (htoral : ToralDiagGSp 2 ψ Fo) {d : X} (hd : d ∈ deltaCore Fo) {w : X} (hw : w ∈ ψ.range) :
    d * w = w * d := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  have hodd : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp2
  exact deltaCore_trivial_gsp hodd h4 ψ hker hnorm hcard hF2 hfaith htoral hd hw

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
