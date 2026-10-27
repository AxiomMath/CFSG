module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainAffine
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInStage1D

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

section DichX

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G}
  {ψ : V6 → G} {p u : Fin 6 → G} {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  {Γ : Subgroup (Equiv.Perm V6)}

theorem linK_zero (σ : hS.linK.range) : (σ : Equiv.Perm V6) 0 = 0 := by
  obtain ⟨x, hx⟩ := σ.2
  rw [← hx]
  exact map_zero_of_mem_linGroup (hS.rad.linHom_mem_linGroup _)

variable (hΓ0 : ∀ γ ∈ Γ, γ 0 = 0 → γ ∈ hS.linK.range) (hKΓ : hS.linK.range ≤ Γ)
include hΓ0 hKΓ

omit hΓ0 in
theorem lin_mem_orbitX {v : V6} (hv : v ∈ MulAction.orbit Γ (0 : V6)) {x : G}
    (hx : x ∈ P ⊔ zpowers x₀) : lin ψ x v ∈ MulAction.orbit Γ (0 : V6) :=
  perm_mem_orbit hv (hKΓ ⟨⟨x, hx⟩, rfl⟩)

theorem card_eqX [Finite G] :
    Nat.card Γ = Nat.card (MulAction.orbit Γ (0 : V6)) * oBound ε := by
  have e := MulAction.orbitProdStabilizerEquivGroup Γ (0 : V6)
  rw [← Nat.card_congr e, Nat.card_prod]
  congr 1
  have hstab : MulAction.stabilizer Γ (0 : V6) ≃ hS.linK.range :=
    { toFun := fun γ => ⟨(γ : Γ), hΓ0 _ (γ : Γ).2 γ.2⟩
      invFun := fun σ => ⟨⟨σ, hKΓ σ.2⟩, linK_zero hS σ⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr hstab]
  have h := hS.card_linK
  rw [hS.card_K, hS.rad.card_P] at h
  have := oBound_even ε
  omega

variable (hΓaff : ∀ γ ∈ Γ, ∀ x y z : V6, γ (x + y + z) = γ x + γ y + γ z)
include hΓaff

theorem false_of_ns_orbitX [Finite G]
    (hO : ∀ v, v ∈ MulAction.orbit Γ (0 : V6) ↔ (v = 0 ∨ qfV ε v = 1)) : False := by
  classical
  obtain ⟨r, hr, hrc⟩ := ns_card ε
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> norm_num
  have : Fact r.Prime := ⟨hrp⟩
  have hOcard : Nat.card (MulAction.orbit Γ (0 : V6)) = r := by
    have hset : MulAction.orbit Γ (0 : V6) =
        ↑(Finset.univ.filter fun v : V6 => v = 0 ∨ qfV ε v = 1) := by
      ext v
      simp [hO]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, hrc]
  have hcard := card_eqX hS hΓ0 hKΓ
  rw [hOcard] at hcard
  obtain ⟨γ, hγ⟩ :=
    exists_prime_orderOf_dvd_card' (G := Γ) r (by rw [hcard]; exact dvd_mul_right _ _)
  set Λ := linPartHom Γ hΓaff
  set σ := Λ γ
  have hσr : σ ^ r = 1 := by rw [← map_pow, ← hγ, pow_orderOf_eq_one, map_one]
  set F : AddSubgroup V6 :=
    { carrier := {v | σ v = v}
      zero_mem' := map_zero_of_mem_linGroup (linPartHom_mem_linGroup hΓaff γ)
      add_mem' := fun {v w} hv hw => by
        change σ (v + w) = v + w
        rw [linPartHom_mem_linGroup hΓaff γ v w]
        exact congrArg₂ (· + ·) hv hw
      neg_mem' := fun {v} hv => by
        change σ (-v) = -v
        rw [v6_neg]
        exact hv }
  have hZ : IsPGroup r (zpowers σ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    rcases (Nat.dvd_prime hrp).1 (orderOf_dvd_of_pow_eq_one hσr) with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      have hγ2 : γ * γ = 1 := by
        apply Subtype.ext
        refine Equiv.ext fun v => ?_
        have h1 : ∀ w, (γ : Equiv.Perm V6) w = w + (γ : Equiv.Perm V6) 0 := fun w => by
          have := congrArg (fun τ : Equiv.Perm V6 => τ w) h
          simp only [σ, Λ, linPartHom_apply, Equiv.Perm.one_apply] at this
          calc (γ : Equiv.Perm V6) w = ((γ : Equiv.Perm V6) w + (γ : Equiv.Perm V6) 0) +
                (γ : Equiv.Perm V6) 0 := by rw [add_assoc, v6_add_self, add_zero]
            _ = w + (γ : Equiv.Perm V6) 0 := by rw [this]
        simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, Subgroup.coe_one, Equiv.Perm.one_apply]
        rw [h1, h1 v, add_assoc, v6_add_self, add_zero]
      have := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hγ2 : γ ^ 2 = 1)
      rw [hγ] at this
      have := Nat.le_of_dvd (by norm_num) this
      rcases hr with rfl | rfl <;> omega
    · exact h
  have hmod := hZ.card_modEq_card_fixedPoints V6
  have hfix : Nat.card (MulAction.fixedPoints (zpowers σ) V6) = Nat.card F := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    change v ∈ MulAction.fixedPoints (zpowers σ) V6 ↔ σ v = v
    simp only [MulAction.mem_fixedPoints, Subtype.forall, mem_zpowers_iff]
    constructor
    · intro h
      exact h σ ⟨1, zpow_one σ⟩
    · rintro hv _ ⟨n, rfl⟩
      change (σ ^ n) v = v
      have hv' : σ v = v := hv
      induction n using Int.induction_on with
      | zero => rfl
      | succ n ih => rw [_root_.zpow_add_one, Equiv.Perm.mul_apply, hv', ih]
      | pred n ih =>
        rw [_root_.zpow_sub_one, Equiv.Perm.mul_apply]
        have : σ⁻¹ v = v := by rw [← hv', perm_inv_apply, hv']
        rw [this, ih]
  rw [hfix] at hmod
  have hV : Nat.card V6 = 64 := by rw [Nat.card_eq_fintype_card]; simp
  rw [hV] at hmod
  have hdvd : Nat.card F ∣ 64 := hV ▸ F.card_addSubgroup_dvd_card
  have hF64 : Nat.card F = 64 :=
    eq_64_of_dvd r hr _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hdvd)) hdvd hmod.symm
  have hFtop : F = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [hF64, hV]
  have hσ1 : σ = 1 := Equiv.ext fun v => by
    have : v ∈ F := hFtop ▸ AddSubgroup.mem_top v
    exact this
  have hγ2 : γ * γ = 1 := by
    apply Subtype.ext
    refine Equiv.ext fun v => ?_
    have h1 : ∀ w, (γ : Equiv.Perm V6) w = w + (γ : Equiv.Perm V6) 0 := fun w => by
      have := congrArg (fun τ : Equiv.Perm V6 => τ w) hσ1
      simp only [σ, Λ, linPartHom_apply, Equiv.Perm.one_apply] at this
      calc (γ : Equiv.Perm V6) w = ((γ : Equiv.Perm V6) w + (γ : Equiv.Perm V6) 0) +
            (γ : Equiv.Perm V6) 0 := by rw [add_assoc, v6_add_self, add_zero]
        _ = w + (γ : Equiv.Perm V6) 0 := by rw [this]
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, Subgroup.coe_one, Equiv.Perm.one_apply]
    rw [h1, h1 v, add_assoc, v6_add_self, add_zero]
  have := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hγ2 : γ ^ 2 = 1)
  rw [hγ] at this
  have := Nat.le_of_dvd (by norm_num) this
  rcases hr with rfl | rfl <;> omega

theorem translations_of_fullX [Finite G]
    (hO : ∀ v, v ∈ MulAction.orbit Γ (0 : V6)) :
    ∀ w : V6, ∃ γ ∈ Γ, ∀ v, γ v = v + w := by
  classical
  let W₀ : AddSubgroup V6 :=
    { carrier := {w | ∃ γ ∈ Γ, ∀ v, γ v = v + w}
      zero_mem' := ⟨1, one_mem Γ, fun v => by simp⟩
      add_mem' := fun {w w'} ⟨γ, hγ, h1⟩ ⟨δ, hδ, h2⟩ =>
        ⟨γ * δ, mul_mem hγ hδ, fun v => by
          rw [Equiv.Perm.mul_apply, h1, h2]; abel⟩
      neg_mem' := fun {w} hw => by
        change ∃ γ ∈ Γ, ∀ v, γ v = v + -w
        rw [v6_neg]
        exact hw }
  have hW₀P : ∀ x ∈ P, ∀ w ∈ W₀, lin ψ x w ∈ W₀ := by
    rintro x hx w ⟨γ, hγ, h1⟩
    set σ := hS.linK ⟨x, mem_sup_left hx⟩
    have hσΓ : σ ∈ Γ := hKΓ ⟨⟨x, mem_sup_left hx⟩, rfl⟩
    have hσadd : σ ∈ linGroup := hS.rad.linHom_mem_linGroup _
    refine ⟨σ * γ * σ⁻¹, mul_mem (mul_mem hσΓ hγ) (inv_mem hσΓ), fun v => ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hσadd, perm_apply_inv]
    rfl
  by_cases htop : W₀ = ⊤
  · intro w
    have : w ∈ W₀ := htop ▸ AddSubgroup.mem_top w
    exact this
  exfalso
  have hbot : W₀ = ⊥ := by
    by_contra hne
    exact htop (eq_top_of_ne_bot_v6 hS.rad hW₀P hne)
  set Λ := linPartHom Γ hΓaff
  have hinj : Function.Injective Λ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have h1 : ∀ v, (γ : Equiv.Perm V6) v = v + (γ : Equiv.Perm V6) 0 := fun v => by
      have := congrArg (fun τ : Equiv.Perm V6 => τ v) hγ
      simp only [Λ, linPartHom_apply, Equiv.Perm.one_apply] at this
      calc (γ : Equiv.Perm V6) v = ((γ : Equiv.Perm V6) v + (γ : Equiv.Perm V6) 0) +
            (γ : Equiv.Perm V6) 0 := by rw [add_assoc, v6_add_self, add_zero]
        _ = v + (γ : Equiv.Perm V6) 0 := by rw [this]
    have h0 : (γ : Equiv.Perm V6) 0 ∈ W₀ := ⟨γ, γ.2, h1⟩
    rw [hbot, AddSubgroup.mem_bot] at h0
    apply Subtype.ext
    exact Equiv.ext fun v => by rw [h1, h0, add_zero]; rfl
  set X := Λ.range
  have hOcard : Nat.card (MulAction.orbit Γ (0 : V6)) = 64 := by
    have hset : MulAction.orbit Γ (0 : V6) = Set.univ := Set.eq_univ_of_forall hO
    rw [hset, Nat.card_univ, Nat.card_eq_fintype_card]
    simp
  have hcardX : Nat.card X = 64 * oBound ε := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_eqX hS hΓ0 hKΓ, hOcard]
  have hob : 0 < oBound ε := by cases ε <;> decide
  have hlinP : ∀ x ∈ P, ∃ σ ∈ X, ∀ v, σ v = lin ψ x v := by
    intro x hx
    refine ⟨Λ ⟨hS.linK ⟨x, mem_sup_left hx⟩, hKΓ ⟨⟨x, mem_sup_left hx⟩, rfl⟩⟩, ⟨_, rfl⟩,
      fun v => ?_⟩
    simp only [Λ, linPartHom_apply]
    rw [linK_zero hS ⟨_, ⟨⟨x, mem_sup_left hx⟩, rfl⟩⟩, add_zero]
    rfl
  have hXlin : ∀ σ ∈ X, σ ∈ linGroup := by
    rintro _ ⟨γ, rfl⟩
    exact linPartHom_mem_linGroup hΓaff γ
  by_cases horth : X ≤ orthGroup ε
  · have := (Subgroup.card_le_of_le horth).trans (card_orthGroup_le ε)
    omega
  obtain ⟨σ, hσX, hσo⟩ := Set.not_subset.1 horth
  have hσlin := hXlin σ hσX
  obtain ⟨v₁, hv₁⟩ : ∃ v, qfV ε (σ v) ≠ qfV ε v := by
    by_contra hcon
    push Not at hcon
    exact hσo ⟨hσlin, hcon⟩
  have he₀ : (Pi.single 0 1 : V6) ≠ 0 := fun h => by
    have := congrFun h 0
    simp at this
  have hte₀ : (Pi.single 0 1 : V6) = toVec 6 1 := by rw [← toVec_two_pow' 0]; rfl
  have hqe₀ : qfV ε (Pi.single 0 1 : V6) = 0 := by
    rw [hte₀, qfV_toVec ε (by norm_num), qfB_one]
    rfl
  have hl0 : σ 0 = 0 := map_zero_of_mem_linGroup hσlin
  have hv0 : v₁ ≠ 0 := fun h => hv₁ (by rw [h, hl0])
  have hu0 : σ v₁ ≠ 0 := fun h => hv0 (σ.injective (h.trans hl0.symm))
  have htrans : ∀ w : V6, w ≠ 0 → ∃ τ ∈ X, τ (Pi.single 0 1) = w := by
    intro w hw0
    rcases qfV_cases ε w with hw | hw
    · obtain ⟨x, hx, hxw⟩ := hS.rad.exists_lin_eq he₀ hw0 (hqe₀.trans hw.symm)
      obtain ⟨τ, hτX, hτ⟩ := hlinP x hx
      exact ⟨τ, hτX, by rw [hτ, hxw]⟩
    · rcases qfV_cases ε v₁ with h0 | h1
      · have hq1 : qfV ε (σ v₁) = 1 :=
          (qfV_cases ε _).resolve_left fun h => hv₁ (h.trans h0.symm)
        obtain ⟨x₁, hx₁, hx₁v⟩ := hS.rad.exists_lin_eq he₀ hv0 (hqe₀.trans h0.symm)
        obtain ⟨x₂, hx₂, hx₂w⟩ := hS.rad.exists_lin_eq hu0 hw0 (hq1.trans hw.symm)
        obtain ⟨τ₁, hτ₁X, hτ₁⟩ := hlinP x₁ hx₁
        obtain ⟨τ₂, hτ₂X, hτ₂⟩ := hlinP x₂ hx₂
        refine ⟨τ₂ * σ * τ₁, mul_mem (mul_mem hτ₂X hσX) hτ₁X, ?_⟩
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ₁, hx₁v, hτ₂, hx₂w]
      · have hq0 : qfV ε (σ v₁) = 0 :=
          (qfV_cases ε _).resolve_right fun h => hv₁ (h.trans h1.symm)
        obtain ⟨x₁, hx₁, hx₁v⟩ := hS.rad.exists_lin_eq he₀ hu0 (hqe₀.trans hq0.symm)
        obtain ⟨x₂, hx₂, hx₂w⟩ := hS.rad.exists_lin_eq hv0 hw0 (h1.trans hw.symm)
        obtain ⟨τ₁, hτ₁X, hτ₁⟩ := hlinP x₁ hx₁
        obtain ⟨τ₂, hτ₂X, hτ₂⟩ := hlinP x₂ hx₂
        refine ⟨τ₂ * σ⁻¹ * τ₁, mul_mem (mul_mem hτ₂X (inv_mem hσX)) hτ₁X, ?_⟩
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ₁, hx₁v, perm_inv_apply, hτ₂, hx₂w]
  have horb : Nat.card (MulAction.orbit X (Pi.single 0 1 : V6)) = 63 := by
    have e : MulAction.orbit X (Pi.single 0 1 : V6) ≃ {w : V6 // w ≠ 0} :=
      { toFun := fun w => ⟨w.1, by
          obtain ⟨τ, hτ⟩ := w.2
          intro h
          have hτlin := hXlin τ τ.2
          have h1 : (τ : Equiv.Perm V6) (Pi.single 0 1) = (τ : Equiv.Perm V6) 0 := by
            rw [map_zero_of_mem_linGroup hτlin, ← h]
            exact hτ
          exact he₀ ((τ : Equiv.Perm V6).injective h1)⟩
        invFun := fun w => ⟨w.1, by
          obtain ⟨τ, hτX, hτ⟩ := htrans w.1 w.2
          exact ⟨⟨τ, hτX⟩, hτ⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup X (Pi.single 0 1 : V6))
  rw [Nat.card_prod, horb, hcardX] at hos
  cases ε
  ·
    have hstab : Nat.card (MulAction.stabilizer X (Pi.single 0 1 : V6)) = 40960 := by
      simp only [oBound] at hos
      omega
    obtain ⟨hcube, hfix, hmove⟩ := Setup.plus_gen0_facts
    obtain ⟨σ₃, hσ₃X, hσ₃⟩ := hlinP (p 0) (hS.rad.p_mem 0)
    have hσ₃' : ∀ w, σ₃ w = genMat .plus 0 *ᵥ w := fun w => by rw [hσ₃, hS.rad.lin_p 0 w]; rfl
    have hσ₃e : σ₃ (Pi.single 0 1) = Pi.single 0 1 := by
      rw [hσ₃', hte₀, genMat, mulVec_toVec, hfix]
    have hσ₃3 : σ₃ ^ 3 = 1 := Equiv.ext fun w => by
      rw [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ₃',
        hσ₃', hσ₃', ← toVec_vecBits w, genMat, mulVec_toVec, mulVec_toVec, mulVec_toVec,
        hcube _ (vecBits_lt w)]
      rfl
    have hσ₃1 : σ₃ ≠ 1 := fun h => by
      have h2 := congrArg (fun τ : Equiv.Perm V6 => τ (toVec 6 2)) h
      simp only [hσ₃', genMat, mulVec_toVec, Equiv.Perm.coe_one, id] at h2
      exact hmove (toVec_injective (bmulVec_lt _ _) (by norm_num) h2)
    let s : MulAction.stabilizer X (Pi.single 0 1 : V6) := ⟨⟨σ₃, hσ₃X⟩, hσ₃e⟩
    have hs3 : orderOf s = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · exact Subtype.ext (Subtype.ext hσ₃3)
      · intro h
        exact hσ₃1 (congrArg (fun z : MulAction.stabilizer X (Pi.single 0 1 : V6) =>
          ((z : X) : Equiv.Perm V6)) h)
    have := orderOf_dvd_natCard s
    rw [hs3, hstab] at this
    norm_num at this
  ·
    simp only [oBound] at hos
    omega

theorem affine_trichotomy [Finite G] :
    (∀ γ ∈ Γ, γ 0 = 0) ∨ (∀ w : V6, ∃ γ ∈ Γ, ∀ v, γ v = v + w) ∨
      (∀ v, v ∈ MulAction.orbit Γ (0 : V6) ↔ qfV ε v = 0) := by
  by_cases h0 : ∀ γ ∈ Γ, γ 0 = 0
  · exact Or.inl h0
  right
  push Not at h0
  obtain ⟨γ₀, hγ₀, hne⟩ := h0
  have hv₀ : γ₀ 0 ∈ MulAction.orbit Γ (0 : V6) := mem_orbit_iff.2 ⟨γ₀, hγ₀, rfl⟩
  have hsame : ∀ v ∈ MulAction.orbit Γ (0 : V6), v ≠ 0 → ∀ w, w ≠ 0 → qfV ε w = qfV ε v →
      w ∈ MulAction.orbit Γ (0 : V6) := by
    intro v hv hv0 w hw hq
    obtain ⟨x, hx, hxw⟩ := hS.rad.exists_lin_eq hv0 hw hq.symm
    rw [← hxw]
    exact lin_mem_orbitX hS hKΓ hv (mem_sup_left hx)
  have h0O : (0 : V6) ∈ MulAction.orbit Γ (0 : V6) := mem_orbit_iff.2 ⟨1, one_mem _, rfl⟩
  by_cases hboth : ∃ v ∈ MulAction.orbit Γ (0 : V6), v ≠ 0 ∧ qfV ε v ≠ qfV ε (γ₀ 0)
  · obtain ⟨v₁, hv₁, hv₁0, hv₁q⟩ := hboth
    refine Or.inl (translations_of_fullX hS hΓ0 hKΓ hΓaff fun w => ?_)
    by_cases hw0 : w = 0
    · rw [hw0]; exact h0O
    by_cases hq : qfV ε w = qfV ε (γ₀ 0)
    · exact hsame _ hv₀ hne w hw0 hq
    · refine hsame v₁ hv₁ hv₁0 w hw0 ?_
      rcases qfV_cases ε w with h1 | h1 <;> rcases qfV_cases ε v₁ with h2 | h2 <;>
        rcases qfV_cases ε (γ₀ 0) with h3 | h3 <;> simp_all
  · push Not at hboth
    have hO : ∀ v, v ∈ MulAction.orbit Γ (0 : V6) ↔ (v = 0 ∨ qfV ε v = qfV ε (γ₀ 0)) := by
      intro v
      constructor
      · intro hv
        by_cases hv0 : v = 0
        · exact Or.inl hv0
        · exact Or.inr (hboth v hv hv0)
      · rintro (rfl | hq)
        · exact h0O
        · by_cases hv0 : v = 0
          · rw [hv0]; exact h0O
          · exact hsame _ hv₀ hne v hv0 hq
    rcases qfV_cases ε (γ₀ 0) with hq | hq
    · refine Or.inr fun v => ?_
      rw [hO, hq]
      constructor
      · rintro (rfl | h)
        · exact qfV_zero ε
        · exact h
      · exact fun h => Or.inr h
    · exact (false_of_ns_orbitX hS hΓ0 hKΓ hΓaff fun v => by rw [hO, hq]).elim

end DichX

end CFSG.EvenSmallLie.OmegaEight.Chain
