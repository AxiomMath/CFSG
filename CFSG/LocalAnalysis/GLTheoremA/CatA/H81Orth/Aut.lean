module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Weights
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsOrthLow
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped commutatorElement

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Perfect

theorem apply_comm_of_perfect {G : Subgroup (V ≃ₗ[K] V)} (hG : ⁅G, G⁆ = G) (τ : V ≃+ V)
    (h : ∀ g ∈ G, ∃ c : K, c ≠ 0 ∧ ∀ v, τ (g v) = c • g (τ v)) {g : V ≃ₗ[K] V} (hg : g ∈ G)
    (v : V) : τ (g v) = g (τ v) := by
  let C : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {a | ∀ v, τ (a v) = a (τ v)}
      one_mem' := fun _ => rfl
      mul_mem' := fun {a b} ha hb v => by
        show τ (a (b v)) = a (b (τ v))
        rw [ha, hb]
      inv_mem' := fun {a} ha v => by
        show τ (a⁻¹ v) = a⁻¹ (τ v)
        have h1 := ha (a⁻¹ v)
        rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h1
        rw [LinearEquiv.coe_inv, h1, LinearEquiv.symm_apply_apply] }
  have hinv : ∀ a ∈ G, ∀ c : K, c ≠ 0 → (∀ v, τ (a v) = c • a (τ v)) →
      ∀ v, τ (a⁻¹ v) = c⁻¹ • a⁻¹ (τ v) := by
    intro a _ c hc ha v
    have h1 := ha (a⁻¹ v)
    rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h1
    rw [LinearEquiv.coe_inv, h1, map_smul, LinearEquiv.symm_apply_apply, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hle : ⁅G, G⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro a ha b hb v
    obtain ⟨c, hc, hac⟩ := h a ha
    obtain ⟨d, hd, hbd⟩ := h b hb
    have hai := hinv a ha c hc hac
    have hbi := hinv b hb d hd hbd
    show τ (⁅a, b⁆ v) = ⁅a, b⁆ (τ v)
    simp only [commutatorElement_def, LinearEquiv.mul_apply]
    rw [hac, hbd, hai, hbi]
    simp only [map_smul, smul_smul]
    rw [show c * (d * (c⁻¹ * d⁻¹)) = 1 by field_simp, one_smul]
  exact hle (by rw [hG]; exact hg) v

end Perfect

section Eichler

theorem eichler_pow {u w : V} (hw : polar Q u w = 0) (n : ℕ) :
    eichler Q u w ^ n = eichler Q u (n • w) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, eichler_zero_right]
  | succ n ih =>
    have hnw : polar Q u (n • w) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, polar_smul_right, hw, smul_zero]
    rw [pow_succ, ih, eichler_mul hnw hw, succ_nsmul]

theorem eichler_pow_ringChar {u w : V} (hw : polar Q u w = 0) :
    eichler Q u w ^ ringChar K = 1 := by
  rw [eichler_pow hw, ← Nat.cast_smul_eq_nsmul K, ringChar.Nat.cast_ringChar, zero_smul,
    eichler_zero_right]

variable [FiniteDimensional K V] {p : ℕ} {x : V ≃ₗ[K] V}

theorem eichler_mem_supportedFixedDerived [Finite K] (hx : OddOrderIsometry Q p x)
    (hK : ringChar K ≠ 2) {u w : V} (hu : u ∈ fixedSpace x) (hw : w ∈ fixedSpace x)
    (huw : polar Q u w = 0) : eichler Q u w ∈ supportedFixedDerived Q x := by
  obtain ⟨-, horth⟩ := hx.fixed_others
  have hxu : x u = u := mem_fixedSpace.mp hu
  have hxw : x w = w := mem_fixedSpace.mp hw
  have hcomm : eichler Q u w * x = x * eichler Q u w := by
    have h := eichler_conj hx.mem u w
    rw [hxu, hxw] at h
    calc eichler Q u w * x = (x * eichler Q u w * x⁻¹) * x := by rw [h]
      _ = x * eichler Q u w := by group
  have hS : eichler Q u w ∈ supportedBlock Q x (X - 1) := by
    refine mem_supportedBlock.mpr ⟨⟨eichler_mem_orthogonalGroup Q u w,
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩, fun r hr => ?_⟩
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_comm]; exact horth u hu r hr
    · rw [polar_comm]; exact horth w hw r hr
  refine mem_supportedFixedDerived.mpr ⟨hS, ?_⟩
  have hpow : (restrictFixed Q x ⟨eichler Q u w, hS⟩) ^ ringChar K = 1 := by
    rw [← map_pow]
    have : (⟨eichler Q u w, hS⟩ : ↥(supportedBlock Q x (X - 1))) ^ ringChar K = 1 :=
      Subtype.ext (eichler_pow_ringChar huw)
    rw [this, map_one]
  have hodd : Odd (ringChar K) :=
    (CharP.char_is_prime K (ringChar K)).eq_two_or_odd'.resolve_left hK
  exact CFSG.ComponentClassification.HarrisLit.L33.OC.mem_omega_of_odd hK
    hx.polarBilin_fixed_nondegenerate (restrictFixed_mem_orthogonalGroup _)
    (hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow))

end Eichler

section Siegel

theorem ringEquiv_apply_eq_of_commute_eichler (σ : V ≃+ V) (φ : K ≃+* K)
    (hσ : ∀ (c : K) (v : V), σ (c • v) = φ c • σ v) {u v w : V} (hQu : Q u = 0) (hQw : Q w = 0)
    (huw : polar Q u w = 0) (hvu : polar Q v u = 1) (hvw : polar Q v w = 0) (hw0 : w ≠ 0)
    (hcomm : ∀ s : K, ∀ z, σ (eichler Q u (s • w) z) = eichler Q u (s • w) (σ z)) (s : K) :
    φ s = s := by
  have hus : ∀ s : K, polar Q u (s • w) = 0 := fun s => by
    rw [polar_smul_right, huw, smul_zero]
  have hEv : ∀ s : K, eichler Q u (s • w) v = v + s • w := fun s => by
    rw [eichler_apply hQu (hus s), hvu, one_smul, polar_smul_right, hvw, smul_zero,
      QuadraticMap.map_smul, hQw, smul_zero, zero_mul, add_zero, zero_smul, sub_zero]
  have hEσ : ∀ s : K, eichler Q u (s • w) (σ v) =
      σ v + s • (polar Q (σ v) u • w - polar Q (σ v) w • u) := fun s => by
    rw [eichler_apply hQu (hus s), polar_smul_right, QuadraticMap.map_smul, hQw, smul_zero,
      zero_mul, add_zero, smul_eq_mul]
    module
  have key : ∀ s : K, φ s • σ w = s • (polar Q (σ v) u • w - polar Q (σ v) w • u) := by
    intro s
    have h := hcomm s v
    rw [hEv, map_add, hσ, hEσ] at h
    exact add_left_cancel h
  have h1 := key 1
  rw [map_one, one_smul, one_smul] at h1
  have h2 := key s
  rw [← h1] at h2
  have hσw : σ w ≠ 0 := fun h => hw0 (σ.injective (by rw [h, map_zero]))
  have h3 : (φ s - s) • σ w = 0 := by rw [sub_smul, h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hσw)

theorem exists_singular_pair_partner [Finite K] {U : Type} [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (hodd : Odd (Nat.card K)) (QU : QuadraticForm K U)
    (hQU : (polarBilin QU).Nondegenerate) (hdim : 5 ≤ finrank K U) :
    ∃ u v w : U, QU u = 0 ∧ QU w = 0 ∧ polar QU u w = 0 ∧ polar QU v u = 1 ∧
      polar QU v w = 0 ∧ w ≠ 0 := by
  obtain ⟨m, P, A, horth, -, -, -, -, -, -, hA2, hdimU, -⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.finite_odd_quadratic_low_Witt_dimension_bound
      hodd QU hQU).2.1
  have hm : 2 ≤ m := by omega
  set P₀ := P ⟨0, by omega⟩
  set P₁ := P ⟨1, by omega⟩
  have h01 : P₀.Orth P₁ := horth _ _ (by simp [Fin.ext_iff])
  refine ⟨P₀.e, P₀.f, P₁.e, P₀.Q_e, P₁.Q_e, h01.ee, ?_, h01.fe, ?_⟩
  · rw [polar_comm]; exact P₀.polar_ef
  · intro h
    have := P₁.polar_ef
    rw [h, polar_zero_left] at this
    exact zero_ne_one this

end Siegel

section FixedVector

theorem eq_zero_of_forall_mem_omega_apply_eq [Finite K] {U : Type} [AddCommGroup U]
    [Module K U] [FiniteDimensional K U] (hK : 2 < Nat.card K) (QU : QuadraticForm K U)
    (hQU : (polarBilin QU).Nondegenerate) (hdim : 3 ≤ finrank K U) {w : U}
    (hw : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup QU, TauCeti.QuadraticMap.orthogonalGroup QU⁆,
      g w = w) : w = 0 := by
  classical
  set f : U →ₗ[K] K := (polarBilin QU).flip w
  have hf : ∀ x, f x = polar QU x w := fun x => rfl
  set M : U →ₗ[K] U := f.smulRight w
  have hM : ∀ x, M x = polar QU x w • w := fun x => rfl
  have hcomm : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup QU,
      TauCeti.QuadraticMap.orthogonalGroup QU⁆, M ∘ₗ (g : U →ₗ[K] U) = (g : U →ₗ[K] U) ∘ₗ M := by
    intro g hg
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup QU := orthDerived_le_orthogonalGroup' QU hg
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hM, map_smul, hw g hg]
    congr 1
    calc polar QU (g x) w = polar QU (g x) (g w) := by rw [hw g hg]
      _ = polar QU x w := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO x w
  obtain ⟨c, hc⟩ := ((CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
    hK QU hQU hdim).1 M).mp hcomm
  have hne : LinearMap.ker f ≠ ⊥ := by
    intro h
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : finrank K (LinearMap.range f) ≤ 1 :=
      (Submodule.finrank_le _).trans (Module.finrank_self K).le
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxw : f x = 0 := hxk
  have hc0 : c = 0 := by
    have h1 : M x = c • x := by rw [hc]; rfl
    rw [hM, show polar QU x w = f x from rfl, hxw, zero_smul] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hx0
  by_contra hw0
  apply hw0
  refine CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero hQU fun z => ?_
  have h1 : M z = c • z := by rw [hc]; rfl
  rw [hM, hc0, zero_smul] at h1
  rw [polar_comm]
  exact (smul_eq_zero.mp h1).resolve_right hw0

end FixedVector

section Perfectness

variable [Finite K]

theorem commutator_orthDerived_eq {U : Type} [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (hodd : Odd (Nat.card K)) (QU : QuadraticForm K U)
    (hQU : (polarBilin QU).Nondegenerate) (hdim : 5 ≤ finrank K U) :
    ⁅orthDerived QU, orthDerived QU⁆ = orthDerived QU := by
  set O := TauCeti.QuadraticMap.orthogonalGroup QU
  have hq :=
    CFSG.ComponentClassification.OddSelector.commutator_orthogonalGroup_quasisimple hodd QU hQU hdim
  haveI : Group.IsPerfect ↥(commutator ↥O) := hq.1
  let e : ↥(commutator ↥O) ≃* ↥(orthDerived QU) :=
    (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator O))
  haveI : Group.IsPerfect ↥(orthDerived QU) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Subgroup.commutator_eq_self

variable [FiniteDimensional K V] {p : ℕ} {x : V ≃ₗ[K] V}

theorem commutator_supportedFixedDerived_eq (hx : OddOrderIsometry Q p x)
    (hodd : Odd (Nat.card K)) (hW : 5 ≤ finrank K (fixedSpace x)) :
    ⁅supportedFixedDerived Q x, supportedFixedDerived Q x⁆ = supportedFixedDerived Q x := by
  haveI : Group.IsPerfect ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
    Subgroup.isPerfect_iff.mpr
      (commutator_orthDerived_eq hodd _ hx.polarBilin_fixed_nondegenerate hW)
  haveI : Group.IsPerfect ↥(supportedFixedDerived Q x) :=
    Group.IsPerfect.ofSurjective (f := (supportedFixedDerivedEquiv hx).symm.toMonoidHom)
      (supportedFixedDerivedEquiv hx).symm.surjective
  exact Subgroup.commutator_eq_self

end Perfectness

section Spaces

variable [FiniteDimensional K V] {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_smul_of_projT_eq {g g' : ↥(orthDerived Q)} (h : projT Q g' = projT Q g) :
    ∃ c : K, ∀ v, (g' : V ≃ₗ[K] V) v = c • (g : V ≃ₗ[K] V) v := by
  have hmem : g⁻¹ * g' ∈ (scalars K V).subgroupOf (orthDerived Q) := QuotientGroup.eq.mp h.symm
  obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hmem)
  refine ⟨c, fun v => ?_⟩
  have h2 : (g : V ≃ₗ[K] V) (((g⁻¹ * g' : ↥(orthDerived Q)) : V ≃ₗ[K] V) v) =
      (g' : V ≃ₗ[K] V) v := by
    simp
  rw [← h2, hc v, map_smul]

theorem mem_fixedSpace_of_forall_polar_eq_zero (hx : OddOrderIsometry Q p x) {v : V}
    (hv : ∀ r ∈ othersSpace x.toLinearMap (X - 1), polar Q v r = 0) : v ∈ fixedSpace x := by
  obtain ⟨hcompl, horth⟩ := hx.fixed_others
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
  have hr0 : r = 0 := by
    refine hx.regular r fun z => ?_
    obtain ⟨w', hw', r', hr', rfl⟩ := exists_add_of_isCompl hcompl z
    have h1 := hv r' hr'
    rw [polar_add_left, horth w hw r' hr', zero_add] at h1
    rw [polar_add_right, h1, add_zero, polar_comm, horth w' hw' r hr]
  rw [hr0, add_zero]
  exact hw

theorem polarBilin_othersSpace_nondegenerate (hx : OddOrderIsometry Q p x) :
    (polarBilin (Q.comp (othersSpace x.toLinearMap (X - 1)).subtype)).Nondegenerate := by
  obtain ⟨hcompl, horth⟩ := hx.fixed_others
  have key : ∀ u : othersSpace x.toLinearMap (X - 1),
      (∀ w : othersSpace x.toLinearMap (X - 1), polar Q (u : V) (w : V) = 0) → u = 0 := by
    intro u hu
    refine Subtype.ext (hx.regular _ fun v => ?_)
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
    rw [polar_add_right, hu ⟨r, hr⟩, polar_comm, horth w hw u u.2, zero_add]
  refine ⟨fun u hu => key u fun w => ?_, fun u hu => key u fun w => ?_⟩
  · have := hu w
    rwa [polarBilin_apply_apply, polar_comp_subtype] at this
  · have := hu w
    rwa [polarBilin_apply_apply, polar_comp_subtype, polar_comm] at this

theorem mem_othersSpace_of_forall_apply_eq [Finite K] (hx : OddOrderIsometry Q p x)
    (hK : 2 < Nat.card K) (hW : 3 ≤ finrank K (fixedSpace x)) {v : V}
    (hv : ∀ s ∈ supportedFixedDerived Q x, s v = v) : v ∈ othersSpace x.toLinearMap (X - 1) := by
  obtain ⟨hcompl, -⟩ := hx.fixed_others
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
  have hw0 : (⟨w, hw⟩ : fixedSpace x) = 0 := by
    refine eq_zero_of_forall_mem_omega_apply_eq hK _ hx.polarBilin_fixed_nondegenerate hW
      fun g hg => ?_
    obtain ⟨s, hs⟩ := restrictFixed_surjective hx g (orthDerived_le_orthogonalGroup' _ hg)
    have hs' : restrictFixed Q x s ∈ orthDerived (Q.comp (fixedSpace x).subtype) := hs ▸ hg
    have hsS : (s : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x :=
      mem_supportedFixedDerived.mpr ⟨s.2, hs'⟩
    have h1 := hv _ hsS
    have hsr : (s : V ≃ₗ[K] V) r = r := (mem_supportedBlock.mp s.2).2 r hr
    rw [map_add, hsr] at h1
    have hsw : (s : V ≃ₗ[K] V) w = w := add_right_cancel h1
    rw [← hs]
    exact Subtype.ext hsw
  have : w = 0 := congrArg Subtype.val hw0
  rw [this, zero_add]
  exact hr

end Spaces

section Main

variable [Finite K] [FiniteDimensional K V] {p : ℕ}

theorem apply_comm_of_mem_supportedFixedDerived [Nontrivial V] {y : ↥(orthDerived Q)}
    (hy : OddOrderIsometry Q p (y : V ≃ₗ[K] V))
    (hS : ⁅supportedFixedDerived Q (y : V ≃ₗ[K] V), supportedFixedDerived Q (y : V ≃ₗ[K] V)⁆ =
      supportedFixedDerived Q (y : V ≃ₗ[K] V))
    (α : MulAut (ProjOrthDerived Q))
    (hαJ : ∀ j ∈ fixedComponentImage Q (y : V ≃ₗ[K] V), α j = j) (σ : V ≃+ V)
    (hind : ∀ g : ↥(orthDerived Q), ∃ g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) (σ v) = σ ((g : V ≃ₗ[K] V) v)) ∧ α (projT Q g) = projT Q g')
    {s : V ≃ₗ[K] V} (hs : s ∈ supportedFixedDerived Q (y : V ≃ₗ[K] V)) (v : V) :
    σ (s v) = s (σ v) := by
  refine apply_comm_of_perfect hS σ (fun g hg => ?_) hs v
  set gΩ : ↥(orthDerived Q) := ⟨g, hy.supportedFixedDerived_le_orthDerived hg⟩
  obtain ⟨g', hg'σ, hg'α⟩ := hind gΩ
  have hJ : projT Q gΩ ∈ fixedComponentImage Q (y : V ≃ₗ[K] V) :=
    ⟨gΩ, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  rw [hαJ _ hJ] at hg'α
  obtain ⟨c, hc⟩ := exists_smul_of_projT_eq hg'α.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    apply hv₀
    have := hc ((g' : V ≃ₗ[K] V).symm v₀)
    rw [LinearEquiv.apply_symm_apply, zero_smul] at this
    exact this
  refine ⟨c, hc0, fun v => ?_⟩
  calc σ (g v) = (g' : V ≃ₗ[K] V) (σ v) := (hg'σ v).symm
    _ = c • g (σ v) := hc (σ v)

theorem exists_eq_conj_of_similitude (hQ : (polarBilin Q).Nondegenerate) (hK : ringChar K ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) {y : ↥(orthDerived Q)}
    (hy : OddOrderIsometry Q p (y : V ≃ₗ[K] V))
    (hR : finrank K (othersSpace (y : V ≃ₗ[K] V).toLinearMap (X - 1)) = 2)
    (hW : 5 ≤ finrank K (fixedSpace (y : V ≃ₗ[K] V)))
    (α : MulAut (ProjOrthDerived Q)) (hα : α ^ p = 1)
    (hαJ : ∀ j ∈ fixedComponentImage Q (y : V ≃ₗ[K] V), α j = j)
    (σ : V ≃+ V) (φ : K ≃+* K) (μ : K) (hσ : ∀ (c : K) (v : V), σ (c • v) = φ c • σ v)
    (hμ : ∀ v, Q (σ v) = μ * φ (Q v))
    (hind : ∀ g : ↥(orthDerived Q), ∃ g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) (σ v) = σ ((g : V ≃ₗ[K] V) v)) ∧ α (projT Q g) = projT Q g') :
    ∃ k : ℤ, α = MulAut.conj (projT Q y ^ k) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set x : V ≃ₗ[K] V := (y : V ≃ₗ[K] V) with hxdef
  set W := fixedSpace x with hWdef
  set R := othersSpace x.toLinearMap (X - 1) with hRdef
  obtain ⟨hcompl, horth⟩ := hy.fixed_others
  have hodd : Odd (Nat.card K) := by
    have := Fintype.ofFinite K
    by_contra h
    apply hK
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
    exact Nat.not_odd_iff.mp h
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hK2 : 2 < Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have : Nat.card K ≠ 2 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
    omega
  have hVW : finrank K V = finrank K W + 2 := by
    rw [← hR]; exact (Submodule.finrank_add_eq_of_isCompl hcompl).symm
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hσS : ∀ s ∈ supportedFixedDerived Q x, ∀ v, σ (s v) = s (σ v) := fun s hs v =>
    apply_comm_of_mem_supportedFixedDerived hy (commutator_supportedFixedDerived_eq hy hodd hW) α
      hαJ σ hind hs v
  obtain ⟨u, v₀, w, hQu, hQw, huw, hvu, hvw, hw0⟩ :=
    exists_singular_pair_partner hodd (Q.comp W.subtype) hy.polarBilin_fixed_nondegenerate hW
  have huw' : polar Q (u : V) (w : V) = 0 := by rw [← polar_comp_subtype]; exact huw
  have hvu' : polar Q (v₀ : V) (u : V) = 1 := by rw [← polar_comp_subtype]; exact hvu
  have hvw' : polar Q (v₀ : V) (w : V) = 0 := by rw [← polar_comp_subtype]; exact hvw
  have hφ : ∀ s, φ s = s := by
    intro s
    refine ringEquiv_apply_eq_of_commute_eichler (Q := Q) σ φ hσ (u := (u : V)) (v := (v₀ : V))
      (w := (w : V)) hQu hQw huw' hvu' hvw' (fun h => hw0 (Subtype.ext h)) (fun t z => ?_) s
    refine hσS _ (eichler_mem_supportedFixedDerived hy hK u.2 (W.smul_mem t w.2) ?_) z
    rw [polar_smul_right, huw', smul_zero]
  let σL : V ≃ₗ[K] V := σ.toLinearEquiv fun c v => by rw [hσ, hφ]
  have hμ' : ∀ v, Q (σ v) = μ * Q v := fun v => by rw [hμ, hφ]
  have hpolσ : ∀ a b, polar Q (σ a) (σ b) = μ * polar Q a b := fun a b => by
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hμ', hμ', hμ']
    ring
  have hσR : ∀ r ∈ R, σ r ∈ R := by
    intro r hr
    refine mem_othersSpace_of_forall_apply_eq hy hK2 ((by norm_num : (3 : ℕ) ≤ 5).trans hW)
      fun s hs => ?_
    rw [← hσS s hs r, (mem_supportedBlock.mp (supportedFixedDerived_le_supportedBlock hs)).2 r hr]
  have hσRsurj : ∀ r ∈ R, ∃ r₀ ∈ R, σ r₀ = r := by
    have hle : R.map σL.toLinearMap ≤ R := by
      rintro _ ⟨r, hr, rfl⟩
      exact hσR r hr
    have heq : R.map σL.toLinearMap = R :=
      Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq σL R)
    intro r hr
    rw [← heq] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    exact ⟨r₀, hr₀, rfl⟩
  have hσW : ∀ v ∈ W, σL v ∈ W := by
    intro v hv
    refine mem_fixedSpace_of_forall_polar_eq_zero hy fun r hr => ?_
    obtain ⟨r₀, hr₀, rfl⟩ := hσRsurj r hr
    show polar Q (σ v) (σ r₀) = 0
    rw [hpolσ, horth v hv r₀ hr₀, mul_zero]
  let M : W →ₗ[K] W := σL.toLinearMap.restrict hσW
  have hMcomm : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype),
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)⁆,
      M ∘ₗ (g : W →ₗ[K] W) = (g : W →ₗ[K] W) ∘ₗ M := by
    intro g hg
    obtain ⟨s, hs⟩ := restrictFixed_surjective hy g (orthDerived_le_orthogonalGroup' _ hg)
    have hs' : restrictFixed Q x s ∈ orthDerived (Q.comp W.subtype) := hs ▸ hg
    have hsS : (s : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x :=
      mem_supportedFixedDerived.mpr ⟨s.2, hs'⟩
    refine LinearMap.ext fun z => Subtype.ext ?_
    rw [← hs]
    show σ ((s : V ≃ₗ[K] V) z) = (s : V ≃ₗ[K] V) (σ z)
    exact hσS _ hsS z
  obtain ⟨lam, hlam⟩ :=
    ((CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
      hK2 (Q.comp W.subtype) hy.polarBilin_fixed_nondegenerate (by omega)).1 M).mp hMcomm
  have hσlam : ∀ v ∈ W, σ v = lam • v := fun v hv => by
    have h1 := congrArg (fun f : W →ₗ[K] W => ((f ⟨v, hv⟩ : W) : V)) hlam
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul] at h1
    exact h1
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : W, Q (w₁ : V) ≠ 0 :=
    CFSG.ClassicalInvolution.Q3.exists_quadratic_ne_zero hy.polarBilin_fixed_nondegenerate
  have hw₁0 : (w₁ : V) ≠ 0 := fun h => hw₁ (by rw [h, QuadraticMap.map_zero])
  have hlam0 : lam ≠ 0 := by
    intro h
    have h1 := hσlam _ w₁.2
    rw [h, zero_smul] at h1
    exact hw₁0 (σ.injective (by rw [h1, map_zero]))
  have hμlam : μ = lam * lam := by
    have h1 := hμ' (w₁ : V)
    rw [hσlam _ w₁.2, QuadraticMap.map_smul, smul_eq_mul] at h1
    exact (mul_right_cancel₀ hw₁ h1).symm
  set A : V ≃ₗ[K] V := σL.trans (LinearEquiv.smulOfNeZero K V lam⁻¹ (inv_ne_zero hlam0))
    with hAdef
  have hA : ∀ v, A v = lam⁻¹ • σ v := fun v => rfl
  have hAW : ∀ v ∈ W, A v = v := fun v hv => by
    rw [hA, hσlam v hv, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  have hAQ : ∀ v, Q (A v) = Q v := fun v => by
    rw [hA, QuadraticMap.map_smul, hμ', hμlam, smul_eq_mul]
    field_simp
  have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hAQ
  have hAR : ∀ r ∈ R, A r ∈ R := fun r hr => by rw [hA]; exact R.smul_mem _ (hσR r hr)
  have hindA : ∀ g : ↥(orthDerived Q), ∃ g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) (A v) = A ((g : V ≃ₗ[K] V) v)) ∧ α (projT Q g) = projT Q g' := by
    intro g
    obtain ⟨g', hg', hα'⟩ := hind g
    exact ⟨g', fun v => by rw [hA, hA, map_smul, hg'], hα'⟩
  have hAWn : ∀ n : ℕ, ∀ v ∈ W, (A ^ n) v = v := by
    intro n
    induction n with
    | zero => intro v _; rfl
    | succ n ih =>
      intro v hv
      rw [pow_succ', LinearEquiv.mul_apply, ih v hv, hAW v hv]
  have hARn : ∀ n : ℕ, ∀ r ∈ R, (A ^ n) r ∈ R := by
    intro n
    induction n with
    | zero => intro r hr; exact hr
    | succ n ih =>
      intro r hr
      rw [pow_succ', LinearEquiv.mul_apply]
      exact hAR _ (ih r hr)
  have hpowind : ∀ n : ℕ, ∀ g : ↥(orthDerived Q), ∃ g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) ((A ^ n) v) = (A ^ n) ((g : V ≃ₗ[K] V) v)) ∧
        (α ^ n) (projT Q g) = projT Q g' := by
    intro n
    induction n with
    | zero => intro g; exact ⟨g, fun v => rfl, rfl⟩
    | succ n ih =>
      intro g
      obtain ⟨g₁, hg₁, hα₁⟩ := ih g
      obtain ⟨g₂, hg₂, hα₂⟩ := hindA g₁
      refine ⟨g₂, fun v => ?_, ?_⟩
      · rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg₂, hg₁]
      · rw [pow_succ', MulAut.mul_apply, hα₁, hα₂]
  have hAp : A ^ p = 1 := by
    have hcomm : ∀ g ∈ orthDerived Q, ∀ v, (A ^ p) (g v) = g ((A ^ p) v) := by
      intro g hg v
      refine apply_comm_of_perfect (commutator_orthDerived_eq hodd Q hQ (by omega))
        (A ^ p).toAddEquiv (fun g₀ hg₀ => ?_) hg v
      obtain ⟨g', hg', hα'⟩ := hpowind p ⟨g₀, hg₀⟩
      rw [hα, MulAut.one_apply] at hα'
      obtain ⟨c, hc⟩ := exists_smul_of_projT_eq hα'.symm
      have hc0 : c ≠ 0 := by
        rintro rfl
        obtain ⟨v₁, hv₁⟩ := exists_ne (0 : V)
        apply hv₁
        have := hc ((g' : V ≃ₗ[K] V).symm v₁)
        rw [LinearEquiv.apply_symm_apply, zero_smul] at this
        exact this
      refine ⟨c, hc0, fun z => ?_⟩
      calc (A ^ p) (g₀ z) = (g' : V ≃ₗ[K] V) ((A ^ p) z) := (hg' z).symm
        _ = c • g₀ ((A ^ p) z) := hc _
    obtain ⟨c, hc⟩ :=
      ((CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
        hK2 Q hQ (by omega)).1 (A ^ p).toLinearMap).mp
        (fun g hg => LinearMap.ext fun v => hcomm g hg v)
    have hcv : ∀ v, (A ^ p) v = c • v := fun v => by
      have := congrArg (fun f : V →ₗ[K] V => f v) hc
      simpa using this
    have hc1 : c = 1 := by
      have h1 := hcv w₁
      rw [hAWn p _ w₁.2] at h1
      have : (c - 1) • (w₁ : V) = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hw₁0)
    refine LinearEquiv.ext fun v => ?_
    rw [hcv, hc1, one_smul]
    rfl
  have hAinv : A.symm = A ^ (p - 1) := by
    have h1 : A * A ^ (p - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le, hAp]
    exact (inv_eq_of_mul_eq_one_right h1 : A⁻¹ = A ^ (p - 1))
  have hAinvR : ∀ r ∈ R, A.symm r ∈ R := fun r hr => by rw [hAinv]; exact hARn _ r hr
  have hxR : ∀ r ∈ R, x r ∈ R := fun r hr =>
    mem_othersSpace_of_apply (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hr
  have hxinvR : ∀ r ∈ R, x.symm r ∈ R := fun r hr =>
    mem_othersSpace_of_apply (symm_mem_centralizer x
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hr
  set AR : R ≃ₗ[K] R := restrictEquiv R A hAR hAinvR with hARdef
  set xR : R ≃ₗ[K] R := restrictEquiv R x hxR hxinvR with hxRdef
  have hQR := polarBilin_othersSpace_nondegenerate hy
  have hARO : AR ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun r => hAQ r
  have hxRO : xR ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun r =>
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hy.mem) r
  have hrestrict_pow : ∀ (g : V ≃ₗ[K] V) (h1 : ∀ r ∈ R, g r ∈ R) (h2 : ∀ r ∈ R, g.symm r ∈ R)
      (n : ℕ) (r : R), (((restrictEquiv R g h1 h2) ^ n) r : V) = (g ^ n) r := by
    intro g h1 h2 n
    induction n with
    | zero => intro r; rfl
    | succ n ih =>
      intro r
      rw [pow_succ', LinearEquiv.mul_apply, coe_restrictEquiv, ih, pow_succ', LinearEquiv.mul_apply]
  have hARp : AR ^ p = 1 := LinearEquiv.ext fun r => Subtype.ext (by
    rw [hrestrict_pow, hAp]; rfl)
  have hxRp : xR ^ p = 1 := LinearEquiv.ext fun r => Subtype.ext (by
    rw [hrestrict_pow, hy.pow_eq_one]; rfl)
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hdetA := CFSG.ClassicalInvolution.Q3.det_eq_one_of_odd_orderOf h2 hQR hARO
    (hpodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hARp))
  have hdetx := CFSG.ClassicalInvolution.Q3.det_eq_one_of_odd_orderOf h2 hQR hxRO
    (hpodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hxRp))
  have hcommR := CFSG.ClassicalInvolution.Q3.commute_of_det_eq_one_of_finrank_le_two h2 hQR
    hR.le hARO hxRO hdetA hdetx
  have hAx : A * x = x * A := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨w', hw', r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
    simp only [LinearEquiv.mul_apply, map_add]
    rw [mem_fixedSpace.mp hw', hAW w' hw', mem_fixedSpace.mp hw']
    congr 1
    have := congrArg (fun f : R ≃ₗ[K] R => ((f ⟨r, hr⟩ : R) : V)) hcommR
    simpa [hARdef, hxRdef] using this
  have hx1 : x ≠ 1 := by
    intro h1
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (show R ≠ ⊥ from fun h => by rw [h, finrank_bot] at hR; exact absurd hR (by norm_num))
    have hrW : r ∈ W := by rw [mem_fixedSpace, h1]; rfl
    exact hr0 ((Submodule.disjoint_def.mp hcompl.disjoint) r hrW hr)
  have hAz : A ∈ Subgroup.zpowers x := by
    set A' : Subgroup (V ≃ₗ[K] V) := Subgroup.closure ({A, x} : Set (V ≃ₗ[K] V)) with hA'def
    haveI : IsMulCommutative ↥A' := Subgroup.isMulCommutative_closure
      (Set.pairwise_pair.mpr fun _ => ⟨hAx, hAx.symm⟩)
    letI : CommGroup ↥A' := { (inferInstance : Group ↥A') with mul_comm := fun a b => mul_comm' a b }
    have hcommA' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥A') ⟨b, hb⟩)
    have hexp : ∀ g ∈ A', g ^ p = 1 := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        rcases hg with rfl | hg
        · exact hAp
        · rw [Set.mem_singleton_iff.mp hg]; exact hy.pow_eq_one
      | one => exact one_pow p
      | mul a b ha hb iha ihb => rw [(Commute.mul_pow (hcommA' a ha b hb) p), iha, ihb, one_mul]
      | inv a ha iha => rw [inv_pow, iha, inv_one]
    have hA'O : A' ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [Subgroup.closure_le]
      rintro g (rfl | hg)
      · exact hAO
      · rw [Set.mem_singleton_iff.mp hg]; exact hy.mem
    have hA'W : ∀ g ∈ A', ∀ v ∈ W, g v = v := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        rcases hg with rfl | hg
        · exact hAW
        · rw [Set.mem_singleton_iff.mp hg]; exact fun v hv => mem_fixedSpace.mp hv
      | one => exact fun v _ => rfl
      | mul a b ha hb iha ihb =>
        intro v hv
        rw [LinearEquiv.mul_apply, ihb v hv, iha v hv]
      | inv a ha iha =>
        intro v hv
        rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq]
        exact (iha v hv).symm
    haveI : Finite (V ≃ₗ[K] V) := by
      have : Finite V := Module.finite_of_finite K
      exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    let ρ : Representation K ↥A' V :=
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp A'.subtype
    have hρ : Function.Injective ρ := fun a b h => Subtype.ext (LinearEquiv.ext fun v =>
      congrArg (fun f : V →ₗ[K] V => f v) h)
    have hρA : ∀ a : ↥A', a ^ p = 1 := fun a => Subtype.ext (hexp a a.2)
    have hρQ : ∀ (a : ↥A') (v : V), Q (ρ a v) = Q v := fun a v =>
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hA'O a.2)) v
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥A')).mp fun a =>
      ⟨1, by rw [pow_one]; exact hρA a⟩
    obtain ⟨T, -, hTn, hsum, hge, -⟩ :=
      Wt.exists_support ρ hp hρA hy.cast_ne_zero Q hQ h2 hρQ hp2 hρ hn
    have hfix : finrank K W ≤ finrank K (Wt.fixedSpace ρ ⊤) := by
      refine Submodule.finrank_mono fun v hv => ?_
      exact (Wt.mem_fixedSpace ρ).mpr fun a _ => hA'W a a.2 v hv
    have hge2 := Finset.card_nsmul_le_sum T _ 2 hge
    rw [smul_eq_mul] at hge2
    have hn1 : n ≤ 1 := by omega
    have hcardA' : Nat.card ↥A' ≤ p := by
      rw [hn]
      calc p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hn1
        _ = p := pow_one p
    have hxA' : x ∈ A' := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hzp : Subgroup.zpowers x = A' := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxA') ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hy.pow_eq_one hx1]
      exact hcardA'
    rw [hzp]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hAz
  refine ⟨k, MulEquiv.ext fun t => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective ((scalars K V).subgroupOf (orthDerived Q)) t
  obtain ⟨g', hg', hα'⟩ := hindA g
  have hg'eq : g' = y ^ k * g * (y ^ k)⁻¹ := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have h1 := hg' (A.symm v)
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [h1, ← hk]
    simp [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, hxdef]
  change α (projT Q g) = _
  rw [hα', hg'eq, map_mul, map_mul, map_inv, map_zpow, MulAut.conj_apply]

end Main

end CFSG.LocalAnalysis.GLTheoremA.H81Orth
