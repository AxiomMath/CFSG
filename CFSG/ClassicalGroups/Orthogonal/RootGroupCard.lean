module

public import Mathlib.FieldTheory.Finiteness
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem sq_eq_one_of_mem_rootGroup (h2 : (2 : K) = 0) {u : V} {g : V ≃ₗ[K] V}
    (hg : g ∈ rootGroup Q u) : g * g = 1 := by
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  rw [eichler_mul hw hw, ← two_smul K w, h2, zero_smul, eichler_zero_right]

theorem polar_apply_eichler_self {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (y : V) :
    polar Q y (eichler Q u w y) = 2 * Q y - Q w * polar Q y u ^ 2 := by
  rw [eichler_apply hu hw, polar_sub_right, polar_add_right, polar_smul_right_eq,
    polar_smul_right_eq, polar_self_eq_two_mul]
  ring

private theorem eq_add_smul_of_smul_sub_eq {a : K} (ha : a ≠ 0) {w w' u : V} {d : K}
    (h : a • w' - a • w = d • u) : w' = w + (a⁻¹ * d) • u := by
  have h0 : a • (w' - (w + (a⁻¹ * d) • u)) = 0 := by
    rw [smul_sub, smul_add, smul_smul, mul_inv_cancel_left₀ ha, ← h]
    abel
  exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_left ha)

theorem eichler_eq_eichler_iff (hQ : (polarBilin Q).Nondegenerate) {u w w' : V} (hu : Q u = 0)
    (hu0 : u ≠ 0) (hw : polar Q u w = 0) (hw' : polar Q u w' = 0) :
    eichler Q u w = eichler Q u w' ↔ ∃ c : K, w' = w + c • u := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ : ∃ y, polar Q y u ≠ 0 := by
      obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hu0
      exact ⟨y, by rwa [polar_comm]⟩
    have hyw := DFunLike.congr_fun h y
    rw [eichler_apply hu hw, eichler_apply hu hw'] at hyw
    have h1 : polar Q y u • w' - polar Q y u • w =
        (polar Q y w' + Q w' * polar Q y u - (polar Q y w + Q w * polar Q y u)) • u := by
      linear_combination (norm := module) hyw.symm
    exact ⟨_, eq_add_smul_of_smul_sub_eq hy h1⟩
  · rintro ⟨c, rfl⟩
    exact (eichler_add_smul_self hu w c).symm

private theorem finrank_perp [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (P : HypPair Q) : Module.finrank K P.perp = Module.finrank K V - 2 := by
  have hli : LinearIndependent K ![P.e, P.f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (polar Q P.f) hst
    have h2 := congrArg (polar Q P.e) hst
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_fe, P.polar_ff,
      polar_zero_right, mul_one, mul_zero, add_zero] at h1
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ee, P.polar_ef,
      polar_zero_right, mul_zero, mul_one, zero_add] at h2
    exact ⟨h1, h2⟩
  have hperp : P.perp = LinearMap.BilinForm.orthogonal (polarBilin Q)
      (Submodule.span K (Set.range ![P.e, P.f])) := by
    ext x
    rw [HypPair.mem_perp, LinearMap.BilinForm.orthogonal, Submodule.mem_orthogonalBilin_span]
    simp
    exact and_comm
  have hspan : Module.finrank K (Submodule.span K (Set.range ![P.e, P.f])) = 2 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  rw [hperp, LinearMap.BilinForm.finrank_orthogonal hQ, hspan]

private theorem eichler_injective_perp (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {x y : V} (hx : x ∈ P.perp) (hy : y ∈ P.perp)
    (hxy : eichler Q P.e x = eichler Q P.e y) : x = y := by
  obtain ⟨c, rfl⟩ := (eichler_eq_eichler_iff hQ P.Q_e P.e_ne_zero
    (HypPair.mem_perp.mp hx).1 (HypPair.mem_perp.mp hy).1).mp hxy
  have hc : c = 0 := by
    have h := (HypPair.mem_perp.mp hy).2
    rw [polar_add_right, polar_smul_right_eq, (HypPair.mem_perp.mp hx).2, P.polar_fe, mul_one,
      zero_add] at h
    exact h
  rw [hc, zero_smul, add_zero]

private theorem exists_perp_eichler_eq (P : HypPair Q) {w : V} (hw : polar Q P.e w = 0) :
    ∃ x ∈ P.perp, eichler Q P.e x = eichler Q P.e w := by
  have hw' : polar Q w P.e = 0 := by rwa [polar_comm]
  have h := P.eq_add_proj w
  rw [hw', zero_smul, add_zero] at h
  have h3 : P.proj w + polar Q w P.f • P.e = w := (add_comm _ _).trans h.symm
  refine ⟨P.proj w, P.proj_mem_perp w, ?_⟩
  have h2 := eichler_add_smul_self P.Q_e (P.proj w) (polar Q w P.f)
  rw [h3] at h2
  exact h2.symm

theorem card_rootGroup [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {u : V} (hu : Q u = 0) (hu0 : u ≠ 0) :
    Nat.card (rootGroup Q u) = Nat.card K ^ (Module.finrank K V - 2) := by
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hu hu0
  let f : P.perp → rootGroup Q P.e := fun x =>
    ⟨eichler Q P.e x, eichler_mem_rootGroup (HypPair.mem_perp.mp x.2).1⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => Subtype.ext ?_, fun g => ?_⟩
    · exact eichler_injective_perp hQ P x.2 y.2 (congrArg Subtype.val hxy)
    · obtain ⟨w, hw, hwg⟩ := mem_rootGroup.mp g.2
      obtain ⟨x, hx, hxw⟩ := exists_perp_eichler_eq P hw
      exact ⟨⟨x, hx⟩, Subtype.ext (hxw.trans hwg)⟩
  have hcard : Nat.card P.perp = Nat.card K ^ Module.finrank K P.perp :=
    Module.natCard_eq_pow_finrank
  rw [← Nat.card_eq_of_bijective f hf, hcard, finrank_perp hQ P]

end CFSG.ClassicalGroups.Orthogonal
