module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem y7b_exists_perm3_hom {X M U : Subgroup G} (hMU : M ≤ U)
    (hUM : ∀ u ∈ U, ∀ m ∈ M, u * m * u⁻¹ ∈ M)
    (hXU : ∀ x ∈ X, ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hXM : ∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (h4 : M.relIndex U = 4) (hsq : ∀ u ∈ U, u ^ 2 ∈ M) :
    ∃ ρ : ↥X →* Equiv.Perm (Fin 3), ∀ x : ↥X, ρ x = 1 ↔ ∀ u ∈ U, ⁅(x : G), u⁆ ∈ M := by
  classical
  let N : Subgroup ↥U := M.subgroupOf U
  have hN : N.Normal :=
    (Subgroup.normal_subgroupOf_iff hMU).mpr fun m u hm hu => hUM u hu m hm
  haveI : N.Normal := hN
  have hN4 : N.index = 4 := by simpa only [N, Subgroup.relIndex] using h4
  haveI hNfi : N.FiniteIndex := ⟨by omega⟩
  haveI : Fintype (↥U ⧸ N) := N.fintypeQuotientOfFiniteIndex
  have hcardQ : Nat.card (↥U ⧸ N) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact hN4
  let cx : ↥X →* MulAut ↥U := MonoidHom.mk'
    (fun x =>
      { toFun := fun u => ⟨(x : G) * (u : G) * (x : G)⁻¹, hXU x x.2 u u.2⟩
        invFun := fun u => ⟨(x : G)⁻¹ * (u : G) * (x : G),
          by simpa only [inv_inv] using hXU x⁻¹ (X.inv_mem x.2) u u.2⟩
        left_inv := by intro u; exact Subtype.ext (by push_cast; group)
        right_inv := by intro u; exact Subtype.ext (by push_cast; group)
        map_mul' := by intro u v; exact Subtype.ext (by push_cast; group) })
    (by
      intro x y
      refine MulEquiv.ext fun u => ?_
      rw [MulAut.mul_apply]
      exact Subtype.ext (by
        change (x : G) * (y : G) * (u : G) * ((x : G) * (y : G))⁻¹ =
          (x : G) * ((y : G) * (u : G) * (y : G)⁻¹) * (x : G)⁻¹
        group))
  have hcxN (x : ↥X) : N.map ((cx x).toMonoidHom) = N := by
    apply le_antisymm
    · intro u hu
      rw [Subgroup.mem_map] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      rw [Subgroup.mem_subgroupOf] at hv ⊢
      exact hXM x x.2 v.val hv
    · intro u hu
      rw [Subgroup.mem_map]
      refine ⟨(cx x).symm u, ?_, (cx x).apply_symm_apply u⟩
      rw [Subgroup.mem_subgroupOf] at hu ⊢
      change (x : G)⁻¹ * (u : G) * (x : G) ∈ M
      simpa only [inv_inv] using hXM x⁻¹ (X.inv_mem x.2) (u : G) hu
  let φ : ↥X →* MulAut (↥U ⧸ N) := MonoidHom.mk'
    (fun x => QuotientGroup.congr N N (cx x) (hcxN x))
    (by
      intro x y
      refine MulEquiv.ext fun v => ?_
      induction v using QuotientGroup.induction_on with
      | H s =>
        change (⟦(cx (x * y)) s⟧ : ↥U ⧸ N) = ⟦(cx x) ((cx y) s)⟧
        rw [map_mul, MulAut.mul_apply])
  let S := {q : ↥U ⧸ N // q ≠ 1}
  haveI : Fintype S := inferInstance
  have hcardS : Fintype.card S = 3 := by
    have h := Fintype.card_subtype_compl (fun q : ↥U ⧸ N => q = 1)
    rw [Fintype.card_subtype_eq] at h
    have hQ : Fintype.card (↥U ⧸ N) = 4 := by
      rw [← Nat.card_eq_fintype_card]; exact hcardQ
    simpa only [hQ, S] using h
  let e3 : S ≃ Fin 3 := Fintype.equivFinOfCardEq hcardS
  let π : MulAut (↥U ⧸ N) →* Equiv.Perm S := MonoidHom.mk'
    (fun f => (f : (↥U ⧸ N) ≃ (↥U ⧸ N)).subtypeEquiv
      (fun q => (MulEquiv.map_eq_one_iff f).not.symm))
    (by intro f g; ext s; rfl)
  let ρ : ↥X →* Equiv.Perm (Fin 3) :=
    (e3.permCongrHom.toMonoidHom).comp (π.comp φ)
  refine ⟨ρ, fun x => ?_⟩
  have hφ1 : φ x = 1 ↔ ∀ q : ↥U ⧸ N, φ x q = q := by
    constructor
    · intro h q; rw [h]; rfl
    · intro h; ext q; exact h q
  have hq (u : ↥U) : φ x ⟦u⟧ = ⟦u⟧ ↔ ⁅(x : G), (u : G)⁆ ∈ M := by
    rw [show φ x (⟦u⟧ : ↥U ⧸ N) = ⟦(cx x) u⟧ from rfl]
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have h2 : (((cx x) u / u : ↥U) : G) = ⁅(x : G), (u : G)⁆ := by
      rw [commutatorElement_def]
      simp [cx, Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [div_eq_mul_inv]
    rw [h2]
  have hqall : (∀ q : ↥U ⧸ N, φ x q = q) ↔ ∀ u : ↥U, ⁅(x : G), (u : G)⁆ ∈ M := by
    constructor
    · intro h u; exact (hq u).mp (h ⟦u⟧)
    · intro h q
      refine QuotientGroup.induction_on q (fun u => ?_)
      exact (hq u).mpr (h u)
  have hπ1 : π (φ x) = 1 ↔ φ x = 1 := by
    constructor
    · intro h
      ext q
      by_cases hq1 : q = 1
      · subst hq1; simp
      · have h2 := congrArg (fun g : Equiv.Perm S => g ⟨q, hq1⟩) h
        exact congrArg Subtype.val h2
    · intro h; rw [h, map_one]
  have hτ1 : e3.permCongrHom (π (φ x)) = 1 ↔ π (φ x) = 1 :=
    MulEquiv.map_eq_one_iff e3.permCongrHom
  change e3.permCongrHom (π (φ x)) = 1 ↔ ∀ u ∈ U, ⁅(x : G), u⁆ ∈ M
  rw [hτ1, hπ1, hφ1, hqall]
  exact Subtype.forall

end CFSG.OddStandard.HigherRank.YamadaG23
