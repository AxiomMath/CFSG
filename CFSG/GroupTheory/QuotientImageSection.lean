module

public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

theorem exists_normal_quotientEquiv_map (K : Subgroup G) [K.Normal] (A : Subgroup G)
    (N : Subgroup ↥A) [N.Normal] (hN : ∀ a : ↥A, (a : G) ∈ K → a ∈ N) :
    ∃ N' : Subgroup ↥(A.map (QuotientGroup.mk' K)), ∃ _ : N'.Normal,
      Nonempty ((↥(A.map (QuotientGroup.mk' K)) ⧸ N') ≃* (↥A ⧸ N)) := by
  classical
  let f : ↥A →* ↥(A.map (QuotientGroup.mk' K)) :=
    { toFun := fun a => ⟨QuotientGroup.mk' K (a : G), Subgroup.mem_map_of_mem _ a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨a, ha⟩, rfl⟩
  have hker : f.ker = K.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : QuotientGroup.mk' K (a : G) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff (a : G)).mp h1
    · intro ha
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (a : G)).mpr ha
  let e1 : (↥A ⧸ K.subgroupOf A) ≃* ↥(A.map (QuotientGroup.mk' K)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hle : K.subgroupOf A ≤ N := fun a ha => hN a ha
  let N' : Subgroup ↥(A.map (QuotientGroup.mk' K)) :=
    (N.map (QuotientGroup.mk' (K.subgroupOf A))).map e1.toMonoidHom
  have hN' : N'.Normal :=
    ((inferInstance : N.Normal).map (QuotientGroup.mk' (K.subgroupOf A))
      (QuotientGroup.mk'_surjective (K.subgroupOf A))).map e1.toMonoidHom e1.surjective
  refine ⟨N', hN', ?_⟩
  let e2 : ((↥A ⧸ K.subgroupOf A) ⧸
      (N.map (QuotientGroup.mk' (K.subgroupOf A)))) ≃* (↥A ⧸ N) :=
    QuotientGroup.quotientQuotientEquivQuotient (K.subgroupOf A) N hle
  let e3 : ((↥A ⧸ K.subgroupOf A) ⧸
      (N.map (QuotientGroup.mk' (K.subgroupOf A)))) ≃*
      (↥(A.map (QuotientGroup.mk' K)) ⧸ N') :=
    QuotientGroup.congr (N.map (QuotientGroup.mk' (K.subgroupOf A))) N' e1 rfl
  exact ⟨e3.symm.trans e2⟩

end CFSG.GroupTheory
