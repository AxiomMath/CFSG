module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAmalgam

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance e8PilotAmalgamWeylNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

namespace E8Neighbour

@[expose] def word : E8Neighbour → List (Fin (Tag.rank .E8))
  | high => []
  | two => [3, 2, 0, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7]
  | six => [4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7]

noncomputable abbrev weyl (N : E8Neighbour) : WeylGroup .E8 :=
  (coxeterSystem .E8).wordProd N.word

theorem weyl_smul_highRoot (N : E8Neighbour) : N.weyl • highRoot .E8 = N.root := by
  cases N
  · simp only [weyl, word, CoxeterSystem.wordProd_nil, one_smul]
    rfl
  · simp only [weyl, word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
      mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  · simp only [weyl, word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
      mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)

end E8Neighbour

open E8Neighbour

section Weyl


theorem image_smul_orthRoots (w : WeylGroup .E8) (θ : Fin (Tag.rank .E8) → ℤ) :
    (fun α => w • α) '' orthRoots θ = orthRoots (w • θ) := by
  ext γ
  constructor
  · rintro ⟨α, ⟨hα, h0⟩, rfl⟩
    exact ⟨IsRoot.smul hα w, by rw [iform_smul, h0]⟩
  · rintro ⟨hγ, h0⟩
    refine ⟨w⁻¹ • γ, ⟨(isRoot_smul_iff w⁻¹).2 hγ, ?_⟩, smul_inv_smul w γ⟩
    rw [← iform_smul w, smul_inv_smul, h0]

theorem image_weyl_orthRoots_highRoot (N : E8Neighbour) :
    (fun α => N.weyl • α) '' orthRoots (highRoot .E8) = orthRoots N.root := by
  rw [image_smul_orthRoots, weyl_smul_highRoot]

end Weyl

section Rep


namespace E8Neighbour

variable (K : Type) [Field K]

@[expose] noncomputable def rep (N : E8Neighbour) : adjointGroup .E8 K :=
  (N.word.map (CFSG.LieType.Chevalley.weylElement .E8 K)).prod

variable {K}

theorem coe_rep (N : E8Neighbour) :
    (N.rep K : ModGL .E8 K) = (N.word.map fun i => weylElt .E8 K i 1).prod := by
  rw [rep, ← Subgroup.coe_subtype, map_list_prod, List.map_map]
  rfl

end E8Neighbour

variable {K : Type} [Field K]


theorem map_conj_rep_rootSubgroup (N : E8Neighbour) {γ : Fin (Tag.rank .E8) → ℤ}
    (hγ : IsRoot .E8 γ) :
    (rootSubgroup .E8 K γ).map (MulAut.conj (N.rep K : ModGL .E8 K)).toMonoidHom =
      rootSubgroup .E8 K (N.weyl • γ) := by
  rw [coe_rep]
  exact map_conj_prod_weylElt_rootSubgroup K N.word hγ

theorem map_conj_rep_rootSpan (N : E8Neighbour) {S : Set (Fin (Tag.rank .E8) → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot .E8 γ) :
    (rootSpan .E8 K S).map (MulAut.conj (N.rep K : ModGL .E8 K)).toMonoidHom =
      rootSpan .E8 K ((fun α => N.weyl • α) '' S) := by
  simp only [rootSpan, Subgroup.map_iSup, iSup_image]
  exact iSup_congr fun γ => iSup_congr fun hγ => map_conj_rep_rootSubgroup N (hS γ hγ)

theorem map_conj_map_subtype_E8 (H : Subgroup (adjointGroup .E8 K)) (n : adjointGroup .E8 K) :
    (H.map (MulAut.conj n).toMonoidHom).map (adjointGroup .E8 K).subtype =
      (H.map (adjointGroup .E8 K).subtype).map (MulAut.conj (n : ModGL .E8 K)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_conj_rep_subgroupOf_rootSpan (N : E8Neighbour) {S : Set (Fin (Tag.rank .E8) → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot .E8 γ) :
    ((rootSpan .E8 K S).subgroupOf (adjointGroup .E8 K)).map
        (MulAut.conj (N.rep K)).toMonoidHom =
      (rootSpan .E8 K ((fun α => N.weyl • α) '' S)).subgroupOf (adjointGroup .E8 K) := by
  apply Subgroup.map_injective (adjointGroup .E8 K).subtype_injective
  rw [map_conj_map_subtype_E8, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (rootSpan_le_adjointGroup_E8 S),
    inf_of_le_left (rootSpan_le_adjointGroup_E8 _), map_conj_rep_rootSpan N hS]

theorem map_conj_rep_e7Levi (N : E8Neighbour) :
    (e7Levi K).map (MulAut.conj (N.rep K)).toMonoidHom = N.levi K := by
  rw [← levi_high, levi, map_conj_rep_subgroupOf_rootSpan N fun γ hγ => hγ.1, root,
    image_weyl_orthRoots_highRoot]
  rfl

theorem map_conj_rep_rootSubgroup_sup (N : E8Neighbour) :
    (rootSubgroup .E8 K (highRoot .E8) ⊔ rootSubgroup .E8 K (-highRoot .E8)).map
        (MulAut.conj (N.rep K : ModGL .E8 K)).toMonoidHom =
      rootSubgroup .E8 K N.root ⊔ rootSubgroup .E8 K (-N.root) := by
  rw [Subgroup.map_sup, map_conj_rep_rootSubgroup N (isRoot_highRoot _),
    map_conj_rep_rootSubgroup N (IsRoot.neg (isRoot_highRoot _)), smul_neg, weyl_smul_highRoot]

theorem map_conj_rep_rootSL2 (N : E8Neighbour) :
    ((rootSubgroup .E8 K (highRoot .E8) ⊔ rootSubgroup .E8 K (-highRoot .E8)).subgroupOf
        (adjointGroup .E8 K)).map (MulAut.conj (N.rep K)).toMonoidHom =
      (rootSubgroup .E8 K N.root ⊔ rootSubgroup .E8 K (-N.root)).subgroupOf
        (adjointGroup .E8 K) := by
  have hle : ∀ γ : Fin (Tag.rank .E8) → ℤ,
      rootSubgroup .E8 K γ ⊔ rootSubgroup .E8 K (-γ) ≤ adjointGroup .E8 K :=
    fun γ => sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ))
  apply Subgroup.map_injective (adjointGroup .E8 K).subtype_injective
  rw [map_conj_map_subtype_E8, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (hle _), inf_of_le_left (hle _), map_conj_rep_rootSubgroup_sup]

end Rep

end CFSG.SeitzReduction.E8Pilot
