module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAmalgam

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance e7PilotAmalgamWeylNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

namespace E7Neighbour

@[expose] def word : E7Neighbour → List (Fin (Tag.rank .E7))
  | high => []
  | seven => [5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0]
  | four => [1, 2, 0, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0]

noncomputable abbrev weyl (N : E7Neighbour) : WeylGroup .E7 :=
  (coxeterSystem .E7).wordProd N.word

theorem weyl_smul_highRoot (N : E7Neighbour) : N.weyl • highRoot .E7 = N.root := by
  cases N
  · simp only [weyl, word, CoxeterSystem.wordProd_nil, one_smul]
    rfl
  · simp only [weyl, word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
      mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  · simp only [weyl, word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
      mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)

end E7Neighbour

open E7Neighbour

section Weyl


theorem image_smul_orthRoots (w : WeylGroup .E7) (θ : Fin (Tag.rank .E7) → ℤ) :
    (fun α => w • α) '' orthRoots θ = orthRoots (w • θ) := by
  ext γ
  constructor
  · rintro ⟨α, ⟨hα, h0⟩, rfl⟩
    exact ⟨IsRoot.smul hα w, by rw [iform_smul, h0]⟩
  · rintro ⟨hγ, h0⟩
    refine ⟨w⁻¹ • γ, ⟨(isRoot_smul_iff w⁻¹).2 hγ, ?_⟩, smul_inv_smul w γ⟩
    rw [← iform_smul w, smul_inv_smul, h0]

theorem image_weyl_orthRoots_highRoot (N : E7Neighbour) :
    (fun α => N.weyl • α) '' orthRoots (highRoot .E7) = orthRoots N.root := by
  rw [image_smul_orthRoots, weyl_smul_highRoot]

end Weyl

section Rep


namespace E7Neighbour

variable (K : Type) [Field K]

@[expose] noncomputable def rep (N : E7Neighbour) : adjointGroup .E7 K :=
  (N.word.map (CFSG.LieType.Chevalley.weylElement .E7 K)).prod

variable {K}

theorem coe_rep (N : E7Neighbour) :
    (N.rep K : ModGL .E7 K) = (N.word.map fun i => weylElt .E7 K i 1).prod := by
  rw [rep, ← Subgroup.coe_subtype, map_list_prod, List.map_map]
  rfl

end E7Neighbour

variable {K : Type} [Field K]


theorem map_conj_rep_rootSubgroup (N : E7Neighbour) {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : IsRoot .E7 γ) :
    (rootSubgroup .E7 K γ).map (MulAut.conj (N.rep K : ModGL .E7 K)).toMonoidHom =
      rootSubgroup .E7 K (N.weyl • γ) := by
  rw [coe_rep]
  exact map_conj_prod_weylElt_rootSubgroup K N.word hγ

theorem map_conj_rep_rootSpan (N : E7Neighbour) {S : Set (Fin (Tag.rank .E7) → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot .E7 γ) :
    (rootSpan .E7 K S).map (MulAut.conj (N.rep K : ModGL .E7 K)).toMonoidHom =
      rootSpan .E7 K ((fun α => N.weyl • α) '' S) := by
  simp only [rootSpan, Subgroup.map_iSup, iSup_image]
  exact iSup_congr fun γ => iSup_congr fun hγ => map_conj_rep_rootSubgroup N (hS γ hγ)

theorem map_conj_map_subtype_E7 (H : Subgroup (adjointGroup .E7 K)) (n : adjointGroup .E7 K) :
    (H.map (MulAut.conj n).toMonoidHom).map (adjointGroup .E7 K).subtype =
      (H.map (adjointGroup .E7 K).subtype).map (MulAut.conj (n : ModGL .E7 K)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_conj_rep_subgroupOf_rootSpan (N : E7Neighbour) {S : Set (Fin (Tag.rank .E7) → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot .E7 γ) :
    ((rootSpan .E7 K S).subgroupOf (adjointGroup .E7 K)).map
        (MulAut.conj (N.rep K)).toMonoidHom =
      (rootSpan .E7 K ((fun α => N.weyl • α) '' S)).subgroupOf (adjointGroup .E7 K) := by
  apply Subgroup.map_injective (adjointGroup .E7 K).subtype_injective
  rw [map_conj_map_subtype_E7, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (EPilot.rootSpan_le_adjointGroup' S),
    inf_of_le_left (EPilot.rootSpan_le_adjointGroup' _), map_conj_rep_rootSpan N hS]

theorem map_conj_rep_perpLevi (N : E7Neighbour) :
    (EPilot.perpLevi .E7 K).map (MulAut.conj (N.rep K)).toMonoidHom = N.levi K := by
  rw [← levi_high, levi, map_conj_rep_subgroupOf_rootSpan N fun γ hγ => hγ.1, root,
    image_weyl_orthRoots_highRoot]
  rfl

theorem map_conj_rep_rootSubgroup_sup (N : E7Neighbour) :
    (rootSubgroup .E7 K (highRoot .E7) ⊔ rootSubgroup .E7 K (-highRoot .E7)).map
        (MulAut.conj (N.rep K : ModGL .E7 K)).toMonoidHom =
      rootSubgroup .E7 K N.root ⊔ rootSubgroup .E7 K (-N.root) := by
  rw [Subgroup.map_sup, map_conj_rep_rootSubgroup N (isRoot_highRoot _),
    map_conj_rep_rootSubgroup N (IsRoot.neg (isRoot_highRoot _)), smul_neg, weyl_smul_highRoot]

theorem map_conj_rep_rootSL2 (N : E7Neighbour) :
    ((rootSubgroup .E7 K (highRoot .E7) ⊔ rootSubgroup .E7 K (-highRoot .E7)).subgroupOf
        (adjointGroup .E7 K)).map (MulAut.conj (N.rep K)).toMonoidHom =
      (rootSubgroup .E7 K N.root ⊔ rootSubgroup .E7 K (-N.root)).subgroupOf
        (adjointGroup .E7 K) := by
  have hle : ∀ γ : Fin (Tag.rank .E7) → ℤ,
      rootSubgroup .E7 K γ ⊔ rootSubgroup .E7 K (-γ) ≤ adjointGroup .E7 K :=
    fun γ => sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ))
  apply Subgroup.map_injective (adjointGroup .E7 K).subtype_injective
  rw [map_conj_map_subtype_E7, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (hle _), inf_of_le_left (hle _), map_conj_rep_rootSubgroup_sup]

end Rep

end CFSG.SeitzReduction.E7Pilot
