module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAmalgam

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance e6PilotAmalgamWeylNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

namespace E6Neighbour

@[expose] def word : E6Neighbour → List (Fin (Tag.rank .E6))
  | high => []
  | six => [4, 3, 2, 1, 3, 4, 0, 2, 3, 1]
  | three => [3, 4, 5, 1, 3, 4, 0, 2, 3, 1]

noncomputable abbrev weyl (N : E6Neighbour) : WeylGroup .E6 :=
  (coxeterSystem .E6).wordProd N.word

theorem weyl_smul_highRoot (N : E6Neighbour) : N.weyl • highRoot .E6 = N.root := by
  cases N
  · simp only [weyl, word, CoxeterSystem.wordProd_nil, one_smul]
    rfl
  · simp only [weyl, word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
      mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  · simp only [weyl, word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
      mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)

end E6Neighbour

open E6Neighbour

section Weyl


theorem image_smul_orthRoots (w : WeylGroup .E6) (θ : Fin (Tag.rank .E6) → ℤ) :
    (fun α => w • α) '' orthRoots θ = orthRoots (w • θ) := by
  ext γ
  constructor
  · rintro ⟨α, ⟨hα, h0⟩, rfl⟩
    exact ⟨IsRoot.smul hα w, by rw [iform_smul, h0]⟩
  · rintro ⟨hγ, h0⟩
    refine ⟨w⁻¹ • γ, ⟨(isRoot_smul_iff w⁻¹).2 hγ, ?_⟩, smul_inv_smul w γ⟩
    rw [← iform_smul w, smul_inv_smul, h0]

theorem image_weyl_orthRoots_highRoot (N : E6Neighbour) :
    (fun α => N.weyl • α) '' orthRoots (highRoot .E6) = orthRoots N.root := by
  rw [image_smul_orthRoots, weyl_smul_highRoot]

end Weyl

section Rep


namespace E6Neighbour

variable (K : Type) [Field K]

@[expose] noncomputable def rep (N : E6Neighbour) : adjointGroup .E6 K :=
  (N.word.map (CFSG.LieType.Chevalley.weylElement .E6 K)).prod

variable {K}

theorem coe_rep (N : E6Neighbour) :
    (N.rep K : ModGL .E6 K) = (N.word.map fun i => weylElt .E6 K i 1).prod := by
  rw [rep, ← Subgroup.coe_subtype, map_list_prod, List.map_map]
  rfl

end E6Neighbour

variable {K : Type} [Field K]


theorem map_conj_rep_rootSubgroup (N : E6Neighbour) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) :
    (rootSubgroup .E6 K γ).map (MulAut.conj (N.rep K : ModGL .E6 K)).toMonoidHom =
      rootSubgroup .E6 K (N.weyl • γ) := by
  rw [coe_rep]
  exact map_conj_prod_weylElt_rootSubgroup K N.word hγ

theorem map_conj_rep_rootSpan (N : E6Neighbour) {S : Set (Fin (Tag.rank .E6) → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot .E6 γ) :
    (rootSpan .E6 K S).map (MulAut.conj (N.rep K : ModGL .E6 K)).toMonoidHom =
      rootSpan .E6 K ((fun α => N.weyl • α) '' S) := by
  simp only [rootSpan, Subgroup.map_iSup, iSup_image]
  exact iSup_congr fun γ => iSup_congr fun hγ => map_conj_rep_rootSubgroup N (hS γ hγ)

theorem map_conj_map_subtype_E6 (H : Subgroup (adjointGroup .E6 K)) (n : adjointGroup .E6 K) :
    (H.map (MulAut.conj n).toMonoidHom).map (adjointGroup .E6 K).subtype =
      (H.map (adjointGroup .E6 K).subtype).map (MulAut.conj (n : ModGL .E6 K)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_conj_rep_subgroupOf_rootSpan (N : E6Neighbour) {S : Set (Fin (Tag.rank .E6) → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot .E6 γ) :
    ((rootSpan .E6 K S).subgroupOf (adjointGroup .E6 K)).map
        (MulAut.conj (N.rep K)).toMonoidHom =
      (rootSpan .E6 K ((fun α => N.weyl • α) '' S)).subgroupOf (adjointGroup .E6 K) := by
  apply Subgroup.map_injective (adjointGroup .E6 K).subtype_injective
  rw [map_conj_map_subtype_E6, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (rootSpan_le_adjointGroup_E6 S),
    inf_of_le_left (rootSpan_le_adjointGroup_E6 _), map_conj_rep_rootSpan N hS]

theorem map_conj_rep_a5Levi (N : E6Neighbour) :
    (a5Levi K).map (MulAut.conj (N.rep K)).toMonoidHom = N.levi K := by
  rw [← levi_high, levi, map_conj_rep_subgroupOf_rootSpan N fun γ hγ => hγ.1, root,
    image_weyl_orthRoots_highRoot]
  rfl

theorem map_conj_rep_rootSubgroup_sup (N : E6Neighbour) :
    (rootSubgroup .E6 K (highRoot .E6) ⊔ rootSubgroup .E6 K (-highRoot .E6)).map
        (MulAut.conj (N.rep K : ModGL .E6 K)).toMonoidHom =
      rootSubgroup .E6 K N.root ⊔ rootSubgroup .E6 K (-N.root) := by
  rw [Subgroup.map_sup, map_conj_rep_rootSubgroup N (isRoot_highRoot _),
    map_conj_rep_rootSubgroup N (IsRoot.neg (isRoot_highRoot _)), smul_neg, weyl_smul_highRoot]

theorem map_conj_rep_rootSL2 (N : E6Neighbour) :
    ((rootSubgroup .E6 K (highRoot .E6) ⊔ rootSubgroup .E6 K (-highRoot .E6)).subgroupOf
        (adjointGroup .E6 K)).map (MulAut.conj (N.rep K)).toMonoidHom =
      (rootSubgroup .E6 K N.root ⊔ rootSubgroup .E6 K (-N.root)).subgroupOf
        (adjointGroup .E6 K) := by
  have hle : ∀ γ : Fin (Tag.rank .E6) → ℤ,
      rootSubgroup .E6 K γ ⊔ rootSubgroup .E6 K (-γ) ≤ adjointGroup .E6 K :=
    fun γ => sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ))
  apply Subgroup.map_injective (adjointGroup .E6 K).subtype_injective
  rw [map_conj_map_subtype_E6, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (hle _), inf_of_le_left (hle _), map_conj_rep_rootSubgroup_sup]

end Rep

end CFSG.SeitzReduction.E6Pilot
