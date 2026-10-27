module

public import CFSG.LieType.Chevalley.GraphFixedBorelOvergroups
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

variable (t K σ) in
@[expose] def orbitRankOneGroup
    (a : Fin t.foldedTag.rank) : Subgroup (ModGL t.tag K) :=
  Subgroup.closure (Set.range (fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K)) ∪
    Set.range (fun c : orbitField t K σ a => (orbitY t K σ a c : ModGL t.tag K)))

theorem orbitN_one_mem_orbitRankOneGroup
    (a : Fin t.foldedTag.rank) :
    (orbitN t K σ a 1 : ModGL t.tag K) ∈ orbitRankOneGroup t K σ a := by
  rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
    (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩))) (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))

theorem canonicalRep_list_prod_orbitReflection :
    ∀ ω : List (Fin t.foldedTag.rank),
      ω.length = t.orbitLength (ω.map t.orbitReflection).prod →
        canonicalRep (coxeterSystem t.tag) K (ω.map t.orbitReflection).prod =
          (ω.map fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)).prod
  | [], _ => by rw [List.map_nil, List.prod_nil, List.map_nil, List.prod_nil, canonicalRep_one]
  | a :: ω, hlen => by
    set w' := (ω.map t.orbitReflection).prod
    have hw' : w' ∈ relWeylTwist t := t.list_prod_orbitReflection_mem ω
    have hww' : ((a :: ω).map t.orbitReflection).prod = t.orbitReflection a * w' := by
      rw [List.map_cons, List.prod_cons]
    rw [hww', List.length_cons] at hlen
    have hle : t.orbitLength w' ≤ ω.length := orbitLength_le t ω
    have hle' := orbitLength_orbitReflection_mul_le hw' a
    have hlen' : ω.length = t.orbitLength w' := by omega
    have hup : t.orbitLength (t.orbitReflection a * w') = t.orbitLength w' + 1 := by omega
    have hpos := forall_height_inv_smul_pos_of_orbitLength hw' hup
    have hl := (length_orbitReflection_mul_of_pos t hw' hpos).2
    have hadd : (coxeterSystem t.tag).length (t.orbitReflection a * w') =
        (coxeterSystem t.tag).length (t.orbitReflection a) + (coxeterSystem t.tag).length w' := by
      rw [hl, length_orbitReflection, add_comm]
    rw [hww', canonicalRep_mul_of_length_eq hadd, List.map_cons, List.prod_cons,
      canonicalRep_list_prod_orbitReflection ω hlen']

theorem canonicalRep_mem_iSup_orbitRankOneGroup
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    canonicalRep (coxeterSystem t.tag) K w ∈ ⨆ a, orbitRankOneGroup t K σ a := by
  obtain ⟨ω, rfl, hlen⟩ := exists_reduced_orbitWord hw
  rw [canonicalRep_list_prod_orbitReflection ω hlen]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  rw [canonicalRep_orbitReflection_eq_orbitN t σ a]
  exact Subgroup.mem_iSup_of_mem a (orbitN_one_mem_orbitRankOneGroup a)

theorem graphFixedRootGroup_eq_iSup_orbitRankOneGroup
    (hσ : Function.Surjective σ) :
    graphFixedRootGroup t K σ = ⨆ a, orbitRankOneGroup t K σ a := by
  refine le_antisymm ?_ (iSup_le fun a => (Subgroup.closure_le _).2 ?_)
  · rw [graphFixedRootGroup_eq_closure σ hσ, Subgroup.closure_le]
    rintro _ ⟨w, hw, a, c, rfl⟩
    have hn := canonicalRep_mem_iSup_orbitRankOneGroup (K := K) (σ := σ) hw
    exact mul_mem (mul_mem hn (Subgroup.mem_iSup_of_mem a
      (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)))) (inv_mem hn)
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
        (orbitX_mem_graphFixedPosUnipotent t σ a c)
    · exact graphFixedNegUnipotent_le_graphFixedRootGroup t K σ
        (orbitY_mem_graphFixedNegUnipotent t σ a c)

theorem exceptional_fixed_simple_pair_generation
    (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K) :
    graphFixedRootGroup t K σ.toRingHom = ⨆ a, orbitRankOneGroup t K σ.toRingHom a ∧
    (∀ w ∈ relWeylTwist t,
      canonicalRep (coxeterSystem t.tag) K w ∈ ⨆ a, orbitRankOneGroup t K σ.toRingHom a) ∧
    ∀ ω : List (Fin t.foldedTag.rank),
      ω.length = t.orbitLength (ω.map t.orbitReflection).prod →
        canonicalRep (coxeterSystem t.tag) K (ω.map t.orbitReflection).prod =
          (ω.map fun a => (orbitN t K σ.toRingHom a 1 : ModGL t.tag K)).prod := by
  refine ⟨graphFixedRootGroup_eq_iSup_orbitRankOneGroup σ.surjective,
    fun w hw => canonicalRep_mem_iSup_orbitRankOneGroup hw, fun ω hω => ?_⟩
  rw [canonicalRep_list_prod_orbitReflection ω hω]
  exact congrArg List.prod (List.map_congr_left fun a _ =>
    canonicalRep_orbitReflection_eq_orbitN t σ.toRingHom a)

end CFSG.LieType.Chevalley
