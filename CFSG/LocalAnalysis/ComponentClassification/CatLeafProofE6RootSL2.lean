module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6Levi

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial
open CFSG.Timmesfeld.LevisExtras (tv01_eq_sl2Upper tv10_eq_sl2Lower)
open CFSG.ClassicalInvolution.WeakCT (spBlock hom_ext_sl2 blk blk_zero_tv01 blk_zero_tv10
  blk_one_tv01 blk_one_tv10 tv_zero_one_one_ne_one)
open scoped MatrixGroups Matrix

section Pair

variable {M N : Type*} [Group M] [Group N]

@[expose] def pairHom (f g : M →* N) (h : ∀ a b, Commute (f a) (g b)) : M →* N :=
  (f.noncommCoprod g h).comp ((MonoidHom.id M).prod (MonoidHom.id M))

theorem pairHom_apply (f g : M →* N) (h : ∀ a b, Commute (f a) (g b)) (a : M) :
    pairHom f g h a = f a * g a :=
  rfl

theorem commute_of_mem_closure {S T : Set N} (h : ∀ s ∈ S, ∀ t ∈ T, Commute s t) {x y : N}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure T) : Commute x y := by
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).2 fun t ht => Subgroup.mem_centralizer_iff.2 fun s hs =>
      (h s hs t ht).eq
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set N) :=
    (Subgroup.closure_le _).2 fun s hs => Subgroup.mem_centralizer_iff.2 fun t ht =>
      (Subgroup.mem_centralizer_iff.1 (h1 ht) s hs).symm
  exact (Subgroup.mem_centralizer_iff.1 (h2 hx) y hy).symm

end Pair

section SimpleRoot

variable {K : Type} [Field K]

theorem tv_zero_one_eq_uSL (c : K) : (tv 0 1 c : SL(2, K)) = uSL c := by
  rw [tv01_eq_sl2Upper]
  rfl

theorem tv_one_zero_eq_vSL (c : K) : (tv 1 0 c : SL(2, K)) = vSL c := by
  rw [tv10_eq_sl2Lower]
  rfl

theorem simpleRootSL2_tv01
    {τ : Tag} (i : Fin τ.rank) (c : K) : simpleRootSL2 τ K i (tv 0 1 c) = xUnit τ K i c := by
  rw [tv_zero_one_eq_uSL, simpleRootSL2_uSL]

theorem simpleRootSL2_tv10
    {τ : Tag} (i : Fin τ.rank) (c : K) : simpleRootSL2 τ K i (tv 1 0 c) = yUnit τ K i c := by
  rw [tv_one_zero_eq_vSL, simpleRootSL2_vSL]

theorem commute_simpleRootSL2_of_orth
    {t : TwistTag} {i j : Fin t.tag.rank} (hij : i ≠ j)
    (h0 : (Pi.single i 1 : Fin t.tag.rank → ℤ) ⬝ᵥ
      (t.tag.symmetrizedCartan *ᵥ (Pi.single j 1 : Fin t.tag.rank → ℤ)) = 0) (A B : SL2 K) :
    Commute (simpleRootSL2 t.tag K i A) (simpleRootSL2 t.tag K j B) := by
  have hxx : ∀ c d : K, Commute (xUnit t.tag K i c) (xUnit t.tag K j d) := fun c d => by
    rw [← pinnedX_single, ← pinnedX_single]
    exact commute_pinnedX_of_rootForm_eq_zero K (isRoot_single _ i) (isRoot_single _ j) h0 c d
  have hyy : ∀ c d : K, Commute (yUnit t.tag K i c) (yUnit t.tag K j d) := fun c d => by
    rw [← pinnedX_neg_single, ← pinnedX_neg_single]
    refine commute_pinnedX_of_rootForm_eq_zero K (isRoot_neg_single _ i)
      (isRoot_neg_single _ j) ?_ c d
    rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, h0]
  have hA : simpleRootSL2 t.tag K i A ∈
      Subgroup.closure (Set.range (xUnit t.tag K i) ∪ Set.range (yUnit t.tag K i)) := by
    rw [← range_simpleRootSL2]
    exact ⟨A, rfl⟩
  have hB : simpleRootSL2 t.tag K j B ∈
      Subgroup.closure (Set.range (xUnit t.tag K j) ∪ Set.range (yUnit t.tag K j)) := by
    rw [← range_simpleRootSL2]
    exact ⟨B, rfl⟩
  refine commute_of_mem_closure ?_ hA hB
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
  · exact hxx c d
  · exact commute_xUnit_yUnit_of_ne hij c d
  · exact (commute_xUnit_yUnit_of_ne hij.symm d c).symm
  · exact hyy c d

end SimpleRoot

section Edges

variable (K : Type) [Field K]

theorem coe_xPar_e6
    (i : Fin Tag.E6.rank) (c : K) :
    ((xPar (rootOperatorFamily .E6) (Pi.single i 1) c : adjointGroup .E6 K) : ModGL .E6 K) =
        xUnit .E6 K i c ∧
      ((xPar (rootOperatorFamily .E6) (-Pi.single i 1) c : adjointGroup .E6 K) : ModGL .E6 K) =
        yUnit .E6 K i c := by
  refine ⟨?_, ?_⟩
  · rw [xPar_simple, RootOperatorFamily.coe_eltElement, RootOperatorFamily.eltUnit_simple]
  · rw [xPar_neg_simple, RootOperatorFamily.coe_eltElement,
      RootOperatorFamily.eltUnit_neg_simple]

variable [Finite K]

theorem exists_e6_sl3
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j) (h1 : Tag.cartan .E6 i j = -1)
    (h2 : Tag.cartan .E6 j i = -1)
    (hl : ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E6 i l + 2 * Tag.cartan .E6 j l) :
    ∃ ψ : SL(3, K) →* ModGL TwistTag.E6.tag K,
      ψ.comp (blk K 0) = simpleRootSL2 TwistTag.E6.tag K i ∧
        ψ.comp (blk K 1) = simpleRootSL2 TwistTag.E6.tag K j := by
  obtain ⟨O, C, hE⟩ := exists_e6_chevalleyExtras K
  obtain ⟨l, hl⟩ := hl
  obtain ⟨emb, -, -, hv⟩ := ClassicalInvolution.WeakCT.exists_sl3Levi hE rfl hij h1 h2 hl
  refine ⟨(adjointGroup .E6 K).subtype.comp emb, sl3_comp_blk
    (u := xUnit TwistTag.E6.tag K i) (v := yUnit TwistTag.E6.tag K i)
    (u' := xUnit TwistTag.E6.tag K j) (v' := yUnit TwistTag.E6.tag K j) (fun c => ?_)
    (fun c => ?_) (fun c => ?_)⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show ((emb (tv 0 1 c) : adjointGroup .E6 K) : ModGL .E6 K) = _
      rw [(hv c).1]
      exact (coe_xPar_e6 K i c).1
    · show ((emb (tv 1 0 c) : adjointGroup .E6 K) : ModGL .E6 K) = _
      rw [(hv c).2.1]
      exact (coe_xPar_e6 K i c).2
    · show ((emb (tv 1 2 c) : adjointGroup .E6 K) : ModGL .E6 K) = _
      rw [(hv c).2.2.1]
      exact (coe_xPar_e6 K j c).1
    · show ((emb (tv 2 1 c) : adjointGroup .E6 K) : ModGL .E6 K) = _
      rw [(hv c).2.2.2]
      exact (coe_xPar_e6 K j c).2
  · exact ⟨simpleRootSL2_tv01 i c, simpleRootSL2_tv10 i c⟩
  · exact ⟨simpleRootSL2_tv01 j c, simpleRootSL2_tv10 j c⟩

end Edges

end CFSG.ComponentClassification.CatLeafProof
