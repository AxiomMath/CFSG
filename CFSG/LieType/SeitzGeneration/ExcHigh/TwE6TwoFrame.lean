module

public import CFSG.RankThree.Chevalley.SteinbergCFTwistedE6CommutingSL2
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley

variable {K : Type} [Field K]

theorem orbitRankOneHom_E6_singleton_injective_all (σ : K →+* K)
    (a : Fin TwistTag.E6.foldedTag.rank) (ha : (TwistTag.E6.orbit a).card = 1) :
    Function.Injective (orbitRankOneHom TwistTag.E6 K σ a) := by
  by_cases hK : ringChar K = 2
  · haveI : CharP K 2 := ringChar.of_eq hK
    obtain ⟨R, hRu, -, hRH, hRW, -, -, -, hRker, -⟩ :=
      exceptional_fixed_rank_one_central_image TwistTag.E6 K σ a
    have hR : R = orbitRankOneHom TwistTag.E6 K σ a :=
      SL2_hom_ext (fun s => by rw [hRu, orbitRankOneHom_uSL])
        (fun u => by rw [hRH, orbitRankOneHom_HSL]) (by rw [hRW, orbitRankOneHom_WSL])
    rw [← hR, injective_iff_map_eq_one]
    intro g hg
    obtain ⟨l, hl, hgl⟩ := hRker g (MonoidHom.mem_ker.2 hg)
    have hl1 : (l : orbitField TwistTag.E6 K σ a) = 1 := by
      apply Subtype.ext
      have h2 : ((l : orbitField TwistTag.E6 K σ a) : K) ^ 2 = 1 := by
        have := congrArg Subtype.val hl
        simpa using this
      exact CharTwo.sq_injective (show ((l : orbitField TwistTag.E6 K σ a) : K) ^ 2 =
        (1 : K) ^ 2 by rw [h2, one_pow])
    refine Subtype.ext ?_
    rw [hgl, hl1, one_smul, Matrix.SpecialLinearGroup.coe_one]
  · exact orbitRankOneHom_E6_singleton_injective hK σ a ha

@[expose] def frameRoot : Fin 4 → (Fin TwistTag.E6.tag.rank → ℤ) :=
  ![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0], e6Vec ![1, 0, 1, 1, 1, 1],
    e6Vec ![1, 2, 2, 3, 2, 1]]

theorem orbitRankOneHom_range_le (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank) :
    (orbitRankOneHom TwistTag.E6 K σ a).range ≤ graphFixedRootGroup .E6 K σ := by
  rw [orbitRankOneHom_range, Subgroup.closure_le]
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
      (orbitX_mem_graphFixedPosUnipotent _ σ a _)
  · exact graphFixedNegUnipotent_le_graphFixedRootGroup _ K σ
      (orbitY_mem_graphFixedNegUnipotent _ σ a _)

theorem fix_le_orbitField (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1) :
    RingHom.eqLocusField σ (RingHom.id K) ≤ orbitField .E6 K σ a := fun c hc => by
  rw [mem_orbitField, ha, pow_one]
  exact hc

@[expose] def fixIncl (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K)) →*
      Matrix.SpecialLinearGroup (Fin 2) (orbitField .E6 K σ a) :=
  Matrix.SpecialLinearGroup.map (Subfield.inclusion (fix_le_orbitField σ a ha))

theorem fixIncl_injective (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1) : Function.Injective (fixIncl σ a ha) :=
  SL2_map_injective _

@[expose] def rankOneFix (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K)) →*
      ModGL TwistTag.E6.tag K :=
  (orbitRankOneHom TwistTag.E6 K σ a).comp (fixIncl σ a ha)

theorem rankOneFix_injective (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1) : Function.Injective (rankOneFix σ a ha) :=
  (orbitRankOneHom_E6_singleton_injective_all σ a ha).comp (fixIncl_injective σ a ha)

theorem rankOneFix_mem_graphFixed (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1)
    (A : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) :
    rankOneFix σ a ha A ∈ graphFixedRootGroup .E6 K σ :=
  orbitRankOneHom_range_le σ a ⟨fixIncl σ a ha A, rfl⟩

theorem rankOneFix_mem_rootPair (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1) {j : Fin TwistTag.E6.tag.rank}
    (hj : TwistTag.E6.orbit a = {j})
    (A : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) :
    rankOneFix σ a ha A ∈ rootSubgroup TwistTag.E6.tag K (Pi.single j 1) ⊔
      rootSubgroup TwistTag.E6.tag K (-Pi.single j 1) := by
  have hjk : ∀ k, (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a) = j := fun k => by
    have h := TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) k
    rwa [hj, Finset.mem_singleton] at h
  have hRQ : (orbitRankOneHom TwistTag.E6 K σ a).range ≤
      rootSubgroup TwistTag.E6.tag K (Pi.single j 1) ⊔
        rootSubgroup TwistTag.E6.tag K (-Pi.single j 1) := by
    rw [orbitRankOneHom_range, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitX]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hjk k, ← pinnedX_single]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitY]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hjk k, ← pinnedX_neg_single]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
  exact hRQ ⟨fixIncl σ a ha A, rfl⟩

theorem orbitN_mem_graphFixed (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank) :
    (orbitN .E6 K σ a 1 : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup .E6 K σ := by
  rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_mem (mul_mem (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
    (orbitX_mem_graphFixedPosUnipotent _ σ a _)) (graphFixedNegUnipotent_le_graphFixedRootGroup
      _ K σ (orbitY_mem_graphFixedNegUnipotent _ σ a _)))
    (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
      (orbitX_mem_graphFixedPosUnipotent _ σ a _))

abbrev orbLeaf : Fin TwistTag.E6.foldedTag.rank := ⟨2, by decide⟩

abbrev orbCenter : Fin TwistTag.E6.foldedTag.rank := ⟨3, by decide⟩

theorem orbLeaf_card : (TwistTag.E6.orbit orbLeaf).card = 1 := by decide

theorem orbCenter_card : (TwistTag.E6.orbit orbCenter).card = 1 := by decide

theorem orbLeaf_orbit :
    TwistTag.E6.orbit orbLeaf = {(⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank)} := by decide

theorem orbCenter_orbit :
    TwistTag.E6.orbit orbCenter = {(⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank)} := by decide

@[expose] def frameSeq : Fin 4 → List (Fin TwistTag.E6.foldedTag.rank) :=
  ![[], [⟨1, by decide⟩], [⟨1, by decide⟩, ⟨0, by decide⟩],
    [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩,
      ⟨2, by decide⟩, ⟨3, by decide⟩]]

@[expose] def frameConj (σ : K →+* K) (i : Fin 4) : ModGL TwistTag.E6.tag K :=
  ((frameSeq i).map fun a => (orbitN .E6 K σ a 1 : ModGL TwistTag.E6.tag K)).reverse.prod

theorem frameConj_mem (σ : K →+* K) (i : Fin 4) :
    frameConj σ i ∈ graphFixedRootGroup .E6 K σ :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
    exact orbitN_mem_graphFixed σ a

@[expose] def frameRaw (σ : K →+* K) (i : Fin 4) :
    Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K)) →*
      ModGL TwistTag.E6.tag K :=
  (MulAut.conj (frameConj σ i)).toMonoidHom.comp (rankOneFix σ orbLeaf orbLeaf_card)

theorem frameRaw_mem_graphFixed (σ : K →+* K) (i : Fin 4)
    (A : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) :
    frameRaw σ i A ∈ graphFixedRootGroup .E6 K σ :=
  mul_mem (mul_mem (frameConj_mem σ i) (rankOneFix_mem_graphFixed σ orbLeaf orbLeaf_card A))
    (inv_mem (frameConj_mem σ i))

theorem frameSeq_fold (i : Fin 4) :
    (frameSeq i).foldl (fun v a => TwistTag.E6.orbitReflection a • v)
      (Pi.single ⟨3, by decide⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ) = frameRoot i := by
  have he3 : (Pi.single ⟨3, by decide⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      e6Vec ![0, 0, 0, 1, 0, 0] := by decide +kernel
  obtain ⟨h1, h2, h3⟩ := e6_fold_roots
  fin_cases i
  · exact he3
  · rw [he3]; exact h1
  · rw [he3]; exact h2
  · rw [he3]; exact h3

theorem frameRaw_mem_rootPair (σ : K →+* K) (i : Fin 4)
    (A : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) :
    frameRaw σ i A ∈ rootSubgroup TwistTag.E6.tag K (frameRoot i) ⊔
      rootSubgroup TwistTag.E6.tag K (-(frameRoot i)) := by
  rw [← frameSeq_fold i, ← map_conj_orbitN_list_rootPair .E6 σ (frameSeq i) (isRoot_single _ _)]
  exact ⟨_, rankOneFix_mem_rootPair σ orbLeaf orbLeaf_card orbLeaf_orbit A, rfl⟩

@[expose] def frameHom (σ : K →+* K) (i : Fin 4) :
    Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K)) →*
      graphFixedRootGroup .E6 K σ :=
  (frameRaw σ i).codRestrict _ (frameRaw_mem_graphFixed σ i)

theorem coe_frameHom (σ : K →+* K) (i : Fin 4)
    (A : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) :
    ((frameHom σ i A : graphFixedRootGroup .E6 K σ) : ModGL TwistTag.E6.tag K) =
      frameRaw σ i A := rfl

theorem frameHom_injective (σ : K →+* K) (i : Fin 4) : Function.Injective (frameHom σ i) :=
  fun A B hAB =>
    (rankOneFix_injective σ orbLeaf orbLeaf_card)
      ((MulAut.conj (frameConj σ i)).injective (congrArg Subtype.val hAB))

theorem frameHom_mem_rootPair (σ : K →+* K) (i : Fin 4)
    (A : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) :
    ((frameHom σ i A : graphFixedRootGroup .E6 K σ) : ModGL TwistTag.E6.tag K) ∈
      rootSubgroup TwistTag.E6.tag K (frameRoot i) ⊔
        rootSubgroup TwistTag.E6.tag K (-(frameRoot i)) :=
  frameRaw_mem_rootPair σ i A

theorem frameHom_commute (σ : K →+* K) {i j : Fin 4} (hij : i ≠ j)
    (A B : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) :
    frameHom σ i A * frameHom σ j B = frameHom σ j B * frameHom σ i A := by
  obtain ⟨hroot, hcheck⟩ := e6_four_roots_check
  obtain ⟨h0, hp, hm⟩ := hcheck i j hij
  exact Subtype.ext (commute_of_mem_rootPair_of_check (hroot i) (hroot j) h0 hp hm
    (frameRaw_mem_rootPair σ i A) (frameRaw_mem_rootPair σ j B))

section Torus

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical

theorem commute_rootDiagUnit_of_rootChar_eq_one (b : Fin TwistTag.E6.tag.rank → Kˣ)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (hb : rootChar b β = 1)
    {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ rootSubgroup TwistTag.E6.tag K β ⊔ rootSubgroup TwistTag.E6.tag K (-β)) :
    Commute (rootDiagUnit TwistTag.E6.tag b) x := by
  rw [← range_rootSL2_of_isRoot hβ] at hx
  obtain ⟨B, rfl⟩ := hx
  have h := rootDiagUnit_conj_rootSL2 (K := K) b hβ B
  rw [hb] at h
  have h1 : conjSL (diagUnitOne (1 : Kˣ)) B = B := by
    rw [diagUnitOne_one]
    apply Subtype.ext
    rw [coe_conjSL]
    simp
  rw [h1] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem isRoot_frameRoot (i : Fin 4) : IsRoot TwistTag.E6.tag (frameRoot i) := by
  have h := (e6_four_roots_check).1 i
  exact RootOps.isRootB_iff.1 h

@[expose] def e6TorParam (j : Fin Tag.E6.rank) (μ : Kˣ) : Fin Tag.E6.rank → Kˣ :=
  fun k => μ ^ Tag.E6.cartan j k

theorem rootChar_e6TorParam (j : Fin Tag.E6.rank) (μ : Kˣ) (z : Fin Tag.E6.rank → ℤ) :
    rootChar (e6TorParam j μ) z = μ ^ (∑ k, Tag.E6.cartan j k * z k) := by
  rw [rootChar, ← prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [e6TorParam, ← zpow_mul]

variable (σ : K →+* K)

abbrev sU : Kˣ →* Kˣ := Units.map (σ : K →* K)

@[expose] def normOne : Subgroup Kˣ where
  carrier := {u | sU σ u = u⁻¹}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb, mul_inv]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

@[expose] def e6TorParamHom (j : Fin Tag.E6.rank) : Kˣ →* (Fin Tag.E6.rank → Kˣ) :=
  Pi.monoidHom fun k => zpowGroupHom (Tag.E6.cartan j k)

@[expose] def torusTupleHom : Kˣ × Kˣ →* (Fin Tag.E6.rank → Kˣ) :=
  (e6TorParamHom ⟨0, by decide⟩).comp (MonoidHom.fst Kˣ Kˣ) *
    (e6TorParamHom ⟨5, by decide⟩).comp ((sU σ).comp (MonoidHom.fst Kˣ Kˣ)) *
    ((e6TorParamHom ⟨2, by decide⟩).comp (MonoidHom.snd Kˣ Kˣ) *
      (e6TorParamHom ⟨4, by decide⟩).comp ((sU σ).comp (MonoidHom.snd Kˣ Kˣ)))

@[expose] def torusTuple (u v : Kˣ) : Fin Tag.E6.rank → Kˣ := torusTupleHom σ (u, v)

theorem rootChar_mul_apply {τ : Tag} (a b : Fin τ.rank → Kˣ) (u : Fin τ.rank → ℤ) :
    rootChar (a * b) u = rootChar a u * rootChar b u := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem torusTuple_eq (u v : Kˣ) :
    torusTuple σ u v = e6TorParam ⟨0, by decide⟩ u * e6TorParam ⟨5, by decide⟩ (sU σ u) *
      (e6TorParam ⟨2, by decide⟩ v * e6TorParam ⟨4, by decide⟩ (sU σ v)) := by
  funext k
  rfl

theorem rootChar_torusTuple (u v : Kˣ) (z : Fin Tag.E6.rank → ℤ) :
    rootChar (torusTuple σ u v) z =
      u ^ (∑ k, Tag.E6.cartan ⟨0, by decide⟩ k * z k) *
        (sU σ u) ^ (∑ k, Tag.E6.cartan ⟨5, by decide⟩ k * z k) *
        (v ^ (∑ k, Tag.E6.cartan ⟨2, by decide⟩ k * z k) *
          (sU σ v) ^ (∑ k, Tag.E6.cartan ⟨4, by decide⟩ k * z k)) := by
  rw [torusTuple_eq, rootChar_mul_apply, rootChar_mul_apply, rootChar_mul_apply,
    rootChar_e6TorParam, rootChar_e6TorParam, rootChar_e6TorParam, rootChar_e6TorParam]

theorem pairing_frame (i : Fin 4) :
    (∑ k, Tag.E6.cartan ⟨0, by decide⟩ k * frameRoot i k) =
      ∑ k, Tag.E6.cartan ⟨5, by decide⟩ k * frameRoot i k ∧
    (∑ k, Tag.E6.cartan ⟨2, by decide⟩ k * frameRoot i k) =
      ∑ k, Tag.E6.cartan ⟨4, by decide⟩ k * frameRoot i k := by
  fin_cases i <;> decide

theorem rootChar_torusTuple_frame {u v : Kˣ} (hu : u ∈ normOne σ) (hv : v ∈ normOne σ) (i : Fin 4) :
    rootChar (torusTuple σ u v) (frameRoot i) = 1 := by
  obtain ⟨h1, h2⟩ := pairing_frame i
  have hu' : sU σ u = u⁻¹ := hu
  have hv' : sU σ v = v⁻¹ := hv
  refine (rootChar_torusTuple σ u v (frameRoot i)).trans ?_
  rw [hu', hv', ← h1, ← h2, inv_zpow', inv_zpow', ← zpow_add, ← zpow_add]
  simp

@[expose] def torusAB (u v : Kˣ) : ModGL Tag.E6 K :=
  rootDiagUnit Tag.E6 (torusTuple σ u v)

theorem commute_torusAB_frame {u v : Kˣ} (hu : u ∈ normOne σ) (hv : v ∈ normOne σ) (i : Fin 4)
    {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ rootSubgroup TwistTag.E6.tag K (frameRoot i) ⊔
      rootSubgroup TwistTag.E6.tag K (-(frameRoot i))) :
    Commute (torusAB σ u v) x :=
  commute_rootDiagUnit_of_rootChar_eq_one _ (isRoot_frameRoot i)
    (rootChar_torusTuple_frame σ hu hv i) hx

@[expose] def torusABHom : Kˣ × Kˣ →* ModGL TwistTag.E6.tag K :=
  (rootDiagUnitHom TwistTag.E6.tag K).comp (torusTupleHom σ)

theorem orbitH_eq_prod (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (w : (orbitField TwistTag.E6 K σ a)ˣ) :
    ((orbitH TwistTag.E6 K σ a w : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
      ((List.range (TwistTag.E6.orbit a).card).map fun k =>
        torusElt TwistTag.E6.tag K ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a))
          (Units.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ a).subtype : _ →+* K).toMonoidHom
            w)).prod := by
  obtain ⟨R, hRu, -, hRH, hRW, -, -, -, -, hRformula⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.E6 K σ a
  have h := hRformula (simpleRootSL2 TwistTag.E6.tag K) (fun i c => simpleRootSL2_uSL i c)
    (fun i u => simpleRootSL2_HSL i u) (fun i => simpleRootSL2_WSL i) (HSL w)
  rw [hRH] at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro k _
  rw [map_HSL, simpleRootSL2_HSL]

@[expose] def orbUnit (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank) (w : Kˣ)
    (hw : (σ ^ (TwistTag.E6.orbit a).card) (w : K) = w) :
    (orbitField TwistTag.E6 K σ a)ˣ where
  val := ⟨(w : K), mem_orbitField.2 hw⟩
  inv := ⟨((w⁻¹ : Kˣ) : K), mem_orbitField.2 (by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hw])⟩
  val_inv := Subtype.ext (by simp)
  inv_val := Subtype.ext (by simp)

theorem sigma_sq_of_normOne (σ : K →+* K) {u : Kˣ} (hu : u ∈ normOne σ) :
    (σ ^ 2) (u : K) = u := by
  have hu' : sU σ u = u⁻¹ := hu
  have h1 : σ (u : K) = ((u⁻¹ : Kˣ) : K) := congrArg Units.val hu'
  rw [pow_two, RingHom.mul_def, RingHom.comp_apply, h1, Units.val_inv_eq_inv_val, map_inv₀]
  have h2 : σ (u : K) = ((u⁻¹ : Kˣ) : K) := h1
  rw [h2, Units.val_inv_eq_inv_val, inv_inv]

abbrev nd0 : Fin TwistTag.E6.tag.rank := ⟨0, by decide⟩
abbrev nd2 : Fin TwistTag.E6.tag.rank := ⟨2, by decide⟩
abbrev nd4 : Fin TwistTag.E6.tag.rank := ⟨4, by decide⟩
abbrev nd5 : Fin TwistTag.E6.tag.rank := ⟨5, by decide⟩
abbrev orb0 : Fin TwistTag.E6.foldedTag.rank := ⟨0, by decide⟩
abbrev orb1 : Fin TwistTag.E6.foldedTag.rank := ⟨1, by decide⟩

theorem orb0_card : (TwistTag.E6.orbit orb0).card = 2 := by decide
theorem orb1_card : (TwistTag.E6.orbit orb1).card = 2 := by decide
theorem orb0_min : TwistTag.E6.orbitMin orb0 = nd0 := by decide
theorem orb0_perm : TwistTag.E6.perm (TwistTag.E6.orbitMin orb0) = nd5 := by decide
theorem orb1_min : TwistTag.E6.orbitMin orb1 = nd2 := by decide
theorem orb1_perm : TwistTag.E6.perm (TwistTag.E6.orbitMin orb1) = nd4 := by decide

theorem torusAB_eq (σ : K →+* K) (u v : Kˣ) :
    torusAB σ u v =
      torusElt TwistTag.E6.tag K nd0 u * torusElt TwistTag.E6.tag K nd5 (sU σ u) *
        (torusElt TwistTag.E6.tag K nd2 v * torusElt TwistTag.E6.tag K nd4 (sU σ v)) := by
  have m : ∀ a b : Fin Tag.E6.rank → Kˣ, rootDiagUnit (K := K) Tag.E6 (a * b) =
      rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 b := fun a b => rootDiagUnit_mul a b
  rw [torusAB, torusTuple_eq σ u v, m, m, m, torusElt_eq_rootDiagUnit nd0,
    torusElt_eq_rootDiagUnit nd5,
    torusElt_eq_rootDiagUnit nd2, torusElt_eq_rootDiagUnit nd4]
  rfl

theorem orbitH_two (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 2) (w : (orbitField TwistTag.E6 K σ a)ˣ) :
    ((orbitH TwistTag.E6 K σ a w : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
      torusElt TwistTag.E6.tag K (TwistTag.E6.orbitMin a)
          (Units.map (orbitField TwistTag.E6 K σ a).subtype.toMonoidHom w) *
        torusElt TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
          (Units.map (σ.comp (orbitField TwistTag.E6 K σ a).subtype).toMonoidHom w) := by
  rw [orbitH_eq_prod, ha]
  simp [List.range_succ]
  rfl

theorem orbitH_mem (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (w : (orbitField TwistTag.E6 K σ a)ˣ) :
    ((orbitH TwistTag.E6 K σ a w : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) ∈
      graphFixedRootGroup .E6 K σ :=
  orbitRankOneHom_range_le σ a ⟨HSL w, orbitRankOneHom_HSL a w⟩

theorem torusAB_mem (σ : K →+* K) {u v : Kˣ} (hu : u ∈ normOne σ) (hv : v ∈ normOne σ) :
    torusAB σ u v ∈ graphFixedRootGroup .E6 K σ := by
  have hu2 : (σ ^ (TwistTag.E6.orbit orb0).card) (u : K) = u := by
    rw [orb0_card]; exact sigma_sq_of_normOne σ hu
  have hv2 : (σ ^ (TwistTag.E6.orbit orb1).card) (v : K) = v := by
    rw [orb1_card]; exact sigma_sq_of_normOne σ hv
  have h0 := orbitH_two σ orb0 orb0_card (orbUnit σ orb0 u hu2)
  have h1 := orbitH_two σ orb1 orb1_card (orbUnit σ orb1 v hv2)
  rw [orb0_perm, orb0_min] at h0
  rw [orb1_perm, orb1_min] at h1
  have hu0 : Units.map (orbitField TwistTag.E6 K σ orb0).subtype.toMonoidHom
      (orbUnit σ orb0 u hu2) = u := Units.ext rfl
  have hu1 : Units.map (σ.comp (orbitField TwistTag.E6 K σ orb0).subtype).toMonoidHom
      (orbUnit σ orb0 u hu2) = sU σ u := Units.ext rfl
  have hv0 : Units.map (orbitField TwistTag.E6 K σ orb1).subtype.toMonoidHom
      (orbUnit σ orb1 v hv2) = v := Units.ext rfl
  have hv1 : Units.map (σ.comp (orbitField TwistTag.E6 K σ orb1).subtype).toMonoidHom
      (orbUnit σ orb1 v hv2) = sU σ v := Units.ext rfl
  rw [hu0, hu1] at h0
  rw [hv0, hv1] at h1
  rw [torusAB_eq, ← h0, ← h1]
  exact mul_mem (orbitH_mem σ orb0 _) (orbitH_mem σ orb1 _)

@[expose] def torusG : (↥(normOne σ) × ↥(normOne σ)) →* graphFixedRootGroup TwistTag.E6 K σ :=
  ((torusABHom σ).comp ((normOne σ).subtype.prodMap (normOne σ).subtype)).codRestrict _
    fun p => torusAB_mem σ p.1.2 p.2.2

theorem coe_torusG (p : ↥(normOne σ) × ↥(normOne σ)) :
    ((torusG σ p : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) =
      torusAB σ p.1 p.2 := rfl

theorem torusG_commute_frame {ι : Fin 4 → (Matrix.SpecialLinearGroup (Fin 2)
      (RingHom.eqLocusField σ (RingHom.id K)) →* graphFixedRootGroup TwistTag.E6 K σ)}
    (hι : ∀ i A, ((ι i A : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) ∈
      rootSubgroup TwistTag.E6.tag K (frameRoot i) ⊔
        rootSubgroup TwistTag.E6.tag K (-(frameRoot i)))
    (p : ↥(normOne σ) × ↥(normOne σ)) (i : Fin 4)
    (A : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) :
    Commute (torusG σ p) (ι i A) :=
  Subtype.ext (commute_torusAB_frame σ p.1.2 p.2.2 i (hι i A)).eq

theorem cartan_E6_values :
    Tag.E6.cartan ⟨0, by decide⟩ ⟨0, by decide⟩ = 2 ∧
      Tag.E6.cartan ⟨5, by decide⟩ ⟨0, by decide⟩ = 0 ∧
      Tag.E6.cartan ⟨2, by decide⟩ ⟨0, by decide⟩ = -1 ∧
      Tag.E6.cartan ⟨4, by decide⟩ ⟨0, by decide⟩ = 0 ∧
      Tag.E6.cartan ⟨0, by decide⟩ ⟨2, by decide⟩ = -1 ∧
      Tag.E6.cartan ⟨5, by decide⟩ ⟨2, by decide⟩ = 0 ∧
      Tag.E6.cartan ⟨2, by decide⟩ ⟨2, by decide⟩ = 2 ∧
      Tag.E6.cartan ⟨4, by decide⟩ ⟨2, by decide⟩ = 0 := by
  decide

theorem torusG_ker_pow_three {p : ↥(normOne σ) × ↥(normOne σ)} (hp : torusG σ p = 1) :
    p ^ 3 = 1 := by
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := p
  have h1 : torusAB σ u v = 1 := congrArg Subtype.val hp
  have h2 : torusTuple σ u v = 1 :=
    rootDiagUnit_injective (K := K) (τ := Tag.E6) (h1.trans rootDiagUnit_one.symm)
  obtain ⟨c00, c50, c20, c40, c02, c52, c22, c42⟩ := cartan_E6_values
  have e0 := congrFun h2 ⟨0, by decide⟩
  have e2 := congrFun h2 ⟨2, by decide⟩
  rw [torusTuple_eq σ u v] at e0 e2
  simp only [Pi.mul_apply, e6TorParam, Pi.one_apply, c00, c50, c20, c40, c02, c52, c22, c42,
    zpow_zero, mul_one, zpow_neg, zpow_one, zpow_ofNat, pow_zero, pow_one] at e0 e2
  have hv2 : v = u ^ 2 := (mul_inv_eq_one.1 e0).symm
  have hu3 : u ^ 3 = 1 := by
    have h : u ^ 3 = u⁻¹ * v ^ 2 := by rw [hv2]; group
    rw [h, e2]
  have hv3 : v ^ 3 = 1 := by
    have h : v ^ 3 = (u ^ 3) ^ 2 := by rw [hv2]; group
    rw [h, hu3, one_pow]
  exact Prod.ext (Subtype.ext hu3) (Subtype.ext hv3)

end Torus

end CFSG.LieType.SeitzGeneration.ExcHigh
