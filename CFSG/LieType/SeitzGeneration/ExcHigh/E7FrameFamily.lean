module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7FrameTorus
public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusWeyl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeylFive
public import CFSG.HardMathSupport.Timmesfeld.Torality.E8ChainTab
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.StandardType.TableBExcTwo
open scoped MatrixGroups


@[expose] def frameFamily (L : Type) [Field L] : Fin 3 → Fin Tag.E7.rank → Lˣ :=
  ![Pi.mulSingle 5 (-1), Pi.mulSingle 3 (-1), Pi.mulSingle 0 (-1)]

theorem frameE7Root_coord_even : ∀ i : Fin 7,
    frameE7Root i 5 % 2 = 0 ∧ frameE7Root i 3 % 2 = 0 ∧ frameE7Root i 0 % 2 = 0 := by
  decide +kernel

theorem even_of_neg_one_zpow_eq_one {L : Type} [Field L] (h2 : (2 : L) ≠ 0) {n : ℤ}
    (h : (-1 : Lˣ) ^ n = 1) : Even n := by
  have hneg : (-1 : Lˣ) ≠ 1 := by
    intro h1
    apply h2
    have h1' := congrArg (fun u : Lˣ => (u : L)) h1
    simp only [Units.val_neg, Units.val_one] at h1'
    linear_combination -h1'
  rw [neg_one_zpow_eq_ite] at h
  split_ifs at h with he
  · exact he
  · exact absurd h hneg

theorem frameE7Root_mem_familyKernel (L : Type) [Field L] (i : Fin 7) :
    frameE7Root i ∈ familyKernel (τ := Tag.E7) (frameFamily L) := by
  refine ⟨e7Frame_isRoot i, fun s => ?_⟩
  obtain ⟨h5, h3, h0⟩ := frameE7Root_coord_even i
  fin_cases s
  · show rootChar (Pi.mulSingle (5 : Fin Tag.E7.rank) (-1 : Lˣ)) (frameE7Root i) = 1
    rw [rootChar_mulSingle_eq_zpow, Even.neg_one_zpow (Int.even_iff.2 h5)]
  · show rootChar (Pi.mulSingle (3 : Fin Tag.E7.rank) (-1 : Lˣ)) (frameE7Root i) = 1
    rw [rootChar_mulSingle_eq_zpow, Even.neg_one_zpow (Int.even_iff.2 h3)]
  · show rootChar (Pi.mulSingle (0 : Fin Tag.E7.rank) (-1 : Lˣ)) (frameE7Root i) = 1
    rw [rootChar_mulSingle_eq_zpow, Even.neg_one_zpow (Int.even_iff.2 h0)]

theorem eq_frame_of_mem_familyKernel {L : Type} [Field L] (h2 : (2 : L) ≠ 0)
    {α : Fin Tag.E7.rank → ℤ} (hα : α ∈ familyKernel (τ := Tag.E7) (frameFamily L)) :
    ∃ i : Fin 7, α = frameE7Root i ∨ α = -frameE7Root i := by
  obtain ⟨hroot, hker⟩ := hα
  have e5 : (-1 : Lˣ) ^ α 5 = 1 := by
    have h := hker 0
    rwa [show frameFamily L 0 = Pi.mulSingle (5 : Fin Tag.E7.rank) (-1 : Lˣ) from rfl,
      rootChar_mulSingle_eq_zpow] at h
  have e3 : (-1 : Lˣ) ^ α 3 = 1 := by
    have h := hker 1
    rwa [show frameFamily L 1 = Pi.mulSingle (3 : Fin Tag.E7.rank) (-1 : Lˣ) from rfl,
      rootChar_mulSingle_eq_zpow] at h
  have e0 : (-1 : Lˣ) ^ α 0 = 1 := by
    have h := hker 2
    rwa [show frameFamily L 2 = Pi.mulSingle (0 : Fin Tag.E7.rank) (-1 : Lˣ) from rfl,
      rootChar_mulSingle_eq_zpow] at h
  have key : ∀ β ∈ rootFinset .E7, β 5 % 2 = 0 → β 3 % 2 = 0 → β 0 % 2 = 0 →
      ∃ i : Fin 7, β = frameE7Root i ∨ β = -frameE7Root i := by
    decide +kernel
  exact key α (mem_rootFinset.2 hroot) (Int.even_iff.1 (even_of_neg_one_zpow_eq_one h2 e5))
    (Int.even_iff.1 (even_of_neg_one_zpow_eq_one h2 e3))
    (Int.even_iff.1 (even_of_neg_one_zpow_eq_one h2 e0))

@[expose] def frameW : WeylGroup Tag.E7 :=
  ((List.finRange 7).map fun i => rootReflection (frameE7Root i)).prod

theorem frameW_smul_foldr (l : List (Fin 7)) (v : Fin Tag.E7.rank → ℤ) :
    (l.map fun i => rootReflection (frameE7Root i)).prod • v =
      l.foldr (fun i u => u - iform (frameE7Root i) u • frameE7Root i) v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, List.foldr_cons,
      rootReflection_smul_SL (τ := Tag.E7) (fun γ hγ => iform_self_of_isRoot_E7' hγ)
        (e7Frame_isRoot a)]

theorem frameW_fold_single : ∀ k : Fin Tag.E7.rank,
    (List.finRange 7).foldr (fun i u => u - iform (frameE7Root i) u • frameE7Root i)
      (Pi.single k 1 : Fin Tag.E7.rank → ℤ) = -Pi.single k 1 := by
  decide +kernel

theorem frameW_smul_single (k : Fin Tag.E7.rank) :
    frameW • (Pi.single k 1 : Fin Tag.E7.rank → ℤ) = -Pi.single k 1 := by
  rw [frameW, frameW_smul_foldr]
  exact frameW_fold_single k

theorem frameW_eq_qplusW : frameW = qplusW Tag.E7 :=
  ext_single fun k => by
    rw [frameW_smul_single, qplusW_smul_single (τ := Tag.E7) (Or.inl rfl) k]

theorem frameW_smul (u : Fin Tag.E7.rank → ℤ) : frameW • u = -u := by
  rw [frameW_eq_qplusW]
  exact qplusW_smul (τ := Tag.E7) (Or.inl rfl) u

theorem frameW_mem_closure (L : Type) [Field L] :
    frameW ∈ Subgroup.closure ((fun α => rootReflection α) ''
      familyKernel (τ := Tag.E7) (frameFamily L)) := by
  unfold frameW
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨frameE7Root i, frameE7Root_mem_familyKernel L i, rfl⟩

theorem familyGroup_frameFamily_le_frameSpan {L : Type} [Field L] [IsAlgClosed L]
    (h2 : (2 : L) ≠ 0) :
    familyGroup (τ := Tag.E7) (K := L) (frameFamily L) ≤ frameSpan L := by
  unfold familyGroup
  refine sup_le (torusGroup_le_frameSpan (L := L) fun x =>
    IsAlgClosed.exists_pow_nat_eq x two_pos) ?_
  unfold rootSpan
  refine iSup₂_le fun α hα => ?_
  have hrange : ∀ j : Fin 7, (rootSL2 Tag.E7 L (frameE7Root j)).range ≤ frameSpan L := fun j =>
    le_iSup (fun k : Fin 7 => (rootSL2 Tag.E7 L (frameE7Root k)).range) j
  obtain ⟨i, rfl | rfl⟩ := eq_frame_of_mem_familyKernel h2 hα
  · exact (le_sup_left.trans (range_rootSL2_of_isRoot (K := L)
      (e7Frame_isRoot i)).symm.le).trans (hrange i)
  · exact (le_sup_right.trans (range_rootSL2_of_isRoot (K := L)
      (e7Frame_isRoot i)).symm.le).trans (hrange i)

theorem canonicalRep_mem_familyGroup_of_closure_gen {L : Type} [Field L] {ι : Type}
    (a : ι → Fin Tag.E7.rank → L ˣ) {y : WeylGroup Tag.E7}
    (hy : y ∈ Subgroup.closure ((fun α => rootReflection α) '' familyKernel (τ := Tag.E7) a)) :
    canonicalRep (coxeterSystem Tag.E7) L y ∈ familyGroup (τ := Tag.E7) (K := L) a := by
  let R : Subgroup (WeylGroup Tag.E7) :=
    { carrier := {x | canonicalRep (coxeterSystem Tag.E7) L x ∈ familyGroup (τ := Tag.E7) (K := L) a}
      mul_mem' := fun {x x'} hx hx' => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.E7) (R := L) x x'
        have hmul : canonicalRep (coxeterSystem Tag.E7) L (x * x') =
            k⁻¹ * (canonicalRep (coxeterSystem Tag.E7) L x * canonicalRep (coxeterSystem Tag.E7) L x') := by
          rw [hkk]
          group
        show canonicalRep (coxeterSystem Tag.E7) L (x * x') ∈ familyGroup (τ := Tag.E7) (K := L) a
        rw [hmul]
        exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) (mul_mem hx hx')
      one_mem' := by
        show canonicalRep (coxeterSystem Tag.E7) L 1 ∈ familyGroup (τ := Tag.E7) (K := L) a
        rw [canonicalRep_one]
        exact one_mem _
      inv_mem' := fun {x} hx => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.E7) (R := L) x x⁻¹
        rw [mul_inv_cancel, canonicalRep_one, mul_one] at hkk
        have hinv : canonicalRep (coxeterSystem Tag.E7) L x⁻¹ =
            (canonicalRep (coxeterSystem Tag.E7) L x)⁻¹ * k := by
          rw [← hkk]
          group
        show canonicalRep (coxeterSystem Tag.E7) L x⁻¹ ∈ familyGroup (τ := Tag.E7) (K := L) a
        rw [hinv]
        exact mul_mem (inv_mem hx) (Subgroup.mem_sup_left hk) }
  have hgen : ∀ r ∈ (fun α => rootReflection α) '' familyKernel (τ := Tag.E7) a, r ∈ R := by
    rintro r ⟨α, hα, rfl⟩
    show canonicalRep (coxeterSystem Tag.E7) L (rootReflection α) ∈
      familyGroup (τ := Tag.E7) (K := L) a
    have hn := canonicalRep_rootReflection_mem (τ := Tag.E7) (K := L) hα.1
    have hneg : -α ∈ familyKernel (τ := Tag.E7) a :=
      ⟨IsRoot.neg hα.1, fun i => by
        rw [CFSG.RankThree.Chevalley.rootChar_neg_eq_inv, hα.2 i, inv_one]⟩
    have hsub : rootSubgroup Tag.E7 L α ⊔ rootSubgroup Tag.E7 L (-α) ≤
        familyGroup (τ := Tag.E7) (K := L) a :=
      sup_le ((rootSubgroup_le_rootSpan (τ := Tag.E7) (K := L) hα).trans le_sup_right)
        ((rootSubgroup_le_rootSpan (τ := Tag.E7) (K := L) hneg).trans le_sup_right)
    exact (sup_le le_sup_left hsub) hn
  exact (Subgroup.closure_le R).2 (fun r hr => hgen r hr) hy

end CFSG.LieType.SeitzGeneration.ExcHigh
