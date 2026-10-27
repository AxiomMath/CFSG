module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcRows
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lWeilSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameC3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralC3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.RouteD (hiF4 isRoot_hiF4 rankOneHiF4 commutes_rankOneHiF4
  commutes_iSup_left)
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

section Torus

variable {K : Type} [Field K]

theorem a2l_rootDiagUnit_f4BitsC3 :
    rootDiagUnit .F4 (bitsTuple (K := K) f4BitsC3) =
      torusElt .F4 K (f4Node 1) (-1) * torusElt .F4 K (f4Node 3) (-1) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  have hpar : ∀ j : Fin (Tag.rank .F4),
      (f4BitsC3 j = true ∧
        (Tag.cartan .F4 (f4Node 1) j + Tag.cartan .F4 (f4Node 3) j) % 2 = 1) ∨
      (f4BitsC3 j = false ∧
        (Tag.cartan .F4 (f4Node 1) j + Tag.cartan .F4 (f4Node 3) j) % 2 = 0) := by
    decide
  funext j
  rw [Pi.mul_apply, ← zpow_add]
  rcases hpar j with ⟨hb, hm⟩ | ⟨hb, hm⟩
  · rw [(Int.odd_iff.2 hm).neg_one_zpow]
    simp [bitsTuple, hb]
  · rw [(Int.even_iff.2 hm).neg_one_zpow]
    simp [bitsTuple, hb]

theorem a2l_rootDiagUnit_f4BitsC3_mem :
    rootDiagUnit .F4 (bitsTuple (K := K) f4BitsC3) ∈ subsystemGroup .F4 K f4LeviC3 := by
  rw [a2l_rootDiagUnit_f4BitsC3]
  exact mul_mem
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := f4LeviC3) (i := f4Node 1) ⟨2, rfl⟩ (-1)))
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := f4LeviC3) (i := f4Node 3) ⟨0, rfl⟩ (-1)))

theorem a2l_rootDiagUnit_f4BitsC3_mul_self :
    rootDiagUnit .F4 (bitsTuple (K := K) f4BitsC3) *
      rootDiagUnit .F4 (bitsTuple (K := K) f4BitsC3) = 1 := by
  have h : (bitsTuple (K := K) f4BitsC3 * bitsTuple f4BitsC3 : Fin (Tag.rank .F4) → Kˣ) = 1 := by
    funext j
    rcases bitsTuple_mem (K := K) f4BitsC3 j with h | h <;> simp [h]
  rw [← rootDiagUnit_mul, h, rootDiagUnit_one]

theorem a2l_rootDiagUnit_f4BitsC3_ne_one (hK2 : ringChar K ≠ 2) :
    rootDiagUnit .F4 (bitsTuple (K := K) f4BitsC3) ≠ 1 := by
  intro h
  have h1 := congrFun (rootDiagUnit_injective (h.trans (rootDiagUnit_one (τ := .F4)).symm)) 0
  have h2 : bitsTuple (K := K) f4BitsC3 0 = -1 := by simp [bitsTuple, f4BitsC3, listMask]
  rw [h2] at h1
  exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h1)

end Torus

section Datum


theorem a2l_f4_datum_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (hC : HypA2.ChevOddInChev2) : a2lDatum ↥(adjointGroup .F4 K) := by
  classical
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK]; norm_num
  have hcp : CharP K 3 :=
    finite_field_prime_power_characteristic Nat.prime_three le_rfl hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  haveI : Finite (ModGL .F4 K) := finite_modGL
  have ha : ∀ i, bitsTuple (K := K) f4BitsC3 i = 1 ∨ bitsTuple (K := K) f4BitsC3 i = -1 :=
    bitsTuple_mem _
  obtain ⟨hSX, hSn, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _ ha
  set L := subsystemGroup .F4 K f4LeviC3 with hL_def
  set Q := rootSubgroup .F4 K hiF4 ⊔ rootSubgroup .F4 K (-hiF4) with hQ_def
  have hS : rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3)) = L ⊔ Q := by
    rw [rootCharKernel_f4BitsC3 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hSX' : L ⊔ Q ≤ toralCentralizer .F4 K (bitsTuple f4BitsC3) := hS ▸ hSX
  have hSn' : ((L ⊔ Q).subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))).Normal :=
    hS ▸ hSn
  have hHX : L ≤ toralCentralizer .F4 K (bitsTuple f4BitsC3) := le_sup_left.trans hSX'
  have hQmap : (rankOneHiF4 K).map (adjointGroup .F4 K).subtype = Q := by
    rw [rankOneHiF4, Subgroup.map_sup]
    simp only
    rw [map_subtype_rootGroup _ isRoot_hiF4, map_subtype_rootGroup _ (IsRoot.neg isRoot_hiF4)]
  have hcomm' : Commutes (⨆ k, rankOne (f4Datum K).rootGroup (c3Node k)) (rankOneHiF4 K) :=
    commutes_iSup_left.2 fun k => (commutes_rankOneHiF4 (c3Node_val_ne_zero k)).symm
  have hcomm : Commutes L Q := by
    rw [hL_def, ← map_subtype_iSup_c3, ← hQmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' x hx y hy]
  have hLn : (L.subgroupOf (L ⊔ Q)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx y hy)
  have hLsub : CFSG.Assembly.IsSubnormal L (toralCentralizer .F4 K (bitsTuple f4BitsC3)) :=
    .step le_sup_left hLn (.step hSX' hSn' (.refl _))
  obtain ⟨Ψ, hker, hrange, hqL, hlieL⟩ :=
    f4_levi_C3_recognition_frame (K := K) (p := 3) (f := 1) Nat.prime_three (by norm_num) hK' h2
  have hP : Group.IsPerfect (StatedSp 3 K) :=
    (LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num)
      (Or.inr (Or.inl ⟨hK, by norm_num⟩))).1
  let Ψ₂ : StatedSp 3 K →* ↥L :=
    Ψ.codRestrict L fun g => by rw [hL_def, ← hrange]; exact ⟨g, rfl⟩
  have hΨ₂ : Function.Surjective Ψ₂ := by
    intro y
    have hy : (y : ModGL .F4 K) ∈ Ψ.range := by rw [hrange]; exact y.2
    obtain ⟨g, hg⟩ := hy
    exact ⟨g, Subtype.ext hg⟩
  have hker₂ : Ψ₂.ker ≤ center (StatedSp 3 K) := fun g hg =>
    hker (MonoidHom.mem_ker.2 (congrArg Subtype.val (MonoidHom.mem_ker.1 hg)))
  set z : ModGL .F4 K := rootDiagUnit .F4 (bitsTuple (K := K) f4BitsC3) with hz_def
  have hzL : z ∈ L := a2l_rootDiagUnit_f4BitsC3_mem
  have hz2 : z * z = 1 := a2l_rootDiagUnit_f4BitsC3_mul_self
  have hz1 : z ≠ 1 := a2l_rootDiagUnit_f4BitsC3_ne_one hK2
  have hconj : ∀ g ∈ L, z * g = g * z := fun g hg => by
    have h := (mem_toralCentralizer.1 (hHX hg)).2
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hconj g g.2).symm
  haveI := hcp
  obtain ⟨F, _, _, φ, hFcard, hφinj, hφneg⟩ := a2l_exists_weil_sl2_27 K hK
  have hneg : ((φ (a2lNegOne F) : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) (-1 : Kˣ) := hφneg _ rfl
  have hΨneg : Ψ₂ (φ (a2lNegOne F)) = ⟨z, hzL⟩ :=
    a2l_map_neg_one_eq_of_central (by norm_num) hP Ψ₂ hΨ₂ hker₂ hzc
      (fun h => hz1 (congrArg Subtype.val h)) hneg
  have hΨneg' : Ψ (φ (a2lNegOne F)) = z := congrArg Subtype.val hΨneg
  have hΨinj : Function.Injective Ψ :=
    a2l_injective_of_central_kernel (by norm_num) Ψ hker hneg (by rw [hΨneg']; exact hz1)
  let N : Subgroup (ModGL .F4 K) := (Ψ.comp φ).range
  have hNL : N ≤ L := by
    rintro _ ⟨g, rfl⟩
    have : Ψ (φ g) ∈ Ψ.range := ⟨φ g, rfl⟩
    rwa [hrange] at this
  have hzN : z ∈ N := ⟨a2lNegOne F, hΨneg'⟩
  have hφ'inj : Function.Injective (Ψ.comp φ) := hΨinj.comp hφinj
  have hN : HarrisLit.IsSLTwoOver 27 ↥N := by
    haveI := Fintype.ofFinite F
    exact ⟨F, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hFcard],
      ⟨(MonoidHom.ofInjective hφ'inj).symm⟩⟩
  have hZ2 : IsPGroup 2 ↥(center ↥L) :=
    a2l_isPGroup_two_center_of_cover (by norm_num) hP Ψ₂ hΨ₂ hker₂
  have hTU : TypU ↥L := a2l_typU_of_psp_three hC hqL hZ2 hlieL
  have hLcomp : CFSG.Assembly.IsComponentOf L
      (adjointGroup .F4 K ⊓ centralizer ({z} : Set (ModGL .F4 K))) :=
    ⟨hHX, hLsub, (AssemblyBPredicates.isQuasisimple_iff_native _).2 hqL⟩
  exact a2lDatum_of_subgroup_component_of_le (adjointGroup .F4 K) (hHX hzL).1 hz2 hz1
    ⟨13, by norm_num⟩ (by norm_num) hLcomp hNL hzN hN hTU

theorem a2lF4Three_holds (hC : HypA2.ChevOddInChev2) : a2lF4Three := by
  intro X _ _ hX
  have hc := hX.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hc.2
  exact a2lDatum_of_mulEquiv e.symm (a2l_f4_datum_three (by rw [hK]; norm_num) hC)

end Datum

end CFSG.OddStandard.SmallF3.HypA2Leaves
