module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcRows
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSLFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralA5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

section Torus

variable {K : Type} [Field K]

theorem a2l_rootDiagUnit_e6BitsA5 :
    rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) =
      torusElt .E6 K (e6Node 0) (-1) * torusElt .E6 K (e6Node 3) (-1) *
        torusElt .E6 K (e6Node 5) (-1) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  have hpar : ∀ j : Fin (Tag.rank .E6),
      (e6BitsA5 j = true ∧ (Tag.cartan .E6 (e6Node 0) j + Tag.cartan .E6 (e6Node 3) j +
        Tag.cartan .E6 (e6Node 5) j) % 2 = 1) ∨
      (e6BitsA5 j = false ∧ (Tag.cartan .E6 (e6Node 0) j + Tag.cartan .E6 (e6Node 3) j +
        Tag.cartan .E6 (e6Node 5) j) % 2 = 0) := by
    decide
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, ← zpow_add, ← zpow_add]
  rcases hpar j with ⟨hb, hm⟩ | ⟨hb, hm⟩
  · rw [(Int.odd_iff.2 hm).neg_one_zpow]
    simp [bitsTuple, hb]
  · rw [(Int.even_iff.2 hm).neg_one_zpow]
    simp [bitsTuple, hb]

theorem a2l_rootDiagUnit_e6BitsA5_mem :
    rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) ∈ subsystemGroup .E6 K e6LeviA5 := by
  rw [a2l_rootDiagUnit_e6BitsA5]
  exact mul_mem (mul_mem
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := e6LeviA5) (i := e6Node 0) ⟨0, rfl⟩ (-1)))
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := e6LeviA5) (i := e6Node 3) ⟨2, rfl⟩ (-1))))
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := e6LeviA5) (i := e6Node 5) ⟨4, rfl⟩ (-1)))

theorem a2l_rootDiagUnit_e6BitsA5_mul_self :
    rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) *
      rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) = 1 := by
  have h : (bitsTuple (K := K) e6BitsA5 * bitsTuple e6BitsA5 : Fin (Tag.rank .E6) → Kˣ) = 1 := by
    funext j
    rcases bitsTuple_mem (K := K) e6BitsA5 j with h | h <;> simp [h]
  rw [← rootDiagUnit_mul, h, rootDiagUnit_one]

theorem a2l_rootDiagUnit_e6BitsA5_ne_one (hK2 : ringChar K ≠ 2) :
    rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) ≠ 1 := by
  intro h
  have h1 := congrFun (rootDiagUnit_injective (h.trans (rootDiagUnit_one (τ := .E6)).symm))
    (e6Node 1)
  have h2 : bitsTuple (K := K) e6BitsA5 (e6Node 1) = -1 := by
    simp [bitsTuple, show e6BitsA5 (e6Node 1) = true from by decide]
  rw [h2] at h1
  exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h1)

end Torus

section Datum


theorem a2l_e6_datum_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (hC : HypA2.ChevOddInChev2) : a2lDatum ↥(adjointGroup .E6 K) := by
  classical
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK]; norm_num
  have hcp : CharP K 3 :=
    finite_field_prime_power_characteristic Nat.prime_three le_rfl hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  haveI : Finite (ModGL .E6 K) := finite_modGL
  have ha : ∀ i, bitsTuple (K := K) e6BitsA5 i = 1 ∨ bitsTuple (K := K) e6BitsA5 i = -1 :=
    bitsTuple_mem _
  obtain ⟨hSX, hSn, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E6 K hK2 _ ha
  set H := subsystemGroup .E6 K e6LeviA5 with hH_def
  set Q := rootSubgroup .E6 K hiE6 ⊔ rootSubgroup .E6 K (-hiE6) with hQ_def
  have hS : rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5)) = H ⊔ Q := by
    rw [rootCharKernel_e6BitsA5 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hSX' : H ⊔ Q ≤ toralCentralizer .E6 K (bitsTuple e6BitsA5) := hS ▸ hSX
  have hSn' : ((H ⊔ Q).subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))).Normal :=
    hS ▸ hSn
  have hHX : H ≤ toralCentralizer .E6 K (bitsTuple e6BitsA5) := le_sup_left.trans hSX'
  have hQmap : (rootGroup (rootOperatorFamily .E6) K hiE6 ⊔
      rootGroup (rootOperatorFamily .E6) K (-hiE6)).map (adjointGroup .E6 K).subtype = Q := by
    rw [Subgroup.map_sup, map_subtype_rootGroup _ isRoot_hiE6,
      map_subtype_rootGroup _ (IsRoot.neg isRoot_hiE6)]
  have hcomm' : Commutes (⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup
      (e6A5Node k)) (rootGroup (rootOperatorFamily .E6) K hiE6 ⊔
        rootGroup (rootOperatorFamily .E6) K (-hiE6)) :=
    ClassicalInvolution.RouteD.commutes_iSup_left.2 fun k =>
      commutes_rootPair_of_noG2 noG2_E6 (isRoot_single _ _) isRoot_hiE6
        (e6A5Node_ne_hiE6 k).1 (e6A5Node_ne_hiE6 k).2 (iform_e6A5Node_hiE6 k)
        (not_isRoot_e6A5Node_hiE6 k).1 (not_isRoot_e6A5Node_hiE6 k).2
  have hcomm : Commutes H Q := by
    rw [hH_def, show e6LeviA5 = Set.range e6A5Node from rfl,
      ← map_subtype_iSup_rankOne e6A5Node, ← hQmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' x hx y hy]
  have hHn : (H.subgroupOf (H ⊔ Q)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx y hy)
  have hHsub : CFSG.Assembly.IsSubnormal H (toralCentralizer .E6 K (bitsTuple e6BitsA5)) :=
    .step le_sup_left hHn (.step hSX' hSn' (.refl _))
  obtain ⟨Ψ, hker, hrange, -, -⟩ :=
    exists_psi_A5_E6 (K := K) (p := 3) (f := 1) Nat.prime_three (by norm_num) hK'
  obtain ⟨hqH, hlieH⟩ :=
    e6_levi_A5_recognition (K := K) (p := 3) (f := 1) Nat.prime_three (by norm_num) hK'
  have hP : Group.IsPerfect SL(6, K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  let Ψ' : SL(6, K) →* ModGL .E6 K := (adjointGroup .E6 K).subtype.comp Ψ
  have hrange' : Ψ'.range = H := by
    change ((adjointGroup .E6 K).subtype.comp Ψ).range = H
    rw [MonoidHom.range_comp, hrange]
    exact map_subtype_iSup_rankOne e6A5Node
  have hker' : Ψ'.ker ≤ center SL(6, K) := fun g hg =>
    hker (MonoidHom.mem_ker.2 (Subtype.ext (MonoidHom.mem_ker.1 hg)))
  let Ψ₂ : SL(6, K) →* ↥H :=
    Ψ'.codRestrict H fun g => by rw [← hrange']; exact ⟨g, rfl⟩
  have hΨ₂ : Function.Surjective Ψ₂ := by
    intro y
    have hy : (y : ModGL .E6 K) ∈ Ψ'.range := by rw [hrange']; exact y.2
    obtain ⟨g, hg⟩ := hy
    exact ⟨g, Subtype.ext hg⟩
  have hker₂ : Ψ₂.ker ≤ center SL(6, K) := fun g hg =>
    hker' (MonoidHom.mem_ker.2 (congrArg Subtype.val (MonoidHom.mem_ker.1 hg)))
  set z : ModGL .E6 K := rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) with hz_def
  have hzH : z ∈ H := a2l_rootDiagUnit_e6BitsA5_mem
  have hz2 : z * z = 1 := a2l_rootDiagUnit_e6BitsA5_mul_self
  have hz1 : z ≠ 1 := a2l_rootDiagUnit_e6BitsA5_ne_one hK2
  have hconj : ∀ g ∈ H, z * g = g * z := fun g hg => by
    have h := (mem_toralCentralizer.1 (hHX hg)).2
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  have hzc : (⟨z, hzH⟩ : ↥H) ∈ center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hconj g g.2).symm
  haveI := hcp
  obtain ⟨F, _, _, ι, hFcard, hιinj, hιneg⟩ := a2l_exists_sl2_27_sl6 (K := K) hK
  have hg₀ : ((ι (a2lNegOne F) : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = -1 := hιneg _ rfl
  have hcen : ∀ s ∈ center SL(6, K), s = 1 ∨ s = ι (a2lNegOne F) := fun s hs => by
    rcases a2l_center_sl_cases hK (by norm_num) hs with h | h
    · exact Or.inl (Subtype.ext (by rw [h]; rfl))
    · exact Or.inr (Subtype.ext (h.trans hg₀.symm))
  have hΨneg : Ψ₂ (ι (a2lNegOne F)) = ⟨z, hzH⟩ :=
    a2l_map_eq_of_center_pair hP Ψ₂ hΨ₂ hker₂ hcen hzc (fun h => hz1 (congrArg Subtype.val h))
  have hΨneg' : Ψ' (ι (a2lNegOne F)) = z := congrArg Subtype.val hΨneg
  have hΨinj : Function.Injective Ψ' :=
    a2l_injective_of_center_pair Ψ' hker' hcen (by rw [hΨneg']; exact hz1)
  let N : Subgroup (ModGL .E6 K) := (Ψ'.comp ι).range
  have hNH : N ≤ H := by
    rintro _ ⟨g, rfl⟩
    have : Ψ' (ι g) ∈ Ψ'.range := ⟨ι g, rfl⟩
    rwa [hrange'] at this
  have hzN : z ∈ N := ⟨a2lNegOne F, hΨneg'⟩
  have hι'inj : Function.Injective (Ψ'.comp ι) := hΨinj.comp hιinj
  have hN : HarrisLit.IsSLTwoOver 27 ↥N := by
    haveI := Fintype.ofFinite F
    exact ⟨F, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hFcard],
      ⟨(MonoidHom.ofInjective hι'inj).symm⟩⟩
  have hZ2 : IsPGroup 2 ↥(center ↥H) :=
    a2l_isPGroup_two_center_of_center_pair hP Ψ₂ hΨ₂ hker₂ hcen (by
      apply Subtype.ext
      change ((ι (a2lNegOne F) : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
        ((ι (a2lNegOne F) : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = 1
      rw [hg₀]
      simp)
  have hTU : TypU ↥H := by
    refine a2l_typU_of_chev3 hqH hZ2 ⟨.PSL, 6, 1, hlieH⟩
      (a2l_not_inChev2_of_card hC ⟨.PSL, 6, 1, hlieH⟩ ?_)
    rw [GH74.card_of_lieModel_PSL (n := 6) (p := 3) (f := 1) (by norm_num) hlieH]
    decide
  have hHcomp : CFSG.Assembly.IsComponentOf H
      (adjointGroup .E6 K ⊓ centralizer ({z} : Set (ModGL .E6 K))) :=
    ⟨hHX, hHsub, (AssemblyBPredicates.isQuasisimple_iff_native _).2 hqH⟩
  exact a2lDatum_of_subgroup_component_of_le (adjointGroup .E6 K) (hHX hzH).1 hz2 hz1
    ⟨13, by norm_num⟩ (by norm_num) hHcomp hNH hzN hN hTU

theorem a2lE6Three_holds (hC : HypA2.ChevOddInChev2) : a2lE6Three := by
  intro X _ _ hX
  have hc := hX.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hc.2
  exact a2lDatum_of_mulEquiv e.symm (a2l_e6_datum_three (by rw [hK]; norm_num) hC)

end Datum

end CFSG.OddStandard.SmallF3.HypA2Leaves
