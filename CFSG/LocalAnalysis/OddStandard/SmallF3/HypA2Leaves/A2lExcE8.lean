module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcRows
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lLeviToral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTypUEven
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8ToralE7

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

section Frame

@[expose] def e8A5Node : Fin 5 → Fin (Tag.rank .E8) :=
  ![e8Node 1, e8Node 3, e8Node 4, e8Node 5, e8Node 6]

theorem e8A5_adj : ∀ i j : Fin 5, j.val = i.val + 1 → e8A5Node i ≠ e8A5Node j ∧
    Tag.cartan .E8 (e8A5Node i) (e8A5Node j) = -1 ∧
    Tag.cartan .E8 (e8A5Node j) (e8A5Node i) = -1 ∧
    ∃ l : Fin 8,
      ¬ (3 : ℤ) ∣ Tag.cartan .E8 (e8A5Node i) l + 2 * Tag.cartan .E8 (e8A5Node j) l := by
  decide

theorem e8A5_nadj : ∀ i j : Fin 5, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
    e8A5Node i ≠ e8A5Node j ∧ Tag.cartan .E8 (e8A5Node i) (e8A5Node j) = 0 ∧
    Tag.cartan .E8 (e8A5Node j) (e8A5Node i) = 0 := by
  decide

@[expose] def e8LeviA5 : Set (Fin (Tag.rank .E8)) := Set.range e8A5Node

theorem e8LeviA5_subset : e8LeviA5 ⊆ e8LeviE7 := by
  have h : ∀ k : Fin 5, ∃ k' : Fin 7, e8E7Node k' = e8A5Node k := by decide
  rintro _ ⟨k, rfl⟩
  exact h k

theorem exists_psi_A5_E8
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ∃ Ψ : SL(6, K) →* adjointGroup .E8 K, Ψ.ker ≤ Subgroup.center SL(6, K) ∧
      Ψ.range = ⨆ k, rankOne (e8Datum K).rootGroup (e8A5Node k) := by
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSL 6 p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
  obtain ⟨O, C, hE⟩ := exists_e8_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e8A5Node e8A5_adj e8A5_nadj
  obtain ⟨Ψ, hker, hrange, -⟩ :=
    specialLinear_frame_subgroup (m := 5) hadm (by norm_num) hK hcomm hρ hψ
  exact ⟨Ψ, hker, hrange⟩

end Frame

section Torus

variable {K : Type} [Field K]

theorem a2l_rootDiagUnit_e8BitsE7 :
    rootDiagUnit .E8 (bitsTuple (K := K) e8BitsE7) =
      torusElt .E8 K (e8Node 1) (-1) * torusElt .E8 K (e8Node 4) (-1) *
        torusElt .E8 K (e8Node 6) (-1) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  have hpar : ∀ j : Fin (Tag.rank .E8),
      (e8BitsE7 j = true ∧ (Tag.cartan .E8 (e8Node 1) j + Tag.cartan .E8 (e8Node 4) j +
        Tag.cartan .E8 (e8Node 6) j) % 2 = 1) ∨
      (e8BitsE7 j = false ∧ (Tag.cartan .E8 (e8Node 1) j + Tag.cartan .E8 (e8Node 4) j +
        Tag.cartan .E8 (e8Node 6) j) % 2 = 0) := by
    decide
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, ← zpow_add, ← zpow_add]
  rcases hpar j with ⟨hb, hm⟩ | ⟨hb, hm⟩
  · rw [(Int.odd_iff.2 hm).neg_one_zpow]
    simp [bitsTuple, hb]
  · rw [(Int.even_iff.2 hm).neg_one_zpow]
    simp [bitsTuple, hb]

theorem a2l_rootDiagUnit_e8BitsE7_mem :
    rootDiagUnit .E8 (bitsTuple (K := K) e8BitsE7) ∈ subsystemGroup .E8 K e8LeviA5 := by
  rw [a2l_rootDiagUnit_e8BitsE7]
  exact mul_mem (mul_mem
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := e8LeviA5) (i := e8Node 1) ⟨0, rfl⟩ (-1)))
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := e8LeviA5) (i := e8Node 4) ⟨2, rfl⟩ (-1))))
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := e8LeviA5) (i := e8Node 6) ⟨4, rfl⟩ (-1)))

theorem a2l_rootDiagUnit_e8BitsE7_mul_self :
    rootDiagUnit .E8 (bitsTuple (K := K) e8BitsE7) *
      rootDiagUnit .E8 (bitsTuple (K := K) e8BitsE7) = 1 := by
  have h : (bitsTuple (K := K) e8BitsE7 * bitsTuple e8BitsE7 : Fin (Tag.rank .E8) → Kˣ) = 1 := by
    funext j
    rcases bitsTuple_mem (K := K) e8BitsE7 j with h | h <;> simp [h]
  rw [← rootDiagUnit_mul, h, rootDiagUnit_one]

theorem a2l_rootDiagUnit_e8BitsE7_ne_one (hK2 : ringChar K ≠ 2) :
    rootDiagUnit .E8 (bitsTuple (K := K) e8BitsE7) ≠ 1 := by
  intro h
  have h1 := congrFun (rootDiagUnit_injective (h.trans (rootDiagUnit_one (τ := .E8)).symm))
    (e8Node 7)
  have h2 : bitsTuple (K := K) e8BitsE7 (e8Node 7) = -1 := by
    simp [bitsTuple, show e8BitsE7 (e8Node 7) = true from by decide]
  rw [h2] at h1
  exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h1)

end Torus

section Datum


theorem a2l_e8_datum_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (hC : HypA2.ChevOddInChev2) : a2lDatum ↥(adjointGroup .E8 K) := by
  classical
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK]; norm_num
  have hcp : CharP K 3 :=
    finite_field_prime_power_characteristic Nat.prime_three le_rfl hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  haveI : Finite (ModGL .E8 K) := finite_modGL
  have ha : ∀ i, bitsTuple (K := K) e8BitsE7 i = 1 ∨ bitsTuple (K := K) e8BitsE7 i = -1 :=
    bitsTuple_mem _
  set H := subsystemGroup .E8 K e8LeviE7 with hH_def
  set Q := rootSubgroup .E8 K hiE8 ⊔ rootSubgroup .E8 K (-hiE8) with hQ_def
  have hS : rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsE7)) = H ⊔ Q := by
    rw [rootCharKernel_e8BitsE7 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hQmap : (rootGroup (rootOperatorFamily .E8) K hiE8 ⊔
      rootGroup (rootOperatorFamily .E8) K (-hiE8)).map (adjointGroup .E8 K).subtype = Q := by
    rw [Subgroup.map_sup, map_subtype_rootGroup _ isRoot_hiE8,
      map_subtype_rootGroup _ (IsRoot.neg isRoot_hiE8)]
  have hcomm' : Commutes (⨆ k, rankOne (adjDatum (rootOperatorFamily .E8) K).rootGroup
      (e8E7Node k)) (rootGroup (rootOperatorFamily .E8) K hiE8 ⊔
        rootGroup (rootOperatorFamily .E8) K (-hiE8)) :=
    ClassicalInvolution.RouteD.commutes_iSup_left.2 fun k =>
      commutes_rootPair_of_noG2 noG2_E8 (isRoot_single _ _) isRoot_hiE8
        (e8E7Node_ne_hiE8 k).1 (e8E7Node_ne_hiE8 k).2 (iform_e8E7Node_hiE8 k)
        (not_isRoot_e8E7Node_hiE8 k).1 (not_isRoot_e8E7Node_hiE8 k).2
  have hcomm : Commutes H Q := by
    rw [hH_def, show e8LeviE7 = Set.range e8E7Node from rfl,
      ← map_subtype_iSup_rankOne e8E7Node, ← hQmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' x hx y hy]
  obtain ⟨hqH, hlieH⟩ :=
    e8_levi_E7_recognition (K := K) (p := 3) (f := 1) Nat.prime_three (by norm_num) hK'
  have hHcomp := a2l_levi_component_toral hK2 ha hS hcomm hqH
  obtain ⟨Ψ, hker, hrange⟩ :=
    exists_psi_A5_E8 (K := K) (p := 3) (f := 1) Nat.prime_three (by norm_num) hK'
  let Ψ' : SL(6, K) →* ModGL .E8 K := (adjointGroup .E8 K).subtype.comp Ψ
  have hrange' : Ψ'.range = subsystemGroup .E8 K e8LeviA5 := by
    change ((adjointGroup .E8 K).subtype.comp Ψ).range = _
    rw [MonoidHom.range_comp, hrange]
    exact map_subtype_iSup_rankOne e8A5Node
  have hker' : Ψ'.ker ≤ center SL(6, K) := fun g hg =>
    hker (MonoidHom.mem_ker.2 (Subtype.ext (MonoidHom.mem_ker.1 hg)))
  have hAT : Ψ'.range ≤ H := hrange' ▸ a2l_subsystemGroup_mono e8LeviA5_subset
  have hzA : rootDiagUnit .E8 (bitsTuple (K := K) e8BitsE7) ∈ Ψ'.range := by
    rw [hrange']
    exact a2l_rootDiagUnit_e8BitsE7_mem
  have hz2 := a2l_rootDiagUnit_e8BitsE7_mul_self (K := K)
  have hz1 := a2l_rootDiagUnit_e8BitsE7_ne_one hK2
  have hTU : TypU ↥H := by
    have hm : HarrisLit.IsSimpleChevalleyOver 3 (↥H ⧸ center ↥H) := ⟨.E7, 0, 1, hlieH⟩
    refine a2l_typU_of_chev3_even hqH (a2l_two_dvd_card_of_involution H (hAT hzA) hz2 hz1) hm
      (a2l_not_inChev2_of_card hC hm ?_)
    have hcard : Nat.card (↥H ⧸ center ↥H) = Open.ordE7 (3 ^ 1) :=
      ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two (t := .E7) (p := 3) (f := 1)
        (by norm_num) (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hlieH)
    rw [hcard]
    decide
  exact a2l_datum_of_levi_a5 hK hz2 hz1 hHcomp hTU Ψ' hker' hAT hzA

theorem a2lE8Three_holds (hC : HypA2.ChevOddInChev2) : a2lE8Three := by
  intro X _ _ hX
  have hc := hX.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hc.2
  exact a2lDatum_of_mulEquiv e.symm (a2l_e8_datum_three (by rw [hK]; norm_num) hC)

end Datum

end CFSG.OddStandard.SmallF3.HypA2Leaves
