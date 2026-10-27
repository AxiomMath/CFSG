module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcRows
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lLeviToral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTypUEven
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Frame
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofAdjointRoots
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralC3

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeafProof CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

section Frame

@[expose] def e7A5Node : Fin 5 → Fin (Tag.rank .E7) :=
  ![e7Node 2, e7Node 3, e7Node 4, e7Node 5, e7Node 6]

theorem e7A5_adj : ∀ i j : Fin 5, j.val = i.val + 1 → e7A5Node i ≠ e7A5Node j ∧
    Tag.cartan .E7 (e7A5Node i) (e7A5Node j) = -1 ∧
    Tag.cartan .E7 (e7A5Node j) (e7A5Node i) = -1 ∧
    ∃ l : Fin 7,
      ¬ (3 : ℤ) ∣ Tag.cartan .E7 (e7A5Node i) l + 2 * Tag.cartan .E7 (e7A5Node j) l := by
  decide

theorem e7A5_nadj : ∀ i j : Fin 5, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
    e7A5Node i ≠ e7A5Node j ∧ Tag.cartan .E7 (e7A5Node i) (e7A5Node j) = 0 ∧
    Tag.cartan .E7 (e7A5Node j) (e7A5Node i) = 0 := by
  decide

@[expose] def e7LeviA5 : Set (Fin (Tag.rank .E7)) := Set.range e7A5Node

@[expose] def e7LeviD6 : Set (Fin (Tag.rank .E7)) := Set.range e7D6Node

theorem e7LeviA5_subset : e7LeviA5 ⊆ e7LeviD6 := by
  have h : ∀ k : Fin 5, ∃ k' : Fin 6, e7D6Node k' = e7A5Node k := by decide
  rintro _ ⟨k, rfl⟩
  exact h k

theorem exists_psi_A5_E7
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ∃ Ψ : SL(6, K) →* adjointGroup .E7 K, Ψ.ker ≤ Subgroup.center SL(6, K) ∧
      Ψ.range = ⨆ k, rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7A5Node k) := by
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSL 6 p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e7A5Node e7A5_adj e7A5_nadj
  obtain ⟨Ψ, hker, hrange, -⟩ :=
    specialLinear_frame_subgroup (m := 5) hadm (by norm_num) hK hcomm hρ hψ
  exact ⟨Ψ, hker, hrange⟩

theorem exists_psi_D6_E7
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ∃ Ψ : spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 6 K)) ∧
      Ψ.range = ⨆ k, rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7D6Node k) ∧
      IsQuasisimple ↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7D6Node k)) ∧
      Blueprint.LieModel
        (↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7D6Node k)) ⧸
          Subgroup.center
            ↥(⨆ k, rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7D6Node k)))
        .POmegaPlus 6 p f := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .POmegaPlus 6 p f := ⟨hp, hf, by norm_num⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e7D6Node e7D6_adj e7D6_nadj
  exact spinPlus_frame_subgroup hadm (by norm_num) hK hcomm hρ hψ

theorem e7_levi_D6_recognition
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    IsQuasisimple ↥(subsystemGroup .E7 K e7LeviD6) ∧
      Blueprint.LieModel (↥(subsystemGroup .E7 K e7LeviD6) ⧸
        Subgroup.center ↥(subsystemGroup .E7 K e7LeviD6)) .POmegaPlus 6 p f := by
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_D6_E7 hp hp2 hK
  set U := ⨆ k, rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7D6Node k) with hU
  let e : U ≃* subsystemGroup .E7 K e7LeviD6 :=
    (U.equivMapOfInjective _ (adjointGroup .E7 K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_iSup_rankOne e7D6Node))
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv e hqs,
    lieModel_of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hlie⟩

end Frame

section Kernel

@[expose] def e7BitsA1D6 : Fin (Tag.rank .E7) → Bool :=
  listMask [true, false, false, false, false, false, false]

theorem e7BitsA1D6_eq_false : ∀ j : Fin (Tag.rank .E7), j ≠ e7Node 0 → e7BitsA1D6 j = false := by
  decide

theorem maskPairing_e7BitsA1D6 (α : Fin (Tag.rank .E7) → ℤ) :
    maskPairing e7BitsA1D6 α = α (e7Node 0) := by
  rw [maskPairing, Finset.sum_eq_single (e7Node 0)]
  · simp [show e7BitsA1D6 (e7Node 0) = true from by decide]
  · intro j _ hj
    simp [e7BitsA1D6_eq_false j hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem e7_even_zero_cases : ∀ α ∈ rootFinset .E7, Even (α (e7Node 0)) →
    α (e7Node 0) = 0 ∨ α = e7Theta ∨ α = -e7Theta := by
  decide +kernel

theorem e7D6Node_ne_zero : ∀ k : Fin 6, e7D6Node k ≠ e7Node 0 := by decide

theorem eq_zero_of_forall_e7D6Node_ne :
    ∀ i : Fin (Tag.rank .E7), (∀ k, e7D6Node k ≠ i) → i = e7Node 0 := by
  decide

theorem mem_parabolicRoots_e7LeviD6 {α : Fin (Tag.rank .E7) → ℤ} :
    α ∈ parabolicRoots .E7 e7LeviD6 ↔ IsRoot .E7 α ∧ α (e7Node 0) = 0 := by
  refine and_congr_right fun _ => ⟨fun h => h _ ?_, fun h i hi => ?_⟩
  · rintro ⟨k, hk⟩
    exact e7D6Node_ne_zero k hk
  · rw [eq_zero_of_forall_e7D6Node_ne i fun k hk => hi ⟨k, hk⟩]
    exact h

theorem rootCharKernel_e7BitsA1D6
    {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    rootCharKernel (bitsTuple (K := K) e7BitsA1D6) =
      parabolicRoots .E7 e7LeviD6 ∪ {e7Theta, -e7Theta} := by
  rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  ext α
  rw [mem_kernelRoots_maskChar, maskPairing_e7BitsA1D6, Set.mem_union, mem_parabolicRoots_e7LeviD6,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hα, hev⟩
    rcases e7_even_zero_cases α (mem_rootFinset.2 hα) hev with h | h | h
    · exact Or.inl ⟨hα, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨hα, h⟩ | rfl | rfl)
    · exact ⟨hα, by rw [h]; decide⟩
    · exact ⟨isRoot_e7Theta, by decide⟩
    · exact ⟨IsRoot.neg isRoot_e7Theta, by decide⟩

theorem e7D6Node_ne_theta : ∀ k : Fin 6, (Pi.single (e7D6Node k) 1 : Fin (Tag.rank .E7) → ℤ) ≠
    e7Theta ∧ (Pi.single (e7D6Node k) 1 : Fin (Tag.rank .E7) → ℤ) ≠ -e7Theta := by
  decide

theorem iform_e7D6Node_theta : ∀ k : Fin 6,
    iform (Pi.single (e7D6Node k) 1 : Fin (Tag.rank .E7) → ℤ) e7Theta = 0 := by
  decide +kernel

theorem not_isRoot_e7D6Node_theta : ∀ k : Fin 6,
    ¬ IsRoot .E7 (Pi.single (e7D6Node k) 1 + e7Theta) ∧
      ¬ IsRoot .E7 (Pi.single (e7D6Node k) 1 + -e7Theta) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)]
  decide +kernel

end Kernel

section Torus

variable {K : Type} [Field K]

theorem a2l_rootDiagUnit_e7BitsA1D6 :
    rootDiagUnit .E7 (bitsTuple (K := K) e7BitsA1D6) =
      torusElt .E7 K (e7Node 2) (-1) * torusElt .E7 K (e7Node 4) (-1) *
        torusElt .E7 K (e7Node 6) (-1) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  have hpar : ∀ j : Fin (Tag.rank .E7),
      (e7BitsA1D6 j = true ∧ (Tag.cartan .E7 (e7Node 2) j + Tag.cartan .E7 (e7Node 4) j +
        Tag.cartan .E7 (e7Node 6) j) % 2 = 1) ∨
      (e7BitsA1D6 j = false ∧ (Tag.cartan .E7 (e7Node 2) j + Tag.cartan .E7 (e7Node 4) j +
        Tag.cartan .E7 (e7Node 6) j) % 2 = 0) := by
    decide
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, ← zpow_add, ← zpow_add]
  rcases hpar j with ⟨hb, hm⟩ | ⟨hb, hm⟩
  · rw [(Int.odd_iff.2 hm).neg_one_zpow]
    simp [bitsTuple, hb]
  · rw [(Int.even_iff.2 hm).neg_one_zpow]
    simp [bitsTuple, hb]

theorem a2l_rootDiagUnit_e7BitsA1D6_mem :
    rootDiagUnit .E7 (bitsTuple (K := K) e7BitsA1D6) ∈ subsystemGroup .E7 K e7LeviA5 := by
  rw [a2l_rootDiagUnit_e7BitsA1D6]
  exact mul_mem (mul_mem
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := e7LeviA5) (i := e7Node 2) ⟨0, rfl⟩ (-1)))
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := e7LeviA5) (i := e7Node 4) ⟨2, rfl⟩ (-1))))
    (subsystemTorus_le_subsystemGroup
      (torusElt_mem_subsystemTorus (A := e7LeviA5) (i := e7Node 6) ⟨4, rfl⟩ (-1)))

theorem a2l_rootDiagUnit_e7BitsA1D6_mul_self :
    rootDiagUnit .E7 (bitsTuple (K := K) e7BitsA1D6) *
      rootDiagUnit .E7 (bitsTuple (K := K) e7BitsA1D6) = 1 := by
  have h : (bitsTuple (K := K) e7BitsA1D6 * bitsTuple e7BitsA1D6 :
      Fin (Tag.rank .E7) → Kˣ) = 1 := by
    funext j
    rcases bitsTuple_mem (K := K) e7BitsA1D6 j with h | h <;> simp [h]
  rw [← rootDiagUnit_mul, h, rootDiagUnit_one]

theorem a2l_rootDiagUnit_e7BitsA1D6_ne_one (hK2 : ringChar K ≠ 2) :
    rootDiagUnit .E7 (bitsTuple (K := K) e7BitsA1D6) ≠ 1 := by
  intro h
  have h1 := congrFun (rootDiagUnit_injective (h.trans (rootDiagUnit_one (τ := .E7)).symm))
    (e7Node 0)
  have h2 : bitsTuple (K := K) e7BitsA1D6 (e7Node 0) = -1 := by
    simp [bitsTuple, show e7BitsA1D6 (e7Node 0) = true from by decide]
  rw [h2] at h1
  exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h1)

end Torus

section Datum


theorem a2l_e7_datum_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (hC : HypA2.ChevOddInChev2) : a2lDatum ↥(adjointGroup .E7 K) := by
  classical
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK]; norm_num
  have hcp : CharP K 3 :=
    finite_field_prime_power_characteristic Nat.prime_three le_rfl hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  haveI : Finite (ModGL .E7 K) := finite_modGL
  have ha : ∀ i, bitsTuple (K := K) e7BitsA1D6 i = 1 ∨ bitsTuple (K := K) e7BitsA1D6 i = -1 :=
    bitsTuple_mem _
  set H := subsystemGroup .E7 K e7LeviD6 with hH_def
  set Q := rootSubgroup .E7 K e7Theta ⊔ rootSubgroup .E7 K (-e7Theta) with hQ_def
  have hS : rootSpan .E7 K (rootCharKernel (bitsTuple (K := K) e7BitsA1D6)) = H ⊔ Q := by
    rw [rootCharKernel_e7BitsA1D6 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hQmap : (rootGroup (rootOperatorFamily .E7) K e7Theta ⊔
      rootGroup (rootOperatorFamily .E7) K (-e7Theta)).map (adjointGroup .E7 K).subtype = Q := by
    rw [Subgroup.map_sup, map_subtype_rootGroup _ isRoot_e7Theta,
      map_subtype_rootGroup _ (IsRoot.neg isRoot_e7Theta)]
  have hcomm' : Commutes (⨆ k, rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup
      (e7D6Node k)) (rootGroup (rootOperatorFamily .E7) K e7Theta ⊔
        rootGroup (rootOperatorFamily .E7) K (-e7Theta)) :=
    ClassicalInvolution.RouteD.commutes_iSup_left.2 fun k =>
      commutes_rootPair_of_noG2 noG2_E7 (isRoot_single _ _) isRoot_e7Theta
        (e7D6Node_ne_theta k).1 (e7D6Node_ne_theta k).2 (iform_e7D6Node_theta k)
        (not_isRoot_e7D6Node_theta k).1 (not_isRoot_e7D6Node_theta k).2
  have hcomm : Commutes H Q := by
    rw [hH_def, show e7LeviD6 = Set.range e7D6Node from rfl,
      ← map_subtype_iSup_rankOne e7D6Node, ← hQmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' x hx y hy]
  obtain ⟨hqH, hlieH⟩ :=
    e7_levi_D6_recognition (K := K) (p := 3) (f := 1) Nat.prime_three (by norm_num) hK'
  have hHcomp := a2l_levi_component_toral hK2 ha hS hcomm hqH
  obtain ⟨Ψ, hker, hrange⟩ :=
    exists_psi_A5_E7 (K := K) (p := 3) (f := 1) Nat.prime_three (by norm_num) hK'
  let Ψ' : SL(6, K) →* ModGL .E7 K := (adjointGroup .E7 K).subtype.comp Ψ
  have hrange' : Ψ'.range = subsystemGroup .E7 K e7LeviA5 := by
    change ((adjointGroup .E7 K).subtype.comp Ψ).range = _
    rw [MonoidHom.range_comp, hrange]
    exact map_subtype_iSup_rankOne e7A5Node
  have hker' : Ψ'.ker ≤ center SL(6, K) := fun g hg =>
    hker (MonoidHom.mem_ker.2 (Subtype.ext (MonoidHom.mem_ker.1 hg)))
  have hAT : Ψ'.range ≤ H := hrange' ▸ a2l_subsystemGroup_mono e7LeviA5_subset
  have hzA : rootDiagUnit .E7 (bitsTuple (K := K) e7BitsA1D6) ∈ Ψ'.range := by
    rw [hrange']
    exact a2l_rootDiagUnit_e7BitsA1D6_mem
  have hz2 := a2l_rootDiagUnit_e7BitsA1D6_mul_self (K := K)
  have hz1 := a2l_rootDiagUnit_e7BitsA1D6_ne_one hK2
  have hTU : TypU ↥H := by
    have hm : HarrisLit.IsSimpleChevalleyOver 3 (↥H ⧸ center ↥H) := ⟨.POmegaPlus, 6, 1, hlieH⟩
    refine a2l_typU_of_chev3_even hqH (a2l_two_dvd_card_of_involution H (hAT hzA) hz2 hz1) hm
      (a2l_not_inChev2_of_card hC hm ?_)
    have hcard : Nat.card (↥H ⧸ center ↥H) = Open.ordD 6 (3 ^ 1) :=
      (ClassicalInvolution.card_statedClassicalModel_of_ne_two (by norm_num)
        (GH74.statedClassicalModel_of_lieModel (by norm_num) hlieH)).2.2.2.2.1 rfl
    rw [hcard]
    decide
  exact a2l_datum_of_levi_a5 hK hz2 hz1 hHcomp hTU Ψ' hker' hAT hzA

theorem a2lE7Three_holds (hC : HypA2.ChevOddInChev2) : a2lE7Three := by
  intro X _ _ hX
  have hc := hX.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hc.2
  exact a2lDatum_of_mulEquiv e.symm (a2l_e7_datum_three (by rw [hK]; norm_num) hC)

end Datum

end CFSG.OddStandard.SmallF3.HypA2Leaves
