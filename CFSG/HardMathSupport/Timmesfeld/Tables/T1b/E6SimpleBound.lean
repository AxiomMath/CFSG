module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylFix
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6SimpleWeylCheck
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeHyperplane
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagTorus
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.TorusBound
public import Certificates.Certificate63001
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

open scoped Matrix Pointwise

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.StandardType
  CFSG.AGLEmbedding.R3 CFSG.HardMathSupport.Timmesfeld.SporadicRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def e6ExpEquiv : (Fin Tag.E6.rank → ZMod 3) ≃ (Fin 6 → ZMod 3) where
  toFun x := fun k => x (e6Idx k)
  invFun v := fun i => v (e6Idx.symm i)
  left_inv x := by funext i; simp
  right_inv v := by funext k; simp

theorem e6ExpEquiv_adAct (w : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ZMod 3) :
    e6ExpEquiv (TableBExc.E6Three.adAct Tag.E6 3 w x) = e6WeylMat w *ᵥ e6ExpEquiv x := by
  funext k
  simp only [e6ExpEquiv, Equiv.coe_fn_mk, Matrix.mulVec, dotProduct, e6WeylMat_apply,
    e6WeylEntry, TableBExc.E6Three.adAct]
  exact (Fintype.sum_equiv e6Idx _ _ fun j => rfl).symm

@[expose] def e6HypFin : Set (Fin 6 → ZMod 3) :=
  {v | kDotL (vecList6 v) = 0}

theorem kDotL_vecList6_e6ExpEquiv (x : Fin Tag.E6.rank → ZMod 3) :
    kDotL (vecList6 (e6ExpEquiv x)) = 0 ↔ NoOffRest.kDotP 3 x = 0 := by
  revert x
  decide +kernel

theorem e6ExpEquiv_mem_hyp (x : Fin Tag.E6.rank → ZMod 3) :
    e6ExpEquiv x ∈ e6HypFin ↔ x ∈ NoOffRest.hypE6 := by
  exact kDotL_vecList6_e6ExpEquiv x

theorem mem_e6HypFin_vecList6 {v : Fin 6 → ZMod 3} :
    vecList6 v ∈ e6HypVecs () ↔ v ∈ e6HypFin := by
  rw [mem_e6HypVecs]
  exact ⟨fun h => h.2, fun h => ⟨vecList6_mem v, h⟩⟩

theorem card_e6HypFin : Nat.card e6HypFin = 3 ^ 5 := by
  have h : Nat.card e6HypFin = Nat.card ↥(NoOffRest.hypE6) := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun v => ⟨e6ExpEquiv.symm v.1, by
          refine (e6ExpEquiv_mem_hyp (e6ExpEquiv.symm v.1)).1 ?_
          simpa using v.2⟩
        invFun := fun x => ⟨e6ExpEquiv x.1, (e6ExpEquiv_mem_hyp x.1).2 x.2⟩
        left_inv := fun v => by ext; simp
        right_inv := fun x => by ext; simp }
  rw [h, NoOffRest.card_hypE6]

theorem card_e6HypFix_le {w : WeylGroup Tag.E6} {A : List ℕ}
    (hA : toMatL 3 6 A = e6WeylMat w) :
    Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧ e6WeylMat w *ᵥ v = v} ≤ nfixHyp A := by
  classical
  have hsub : vecList6 '' {v : Fin 6 → ZMod 3 | v ∈ e6HypFin ∧ e6WeylMat w *ᵥ v = v} ⊆
      ((e6HypVecs ()).filter fun v => matVecA6 A.toArray v == v).toFinset := by
    rintro _ ⟨v, ⟨hv, hfix⟩, rfl⟩
    simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_filter, beq_iff_eq]
    refine ⟨mem_e6HypFin_vecList6.2 hv, ?_⟩
    rw [matVecA6_toArray]
    have hm : matVecL 3 6 A (vecList6 v) ∈ allVecs 3 6 :=
      (mem_allVecs 3 6 _).2 ⟨length_matVecL 3 6 A _, lt_matVecL (by norm_num) 6 A _⟩
    refine vecOf_inj hm (vecList6_mem v) ?_
    rw [vecOf_matVecL, vecOf_vecList6, hA]
    exact hfix
  calc Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧ e6WeylMat w *ᵥ v = v}
      = Nat.card (vecList6 '' {v : Fin 6 → ZMod 3 | v ∈ e6HypFin ∧
          e6WeylMat w *ᵥ v = v}) :=
        (Nat.card_image_of_injective vecList6_injective _).symm
    _ ≤ Nat.card (((e6HypVecs ()).filter fun v => matVecA6 A.toArray v == v).toFinset :
          Set (List ℕ)) := Nat.card_mono (Finset.finite_toSet _) hsub
    _ = (((e6HypVecs ()).filter fun v => matVecA6 A.toArray v == v).toFinset).card :=
        Nat.card_coe_set_eq _ |>.trans (Set.ncard_coe_finset _)
    _ ≤ nfixHyp A := List.toFinset_card_le _

theorem card_e6HypInter_le {w w' : WeylGroup Tag.E6} {A B : List ℕ}
    (hA : toMatL 3 6 A = e6WeylMat w) (hB : toMatL 3 6 B = e6WeylMat w') :
    Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧ e6WeylMat w *ᵥ v = v ∧
      e6WeylMat w' *ᵥ v = v} ≤ nInterHyp A B := by
  classical
  have hsub : vecList6 '' {v : Fin 6 → ZMod 3 | v ∈ e6HypFin ∧ e6WeylMat w *ᵥ v = v ∧
      e6WeylMat w' *ᵥ v = v} ⊆
      ((e6HypVecs ()).filter fun v => matVecA6 A.toArray v == v &&
        matVecA6 B.toArray v == v).toFinset := by
    rintro _ ⟨v, ⟨hv, hfix, hfix'⟩, rfl⟩
    simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_filter, Bool.and_eq_true,
      beq_iff_eq]
    refine ⟨mem_e6HypFin_vecList6.2 hv, ?_, ?_⟩
    · rw [matVecA6_toArray]
      have hm : matVecL 3 6 A (vecList6 v) ∈ allVecs 3 6 :=
        (mem_allVecs 3 6 _).2 ⟨length_matVecL 3 6 A _, lt_matVecL (by norm_num) 6 A _⟩
      refine vecOf_inj hm (vecList6_mem v) ?_
      rw [vecOf_matVecL, vecOf_vecList6, hA]
      exact hfix
    · rw [matVecA6_toArray]
      have hm : matVecL 3 6 B (vecList6 v) ∈ allVecs 3 6 :=
        (mem_allVecs 3 6 _).2 ⟨length_matVecL 3 6 B _, lt_matVecL (by norm_num) 6 B _⟩
      refine vecOf_inj hm (vecList6_mem v) ?_
      rw [vecOf_matVecL, vecOf_vecList6, hB]
      exact hfix'
  calc Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧ e6WeylMat w *ᵥ v = v ∧
        e6WeylMat w' *ᵥ v = v}
      = Nat.card (vecList6 '' {v : Fin 6 → ZMod 3 | v ∈ e6HypFin ∧ e6WeylMat w *ᵥ v = v ∧
          e6WeylMat w' *ᵥ v = v}) :=
        (Nat.card_image_of_injective vecList6_injective _).symm
    _ ≤ Nat.card (((e6HypVecs ()).filter fun v => matVecA6 A.toArray v == v &&
          matVecA6 B.toArray v == v).toFinset : Set (List ℕ)) :=
        Nat.card_mono (Finset.finite_toSet _) hsub
    _ = (((e6HypVecs ()).filter fun v => matVecA6 A.toArray v == v &&
          matVecA6 B.toArray v == v).toFinset).card :=
        Nat.card_coe_set_eq _ |>.trans (Set.ncard_coe_finset _)
    _ ≤ nInterHyp A B := List.toFinset_card_le _

section Finite

theorem e6SimpleFacts_holds : E6SimpleFacts :=
  e6SimpleFacts_of_check Certificates.certificate63001

theorem card_e6HypFix_mul_card_le_of_le_syl (F : Subgroup (WeylGroup Tag.E6))
    (hF : IsElemAbelian 3 F) (hFP : F ≤ e6Syl) :
    Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧ ∀ w ∈ F, e6WeylMat w *ᵥ v = v} *
      Nat.card F ≤ 3 ^ 5 := by
  classical
  haveI : Fintype F := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := exists_card_pow_of_isElemAbelian hF
  have hdvd : 3 ^ k ∣ 3 ^ 4 := by
    have h := Subgroup.card_dvd_of_le hFP
    rw [hk, card_e6Syl, show (81 : ℕ) = 3 ^ 4 by norm_num] at h
    exact h
  have hk4 : k ≤ 4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  rw [hk]
  interval_cases k
  ·
    have hbot : F = ⊥ := by
      rw [← Subgroup.card_eq_one]
      simpa using hk
    subst hbot
    have hE : Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
        ∀ w ∈ (⊥ : Subgroup (WeylGroup Tag.E6)), e6WeylMat w *ᵥ v = v} =
        Nat.card e6HypFin := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun v => ⟨v.1, v.2.1⟩
          invFun := fun v => ⟨v.1, v.2, by simp⟩
          left_inv := fun v => rfl
          right_inv := fun v => rfl }
    rw [hE, card_e6HypFin]
    norm_num
  ·
    obtain ⟨x, hx⟩ : ∃ x : F, x ≠ 1 := by
      have h1 : 1 < Nat.card F := by rw [hk]; norm_num
      by_contra hcon
      push Not at hcon
      have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 fun y hy =>
        congrArg Subtype.val (hcon ⟨y, hy⟩)
      rw [hbot, Subgroup.card_bot] at h1
      exact absurd h1 (by norm_num)
    have hxne : (x : WeylGroup Tag.E6) ≠ 1 := fun h => hx (Subtype.ext h)
    have hx3 : (x : WeylGroup Tag.E6) ^ 3 = 1 := hF.2 (x : WeylGroup Tag.E6) x.2
    obtain ⟨A, hA, hAM, hAO⟩ := exists_isO3L (hFP x.2) hxne hx3
    have hle : Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
        ∀ w ∈ F, e6WeylMat w *ᵥ v = v} ≤
        Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
          e6WeylMat (x : WeylGroup Tag.E6) *ᵥ v = v} :=
      Nat.card_mono (Set.toFinite _) fun v hv => ⟨hv.1, hv.2 x x.2⟩
    have h27 : Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
        e6WeylMat (x : WeylGroup Tag.E6) *ᵥ v = v} ≤ 27 :=
      (card_e6HypFix_le hAM).trans
        (e6SimpleFacts_holds.nfix_le A (List.mem_filter.2 ⟨hA, hAO⟩))
    calc Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
          ∀ w ∈ F, e6WeylMat w *ᵥ v = v} * 3 ^ 1
        ≤ 27 * 3 := Nat.mul_le_mul (hle.trans h27) (by norm_num)
      _ ≤ 3 ^ 5 := by norm_num
  ·
    have hcardF : 9 ≤ Nat.card F := by rw [hk]; norm_num
    obtain ⟨x, hx⟩ : ∃ x : F, x ≠ 1 := by
      have h1 : 1 < Nat.card F := by omega
      by_contra hcon
      push Not at hcon
      have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 fun y hy =>
        congrArg Subtype.val (hcon ⟨y, hy⟩)
      rw [hbot, Subgroup.card_bot] at h1
      exact absurd h1 (by norm_num)
    have hxne : (x : WeylGroup Tag.E6) ≠ 1 := fun h => hx (Subtype.ext h)
    have hx3 : (x : WeylGroup Tag.E6) ^ 3 = 1 := hF.2 (x : WeylGroup Tag.E6) x.2
    have hzcard : Nat.card (Subgroup.zpowers (x : WeylGroup Tag.E6)) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx3 hxne]
    have hnotle : ¬ F ≤ Subgroup.zpowers (x : WeylGroup Tag.E6) := by
      intro hle
      have hdvd : Nat.card F ∣ 3 := by
        rw [← hzcard]
        exact Subgroup.card_dvd_of_le hle
      have h3 : Nat.card F ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    obtain ⟨y, hyF, hyz⟩ :
        ∃ y ∈ F, (y : WeylGroup Tag.E6) ∉ Subgroup.zpowers (x : WeylGroup Tag.E6) := by
      by_contra hcon
      push Not at hcon
      exact hnotle fun z hz => hcon z hz
    have hyne : (y : WeylGroup Tag.E6) ≠ 1 := fun h => hyz (h ▸ Subgroup.one_mem _)
    have hyne' : (y : WeylGroup Tag.E6) ≠ (x : WeylGroup Tag.E6) :=
      fun h => hyz (h ▸ Subgroup.mem_zpowers _)
    have hyne2 : (y : WeylGroup Tag.E6) ≠ (x : WeylGroup Tag.E6) ^ 2 :=
      fun h => hyz (h ▸ (Subgroup.zpowers (x : WeylGroup Tag.E6)).pow_mem
        (Subgroup.mem_zpowers _) 2)
    have hcxy : (x : WeylGroup Tag.E6) * (y : WeylGroup Tag.E6) =
        (y : WeylGroup Tag.E6) * (x : WeylGroup Tag.E6) :=
      congrArg Subtype.val (hF.1.is_comm.comm x ⟨y, hyF⟩)
    have hy3 : (y : WeylGroup Tag.E6) ^ 3 = 1 := hF.2 (y : WeylGroup Tag.E6) hyF
    obtain ⟨A, hA, hAM, hAO⟩ := exists_isO3L (hFP x.2) hxne hx3
    obtain ⟨B, hB, hBM, hBO⟩ := exists_isO3L (hFP hyF) hyne hy3
    have hle : Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
        ∀ w ∈ F, e6WeylMat w *ᵥ v = v} ≤
        Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
          e6WeylMat (x : WeylGroup Tag.E6) *ᵥ v = v ∧
          e6WeylMat (y : WeylGroup Tag.E6) *ᵥ v = v} :=
      Nat.card_mono (Set.toFinite _) fun v hv => ⟨hv.1, hv.2 x x.2, hv.2 y hyF⟩
    have h9 : Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
        e6WeylMat (x : WeylGroup Tag.E6) *ᵥ v = v ∧
        e6WeylMat (y : WeylGroup Tag.E6) *ᵥ v = v} ≤ 9 := by
      refine (card_e6HypInter_le hAM hBM).trans
        (e6SimpleFacts_holds.nInter_le A (List.mem_filter.2 ⟨hA, hAO⟩) B
          (List.mem_filter.2 ⟨hB, hBO⟩) ?_ ?_ ?_)
      · intro hAB
        exact hyne' (e6WeylMat_injective (by rw [← hBM, ← hAB, hAM]))
      · intro hB2
        refine hyne2 (e6WeylMat_injective ?_)
        rw [← hBM, hB2, toMatL_mmulL, hAM, ← map_mul, ← pow_two]
      · apply toMatL_inj6 (mmulL_spec _ _) (mmulL_spec _ _)
        rw [toMatL_mmulL, toMatL_mmulL, hAM, hBM, ← map_mul, ← map_mul, hcxy]
    calc Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
          ∀ w ∈ F, e6WeylMat w *ᵥ v = v} * 3 ^ 2
        ≤ 9 * 9 := Nat.mul_le_mul (hle.trans h9) (by norm_num)
      _ ≤ 3 ^ 5 := by norm_num
  ·
    have hcardF : 9 ≤ Nat.card F := by rw [hk]; norm_num
    obtain ⟨x, hx⟩ : ∃ x : F, x ≠ 1 := by
      have h1 : 1 < Nat.card F := by omega
      by_contra hcon
      push Not at hcon
      have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 fun y hy =>
        congrArg Subtype.val (hcon ⟨y, hy⟩)
      rw [hbot, Subgroup.card_bot] at h1
      exact absurd h1 (by norm_num)
    have hxne : (x : WeylGroup Tag.E6) ≠ 1 := fun h => hx (Subtype.ext h)
    have hx3 : (x : WeylGroup Tag.E6) ^ 3 = 1 := hF.2 (x : WeylGroup Tag.E6) x.2
    have hzcard : Nat.card (Subgroup.zpowers (x : WeylGroup Tag.E6)) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx3 hxne]
    have hnotle : ¬ F ≤ Subgroup.zpowers (x : WeylGroup Tag.E6) := by
      intro hle
      have hdvd : Nat.card F ∣ 3 := by
        rw [← hzcard]
        exact Subgroup.card_dvd_of_le hle
      have h3 : Nat.card F ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    obtain ⟨y, hyF, hyz⟩ :
        ∃ y ∈ F, (y : WeylGroup Tag.E6) ∉ Subgroup.zpowers (x : WeylGroup Tag.E6) := by
      by_contra hcon
      push Not at hcon
      exact hnotle fun z hz => hcon z hz
    have hyne : (y : WeylGroup Tag.E6) ≠ 1 := fun h => hyz (h ▸ Subgroup.one_mem _)
    have hyne' : (y : WeylGroup Tag.E6) ≠ (x : WeylGroup Tag.E6) :=
      fun h => hyz (h ▸ Subgroup.mem_zpowers _)
    have hyne2 : (y : WeylGroup Tag.E6) ≠ (x : WeylGroup Tag.E6) ^ 2 :=
      fun h => hyz (h ▸ (Subgroup.zpowers (x : WeylGroup Tag.E6)).pow_mem
        (Subgroup.mem_zpowers _) 2)
    have hcxy : (x : WeylGroup Tag.E6) * (y : WeylGroup Tag.E6) =
        (y : WeylGroup Tag.E6) * (x : WeylGroup Tag.E6) :=
      congrArg Subtype.val (hF.1.is_comm.comm x ⟨y, hyF⟩)
    have hy3 : (y : WeylGroup Tag.E6) ^ 3 = 1 := hF.2 (y : WeylGroup Tag.E6) hyF
    obtain ⟨A, hA, hAM, hAO⟩ := exists_isO3L (hFP x.2) hxne hx3
    obtain ⟨B, hB, hBM, hBO⟩ := exists_isO3L (hFP hyF) hyne hy3
    have hle : Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
        ∀ w ∈ F, e6WeylMat w *ᵥ v = v} ≤
        Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
          e6WeylMat (x : WeylGroup Tag.E6) *ᵥ v = v ∧
          e6WeylMat (y : WeylGroup Tag.E6) *ᵥ v = v} :=
      Nat.card_mono (Set.toFinite _) fun v hv => ⟨hv.1, hv.2 x x.2, hv.2 y hyF⟩
    have h9 : Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
        e6WeylMat (x : WeylGroup Tag.E6) *ᵥ v = v ∧
        e6WeylMat (y : WeylGroup Tag.E6) *ᵥ v = v} ≤ 9 := by
      refine (card_e6HypInter_le hAM hBM).trans
        (e6SimpleFacts_holds.nInter_le A (List.mem_filter.2 ⟨hA, hAO⟩) B
          (List.mem_filter.2 ⟨hB, hBO⟩) ?_ ?_ ?_)
      · intro hAB
        exact hyne' (e6WeylMat_injective (by rw [← hBM, ← hAB, hAM]))
      · intro hB2
        refine hyne2 (e6WeylMat_injective ?_)
        rw [← hBM, hB2, toMatL_mmulL, hAM, ← map_mul, ← pow_two]
      · apply toMatL_inj6 (mmulL_spec _ _) (mmulL_spec _ _)
        rw [toMatL_mmulL, toMatL_mmulL, hAM, hBM, ← map_mul, ← map_mul, hcxy]
    calc Nat.card {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧
          ∀ w ∈ F, e6WeylMat w *ᵥ v = v} * 3 ^ 3
        ≤ 9 * 27 := Nat.mul_le_mul (hle.trans h9) (by norm_num)
      _ ≤ 3 ^ 5 := by norm_num
  ·
    exfalso
    have hFeq : F = e6Syl :=
      Subgroup.eq_of_le_of_card_ge hFP (by rw [card_e6Syl, hk]; norm_num)
    have ht := wordProd_mem_e6Syl 0 (by norm_num)
    have hc := wordProd_mem_e6Syl 1 (by norm_num)
    rw [← hFeq] at ht hc
    have hcomm := congrArg Subtype.val (hF.1.is_comm.comm ⟨_, ht⟩ ⟨_, hc⟩)
    simp only [Subgroup.coe_mul] at hcomm
    have hM := congrArg e6WeylMat hcomm
    rw [map_mul, map_mul, e6WeylMat_wordProd, e6WeylMat_wordProd,
      e6SylWordsF_getD_val 0 (by norm_num), e6SylWordsF_getD_val 1 (by norm_num),
      ← toMatL_mmulL, ← toMatL_mmulL] at hM
    exact e6SylFacts.noncomm (toMatL_inj6 (mmulL_spec _ _) (mmulL_spec _ _) hM)

def e6HypFixEquiv (F : Subgroup (WeylGroup Tag.E6)) :
    {v : ↥(NoOffRest.hypE6) // ∀ a ∈ F, NoOffRest.hypPerm a v = v} ≃
    {v : Fin 6 → ZMod 3 // v ∈ e6HypFin ∧ ∀ w ∈ F, e6WeylMat w *ᵥ v = v} where
  toFun v :=
    ⟨e6ExpEquiv v.1.1, (e6ExpEquiv_mem_hyp v.1.1).2 v.1.2, fun w hw => by
      have h := congrArg Subtype.val (v.2 w hw)
      rw [NoOffRest.coe_hypPerm_apply] at h
      rw [← e6ExpEquiv_adAct, h]⟩
  invFun v :=
    ⟨⟨e6ExpEquiv.symm v.1, (e6ExpEquiv_mem_hyp (e6ExpEquiv.symm v.1)).1 (by
      rw [Equiv.apply_symm_apply]
      exact v.2.1)⟩, fun w hw => by
      apply Subtype.ext
      rw [NoOffRest.coe_hypPerm_apply]
      have h := v.2.2 w hw
      have h2 : e6ExpEquiv (TableBExc.E6Three.adAct Tag.E6 3 w (e6ExpEquiv.symm v.1)) = v.1 := by
        rw [e6ExpEquiv_adAct, Equiv.apply_symm_apply]
        exact h
      exact e6ExpEquiv.injective (by rw [h2, Equiv.apply_symm_apply])⟩
  left_inv v := by
    ext1
    simp
  right_inv v := by
    ext1
    simp

theorem card_e6Hyp_mul_card_le (F : Subgroup (WeylGroup Tag.E6)) (hF : IsElemAbelian 3 F) :
    Nat.card {v : ↥(NoOffRest.hypE6) // ∀ a ∈ F, NoOffRest.hypPerm a v = v} * Nat.card F ≤
      3 ^ 5 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 F := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hF.2 g g.2)⟩
  obtain ⟨Q, hFQ⟩ := hp.exists_le_sylow
  let P : Sylow 3 (WeylGroup Tag.E6) :=
    Sylow.ofCard e6Syl (by rw [card_e6Syl, card_weylGroup_E6', factorization_51840]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E6) Q P
  have hle : F.map (MulAut.conj g).toMonoidHom ≤ e6Syl := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj g) • x ∈ (MulAut.conj g) • (Q : Subgroup (WeylGroup Tag.E6)) :=
      Subgroup.smul_mem_pointwise_smul x _ _ (hFQ hx)
    rwa [← Sylow.coe_subgroup_smul, hg, Sylow.coe_ofCard] at h1
  have hF' : IsElemAbelian 3 (F.map (MulAut.conj g).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hF (MulAut.conj g).toMonoidHom
  have hcard := NoOffRest.card_fix_map_conj NoOffRest.hypPerm F g
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [← hcard, ← Subgroup.card_map_of_injective hinj]
  rw [Nat.card_congr (e6HypFixEquiv (F.map (MulAut.conj g).toMonoidHom))]
  exact card_e6HypFix_mul_card_le_of_le_syl _ hF' hle

end Finite

section Torus

open CFSG.HardMathSupport.Lang.E6Descent

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def e6K : Fin Tag.E6.rank → ℕ := fun i => (NoOffRest.kE6 i).toNat

theorem e6K_cast (i : Fin Tag.E6.rank) :
    ((NoOffRest.kE6 i : ℤ) : ZMod 3) = (e6K i : ZMod 3) := by
  revert i
  decide +kernel

@[expose] def kChar (a : Fin Tag.E6.rank → Kˣ) : Kˣ := ∏ i, a i ^ (e6K i)

theorem kChar_one : kChar (1 : Fin Tag.E6.rank → Kˣ) = 1 := by
  simp [kChar]

theorem kChar_pow (a : Fin Tag.E6.rank → Kˣ) (n : ℕ) : kChar (a ^ n) = kChar a ^ n := by
  simp only [kChar, Pi.pow_apply]
  have h : (∏ i, (a i ^ n) ^ e6K i) = ∏ i, (a i ^ e6K i) ^ n := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h, Finset.prod_pow]

theorem kChar_zetaVec {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (x : Fin Tag.E6.rank → ZMod 3) :
    kChar (TableBExc.E6Three.zetaVec ζ hζ x) = ζ ^ (∑ i, (x i).val * e6K i) := by
  have h : (∏ i, (ζ ^ (x i).val) ^ (e6K i)) = ∏ i, ζ ^ ((x i).val * e6K i) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_mul]
  simp only [kChar, TableBExc.E6Three.zetaVec_apply]
  rw [h, Finset.prod_pow_eq_pow_sum]

theorem kChar_cartanChar (c : Fin Tag.E6.rank → Kˣ) :
    ∃ y : Kˣ, kChar (cartanChar c) = y ^ 3 := by
  have hT : ∀ j : Fin Tag.E6.rank, ∃ t : ℤ, ∑ i, (Tag.E6.cartan j i : ℤ) * (e6K i : ℤ) = 3 * t := by
    intro j
    have h : (3 : ℤ) ∣ ∑ i, (Tag.E6.cartan j i : ℤ) * (e6K i : ℤ) := by
      revert j
      decide +kernel
    refine ⟨(∑ i, (Tag.E6.cartan j i : ℤ) * (e6K i : ℤ)) / 3, ?_⟩
    rw [mul_comm]
    exact (Int.ediv_mul_cancel h).symm
  choose t ht using hT
  refine ⟨∏ j, c j ^ t j, ?_⟩
  have step1 : kChar (cartanChar c) =
      ∏ j, c j ^ (∑ i, (Tag.E6.cartan j i : ℤ) * (e6K i : ℤ)) := by
    simp only [kChar, cartanChar]
    trans ∏ i, ∏ j, (c j ^ (Tag.E6.cartan j i : ℤ)) ^ (e6K i)
    · refine Finset.prod_congr rfl fun i _ => ?_
      exact (Finset.prod_pow Finset.univ (e6K i) (fun j => c j ^ (Tag.E6.cartan j i : ℤ))).symm
    · trans ∏ j, ∏ i, (c j ^ (Tag.E6.cartan j i : ℤ)) ^ (e6K i)
      · exact Finset.prod_comm
      · refine Finset.prod_congr rfl fun j _ => ?_
        have h : (∏ i, (c j ^ (Tag.E6.cartan j i : ℤ)) ^ (e6K i)) =
            ∏ i, c j ^ ((Tag.E6.cartan j i : ℤ) * (e6K i : ℤ)) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← zpow_natCast, zpow_mul]
        rw [h, Finset.prod_zpow_eq_zpow_sum]
  have step2 : (∏ j, c j ^ (∑ i, (Tag.E6.cartan j i : ℤ) * (e6K i : ℤ))) =
      (∏ j, c j ^ t j) ^ 3 := by
    have h : (∏ j, c j ^ (∑ i, (Tag.E6.cartan j i : ℤ) * (e6K i : ℤ))) =
        ∏ j, (c j ^ t j) ^ 3 := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [ht j, mul_comm, ← zpow_natCast (c j ^ t j) 3, ← zpow_mul]
      norm_num
    rw [h, ← Finset.prod_pow]
  rw [step1, step2]

theorem kChar_eq_one_of_cartanChar (h3 : 3 ∣ Nat.card K - 1) (h9 : ¬ 9 ∣ Nat.card K - 1)
    {c : Fin Tag.E6.rank → Kˣ} (ha3 : cartanChar c ^ 3 = 1) :
    kChar (cartanChar c) = 1 := by
  obtain ⟨y, hy⟩ := kChar_cartanChar c
  have hy9 : y ^ 9 = 1 := by
    have h : kChar (cartanChar c) ^ 3 = 1 := by
      rw [← kChar_pow, ha3, kChar_one]
    rw [hy] at h
    rw [← pow_mul] at h
    norm_num at h
    exact h
  have hdvd9 : orderOf y ∣ 9 := orderOf_dvd_iff_pow_eq_one.2 hy9
  haveI : Fintype Kˣ := Fintype.ofFinite _
  have hdvdq : orderOf y ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    simpa [Nat.card_eq_fintype_card] using orderOf_dvd_card (G := Kˣ) (x := y)
  have hpos : 0 < orderOf y := orderOf_pos y
  have hle9 : orderOf y ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd9
  have hcases : orderOf y = 1 ∨ orderOf y = 3 ∨ orderOf y = 9 := by
    interval_cases hval : orderOf y
    · exact Or.inl rfl
    · exact absurd hdvd9 (by decide)
    · exact Or.inr (Or.inl rfl)
    · exact absurd hdvd9 (by decide)
    · exact absurd hdvd9 (by decide)
    · exact absurd hdvd9 (by decide)
    · exact absurd hdvd9 (by decide)
    · exact absurd hdvd9 (by decide)
    · exact Or.inr (Or.inr rfl)
  have hy3 : y ^ 3 = 1 := by
    rcases hcases with h1 | h3' | h9'
    · rw [orderOf_eq_one_iff.1 h1]; norm_num
    · rw [← h3']; exact pow_orderOf_eq_one y
    · exact absurd (h9' ▸ hdvdq) h9
  rw [hy, hy3]

theorem kDotP_eq_zero_of_kChar {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {x : Fin Tag.E6.rank → ZMod 3} (h : kChar (TableBExc.E6Three.zetaVec ζ hζ x) = 1) :
    NoOffRest.kDotP 3 x = 0 := by
  have hN : ζ ^ (∑ i, (x i).val * e6K i) = 1 := by
    rw [← kChar_zetaVec hζ x, h]
  have hdvd' : orderOf ζ ∣ ∑ i, (x i).val * e6K i := orderOf_dvd_iff_pow_eq_one.2 hN
  rw [hζo] at hdvd'
  have hcast : NoOffRest.kDotP 3 x =
      ((∑ i, (x i).val * e6K i : ℕ) : ZMod 3) := by
    simp only [NoOffRest.kDotP]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [e6K_cast i, ← ZMod.natCast_zmod_val (x i)]
    rw [← Nat.cast_mul]
    congr 1
    exact Nat.mul_comm _ _
  rw [hcast]
  exact (ZMod.natCast_eq_zero_iff _ 3).2 hdvd'

@[expose] noncomputable def e6Mon : Subgroup (adjointGroup Tag.E6 K) :=
  (monomialSubgroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K)

@[expose] noncomputable def e6Tor : Subgroup (adjointGroup Tag.E6 K) :=
  (torusGroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K)

@[expose] noncomputable def e6MonHom : e6Mon (K := K) →* WeylGroup Tag.E6 :=
  (weylQuotientHom Tag.E6 K).comp
    (Subgroup.subgroupOfEquivOfLe
      (monomialSubgroup_le_adjointGroup' (τ := Tag.E6) (K := K))).toMonoidHom

theorem e6MonHom_apply (n : e6Mon (K := K)) :
    e6MonHom n = weylQuotientHom Tag.E6 K
      (Subgroup.subgroupOfEquivOfLe
        (monomialSubgroup_le_adjointGroup' (τ := Tag.E6) (K := K)) n) := rfl

theorem e6MonHom_surjective : Function.Surjective (e6MonHom (K := K)) := by
  have h : Function.Surjective (weylQuotientHom Tag.E6 K) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff,
      ← (coxeterSystem Tag.E6).subgroup_closure_range_simple, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨weylElt Tag.E6 K i 1, weylElt_mem_monomialSubgroup i⟩,
      weylQuotientHom_eq (mapsRootLines_weylElt i)⟩
  exact h.comp (Subgroup.subgroupOfEquivOfLe _).surjective

theorem e6MonHom_eq_one_iff {n : e6Mon (K := K)} :
    e6MonHom n = 1 ↔ (n : adjointGroup Tag.E6 K) ∈ e6Tor (K := K) := by
  rw [e6MonHom_apply]
  set g : monomialSubgroup Tag.E6 K :=
    Subgroup.subgroupOfEquivOfLe (monomialSubgroup_le_adjointGroup'
      (τ := Tag.E6) (K := K)) n with hgdef
  have hcoe : ((g : ModGL Tag.E6 K)) = ((n : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) := rfl
  constructor
  · intro hn
    change ((n : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K
    obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets g.2
    have hmaps : MapsRootLines (g : ModGL Tag.E6 K) w := by
      rw [hgk]
      simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
    have hw : w = 1 := (weylQuotientHom_eq hmaps).symm.trans hn
    have hgk' : (g : ModGL Tag.E6 K) = k := by rw [hgk, hw, canonicalRep_one, mul_one]
    rw [← hcoe, hgk']
    exact hk
  · intro hn
    change ((n : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K at hn
    have hgT : (g : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K := by rwa [hcoe]
    exact weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hgT)

theorem e6Tor_commutative : ∀ a ∈ e6Tor (K := K), ∀ b ∈ e6Tor (K := K), a * b = b * a := by
  intro a ha b hb
  refine Subtype.ext ?_
  exact DiagTorus.Dgrp_comm
    (DiagTorus.torusGroup_le_Dgrp (Subgroup.mem_subgroupOf.1 ha))
    (DiagTorus.torusGroup_le_Dgrp (Subgroup.mem_subgroupOf.1 hb))

theorem not_three_dvd_e6Mon_index (h3 : 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ (e6Mon (K := K)).index := by
  have hidxeq : (e6Mon (K := K)).index =
      (monomialSubgroup Tag.E6 K).relIndex (adjointGroup Tag.E6 K) := by
    have h1 := Subgroup.card_mul_index (e6Mon (K := K))
    have h2 := Subgroup.relIndex_mul_card
      (monomialSubgroup Tag.E6 K) (adjointGroup Tag.E6 K)
    have hcard : Nat.card (e6Mon (K := K)) = Nat.card (monomialSubgroup Tag.E6 K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (monomialSubgroup_le_adjointGroup' (τ := Tag.E6) (K := K))).toEquiv
    rw [hcard] at h1
    rw [inf_of_le_left (monomialSubgroup_le_adjointGroup' (τ := Tag.E6) (K := K))] at h2
    have hpos : 0 < Nat.card (monomialSubgroup Tag.E6 K) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h1, ← h2]
    exact mul_comm _ _
  rw [hidxeq]
  exact DiagTorus.not_three_dvd_relIndex_monomial (K := K) h3

theorem pRank_three_adjointGroup_E6_le_five (h3 : 3 ∣ Nat.card K - 1)
    (h9 : ¬ 9 ∣ Nat.card K - 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 5 := by
  classical
  obtain ⟨ζ, hζ, hζo⟩ := DiagTorus.exists_cube_root (K := K) h3
  refine pRank_le_of_torus_normalizer Nat.prime_three (e6Mon (K := K)) (e6Tor (K := K))
    e6Tor_commutative (not_three_dvd_e6Mon_index h3) (e6MonHom (K := K))
    (fun n => e6MonHom_eq_one_iff (K := K) (n := n)) ?_
  intro F S hF hSel hSH hcen
  have hex : ∀ s : S, ∃ x : Fin Tag.E6.rank → ZMod 3,
      ((s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ x) ∧
      x ∈ NoOffRest.hypE6 ∧
      ∀ w ∈ F, TableBExc.E6Three.adAct Tag.E6 3 w x = x := by
    intro s
    have hsT : ((s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K :=
      Subgroup.mem_subgroupOf.1 (hSH s.2)
    obtain ⟨c, hc⟩ := exists_cartanChar_eq_of_mem_torusGroup (τ := Tag.E6) (K := K) hsT
    have hs3 : (s : adjointGroup Tag.E6 K) ^ 3 = 1 := hSel.2 s s.2
    have hs3' : ((s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ^ 3 = 1 :=
      congrArg Subtype.val hs3
    have ha3 : cartanChar c ^ 3 = 1 := by
      refine rootDiagUnit_injective (τ := Tag.E6) (K := K) ?_
      rw [show rootDiagUnit Tag.E6 (cartanChar c ^ 3) =
        (rootDiagUnit Tag.E6 (cartanChar c)) ^ 3 from
          map_pow (rootDiagUnitHom Tag.E6 K) (cartanChar c) 3]
      rw [← hc, hs3', rootDiagUnit_one]
    obtain ⟨x, hx⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ ha3
    have hxhyp : x ∈ NoOffRest.hypE6 := by
      apply kDotP_eq_zero_of_kChar hζo hζ
      rw [hx]
      exact kChar_eq_one_of_cartanChar h3 h9 ha3
    have hsx : ((s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ x) := by
      rw [hx]; exact hc
    refine ⟨x, hsx, hxhyp, fun w hw => ?_⟩
    obtain ⟨e, he⟩ := e6MonHom_surjective (K := K) w
    have hconj := hcen s s.2 e (by rw [he]; exact hw)
    set m : monomialSubgroup Tag.E6 K :=
      Subgroup.subgroupOfEquivOfLe (monomialSubgroup_le_adjointGroup'
        (τ := Tag.E6) (K := K)) e with hm
    have hmval : (m : ModGL Tag.E6 K) =
        ((e : e6Mon (K := K)) : adjointGroup Tag.E6 K) := rfl
    have hconj' : (m : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 (cartanChar c) *
        (m : ModGL Tag.E6 K)⁻¹ = rootDiagUnit Tag.E6 (cartanChar c) := by
      have h := congrArg Subtype.val hconj
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, ← hmval, hc] using h
    have hweyl : weylAct (weylQuotientHom Tag.E6 K m) (cartanChar c) = cartanChar c := by
      rw [monomial_conj_rootDiagUnit m (cartanChar c)] at hconj'
      exact rootDiagUnit_injective hconj'
    have hwφ : weylQuotientHom Tag.E6 K m = w := he
    have hwa : weylAct w (cartanChar c) = cartanChar c := by
      rw [← hwφ]; exact hweyl
    apply TableBExc.E6Three.zetaVec_injective hζo hζ
    calc TableBExc.E6Three.zetaVec ζ hζ (TableBExc.E6Three.adAct Tag.E6 3 w x)
        = weylTuple w (TableBExc.E6Three.zetaVec ζ hζ x) :=
          (TableBExc.E6Three.weylTuple_zetaVec ζ hζ w x).symm
      _ = weylTuple w (cartanChar c) := by rw [hx]
      _ = cartanChar c := hwa
      _ = TableBExc.E6Three.zetaVec ζ hζ x := hx.symm
  choose x hsx hxhyp hxfix using hex
  let Φ : S → {v : ↥(NoOffRest.hypE6) // ∀ a ∈ F, NoOffRest.hypPerm a v = v} :=
    fun s => ⟨⟨x s, hxhyp s⟩, fun w hw => Subtype.ext (hxfix s w hw)⟩
  have hinj : Function.Injective Φ := by
    intro s s' h
    have hxeq : x s = x s' := congrArg (fun v => (v.1 : Fin Tag.E6.rank → ZMod 3)) h
    refine Subtype.ext (Subtype.ext ?_)
    rw [hsx s, hsx s', hxeq]
  have hle : Nat.card S ≤
      Nat.card {v : ↥(NoOffRest.hypE6) // ∀ a ∈ F, NoOffRest.hypPerm a v = v} :=
    Nat.card_le_card_of_injective Φ hinj
  calc Nat.card S * Nat.card F
      ≤ Nat.card {v : ↥(NoOffRest.hypE6) // ∀ a ∈ F, NoOffRest.hypPerm a v = v} *
          Nat.card F := Nat.mul_le_mul_right _ hle
    _ ≤ 3 ^ 5 := card_e6Hyp_mul_card_le F hF

end Torus

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
