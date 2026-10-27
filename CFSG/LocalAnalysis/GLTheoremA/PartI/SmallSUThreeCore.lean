module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU2
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.SmallSU
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Group
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.GroupTheory.PCore.QuasisimpleNormalCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCU
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.RankThree.PartOne.KFCL.BlockSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SmallSUThreeCore

open CFSG CFSG.Open Matrix CFSG.Fischer
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.RankThree.PartOne.KFCL.BlockSL

theorem reindexGL_surjective {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) : Function.Surjective (reindexGL e) := by
  intro A
  refine ⟨reindexGL e.symm A, ?_⟩
  ext i j
  simp [reindexGL_val, Matrix.reindex_apply]

theorem det_eq_one_of_mem_comap_reindexGL {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : GL ι F4}
    (hA : A ∈ (StatedSU (Fintype.card ι) (2 ^ 1) F4).comap
      (reindexGL (Fintype.equivFin ι))) :
    (A : Matrix ι ι F4).det = 1 := by
  have hSU : StatedSU (Fintype.card ι) (2 ^ 1) F4 =
      gramSU hF4 (idGram F4 (Fintype.card ι)) := unitarySU_eq_gramSU hF4 _
  have hgram : reindexGL (Fintype.equivFin ι) A ∈
      gramSU hF4 (idGram F4 (Fintype.card ι)) := by
    rw [← hSU]
    exact hA
  rw [mem_gramSU, reindexGL_val, Matrix.det_reindex_self] at hgram
  exact hgram.2

theorem unitary_of_mem_comap_reindexGL {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : GL ι F4}
    (hA : A ∈ (StatedSU (Fintype.card ι) (2 ^ 1) F4).comap
      (reindexGL (Fintype.equivFin ι))) :
    ((A : Matrix ι ι F4).map bar)ᵀ * (A : Matrix ι ι F4) = 1 := by
  let e := Fintype.equivFin ι
  have hSU : StatedSU (Fintype.card ι) (2 ^ 1) F4 =
      gramSU hF4 (idGram F4 (Fintype.card ι)) := unitarySU_eq_gramSU hF4 _
  have hgram : reindexGL e A ∈ gramSU hF4 (idGram F4 (Fintype.card ι)) := by
    rw [← hSU]
    exact hA
  rw [mem_gramSU, reindexGL_val, hF4_bar, idGram, Units.val_one, Matrix.mul_one] at hgram
  have h := reindex_unitary e.symm (Matrix.reindex e e (A : Matrix ι ι F4)) hgram.1
  simpa [Matrix.reindex_apply] using h

theorem pPrimeCore_eq_bot_of_det_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {U K : Subgroup (GL ι F4)} (hU : U ≤ K)
    (hdet : ∀ y ∈ K, y ∈ U ↔ (y : Matrix ι ι F4).det = 1)
    (hcore : pPrimeCore 3 ↥U = ⊥) : pPrimeCore 3 ↥K = ⊥ := by
  have hker : U.subgroupOf K = (Matrix.GeneralLinearGroup.det.comp K.subtype).ker := by
    ext z
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact (hdet z.1 z.2).1 h
    · intro h
      exact (hdet z.1 z.2).2 (by
        have h' := congrArg Units.val h
        rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h')
  have hnorm : (U.subgroupOf K).Normal := by rw [hker]; infer_instance
  have hdvd : U.relIndex K ∣ 3 := by
    change (U.subgroupOf K).index ∣ 3
    rw [hker, Subgroup.index_ker]
    exact (Subgroup.card_subgroup_dvd_card _).trans (by rw [Nat.card_units, hF4card]; norm_num)
  have h3 : U.relIndex K ∣ 3 ^ 1 := by simpa using hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 1)).1 h3
  haveI : Finite (GL ι F4) := inferInstance
  have hUcore : GLAPPrimeCoreOf 3 U = ⊥ := gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr hcore
  have hKcore : GLAPPrimeCoreOf 3 K = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_of_relIndex_eq_pow Nat.prime_three hU hnorm hk hUcore
  exact gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mp hKcore

private theorem pPrimeCore_three_statedSU_two_eq_bot_of_gramSU {m : ℕ}
    (hNN : NoNormalPPrime 3 (gramSU hF4 (idGram F4 m))) :
    pPrimeCore 3 ↥(StatedSU m (2 ^ 1) F4) = ⊥ := by
  have hSU : StatedSU m (2 ^ 1) F4 = gramSU hF4 (idGram F4 m) := unitarySU_eq_gramSU hF4 m
  have hg : GLAPPrimeCoreOf 3 (StatedSU m (2 ^ 1) F4) = ⊥ := by
    rw [hSU]
    exact CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.core_eq_bot_of_noNormalPPrime
      Nat.prime_three hNN
  exact gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mp hg

theorem pPrimeCore_three_statedSU_two_eq_bot_of_le_three {m : ℕ} (hm : m ≤ 3) :
    pPrimeCore 3 ↥(StatedSU m (2 ^ 1) F4) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  interval_cases m
  · haveI := CFSG.ComponentClassification.Burgoyne.C.subsingleton_statedSU_of_le_one
      (p := 2) (f := 1) (K := F4) hF4 (m := 0) (by norm_num)
    exact Subgroup.eq_bot_of_subsingleton _
  · haveI := CFSG.ComponentClassification.Burgoyne.C.subsingleton_statedSU_of_le_one
      (p := 2) (f := 1) (K := F4) hF4 (m := 1) (by norm_num)
    exact Subgroup.eq_bot_of_subsingleton _
  · exact pPrimeCore_three_statedSU_two_eq_bot_of_gramSU
      (noNormalPPrime_three_gramSU_of_mem hF4 (f := 1) (by norm_num) (Or.inl rfl))
  · exact pPrimeCore_three_statedSU_two_eq_bot_of_gramSU
      (noNormalPPrime_three_gramSU_of_mem hF4 (f := 1) (by norm_num) (Or.inr rfl))

private theorem pPrimeCore_three_statedSU_two_eq_bot_of_four_six {m : ℕ} (hm4 : 4 ≤ m)
    (hm6 : m ≤ 6) : pPrimeCore 3 ↥(StatedSU m (2 ^ 1) F4) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup (StatedSU m (2 ^ 1) F4) :=
    (StatedScalars (Fin m) F4).subgroupOf (StatedSU m (2 ^ 1) F4)
  have hZcard : Nat.card ↥Z ∣ 3 := by
    have h := CFSG.Quasithin.Vol2.Ch11.SecA.card_scalars_subgroupOf_dvd
      (K := F4) (H := StatedSU m (2 ^ 1) F4)
    simpa [Z, Nat.card_eq_fintype_card, F4.card] using h
  have hZcore : pPrimeCore 3 ↥Z = ⊥ := by
    rw [pPrimeCore_eq_bot_iff]
    intro K hK hcop
    have hKdvd : Nat.card K ∣ 3 := (Subgroup.card_subgroup_dvd_card K).trans hZcard
    rcases (Nat.dvd_prime Nat.prime_three).1 hKdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq (H := K) h1
    · exfalso
      rw [h3] at hcop
      exact (by norm_num : ¬ Nat.Coprime 3 3) hcop
  haveI : Z.Normal := by dsimp [Z]; infer_instance
  have hsimple : IsSimpleGroup (StatedSU m (2 ^ 1) F4 ⧸ Z) := by
    change IsSimpleGroup (StatedProj (StatedSU m (2 ^ 1) F4))
    exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F4 2 1 hF4card m
      (by omega) (by rintro ⟨h, -⟩; omega)
  have hdvd : 3 ∣ Nat.card (StatedSU m (2 ^ 1) F4 ⧸ Z) := by
    change 3 ∣ Nat.card (StatedProj (StatedSU m (2 ^ 1) F4))
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F4) (p := 2) (f := 1)
      (n := m) Nat.prime_two (by norm_num) hF4card (by omega)]
    interval_cases m <;> decide
  exact pPrimeCore_eq_bot_of_normal_quotient_simple Nat.prime_three hZcore hsimple hdvd

theorem pPrimeCore_three_statedSU_two_eq_bot {m : ℕ} (hm : m ≤ 6) :
    pPrimeCore 3 ↥(StatedSU m (2 ^ 1) F4) = ⊥ := by
  by_cases h3 : m ≤ 3
  · exact pPrimeCore_three_statedSU_two_eq_bot_of_le_three h3
  · exact pPrimeCore_three_statedSU_two_eq_bot_of_four_six (by omega) hm

theorem pPrimeCore_comap_reindexGL_statedSU_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι ≤ 6) :
    pPrimeCore 3 ↥((StatedSU (Fintype.card ι) (2 ^ 1) F4).comap
      (reindexGL (Fintype.equivFin ι))) = ⊥ := by
  let e := Fintype.equivFin ι
  have hsurj : Function.Surjective (reindexGL e) := reindexGL_surjective e
  have hinj : Function.Injective (reindexGL e) := reindexGL_injective e
  have hmap : ((StatedSU (Fintype.card ι) (2 ^ 1) F4).comap (reindexGL e)).map (reindexGL e) =
      StatedSU (Fintype.card ι) (2 ^ 1) F4 :=
    Subgroup.map_comap_eq_self_of_surjective hsurj _
  let eSub : ↥((StatedSU (Fintype.card ι) (2 ^ 1) F4).comap (reindexGL e)) ≃*
      ↥(StatedSU (Fintype.card ι) (2 ^ 1) F4) :=
    (Subgroup.equivMapOfInjective _ _ hinj).trans (MulEquiv.subgroupCongr hmap)
  have h := pPrimeCore_map_iso 3 eSub
  rw [pPrimeCore_three_statedSU_two_eq_bot hcard] at h
  exact (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 3 ↥((StatedSU (Fintype.card ι)
    (2 ^ 1) F4).comap (reindexGL e))) (f := eSub.toMonoidHom) eSub.injective).1 h

end CFSG.LocalAnalysis.GLTheoremA.SmallSUThreeCore
