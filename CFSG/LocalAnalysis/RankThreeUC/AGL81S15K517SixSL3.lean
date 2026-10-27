module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K541Even
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpBlocks
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.LocalAnalysis.RankThreeUC.S15 CFSG.LocalAnalysis.RankThreeUC.S15.KFactsPair

section Sl3

theorem isLThreeOdd_of_equiv_sl3 {S : Type} [Group S] {F : Type} [Field F] [Finite F] {k m : ℕ}
    (hk : Odd k) (hF : Nat.card F = 2 ^ k) (hm : m = 3)
    (e : S ≃* Matrix.SpecialLinearGroup (Fin m) F) : IsLThreeOdd S := by
  subst hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk0 : 0 < k := hk.pos
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField 2 k) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 2 k hk0.ne']
  let φ : F ≃+* GaloisField 2 k := FiniteField.ringEquivOfCardEq hcard
  let e1 : S ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 k) :=
    e.trans (CFSG.LargeExtraspecial.A2Mod.slEquiv φ)
  by_cases h1 : k = 1
  · subst h1
    let q : TauCeti.PrimePower := ⟨7, 1, Nat.prime_seven, Nat.one_pos⟩
    have hq7 : q.card = 7 := by
      rw [TauCeti.PrimePower.card_def]
      rfl
    have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [hq7]
      simp
    obtain ⟨e2⟩ := K541Proof.nonempty_equiv_sl3_two_of_catalog_A1 (S := (TauCeti.CFSGIndex.lie
      ⟨.A 1 q, hv⟩).Group) ⟨.A 1 q, hv⟩ q hq7 rfl (MulEquiv.refl _)
    exact ⟨1, odd_one, Or.inl ⟨rfl, ⟨.A 1 q, hv⟩, q, hq7, rfl, ⟨e1.trans e2.symm⟩⟩⟩
  · have hk2 : 2 ≤ k := by omega
    let Q : TauCeti.PrimePower := ⟨2, k, Nat.prime_two, hk0⟩
    have hQc : Q.card = 2 ^ k := by
      rw [TauCeti.PrimePower.card_def]
    have hv : (TauCeti.LieTypeIndex.A 2 Q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [hQc]
      have : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      simp
      omega
    obtain ⟨e2⟩ := K541Proof.nonempty_equiv_sl3_of_catalog_A2 (S := (TauCeti.CFSGIndex.lie
      ⟨.A 2 Q, hv⟩).Group) ⟨.A 2 Q, hv⟩ Q rfl rfl hk rfl (MulEquiv.refl _)
    exact ⟨k, hk, Or.inr ⟨hk2, ⟨.A 2 Q, hv⟩, Q, rfl, rfl, rfl, ⟨e1.trans e2.symm⟩⟩⟩

end Sl3


section SpLevi

open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic

theorem leviM_sp_three_equiv {F : Type} [Field F] :
    Nonempty (↥(leviM (rootDatum 3 F) {i : Fin 3 | i ≠ 2}) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F) := by
  classical
  let B : Finset (Fin 4) := {0, 1, 2}
  have hB : B = blkSet {i : Fin 3 | i ≠ 2} (0 : Fin 4) := by
    ext q
    rw [mem_blkSet]
    simp only [SameBlk, Set.mem_setOf_eq, ne_eq, not_not]
    fin_cases q <;> simp [B] <;> omega
  have hl : Fin.last 3 ∉ B := by simp [B]
  have hnodes : nodesOf B = {i : Fin 3 | i ≠ 2} := by
    ext i
    fin_cases i <;> simp [nodesOf, B]
  have hGA : GA F B = leviM (rootDatum 3 F) {i : Fin 3 | i ≠ 2} :=
    (GA_eq (F := F) hB hl).trans (congrArg (leviM (rootDatum 3 F)) hnodes)
  have hcoords : coordsOf B = Finset.univ := by
    ext i
    fin_cases i <;> simp [mem_coordsOf, B]
  have hc : (coordsOf B).card = 3 := by
    rw [hcoords, Finset.card_univ, Fintype.card_fin]
  have e1 := GA_equiv (F := F) B
  rw [hc] at e1
  exact ⟨(MulEquiv.subgroupCongr hGA).symm.trans e1⟩

end SpLevi


section SpinMinusLevi

open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem leviM_spinMinus_four_equiv :
    Nonempty (↥(leviM (minusDatum 4 hirr)
      {i : Fin (minusDatum 4 hirr).rank | i ≠ ⟨2, show 2 < 4 - 1 by norm_num⟩}) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F) := by
  have hset : runNodes 4 0 1 =
      {i : Fin (minusDatum 4 hirr).rank | i ≠ ⟨2, show 2 < 4 - 1 by norm_num⟩} := by
    ext i
    have h3 : i.val < 3 := i.isLt
    simp only [Set.mem_setOf_eq, ne_eq, runNodes, Fin.ext_iff]
    show (0 ≤ i.val ∧ i.val ≤ 1) ↔ ¬ i.val = 2
    omega
  exact ⟨(MulEquiv.subgroupCongr (congrArg (leviM (minusDatum 4 hirr)) hset)).symm.trans
    (chEquivMinus hirr (lo := 0) (hi := 1) (by omega) (by omega) (by omega)).symm⟩

end SpinMinusLevi

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
