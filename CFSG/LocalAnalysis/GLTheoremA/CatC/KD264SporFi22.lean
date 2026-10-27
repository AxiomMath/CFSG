module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporRecords
public import CFSG.RankThree.Native.Fi22FiveCentralizers

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.RankThree.Native

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.Monster.B.Fischer

section Fi22


theorem kd264SporAt_Fi22 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : KD264Gen.KD264SporAt p .Fi22 := by
  obtain ⟨⟨hQP, -, hQcard, -⟩, ⟨hlinesSet, -⟩, -, hrec⟩ :=
    R3E_Fi22_full_five_centralizers_common_outer_involution
  obtain ⟨-, -, hCP, hCcard, hDP, hDs, hDnab, hDcard, -, -, -, -, -, hcentD⟩ := hrec 0
  have e : CFSG.Blueprint.NativeSporadic.Fi22 ≃* ↥fi22P := fi22PermEquiv
  have hfin : Finite ↥fi22P := inferInstance
  have hs : IsSimpleGroup ↥fi22P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e.symm
  have hcard : Nat.card ↥fi22P = 64561751654400 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Fi22.card_Fi22
  have hnc : ∃ a c : ↥fi22P, a * c ≠ c * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hDnab
    exact ⟨⟨g, hDP hg⟩, ⟨h, hDP hh⟩, fun he => hgh (congrArg Subtype.val he)⟩
  have b : ↥fi22P ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group :=
    e.symm.trans (hbr .Fi22).some
  refine @KD264Gen.kd264SporAt_of_model hOut p hp hp2 .Fi22 ↥fi22P _ hfin hs hnc b ?_
  intro hk2 _ hsq
  have hmem := KD264Gen.prime_sq_dvd_mem hp (by rw [hcard]; norm_num) hsq
  rw [hcard] at hmem
  have hsub : ∀ q ∈ (Nat.primeFactorsList 64561751654400).filter
      (fun q => q ^ 2 ∣ 64561751654400), q = 2 ∨ q = 3 ∨ q = 5 := by
    simp only [Nat.primeFactorsList_ofNat]
    decide +kernel
  have hk2' : ¬ p = 3 := hk2
  rcases hsub p hmem with h | h | h
  · exact absurd h hp2
  · exact absurd h hk2'
  · subst h
    have hl0 : Subgroup.zpowers (fi22FiveLine 0) ∈
        {H : Subgroup (Equiv.Perm (Fin 3510)) | H ≤ fi22FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨0, rfl⟩
    have hxo : orderOf (fi22FiveLine 0) = 5 := by
      rw [← Nat.card_zpowers]; exact hl0.2
    have hxP : fi22FiveLine 0 ∈ fi22P :=
      hQP (hl0.1 (Subgroup.mem_zpowers _))
    have hxD : fi22FiveLine 0 ∈ Subgroup.centralizer (fi22FiveD 0 : Set (Equiv.Perm (Fin 3510))) :=
      (Subgroup.mem_inf.1 (hcentD ▸ Subgroup.mem_zpowers (fi22FiveLine 0))).1
    obtain ⟨J₀, hJ₀⟩ := KD264Gen.exists_comp_of_record Nat.prime_five hxP hxo hDP hDs hDnab
      (by rw [hDcard]; norm_num) hxD (by rw [← hCP, hCcard]) (by rw [hDcard])
    have hxo' : orderOf (⟨fi22FiveLine 0, hxP⟩ : ↥fi22P) = 5 := by
      rw [Subgroup.orderOf_mk, hxo]
    exact KD264Gen.kd264RowData_of_sq Nat.prime_five (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num) _ hxo' hJ₀

end Fi22

end CFSG.RankThree.Native
