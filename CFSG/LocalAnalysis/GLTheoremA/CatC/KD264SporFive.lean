module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporRecords
public import CFSG.RankThree.Native.SuzFiveCentralizers
public import CFSG.RankThree.PartOne.KS.J2
public import CFSG.RankThree.PartOne.KS.HeFiveCentralizers
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.Sporadic.SmallOddCore.J2Local

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem kd264RowData_of_record_sq {n p : ℕ} (hp : p.Prime) {P D R : Subgroup (Equiv.Perm (Fin n))}
    (hsq : p ^ 2 ∣ Nat.card ↥P) (hcube : ¬ p ^ 3 ∣ Nat.card ↥P) {x : Equiv.Perm (Fin n)}
    (hxP : x ∈ P) (hxo : orderOf x = p) (hDP : D ≤ P) (hs : IsSimpleGroup ↥D)
    (hnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) (hpD : p ∣ Nat.card ↥D)
    (hxD : x ∈ Subgroup.centralizer (D : Set (Equiv.Perm (Fin n)))) (hPR : P ≤ R)
    {N : ℕ} (hC : Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) ≤ N)
    (hN : N ≤ 2 * (p * Nat.card ↥D)) : KD264RowData p ↥P := by
  have hle : Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P ≤
      Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R := inf_le_inf_left _ hPR
  obtain ⟨J₀, hJ₀⟩ := exists_comp_of_record hp hxP hxo hDP hs hnab hpD hxD
    ((Subgroup.card_le_of_le hle).trans hC) hN
  exact kd264RowData_of_sq hp hsq hcube ⟨x, hxP⟩ (by rw [Subgroup.orderOf_mk, hxo]) hJ₀

theorem eq_of_prime_sq_dvd {p N : ℕ} (hp : p.Prime) (hN : N ≠ 0) (h : p ^ 2 ∣ N)
    (hS : ∀ q ∈ N.primeFactorsList.filter (fun q => q ^ 2 ∣ N), q ∈ [2, 3, 5, 7]) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have := hS p (prime_sq_dvd_mem hp hN h)
  simpa using this

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen

namespace CFSG.RankThree.Native

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.Sporadic.SuzOddCore


theorem kd264SporAt_Suz (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : KD264Gen.KD264SporAt p .Suz := by
  obtain ⟨⟨hQM, -, -, -, -⟩, ⟨hlinesSet, -⟩, hrecD, hrec0, -⟩ :=
    R3E_Suz_full_five_centralizer_structures
  obtain ⟨hC0, hDs, hDnab, hDM⟩ := hrecD 0
  obtain ⟨hCcard, hDcard, hcentD, -⟩ := hrec0 0 (Or.inl rfl)
  have e : CFSG.Blueprint.NativeSporadic.Suz ≃* ↥suzM := suzEquivM
  have hfin : Finite ↥suzM := inferInstance
  have hs : IsSimpleGroup ↥suzM :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_Suz e.symm
  have hcard : Nat.card ↥suzM = 448345497600 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Suz.card_Suz
  have hnc : ∃ a c : ↥suzM, a * c ≠ c * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hDnab
    exact ⟨⟨g, hDM hg⟩, ⟨h, hDM hh⟩, fun he => hgh (congrArg Subtype.val he)⟩
  have b : ↥suzM ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group := e.symm.trans (hbr .Suz).some
  refine @KD264Gen.kd264SporAt_of_model hOut p hp hp2 .Suz ↥suzM _ hfin hs hnc b ?_
  intro hk2 _ hsq
  have hS : ∀ q ∈ (Nat.primeFactorsList 448345497600).filter (fun q => q ^ 2 ∣ 448345497600),
      q ∈ [2, 3, 5, 7] := by
    simp only [Nat.primeFactorsList_ofNat]
    decide +kernel
  have hk2' : ¬ p = 3 := hk2
  have h7 : ¬ 7 ^ 2 ∣ 448345497600 := by norm_num
  rw [hcard] at hsq
  rcases KD264Gen.eq_of_prime_sq_dvd hp (by norm_num) hsq hS with h | h | h | h
  · exact absurd h hp2
  · exact absurd h hk2'
  · subst h
    have hl0 : Subgroup.zpowers (suzFiveLine 0) ∈
        {H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨0, rfl⟩
    have hxo : orderOf (suzFiveLine 0) = 5 := by rw [← Nat.card_zpowers]; exact hl0.2
    have hxM : suzFiveLine 0 ∈ suzM := hQM (hl0.1 (Subgroup.mem_zpowers _))
    have hxD : suzFiveLine 0 ∈ Subgroup.centralizer (suzFiveD 0 : Set (Equiv.Perm (Fin 1782))) :=
      (Subgroup.mem_inf.1 (hcentD ▸ Subgroup.mem_zpowers (suzFiveLine 0))).1
    exact KD264Gen.kd264RowData_of_record_sq Nat.prime_five (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num) hxM hxo hDM hDs hDnab (by rw [hDcard]; norm_num) hxD
      suzM_le_suzT (by rw [← hC0, hCcard]) (by rw [hDcard])
  · subst h
    exact absurd hsq h7

end CFSG.RankThree.Native

namespace CFSG.RankThree.PartOne

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.Sporadic.SmallOddCore Subgroup

section J2


theorem kd264SporAt_J2 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (h3 : KD264Gen.KD264RowData 3 ↥CFSG.Sporadic.Schreier.j2P) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : KD264Gen.KD264SporAt p .J2 := by
  obtain ⟨⟨hQP, -, -, -, -⟩, ⟨hlinesSet, -⟩, hrecC, -, hrecD⟩ :=
    R3E_J2_full_five_centralizer_structure
  obtain ⟨hC2, -, -, -⟩ := hrecC 2
  obtain ⟨hCcard, hDP, hDs, hDnab, hDcard, -, hcentD, -⟩ := hrecD 2 (by decide)
  have e : CFSG.Blueprint.NativeSporadic.J2 ≃* ↥CFSG.Sporadic.Schreier.j2P :=
    CFSG.Sporadic.Schreier.j2PermEquiv
  have hfin : Finite ↥CFSG.Sporadic.Schreier.j2P := inferInstance
  have hs : IsSimpleGroup ↥CFSG.Sporadic.Schreier.j2P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e.symm
  have hcard : Nat.card ↥CFSG.Sporadic.Schreier.j2P = 604800 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.J2.card_J2
  have hnc : ∃ a c : ↥CFSG.Sporadic.Schreier.j2P, a * c ≠ c * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hDnab
    exact ⟨⟨g, hDP hg⟩, ⟨h, hDP hh⟩, fun he => hgh (congrArg Subtype.val he)⟩
  have b : ↥CFSG.Sporadic.Schreier.j2P ≃* (TauCeti.CFSGIndex.sporadic .J2).Group :=
    e.symm.trans (hbr .J2).some
  refine @KD264Gen.kd264SporAt_of_model hOut p hp hp2 .J2 ↥CFSG.Sporadic.Schreier.j2P _ hfin hs
    hnc b ?_
  intro _ _ hsq
  have hS : ∀ q ∈ (Nat.primeFactorsList 604800).filter (fun q => q ^ 2 ∣ 604800),
      q ∈ [2, 3, 5, 7] := by
    simp only [Nat.primeFactorsList_ofNat]
    decide +kernel
  rw [hcard] at hsq
  rcases KD264Gen.eq_of_prime_sq_dvd hp (by norm_num) hsq hS with h | h | h | h
  · exact absurd h hp2
  · subst h; exact h3
  · subst h
    have hl2 : zpowers (j2FiveLine 2) ∈
        {H : Subgroup (Equiv.Perm (Fin 315)) | H ≤ j2FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨2, rfl⟩
    have hxo : orderOf (j2FiveLine 2) = 5 := by rw [← Nat.card_zpowers]; exact hl2.2
    have hxP : j2FiveLine 2 ∈ CFSG.Sporadic.Schreier.j2P := hQP (hl2.1 (mem_zpowers _))
    have hxD : j2FiveLine 2 ∈ centralizer (j2FiveD 2 : Set (Equiv.Perm (Fin 315))) :=
      (mem_inf.1 (hcentD ▸ mem_zpowers (j2FiveLine 2))).1
    exact KD264Gen.kd264RowData_of_record_sq Nat.prime_five (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num) hxP hxo hDP hDs hDnab (by rw [hDcard]; norm_num) hxD
      j2P_le_j2R (by rw [inf_comm, ← hC2, hCcard]) (by rw [hDcard] <;> norm_num)
  · subst h
    exact absurd hsq (by norm_num)

end J2

section He


theorem kd264SporAt_He (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (h3 : KD264Gen.KD264RowData 3 ↥CFSG.Sporadic.HeldB.heP) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : KD264Gen.KD264SporAt p .He := by
  obtain ⟨⟨hQP, -, -, -⟩, ⟨hlinesSet, -⟩, -, -, ⟨hC0, hCcard⟩,
    ⟨hDs, hDnab, hDcard, hDP, hcentD, -⟩⟩ := R3E_He_full_five_centralizer_structures
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥CFSG.Sporadic.HeldB.heP :=
    CFSG.Sporadic.HeldB.heEquivP
  have hfin : Finite ↥CFSG.Sporadic.HeldB.heP := inferInstance
  have hs : IsSimpleGroup ↥CFSG.Sporadic.HeldB.heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  have hcard : Nat.card ↥CFSG.Sporadic.HeldB.heP = 4030387200 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.He.card_He
  have hnc : ∃ a c : ↥CFSG.Sporadic.HeldB.heP, a * c ≠ c * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hDnab
    exact ⟨⟨g, hDP hg⟩, ⟨h, hDP hh⟩, fun he => hgh (congrArg Subtype.val he)⟩
  have b : ↥CFSG.Sporadic.HeldB.heP ≃* (TauCeti.CFSGIndex.sporadic .He).Group :=
    e.symm.trans (hbr .He).some
  refine @KD264Gen.kd264SporAt_of_model hOut p hp hp2 .He ↥CFSG.Sporadic.HeldB.heP _ hfin hs hnc b
    ?_
  intro hk2 _ hsq
  have hS : ∀ q ∈ (Nat.primeFactorsList 4030387200).filter (fun q => q ^ 2 ∣ 4030387200),
      q ∈ [2, 3, 5, 7] := by
    simp only [Nat.primeFactorsList_ofNat]
    decide +kernel
  have hk2' : ¬ p = 7 := hk2
  rw [hcard] at hsq
  rcases KD264Gen.eq_of_prime_sq_dvd hp (by norm_num) hsq hS with h | h | h | h
  · exact absurd h hp2
  · subst h; exact h3
  · subst h
    have hl0 : zpowers (heFiveLine 0) ∈
        {H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heFiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨0, rfl⟩
    have hxo : orderOf (heFiveLine 0) = 5 := by rw [← Nat.card_zpowers]; exact hl0.2
    have hxP : heFiveLine 0 ∈ CFSG.Sporadic.HeldB.heP := hQP (hl0.1 (mem_zpowers _))
    have hxD : heFiveLine 0 ∈ centralizer (heFiveD0 : Set (Equiv.Perm (Fin 8330))) :=
      (mem_inf.1 (hcentD ▸ mem_zpowers (heFiveLine 0))).1
    exact KD264Gen.kd264RowData_of_record_sq Nat.prime_five (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num) hxP hxo hDP hDs hDnab (by rw [hDcard]; norm_num) hxD
      CFSG.Sporadic.HeldB.heP_le_heAutGroup (by rw [← hC0, hCcard]) (by rw [hDcard])
  · exact absurd h hk2'

end He

end CFSG.RankThree.PartOne
