module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporFive
public import CFSG.RankThree.Native.Co2FiveCentralizers
public import CFSG.RankThree.Native.Co3FiveCentralizers

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem lines_subtype {n p : ℕ} {P Q : Subgroup (Equiv.Perm (Fin n))} (hQP : Q ≤ P) {ι : Type*}
    (line : ι → Equiv.Perm (Fin n))
    (hlinesSet : {H : Subgroup (Equiv.Perm (Fin n)) | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun j => Subgroup.zpowers (line j)))
    (hmem : ∀ j, line j ∈ P) :
    ∀ H : Subgroup ↥P, H ≤ Q.subgroupOf P → Nat.card H = p →
      ∃ j, H = Subgroup.zpowers (⟨line j, hmem j⟩ : ↥P) := by
  intro H hH hc
  have hmap : H.map P.subtype ∈
      {H : Subgroup (Equiv.Perm (Fin n)) | H ≤ Q ∧ Nat.card H = p} := by
    refine ⟨?_, by rw [Subgroup.card_map_of_injective P.subtype_injective]; exact hc⟩
    rintro _ ⟨h, hh, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hH hh)
  rw [hlinesSet] at hmap
  obtain ⟨j, hj⟩ := hmap
  refine ⟨j, Subgroup.map_injective P.subtype_injective ?_⟩
  rw [← hj, MonoidHom.map_zpowers]
  rfl

theorem orderOf_line {n p : ℕ} {Q : Subgroup (Equiv.Perm (Fin n))} {ι : Type*}
    (line : ι → Equiv.Perm (Fin n))
    (hlinesSet : {H : Subgroup (Equiv.Perm (Fin n)) | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun j => Subgroup.zpowers (line j))) (j : ι) :
    line j ∈ Q ∧ orderOf (line j) = p := by
  have h : Subgroup.zpowers (line j) ∈
      {H : Subgroup (Equiv.Perm (Fin n)) | H ≤ Q ∧ Nat.card H = p} := by
    rw [hlinesSet]; exact ⟨j, rfl⟩
  exact ⟨h.1 (Subgroup.mem_zpowers _), by rw [← Nat.card_zpowers]; exact h.2⟩

theorem nonabelian_of_card {n : ℕ} {P Q : Subgroup (Equiv.Perm (Fin n))} (hQP : Q ≤ P)
    {z : Equiv.Perm (Fin n)} (hzQ : z ∈ Q)
    (h : ¬ Nat.card Q ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set (Equiv.Perm (Fin n))) ⊓ P)) :
    ∃ a ∈ (Q.subgroupOf P), ∃ b ∈ (Q.subgroupOf P), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  apply h
  refine Subgroup.card_dvd_of_le fun q hq => ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hQP hq⟩
  have := hcon ⟨q, hQP hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨z, hQP hzQ⟩ (Subgroup.mem_subgroupOf.2 hzQ)
  exact congrArg Subtype.val this

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen

namespace CFSG.RankThree.Native

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

section Co3


theorem kd264SporAt_Co3 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : KD264Gen.KD264SporAt p .Co3 := by
  obtain ⟨⟨hQP, ⟨S, hS⟩, hQcard, -⟩, ⟨hlinesSet, -⟩, htr, hrec0, -, hC0, hC0card, hDs, hDnab,
    hDcard, hcentD, -⟩ := R3E_Co3_full_five_centralizer_structures
  have e : CFSG.Blueprint.NativeSporadic.Co3 ≃* ↥CFSG.Sporadic.Schreier.Co3.co3P :=
    CFSG.Sporadic.Schreier.Co3.co3PermEquiv
  have hfin : Finite ↥CFSG.Sporadic.Schreier.Co3.co3P := inferInstance
  have hs : IsSimpleGroup ↥CFSG.Sporadic.Schreier.Co3.co3P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 e.symm
  have hcard : Nat.card ↥CFSG.Sporadic.Schreier.Co3.co3P = 495766656000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Co3.card_Co3
  have hDP : co3FiveD ≤ CFSG.Sporadic.Schreier.Co3.co3P :=
    co3FiveD_le_C0.trans (hC0 ▸ inf_le_right)
  have hnc : ∃ a c : ↥CFSG.Sporadic.Schreier.Co3.co3P, a * c ≠ c * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hDnab
    exact ⟨⟨g, hDP hg⟩, ⟨h, hDP hh⟩, fun he => hgh (congrArg Subtype.val he)⟩
  have b : ↥CFSG.Sporadic.Schreier.Co3.co3P ≃* (TauCeti.CFSGIndex.sporadic .Co3).Group :=
    e.symm.trans (hbr .Co3).some
  refine @KD264Gen.kd264SporAt_of_model hOut p hp hp2 .Co3 ↥CFSG.Sporadic.Schreier.Co3.co3P _ hfin
    hs hnc b ?_
  intro hk2 _ hsq
  have hS' : ∀ q ∈ (Nat.primeFactorsList 495766656000).filter (fun q => q ^ 2 ∣ 495766656000),
      q ∈ [2, 3, 5, 7] := by
    simp only [Nat.primeFactorsList_ofNat]
    decide +kernel
  have hk2' : ¬ p = 3 := hk2
  rw [hcard] at hsq
  rcases KD264Gen.eq_of_prime_sq_dvd hp (by norm_num) hsq hS' with h | h | h | h
  · exact absurd h hp2
  · exact absurd h hk2'
  · subst h
    have hline := KD264Gen.orderOf_line co3FiveLine hlinesSet
    have hmem : ∀ j, co3FiveLine j ∈ CFSG.Sporadic.Schreier.Co3.co3P := fun j =>
      hQP (hline j).1
    have hxD : co3FiveLine 0 ∈ Subgroup.centralizer (co3FiveD : Set (Equiv.Perm (Fin 276))) :=
      (Subgroup.mem_inf.1 (hcentD ▸ Subgroup.mem_zpowers (co3FiveLine 0))).1
    obtain ⟨J₀, hJ₀⟩ := KD264Gen.exists_comp_of_record Nat.prime_five (hmem 0) (hline 0).2 hDP hDs
      hDnab (by rw [hDcard]; norm_num) hxD (by rw [← hC0, hC0card]) (by rw [hDcard]; norm_num)
    have hScard : Nat.card (S : Subgroup ↥CFSG.Sporadic.Schreier.Co3.co3P) = 5 ^ 3 := by
      rw [hS, show (5 : ℕ) ^ 3 = 125 by norm_num, ← hQcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
    have hnab := KD264Gen.nonabelian_of_card hQP (hline 0).1 (by rw [hQcard, ← hC0, hC0card]; norm_num)
    refine KD264Gen.kd264RowData_of_lines Nat.prime_five S hScard (hS ▸ hnab)
      (fun j => (⟨co3FiveLine j, hmem j⟩ : ↥CFSG.Sporadic.Schreier.Co3.co3P))
      (fun H hH hc => KD264Gen.lines_subtype hQP co3FiveLine hlinesSet hmem H (hS ▸ hH) hc)
      25 fun j hj => ?_
    have hj25 : j ≠ 25 := fun h => hj (by rw [h])
    have hr : co3FiveRecordOf j = 0 := (hrec0 j).2 (fun h => hj25 (Fin.ext h))
    obtain ⟨htP, htj⟩ := htr j
    rw [hr] at htj
    obtain ⟨J₁, hJ₁⟩ := KD264Gen.exists_comp_conj Nat.prime_five ⟨_, htP⟩ _ hJ₀
    have heq : (⟨co3FiveTransporter j, htP⟩ : ↥CFSG.Sporadic.Schreier.Co3.co3P) *
        ⟨co3FiveLine 0, hmem 0⟩ * (⟨co3FiveTransporter j, htP⟩)⁻¹ = ⟨co3FiveLine j, hmem j⟩ :=
      Subtype.ext htj
    rw [heq] at hJ₁
    exact ⟨J₁, hJ₁⟩
  · subst h
    exact absurd hsq (by norm_num)

end Co3

section Co2


theorem kd264SporAt_Co2 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : KD264Gen.KD264SporAt p .Co2 := by
  obtain ⟨⟨hQP, ⟨S, hS⟩, hQcard, -⟩, ⟨hlinesSet, -⟩, htr, hrec0, -, -, -, -, -, -, -, -, hC1,
    hC1card, hDs, hDnab, hDcard, hcentD, -⟩ := R3E_Co2_full_five_centralizer_structures
  have e : CFSG.Blueprint.NativeSporadic.Co2 ≃* ↥CFSG.Sporadic.Co2Cert.co2P :=
    CFSG.Sporadic.Co2Cert.co2PermEquiv
  have hfin : Finite ↥CFSG.Sporadic.Co2Cert.co2P := inferInstance
  have hs : IsSimpleGroup ↥CFSG.Sporadic.Co2Cert.co2P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co2.isSimpleGroup_Co2 e.symm
  have hcard : Nat.card ↥CFSG.Sporadic.Co2Cert.co2P = 42305421312000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Co2.card_Co2
  have hDP : co2FiveD ≤ CFSG.Sporadic.Co2Cert.co2P :=
    co2FiveD_le_C1.trans (hC1 ▸ inf_le_right)
  have hnc : ∃ a c : ↥CFSG.Sporadic.Co2Cert.co2P, a * c ≠ c * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hDnab
    exact ⟨⟨g, hDP hg⟩, ⟨h, hDP hh⟩, fun he => hgh (congrArg Subtype.val he)⟩
  have b : ↥CFSG.Sporadic.Co2Cert.co2P ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group :=
    e.symm.trans (hbr .Co2).some
  refine @KD264Gen.kd264SporAt_of_model hOut p hp hp2 .Co2 ↥CFSG.Sporadic.Co2Cert.co2P _ hfin
    hs hnc b ?_
  intro hk2 _ hsq
  have hS' : ∀ q ∈ (Nat.primeFactorsList 42305421312000).filter (fun q => q ^ 2 ∣ 42305421312000),
      q ∈ [2, 3, 5, 7] := by
    simp only [Nat.primeFactorsList_ofNat]
    decide +kernel
  have hk2' : ¬ p = 3 := hk2
  rw [hcard] at hsq
  rcases KD264Gen.eq_of_prime_sq_dvd hp (by norm_num) hsq hS' with h | h | h | h
  · exact absurd h hp2
  · exact absurd h hk2'
  · subst h
    have hline := KD264Gen.orderOf_line co2FiveLine hlinesSet
    have hmem : ∀ j, co2FiveLine j ∈ CFSG.Sporadic.Co2Cert.co2P := fun j => hQP (hline j).1
    have hxD : co2FiveLine 1 ∈ Subgroup.centralizer (co2FiveD : Set (Equiv.Perm (Fin 2300))) :=
      (Subgroup.mem_inf.1 (hcentD ▸ Subgroup.mem_zpowers (co2FiveLine 1))).1
    obtain ⟨J₀, hJ₀⟩ := KD264Gen.exists_comp_of_record Nat.prime_five (hmem 1) (hline 1).2 hDP hDs
      hDnab (by rw [hDcard]; norm_num) hxD (by rw [← hC1, hC1card]) (by rw [hDcard])
    have hScard : Nat.card (S : Subgroup ↥CFSG.Sporadic.Co2Cert.co2P) = 5 ^ 3 := by
      rw [hS, show (5 : ℕ) ^ 3 = 125 by norm_num, ← hQcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
    have hnab := KD264Gen.nonabelian_of_card hQP (hline 1).1 (by rw [hQcard, ← hC1, hC1card]; norm_num)
    refine KD264Gen.kd264RowData_of_lines Nat.prime_five S hScard (hS ▸ hnab)
      (fun j => (⟨co2FiveLine j, hmem j⟩ : ↥CFSG.Sporadic.Co2Cert.co2P))
      (fun H hH hc => KD264Gen.lines_subtype hQP co2FiveLine hlinesSet hmem H (hS ▸ hH) hc)
      0 fun j hj => ?_
    have hj0 : j ≠ 0 := fun h => hj (by rw [h])
    have hr : co2FiveRecordOf j = 1 := by
      have h1 : co2FiveRecordOf j ≠ 0 := fun h => hj0 (Fin.ext ((hrec0 j).1 h))
      omega
    obtain ⟨htP, htj⟩ := htr j
    rw [hr] at htj
    obtain ⟨J₁, hJ₁⟩ := KD264Gen.exists_comp_conj Nat.prime_five ⟨_, htP⟩ _ hJ₀
    have heq : (⟨co2FiveTransporter j, htP⟩ : ↥CFSG.Sporadic.Co2Cert.co2P) *
        ⟨co2FiveLine 1, hmem 1⟩ * (⟨co2FiveTransporter j, htP⟩)⁻¹ = ⟨co2FiveLine j, hmem j⟩ :=
      Subtype.ext htj
    rw [heq] at hJ₁
    exact ⟨J₁, hJ₁⟩
  · subst h
    exact absurd hsq (by norm_num)

end Co2

end CFSG.RankThree.Native
