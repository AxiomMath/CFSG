module

public import Certificates.Certificate10128
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestHe
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporR3E

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.KDSpor.He7

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open Subgroup
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.RankThree.PartOne
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest (evalW)
open scoped commutatorElement

theorem evalW_mem {G : Type*} [Group G] {m : ℕ} {H : Subgroup G} {g : Fin m → G}
    (hg : ∀ i, g i ∈ H) (w : List (Fin m × Bool)) : evalW g w ∈ H := by
  unfold evalW
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  cases y.2
  · exact H.inv_mem (hg y.1)
  · exact hg y.1

theorem mem_of_pow_eight {G : Type*} [Group G] {C D : Subgroup G} (hDC : D ≤ C)
    (hDn : (D.subgroupOf C).Normal) (hidx : (D.subgroupOf C).index = 7) {g : G} (hg : g ∈ C)
    (h8 : g ^ 8 = 1) : g ∈ D := by
  haveI := hDn
  set N := D.subgroupOf C
  set x : C ⧸ N := QuotientGroup.mk (⟨g, hg⟩ : C)
  have hfin : Nat.card (C ⧸ N) = 7 := by rw [← Subgroup.index]; exact hidx
  haveI : Finite (C ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hfin]; norm_num)
  have h7 : x ^ 7 = 1 := by rw [← hfin]; exact pow_card_eq_one'
  have hx8 : x ^ 8 = 1 := by
    show (QuotientGroup.mk (⟨g, hg⟩ : C) : C ⧸ N) ^ 8 = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨g, hg⟩ : C) ^ 8 = 1 := Subtype.ext (by simpa using h8)
    rw [this, QuotientGroup.mk_one]
  have hx1 : x = 1 := by
    have : x = x ^ 8 * (x ^ 7)⁻¹ := by group
    rw [this, hx8, h7, inv_one, mul_one]
  have hmem : (⟨g, hg⟩ : C) ∈ N := (QuotientGroup.eq_one_iff _).1 hx1
  exact Subgroup.mem_subgroupOf.1 hmem

@[expose] def ppSeven : TauCeti.PrimePower := ⟨7, 1, by norm_num, by norm_num⟩

theorem isChevSimple_seven_L2 (F : Type) [Field F] [Finite F] (hF7 : Nat.card F = 7) :
    IsChevSimple 7 (StatedProj (StatedSL 2 F)) := by
  haveI : Fact ppSeven.p.Prime := ⟨ppSeven.prime_p⟩
  have hv : (TauCeti.LieTypeIndex.A 1 ppSeven).Valid := by
    simp [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, ppSeven, TauCeti.PrimePower.card_def]
  have e : StatedProj (StatedSL 2 F) ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 ppSeven, hv⟩).Group :=
    (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 7 1 (by norm_num)
      (by rw [hF7] <;> norm_num)).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ppSeven hv).symm
  refine Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.A 1 ppSeven, hv⟩, ?_, ⟨e⟩⟩
  show (TauCeti.LieTypeIndex.A 1 ppSeven).characteristic = 7
  rw [TauCeti.LieTypeIndex.characteristic_A]
  rfl

theorem isChevSimple_seven_of_dihedral {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hT : Nat.card T = 168) (S : Sylow 2 T)
    (hS : Nonempty ((S : Subgroup T) ≃* DihedralGroup 4)) : IsChevSimple 7 T := by
  rcases CFSG.Adapters.dihedral_simple_recognition T hnab S 3 (by norm_num) hS with
    ⟨p, f, hp, hp2, hf, hadm, K, _, _, hK, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hodd : Odd (Nat.card K) := by
      rw [hK]
      exact Odd.pow (hp.odd_of_ne_two hp2)
    have hc := CFSG.GH74.GLS.Stage4.card_statedProj_statedSL_two_of_odd (F := K) hodd
    rw [← Nat.card_congr e.toEquiv, hT] at hc
    have hq : Nat.card K = 7 := by
      set q := Nat.card K with hqdef
      have hq3 : 3 ≤ q := by
        have h1 : 1 < q := by rw [hK]; exact Nat.one_lt_pow (by omega) hp.one_lt
        rcases hodd with ⟨k, hk⟩
        omega
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · interval_cases q <;> norm_num at hc
      · have h8 : 8 ≤ q := hgt
        have : 8 * (8 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
          Nat.mul_le_mul h8 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h8 2) 1)
        omega
    exact CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv e.symm
      (isChevSimple_seven_L2 K hq)
  · exfalso
    have := Nat.card_congr e.toEquiv
    rw [hT, Nat.card_eq_fintype_card (α := alternatingGroup (Fin 7)), card_alternatingGroup] at this
    simp [Nat.factorial] at this

section Concrete

open CFSG.Sporadic.HeldB

theorem heSeven_dihedral_check : heSevenDihedralOK () = true := Certificates.certificate10128

@[expose] noncomputable def gC1 (i : Fin 3) : Equiv.Perm (Fin 8330) :=
  permOfArr 8330 heSevenC1Gens[i.val]!

@[expose] noncomputable def heRho : Equiv.Perm (Fin 8330) := evalW gC1 heSevenRhoWord

@[expose] noncomputable def heSigma : Equiv.Perm (Fin 8330) := evalW gC1 heSevenSigmaWord

theorem heRhoSigma_facts :
    heRho ^ 4 = 1 ∧ ¬ heRho ^ 2 = 1 ∧ heSigma * heSigma = 1 ∧
      heSigma * (heRho * heSigma) = heRho ^ 3 ∧ (∀ k < 4, heSigma ≠ heRho ^ k) ∧
      heRho ∈ heSevenC1 ∧ heSigma ∈ heSevenC1 := by
  have h := heSeven_dihedral_check
  unfold heSevenDihedralOK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hval, h4⟩, h2⟩, hs2⟩, hrel⟩, hne⟩ := h
  have hval' : ∀ k < heSevenC1Gens.size, validA 8330 heSevenC1Gens[k]! = true := fun k hk =>
    allLt_spec hval (by simpa [heSevenC1Gens] using hk)
  have hsz : 3 ≤ heSevenC1Gens.size := by simp [heSevenC1Gens]
  have hρ : Rep 8330 (heSevenRhoArr ()) heRho := rep_evalWA hval' hsz heSevenRhoWord
  have hσ : Rep 8330 (heSevenSigmaArr ()) heSigma := rep_evalWA hval' hsz heSevenSigmaWord
  have hmem : ∀ i, gC1 i ∈ heSevenC1 := fun i =>
    Subgroup.subset_closure (mem_permsA (by simpa [heSevenC1Gens] using i.2))
  refine ⟨(eqA_iff (rep_powArr hρ 4) rep_idA).1 h4, fun h => ?_,
    (eqA_iff (rep_compA hσ hσ) rep_idA).1 hs2,
    (eqA_iff (rep_compA hσ (rep_compA hρ hσ)) (rep_powArr hρ 3)).1 hrel, fun k hk h => ?_,
    evalW_mem hmem _, evalW_mem hmem _⟩
  · have := (eqA_iff (rep_powArr hρ 2) rep_idA).2 h
    rw [this] at h2
    exact absurd h2 (by decide)
  · have h1 := allLt_spec hne hk
    simp only [Bool.not_eq_true'] at h1
    have := (eqA_iff hσ (rep_powArr hρ k)).2 h
    rw [this] at h1
    exact absurd h1 (by decide)

theorem heSevenD1_normal_index :
    heSevenD1 ≤ heSevenC1 ∧ (heSevenD1.subgroupOf heSevenC1).Normal ∧
      (heSevenD1.subgroupOf heSevenC1).index = 7 := by
  obtain ⟨-, -, -, -, -, -, ⟨-, hC1card⟩, -, -, ⟨-, -, hDcard, -⟩, -⟩ :=
    R3E_He_full_seven_centralizer_structures
  have hDC : heSevenD1 ≤ heSevenC1 := by
    show ⁅heSevenC1, heSevenC1⁆ ≤ heSevenC1
    rw [Subgroup.commutator_le]
    intro a ha c hc
    rw [commutatorElement_def]
    exact heSevenC1.mul_mem (heSevenC1.mul_mem (heSevenC1.mul_mem ha hc) (heSevenC1.inv_mem ha))
      (heSevenC1.inv_mem hc)
  refine ⟨hDC, ⟨fun n hn g => ?_⟩, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : ⁅(g : Equiv.Perm (Fin 8330)), (n : Equiv.Perm (Fin 8330))⁆ ∈ heSevenD1 :=
      Subgroup.commutator_mem_commutator g.2 n.2
    have h3 : ((g * n * g⁻¹ : heSevenC1) : Equiv.Perm (Fin 8330)) =
        ⁅(g : Equiv.Perm (Fin 8330)), (n : Equiv.Perm (Fin 8330))⁆ * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
    rw [h3]
    exact heSevenD1.mul_mem h1 hn
  · have h1 := Subgroup.index_mul_card (heSevenD1.subgroupOf heSevenC1)
    have h2 : Nat.card (heSevenD1.subgroupOf heSevenC1) = 168 := by
      rw [← hDcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
    rw [h2, hC1card] at h1
    omega

theorem heSevenD1_dihedral_sylow :
    ∃ S : Sylow 2 ↥heSevenD1, Nonempty ((S : Subgroup ↥heSevenD1) ≃* DihedralGroup 4) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h4, h2, hs2, hrel, hne, hρC, hσC⟩ := heRhoSigma_facts
  obtain ⟨hDC, hDn, hidx⟩ := heSevenD1_normal_index
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨hDs, -, hDcard, -⟩, -⟩ :=
    R3E_He_full_seven_centralizer_structures
  have hρD : heRho ∈ heSevenD1 := mem_of_pow_eight hDC hDn hidx hρC (by
    rw [show 8 = 4 * 2 by norm_num, pow_mul, h4, one_pow])
  have hσD : heSigma ∈ heSevenD1 := mem_of_pow_eight hDC hDn hidx hσC (by
    rw [show 8 = 2 * 4 by norm_num, pow_mul, sq, hs2, one_pow])
  haveI : Finite ↥heSevenD1 := Nat.finite_of_card_ne_zero (by rw [hDcard]; norm_num)
  set ρ : ↥heSevenD1 := ⟨heRho, hρD⟩
  set σ : ↥heSevenD1 := ⟨heSigma, hσD⟩
  have hρ4 : ρ ^ 4 = 1 := Subtype.ext (by simpa using h4)
  have hρo : orderOf ρ = 4 := by
    have : orderOf ρ = 2 ^ (1 + 1) := orderOf_eq_prime_pow (p := 2) (n := 1)
      (fun h => h2 (by simpa using congrArg Subtype.val h)) (by simpa using hρ4)
    simpa using this
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simpa [sq] using hs2)
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hσ2)
  have hrel' : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    rw [hσinv]
    have hρinv : ρ⁻¹ = ρ ^ 3 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hρ4])
    rw [hρinv]
    exact Subtype.ext (by simpa [mul_assoc] using hrel)
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hm
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hρo] at hm
    obtain ⟨k, hk, hkσ⟩ := Finset.mem_image.1 hm
    exact hne k (Finset.mem_range.1 hk) (by simpa using (congrArg Subtype.val hkσ).symm)
  obtain ⟨e⟩ := CFSG.RankThree.Literature.nonempty_closure_mulEquiv_dihedralGroup hσ2 hrel' hσρ
  rw [hρo] at e
  have hcard : Nat.card (Subgroup.closure ({ρ, σ} : Set ↥heSevenD1)) =
      2 ^ (Nat.card ↥heSevenD1).factorization 2 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hDcard,
      show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, Nat.factorization_mul_apply_of_coprime (by norm_num),
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 21 by norm_num)]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, ⟨e⟩⟩

theorem kLevel_heSevenD1 : kLevel 7 ↥heSevenD1 ≤ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨hDs, hDnab, hDcard, -⟩, -⟩ :=
    R3E_He_full_seven_centralizer_structures
  haveI : Finite ↥heSevenD1 := Nat.finite_of_card_ne_zero (by rw [hDcard]; norm_num)
  haveI := hDs
  obtain ⟨S, hS⟩ := heSevenD1_dihedral_sylow
  have hnab : ∃ a b : ↥heSevenD1, a * b ≠ b * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hDnab
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, fun e => hgh (congrArg Subtype.val e)⟩
  exact (CFSG.LocalAnalysis.GLTheoremA.KDSpor.kLevel_le_one_of_chev
    (isChevSimple_seven_of_dihedral hnab hDcard S hS)).trans (by norm_num)

end Concrete

section RowHe7

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.Sporadic.HeldB

theorem kdSporRow_He_seven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .He 7 := by
  have hp7 : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨hp7⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrecmem, -, ⟨hC0, -⟩, ⟨hC1, -⟩, ⟨hC2, -⟩,
    ⟨hA0C, hA0n, hA0P, hA0card, -, -, hA0c⟩, ⟨hDs, hDnab, hDcard, hDP, hDcent, -⟩,
    ⟨hA2C, hA2n, hA2P, hA2card, -, hA2c⟩⟩ := R3E_He_full_seven_centralizer_structures
  have hM := heAutModel
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥heP := heEquivP
  have hfin : Finite ↥heP := inferInstance
  have hs : IsSimpleGroup ↥heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  have hc : Nat.card ↥heP = 4030387200 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.He.card_He
  have hpr : ¬ (Nat.card ↥heP).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥heP, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥heP _ hfin hs hpr
  have b : ↥heP ≃* (TauCeti.CFSGIndex.sporadic .He).Group := e.symm.trans (hbr .He).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (heSevenLine j) ≤ heSevenQ ∧
      Nat.card (Subgroup.zpowers (heSevenLine j)) = 7 := by
    intro j
    have h : Subgroup.zpowers (heSevenLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heSevenQ ∧ Nat.card H = 7} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, heSevenLine j ∈ heP :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (heSevenLine j) = 7 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hL0 : LevelOK 7 (⟨heSevenLine 0, hmem 0⟩ : ↥heP) :=
    levelOK_of_pgroup_record hp7 hM.le (hmem 0) hC0 hA0C hA0n hA0P
      (IsPGroup.of_card (n := 3) (by rw [hA0card]; norm_num)) hA0c
  have hL2 : LevelOK 7 (⟨heSevenLine 2, hmem 2⟩ : ↥heP) :=
    levelOK_of_pgroup_record hp7 hM.le (hmem 2) hC2 hA2C hA2n hA2P
      (IsPGroup.of_card (n := 2) (by rw [hA2card]; norm_num)) hA2c
  have hL1 : LevelOK 7 (⟨heSevenLine 1, hmem 1⟩ : ↥heP) := by
    have hDfin : Finite ↥heSevenD1 := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    exact levelOK_of_derived_record (C := heSevenC1) (D := heSevenD1) hp7 hM.le
      (hmem 1) hC1 rfl hDs hDnab hDP hDcent (hord 1)
      (gLAPPrimeCoreOf_inf_eq_bot_of_ambient hp7 hM.le hM.conj_mem
        (gLAPPrimeCoreOf_heSevenRecord_eq_bot 1 (Or.inr (Or.inl rfl))))
      (by rw [hDcard]; norm_num) kLevel_heSevenD1
  have hline : ∀ j, LevelOK 7 (⟨heSevenLine j, hmem j⟩ : ↥heP) := by
    intro j
    obtain ⟨hjR, hjconj⟩ := htrans j
    have hr : LevelOK 7 (⟨heSevenLine (heSevenRecordOf j), hmem _⟩ : ↥heP) := by
      have h := hrecmem j
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h
      · have : heSevenRecordOf j = 0 := Fin.ext h
        rw [this]; exact hL0
      · have : heSevenRecordOf j = 1 := Fin.ext h
        rw [this]; exact hL1
      · have : heSevenRecordOf j = 2 := Fin.ext h
        rw [this]; exact hL2
    have h := levelOK_conj hp7 hM.conj_mem hjR (hmem _) hr
    have heq : (⟨heSevenTransporter j * heSevenLine (heSevenRecordOf j) *
        (heSevenTransporter j)⁻¹, hM.conj_mem _ hjR _ (hmem _)⟩ : ↥heP) =
        ⟨heSevenLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  exact @kdSporRow_of_levelOK .He 7 ↥heP _ hfin hs hOut b hnc hp7 (by norm_num)
    (@levelOK_of_lines 8330 7 hp7 heP heSevenQ hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) _ heSevenLine hlines hmem hline)

end RowHe7

end CFSG.LocalAnalysis.GLTheoremA.KDSpor.He7
