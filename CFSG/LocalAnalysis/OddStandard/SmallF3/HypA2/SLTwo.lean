module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1NoSLTwo
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.Open (StatedLieAdmissible StatedProj StatedSL)
open CFSG.Assembly.LowTwoRank
  (projectiveSpecialLinearGroupEquivStatedProj specialLinearGroupEquivStatedSL)

private theorem card_of_isSLTwoOver' {q : ℕ} {Y : Type} [Group Y]
    (h : HarrisLit.IsSLTwoOver q Y) : Nat.card Y = q * (q ^ 2 - 1) := by
  obtain ⟨F, hF, hFint, hFcard, ⟨e⟩⟩ := h
  letI := hF
  letI := hFint
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
    CFSG.Open.StatedAPI.card_statedSL_two, Nat.card_eq_fintype_card, hFcard]

private theorem isQuasisimple_of_perfect_of_simple_center {Q : Type*} [Group Q]
    (hp : Group.IsPerfect Q) (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) :
    CFSG.IsQuasisimple Q := by
  refine ⟨hp, hs, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨h⟩⟩
  have hperf : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isMulCommutative _ this

private theorem isPGroup_two_center_sl2 (F : Type) [Field F] :
    IsPGroup 2 ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  have hroots : IsPGroup 2 (rootsOfUnity (Fintype.card (Fin 2)) F) := by
    intro x
    exact ⟨1, Subtype.ext (by simpa using x.2)⟩
  exact hroots.of_equiv
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (i := (0 : Fin 2)) (R := F)).symm

private theorem pPrimeCore_eq_bot_of_quasisimple {X : Type*} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hZle : Nat.card ↥(Subgroup.center X) ≤ 2)
    (heven : Even (Nat.card X)) : pPrimeCore 2 X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (pPrimeCore 2 X).Normal := inferInstance
  have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 X)) := CFSG.pPrimeCore_coprime_card
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hle
  · exfalso
    have hcardX : Nat.card X = Nat.card ↥(pPrimeCore 2 X) := by rw [htop, Subgroup.card_top]
    have h2 : 2 ∣ Nat.card X := heven.two_dvd
    rw [hcardX] at h2
    have h21 : 2 = 1 := hcop.eq_one_of_dvd h2
    omega
  · have h1 : Nat.card ↥(pPrimeCore 2 X) ∣ Nat.card ↥(Subgroup.center X) :=
      Subgroup.card_dvd_of_le hle
    have hcenter_pos : 0 < Nat.card ↥(Subgroup.center X) := Nat.card_pos
    have hle2 : Nat.card ↥(pPrimeCore 2 X) ≤ 2 := (Nat.le_of_dvd hcenter_pos h1).trans hZle
    have hn2 : Nat.card ↥(pPrimeCore 2 X) ≠ 2 :=
      fun h2n => absurd (h2n ▸ hcop) (by decide)
    have hn0 : Nat.card ↥(pPrimeCore 2 X) ≠ 0 :=
      fun h0 => absurd (h0 ▸ hcop) (by decide)
    have hn1 : Nat.card ↥(pPrimeCore 2 X) = 1 := by omega
    exact Subgroup.eq_bot_of_card_eq _ hn1

theorem isSLTwoOver_quotient {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q) {N : Type} [Group N]
    (h : HarrisLit.IsSLTwoOver q N) : HarrisLit.IsSLTwoOver q (N ⧸ pPrimeCore 2 N) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL : HarrisLit.IsSLTwoOver q N := h
  obtain ⟨F, hF, hFint, hFcard, ⟨e⟩⟩ := h
  letI := hF
  letI := hFint
  haveI : Finite N := Finite.of_equiv _ e.toEquiv.symm
  have h4 : 4 ≤ Nat.card F := by rw [Nat.card_eq_fintype_card, hFcard]; omega
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    isQuasisimple_of_perfect_of_simple_center
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4)
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)
  have hqN : CFSG.IsQuasisimple N := CFSG.IsQuasisimple.of_mulEquiv e hqSL
  have hZle : Nat.card ↥(Subgroup.center N) ≤ 2 := by
    calc Nat.card ↥(Subgroup.center N)
        = Nat.card ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :=
          Nat.card_congr (Subgroup.centerCongr e).toEquiv
      _ = Nat.card (rootsOfUnity (Fintype.card (Fin 2)) F) :=
          Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
            (i := (0 : Fin 2)) (R := F)).toEquiv
      _ ≤ Fintype.card (Fin 2) := card_rootsOfUnity F (Fintype.card (Fin 2))
      _ = 2 := Fintype.card_fin 2
  have hq2 : Odd (q ^ 2) := hq.pow
  have heven_q : Even (q ^ 2 - 1) := Nat.Odd.sub_odd hq2 odd_one
  have heven : Even (Nat.card N) := by
    rw [card_of_isSLTwoOver' hSL]
    exact Even.mul_left heven_q q
  have hObot : pPrimeCore 2 N = ⊥ := pPrimeCore_eq_bot_of_quasisimple hqN hZle heven
  refine ⟨F, hF, hFint, hFcard, ?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hObot).trans
    ((QuotientGroup.quotientBot).trans e)⟩

theorem isPerfect_of_isSLTwoOver {q : ℕ} (h5 : 5 ≤ q) {N : Type} [Group N]
    (h : HarrisLit.IsSLTwoOver q N) : Group.IsPerfect N := by
  obtain ⟨F, hF, hFint, hFcard, ⟨e⟩⟩ := h
  letI := hF
  letI := hFint
  have h4 : 4 ≤ Nat.card F := by rw [Nat.card_eq_fintype_card, hFcard]; omega
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem isSLTwoOver_of_perfect_central_extension (hGA : TBLit.GriessMultipliersOdd) {q : ℕ}
    (hq : Odd q) (h5 : 5 ≤ q) {E : Type} [Group E] [Finite E] (hE : Group.IsPerfect E)
    {A : Subgroup E} [A.Normal] (hA : A ≤ center E) (hA2 : IsPGroup 2 ↥A)
    (hN : HarrisLit.IsSLTwoOver q (E ⧸ A)) : HarrisLit.IsSLTwoOver q E ∧ A = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNkeep := hN
  obtain ⟨F, hF, hFint, hFcard, ⟨eA⟩⟩ := hN
  letI := hF
  letI := hFint
  have h4 : 4 ≤ Nat.card F := by rw [Nat.card_eq_fintype_card, hFcard]; omega
  obtain ⟨p, hCharP, f, hp, hcardF⟩ := FiniteField.card' F
  haveI : CharP F p := hCharP
  have hqf : p ^ (f : ℕ) = q := by rw [← hcardF]; exact hFcard
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2odd : Odd (2 ^ (f : ℕ)) := by rw [hqf]; exact hq
    rw [Nat.odd_pow_iff f.pos.ne'] at h2odd
    exact absurd h2odd (by decide)
  have h2F : (2 : F) ≠ 0 := by
    intro h0
    have hp_dvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h0
    rcases (Nat.dvd_prime Nat.prime_two).mp hp_dvd with h1 | h2
    · exact hp.ne_one h1
    · exact hp2 h2
  have hkerA : (QuotientGroup.mk' A).ker ≤ Subgroup.center E := by
    rw [QuotientGroup.ker_mk']; exact hA
  have hcenter_comap : (Subgroup.center (E ⧸ A)).comap (QuotientGroup.mk' A) =
      Subgroup.center E :=
    CFSG.LocalCores.comap_center_eq_of_perfect hE (QuotientGroup.mk' A)
      (QuotientGroup.mk'_surjective A) hkerA
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    isQuasisimple_of_perfect_of_simple_center
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4)
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)
  have hqEbar : CFSG.IsQuasisimple (E ⧸ A) := CFSG.IsQuasisimple.of_mulEquiv eA hqSL
  have hqE : CFSG.IsQuasisimple E :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hE (QuotientGroup.mk' A)
      (QuotientGroup.mk'_surjective A) hkerA).mpr hqEbar
  have h2ZQ : IsPGroup 2 ↥(Subgroup.center (E ⧸ A)) :=
    (isPGroup_two_center_sl2 F).of_equiv (Subgroup.centerCongr eA).symm
  have h2Z : IsPGroup 2 ↥(Subgroup.center E) := by
    rw [← hcenter_comap]
    exact h2ZQ.comap_of_ker_isPGroup (QuotientGroup.mk' A) (by
      rw [QuotientGroup.ker_mk']; exact hA2)
  have hnegmem : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, ?_, ?_⟩
    · rw [Fintype.card_fin]; ring
    · ext i j
      by_cases hij : i = j <;>
        simp [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply, hij]
  have hneg1 : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
    intro hh
    have hm := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 0) hh
    simp at hm
    have h2zero : (2 : F) = 0 := by
      have h' := congrArg (fun x : F => x + 1) hm
      rw [neg_add_cancel] at h'
      rw [show (1 : F) + 1 = 2 by norm_num] at h'
      exact h'.symm
    exact h2F h2zero
  have hZQne : Subgroup.center (E ⧸ A) ≠ ⊥ := by
    intro hbot
    have hcenterSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
      rw [← Sol78.map_center_eq_of_mulEquiv eA, hbot, Subgroup.map_bot]
    rw [hcenterSL, Subgroup.mem_bot] at hnegmem
    exact hneg1 hnegmem
  have hZne : Subgroup.center E ≠ ⊥ := by
    intro hbot
    have hmap := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective A)
      (Subgroup.center (E ⧸ A))
    rw [hcenter_comap, hbot, Subgroup.map_bot] at hmap
    exact hZQne hmap.symm
  have hcardNat : Nat.card F = p ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardF
  have hadm : StatedLieAdmissible .PSL 2 p (f : ℕ) := by
    refine ⟨hp, f.pos, le_rfl, ?_, ?_⟩
    · intro h
      have h2 : p ^ (f : ℕ) = 2 := (Prod.mk.inj h).2
      rw [hqf] at h2
      omega
    · intro h
      have h3 : p ^ (f : ℕ) = 3 := (Prod.mk.inj h).2
      rw [hqf] at h3
      omega
  have hiso : (E ⧸ A) ⧸ Subgroup.center (E ⧸ A) ≃* StatedProj (StatedSL 2 F) :=
    (Sol78.centerQuotCongr eA).trans (projectiveSpecialLinearGroupEquivStatedProj 2 F)
  have hmEbar : LieModel ((E ⧸ A) ⧸ Subgroup.center (E ⧸ A)) .PSL 2 p (f : ℕ) :=
    Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hcardNat, ⟨hiso⟩⟩
  have hc : Subgroup.center E =
      ((QuotientGroup.mk' (Subgroup.center (E ⧸ A))).comp (QuotientGroup.mk' A)).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hcenter_comap.symm
  let eZ : E ⧸ Subgroup.center E ≃* (E ⧸ A) ⧸ Subgroup.center (E ⧸ A) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk'_surjective (Subgroup.center (E ⧸ A))).comp
          (QuotientGroup.mk'_surjective A)))
  have hmE : LieModel (E ⧸ Subgroup.center E) .PSL 2 p (f : ℕ) :=
    hmEbar.of_mulEquiv eZ.symm
  have hslE : HarrisLit.IsSLTwoOver q E := by
    have hcover := HarrisLit.T1.isSLTwoOver_of_psl2Cover hGA hp hp2 hqE h2Z hZne hmE
    rwa [hqf] at hcover
  have hcardE : Nat.card E = q * (q ^ 2 - 1) := card_of_isSLTwoOver' hslE
  have hcardEA : Nat.card (E ⧸ A) = q * (q ^ 2 - 1) := card_of_isSLTwoOver' hNkeep
  have hcardA : Nat.card ↥A = 1 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup A
    rw [hcardE, hcardEA] at h
    have hpos : 0 < q * (q ^ 2 - 1) := by
      have h1 : 0 < q := by omega
      have h2 : 0 < q ^ 2 - 1 := by
        have : 1 < q ^ 2 := by nlinarith [h5]
        omega
      exact Nat.mul_pos h1 h2
    have hone : 1 = Nat.card ↥A :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one, ← h])
    exact hone.symm
  exact ⟨hslE, Subgroup.eq_bot_of_card_eq _ hcardA⟩

theorem isSLTwoOver_nine_of_psl_nine (hGA : TBLit.GriessMultipliersOdd) {M : Type} [Group M]
    [Finite M] (hM : HarrisLit.IsTwoQuasisimple M) {w : M} (hw : orderOf w = 2)
    (hwZ : w ∈ Open.fusionZStar M)
    (h : LieModel (M ⧸ Open.fusionZStar M) .PSL 2 3 2) :
    HarrisLit.IsSLTwoOver 9 (M ⧸ pPrimeCore 2 M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := M ⧸ pPrimeCore 2 M
  have hQq : CFSG.IsQuasisimple Q := hM.2
  have hOQ : pPrimeCore 2 Q = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := M) 2
  have h2grp : IsPGroup 2 ↥(Subgroup.center Q) := Sol78.center_isPGroup_two hOQ
  have hwcenter : QuotientGroup.mk' (pPrimeCore 2 M) w ∈ Subgroup.center Q := by
    rw [Sol78.fusionZStar_eq_comap M] at hwZ
    simpa using hwZ
  have hw1 : QuotientGroup.mk' (pPrimeCore 2 M) w ≠ 1 := by
    intro hwq
    have hwmem : w ∈ pPrimeCore 2 M := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hwq
    have hdvd : 2 ∣ Nat.card ↥(pPrimeCore 2 M) := by
      have hle : Subgroup.zpowers w ≤ pPrimeCore 2 M := Subgroup.zpowers_le.mpr hwmem
      have hcard := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hw] at hcard
    have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 M)) :=
      CFSG.pPrimeCore_coprime_card (p := 2) (G := M)
    have h21 : 2 = 1 := hcop.eq_one_of_dvd hdvd
    omega
  have hZ : Subgroup.center Q ≠ ⊥ := by
    intro hbot
    have : QuotientGroup.mk' (pPrimeCore 2 M) w ∈ (⊥ : Subgroup Q) := by
      rw [← hbot]; exact hwcenter
    exact hw1 (Subgroup.mem_bot.mp this)
  have hm : LieModel (Q ⧸ Subgroup.center Q) .PSL 2 3 2 :=
    h.of_mulEquiv (Sol78.coreQuotientCenterEquiv M).symm
  have hsl : HarrisLit.IsSLTwoOver (3 ^ 2) Q :=
    HarrisLit.T1.isSLTwoOver_of_psl2Cover hGA (by norm_num) (by norm_num) hQq h2grp hZ hm
  simpa [Q] using hsl

end CFSG.OddStandard.SmallF3.HypA2
