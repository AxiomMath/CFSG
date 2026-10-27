module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.TypU
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1NoSLTwo
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP5Basic

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.Open (StatedLieAdmissible StatedProj StatedSL)
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)

private theorem typU_of_isSLTwoOver {A B : Type} [Group A] [Group B] [Finite B]
    (hGA : TBLit.GriessMultipliersOdd) (hB2 : HarrisLit.IsTwoQuasisimple B)
    (e : A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B)
    {c : B} (hc : orderOf c = 2) (hcZ : c ∈ Open.fusionZStar B)
    {q : ℕ} (hqodd : Odd q) (hq9 : 9 ≤ q)
    (hAsl : HarrisLit.IsSLTwoOver q (A ⧸ pPrimeCore 2 A)) : TypU B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hF, hFint, hFcard, ⟨eA0⟩⟩ := hAsl
  letI := hF
  letI := hFint
  obtain ⟨p, _hCharP, f, hp, hcardF⟩ := FiniteField.card' F
  have hqf : p ^ (f : ℕ) = q := by rw [← hcardF]; exact hFcard
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2odd : Odd (2 ^ (f : ℕ)) := by rw [hqf]; exact hqodd
    rw [Nat.odd_pow_iff f.pos.ne'] at h2odd
    exact absurd h2odd (by decide)
  have hqodd' : Odd (p ^ (f : ℕ)) := by rw [hqf]; exact hqodd
  have hq9' : 9 ≤ p ^ (f : ℕ) := by rw [hqf]; exact hq9
  have hcardNat : Nat.card F = p ^ (f : ℕ) := by
    rw [← Fintype.card_eq_nat_card]; exact hcardF
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
  let QA := A ⧸ pPrimeCore 2 A
  let QB := B ⧸ pPrimeCore 2 B
  have hiso : QA ⧸ center QA ≃* StatedProj (StatedSL 2 F) :=
    (Sol78.centerQuotCongr eA0).trans (projectiveSpecialLinearGroupEquivStatedProj 2 F)
  have hmQA : LieModel (QA ⧸ center QA) .PSL 2 p (f : ℕ) :=
    Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hcardNat, ⟨hiso⟩⟩
  let eQ : QA ⧸ center QA ≃* QB ⧸ center QB :=
    (Sol78.coreQuotientCenterEquiv A).trans (e.trans (Sol78.coreQuotientCenterEquiv B).symm)
  have hmQB : LieModel (QB ⧸ center QB) .PSL 2 p (f : ℕ) := hmQA.of_mulEquiv eQ
  have hqb : IsQuasisimple QB := hB2.2
  have h2grp : IsPGroup 2 ↥(center QB) :=
    Sol78.center_isPGroup_two (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := B) 2)
  obtain ⟨hcc, hc1⟩ := GS82PumpInputs.mk_mem_center_ne_one (L := B) hcZ hc
  have hZ : center QB ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hcc
    exact hc1 hcc
  have hslB : HarrisLit.IsSLTwoOver (p ^ (f : ℕ)) QB :=
    HarrisLit.T1.isSLTwoOver_of_psl2Cover hGA hp hp2 hqb h2grp hZ hmQB
  exact Or.inl ⟨p ^ (f : ℕ), hqodd', hq9', hslB⟩

private theorem typU_of_typChev {A B : Type} [Group A] [Group B]
    (e : A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hA : GSThmB.TypChev r A) : TypU B :=
  Or.inr (Or.inl ⟨r, hr, hr2, GSThmB.typChev_of_mulEquiv hA e⟩)

private theorem typU_of_psp {A B : Type} [Group A] [Group B]
    (e : A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B)
    (hA : LieModel (A ⧸ Open.fusionZStar A) .PSp 2 3 1) : TypU B :=
  Or.inr (Or.inr (Or.inl (hA.of_mulEquiv e)))

private theorem typU_of_doubleCoverAlt {A B : Type} [Group A] [Group B] [Finite B]
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) (hB2 : HarrisLit.IsTwoQuasisimple B)
    (e : A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B)
    {c : B} (hc : orderOf c = 2) (hcZ : c ∈ Open.fusionZStar B)
    {n : ℕ} (hn7 : 7 ≤ n)
    (hAalt : GH74.GLS.IsDoubleCoverOfAlt (A ⧸ pPrimeCore 2 A) n) : TypU B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_hAq, _hAcard, ⟨eAalt⟩⟩ := hAalt
  let QA := A ⧸ pPrimeCore 2 A
  let QB := B ⧸ pPrimeCore 2 B
  have hqb : IsQuasisimple QB := hB2.2
  haveI : Group.IsPerfect QB := hqb.1
  let eQ : QA ⧸ center QA ≃* QB ⧸ center QB :=
    (Sol78.coreQuotientCenterEquiv A).trans (e.trans (Sol78.coreQuotientCenterEquiv B).symm)
  let eBal : QB ⧸ center QB ≃* alternatingGroup (Fin n) := eQ.symm.trans eAalt
  have hle : Nat.card (center QB) ≤ 2 :=
    Sol78.card_center_le_two hSchur (Q := QB)
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := B) 2) (by omega) eBal
  obtain ⟨hcc, hc1⟩ := GS82PumpInputs.mk_mem_center_ne_one (L := B) hcZ hc
  have hlt : 1 < Nat.card (center QB) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro h
    rw [h, Subgroup.mem_bot] at hcc
    exact hc1 hcc
  have hcardB : Nat.card (center QB) = 2 := by omega
  exact Or.inr (Or.inr (Or.inr ⟨n, hn7, hqb, hcardB, ⟨eBal⟩⟩))

theorem diagonalTransfer_typU (hGA : TBLit.GriessMultipliersOdd)
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) (q₀ : ℕ) :
    GS82PumpInputs.DiagonalTransfer q₀ TypU := by
  intro A B _ _ _ _ _hA2 hB2 hA ⟨e⟩ _N _hN _hNSL c hc _hcN _hNc hcZ
  rcases hA with ⟨q, hqodd, hq9, hAsl⟩ | ⟨r, hr, hr2, hAchev⟩ | hApsp | ⟨n, hn7, hAalt⟩
  · exact typU_of_isSLTwoOver hGA hB2 e hc hcZ hqodd hq9 hAsl
  · exact typU_of_typChev e hr hr2 hAchev
  · exact typU_of_psp e hApsp
  · exact typU_of_doubleCoverAlt hSchur hB2 e hc hcZ hn7 hAalt

end CFSG.OddStandard.SmallF3.HypA2
