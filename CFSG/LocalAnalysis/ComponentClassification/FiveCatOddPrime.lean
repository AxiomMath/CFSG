module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Core
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGLS3
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem card_of_mulEquiv_alt_five {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : Nat.card X = 60 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem lieModel_of_card_sixty (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel X τ n p f) (hX : Nat.card X = 60) : p = 5 := by
  obtain ⟨-, hmul, hfac⟩ := hO X τ n p f hadm hm
  have hp := hadm.1
  have hf := hadm.2.1
  rw [hX] at hmul hfac
  have hdvd : p ^ (lieSylowExponent τ n * f) ∣ 60 := by
    rw [← hfac]
    exact Nat.ordProj_dvd 60 p
  rcases CatLeafProof.lieSylowExponent_ge_three hadm hp2 with ⟨rfl, rfl⟩ | h3
  ·
    obtain ⟨q, hq⟩ : ∃ q, p ^ f = q := ⟨_, rfl⟩
    simp only [lieOrderDivisor, lieOrderNumerator, Finset.Icc_self, Finset.prod_singleton,
      hq] at hmul
    have hqodd : Odd q := hq ▸ (hp.odd_of_ne_two hp2).pow
    have hg : Nat.gcd 2 (q - 1) = 2 :=
      Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one))
    rw [hg, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one] at hmul
    obtain ⟨s, hs⟩ : ∃ s, q ^ 2 = s := ⟨_, rfl⟩
    rw [hs] at hmul
    have hsq : s = q * q := by rw [← hs, sq]
    have hq5 : q ≤ 5 := by
      by_contra hlt
      push Not at hlt
      have h1 : 36 ≤ s := by rw [hsq]; nlinarith
      have h2 : 6 * 35 ≤ q * (s - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hq5' : q = 5 := by
      interval_cases q <;> simp_all
    have hpd : p ∣ 5 := by
      rw [← hq5', ← hq]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpd
  · exfalso
    have h3f : 3 ≤ lieSylowExponent τ n * f := le_trans h3 (Nat.le_mul_of_pos_right _ hf)
    have h27 : p ^ 3 ∣ 60 := (pow_dvd_pow p h3f).trans hdvd
    have hp3 : p ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have h1 : 4 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
      have h2 := Nat.le_of_dvd (by norm_num) h27
      omega
    have h2 := hp.two_le
    interval_cases p
    · exact hp2 rfl
    · revert h27
      decide

theorem fivePump_oddPrime_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput) :
    FivePumpOddPrimeClause := by
  intro S _ _ hs hna τ n p f hp hp2 hm σ P h _ ⟨eP⟩
  have : IsSimpleGroup S := hs
  have hadm := hm.admissible
  have hodd : Blueprint.OddLieType S := ⟨τ, n, p, f, hp, hp2, hadm, hm⟩
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hq : IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna hodd σ hσσ hσ1 L h.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  have hcard : Nat.card (L ⧸ center L) = 60 := card_of_mulEquiv_alt_five (eZ.symm.trans eP)
  rcases hGLS S τ n p f hp hp2 hadm hm σ hσ2 L hcomp with ⟨τ', n', f', hadm', hm'⟩ |
      ⟨-, -, -, h8⟩
  · exact lieModel_of_card_sixty hO hadm' hp2 hm' hcard
  · exfalso
    have h504 := card_of_lieModel_psl_two_eight hO h8
    have hdvd : Nat.card (L ⧸ center L) ∣ Nat.card L := Subgroup.card_quotient_dvd_card _
    rw [hcard, h504] at hdvd
    revert hdvd
    decide

theorem fivePump_oddPrime :
    FivePumpOddPrimeClause :=
  fivePump_oddPrime_of_inputs GrSLit.gls3OddLieAutComponentsInput_holds
    CatLeafProof.lieOrderFormulasInput

end CFSG.ComponentClassification.SolMax.FiveCat
