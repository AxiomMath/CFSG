module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23DiagPi
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndGA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.Sporadic.Recognition.HeMultiplier
public import CFSG.GH74.Generic.GKFAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxRed
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerCase

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.CatFactsL4U4

theorem map_mem_center_of_surjective {A B : Type*} [Group A] [Group B] {π : A →* B}
    (hπ : Function.Surjective π) {x : A} (hx : x ∈ center A) : π x ∈ center B := by
  rw [mem_center_iff]
  intro y
  obtain ⟨w, rfl⟩ := hπ y
  rw [← map_mul, ← map_mul, mem_center_iff.mp hx w]

theorem nonempty_zStarBar_equiv_of_ne {H : Type} [Group H] [Finite H] (h : Hyp52 H)
    (hKa : conjugate h.K h.a ≠ h.K) (hZJ : center (OddBar h.J) = ⊥) :
    Nonempty (ZStarBar h.K ≃* OddBar h.J) := by
  obtain ⟨ι, hι, -, hr⟩ := CF23Diag.exists_iota h hKa
  obtain ⟨π, hπs, hπk, -⟩ := CF23Diag.exists_pi h hKa hι hr
  have hker : π.ker = center (OddBar h.K) := by
    refine le_antisymm hπk fun x hx => ?_
    have h1 := map_mem_center_of_surjective hπs hx
    rw [hZJ, mem_bot] at h1
    exact h1
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  exact ⟨eZ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπs))⟩

theorem card_center_le_two_of_psl_two
    {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ2 : IsPGroup 2 (center Q)) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel (Q ⧸ center Q) .PSL 2 p f) : Nat.card (center Q) ≤ 2 := by
  have hdvd := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess hQ.1
    (MulEquiv.refl (Q ⧸ center Q))
  obtain ⟨-, ⟨e⟩⟩ := TBLit.griessMultipliersOdd_holds _ .PSL 2 p f
    (HarrisLit.models_lieModel_of_lieModel_of_ne_zero (by norm_num) hm) hp2 (Or.inl rfl)
  have hcard : Nat.card (Open.griessHopfMultiplier (Q ⧸ center Q)) =
      Nat.gcd 2 (p ^ f - 1) * ((Blueprint.Multiplier.exceptionalOrders .PSL 2 p f).1 *
        (Blueprint.Multiplier.exceptionalOrders .PSL 2 p f).2) := by
    rw [Nat.card_congr e.toEquiv]
    simp only [Blueprint.Multiplier.generic, Blueprint.Multiplier.exceptional, Nat.card_prod]
    rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
      Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
      Nat.card_zmod, Nat.card_zmod, Nat.card_zmod, Nat.card_zmod]
    rw [show Blueprint.Multiplier.genericOrders .PSL 2 p f = (Nat.gcd 2 (p ^ f - 1), 1) from rfl,
      mul_one]
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hg : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel, Nat.gcd_eq_left (dvd_mul_right 2 k)]
  rw [hcard, hg] at hdvd
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  rw [hn] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ n) ((Blueprint.Multiplier.exceptionalOrders .PSL 2 p f).1 *
      (Blueprint.Multiplier.exceptionalOrders .PSL 2 p f).2) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (HarrisLit.odd_exceptionalOrders_psl hp2))
  exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)

theorem table54_of_ne_cover
    {H : Type} [Group H] [Finite H] (h : Hyp52 H)
    (hKa : conjugate h.K h.a ≠ h.K) (hZK : center (OddBar h.K) ≠ ⊥)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f) : h.Table54 := by
  have hZJ : center (OddBar h.J) = ⊥ := by
    rcases hJ with hA | ⟨p, f, -, -, -, -, hm⟩
    · obtain ⟨e⟩ := hA
      exact IdxRed.center_eq_bot_of_alt (by norm_num) e
    · exact IdxRed.center_eq_bot_of_psl2 hm
  obtain ⟨e⟩ := nonempty_zStarBar_equiv_of_ne h hKa hZJ
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hZ2 : IsPGroup 2 (center (OddBar h.K)) :=
    isPGroup_two_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hle : Nat.card (center (OddBar h.K)) ≤ 2 := by
    rcases hJ with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, -, -, hm⟩
    · exact GH74.Generic.alt_cover_of_central_kernel (by norm_num) h.isQuasisimple_K hZ2
        ((eZ.trans e).trans e7)
    · exact card_center_le_two_of_psl_two h.isQuasisimple_K hZ2 hp hp2
        (OddQuot.lieModel_of_equiv (eZ.trans e).symm hm)
  have hcard2 : Nat.card (center (OddBar h.K)) = 2 := by
    obtain ⟨n, hn⟩ := hZ2.exists_card_eq
    rcases n with _ | n
    · exfalso
      apply hZK
      rw [pow_zero] at hn
      exact Subgroup.eq_bot_of_card_eq _ hn
    · rw [hn] at hle ⊢
      rcases n with _ | n
      · rfl
      · exfalso
        have : 2 ^ 2 ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
  rcases hJ with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, hq, hm⟩
  · exact Or.inl ⟨7, Or.inr (Or.inr rfl), ⟨e7⟩, Or.inr ⟨hKa, hcard2, ⟨e.trans e7⟩⟩⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, f, hp, hp2, hf, hq, hm, hKa, hcard2, OddQuot.lieModel_of_equiv e.symm hm⟩)))))

end CFSG.ComponentClassification.GSThmB.Cov
