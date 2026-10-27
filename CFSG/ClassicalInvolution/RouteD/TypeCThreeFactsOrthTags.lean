module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeFactsOrth

public section

namespace CFSG.ClassicalInvolution.RouteD.LieBridge

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Spin
  CFSG.Blueprint.Chevalley

variable {p e n : ℕ} [hp : Fact p.Prime]

theorem partner_PSL (hadm : StatedLieAdmissible .PSL n p e) (hn : 4 ≤ n) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSL
        (modelUniv .PSL n p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSL
        (modelUniv .PSL n p e hp.out).D, Commutes R R' := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .PSL (m + 1) p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .PSL (m + 1) p e hp.out trivial hadm
  have hk := isLongestRoot_single .PSL (m + 1) p e hp.out trivial hadm ⟨0, by show 0 < m; omega⟩
    trivial
  have hj := isLongestRoot_single .PSL (m + 1) p e hp.out trivial hadm ⟨2, by show 2 < m; omega⟩
    trivial
  refine partner_fund_of_longest (by decide) (by decide)
    (commutingPartner_nonadjacent hct hext hirr hratio
      (k := ⟨0, by show 0 < m; omega⟩) (j := ⟨2, by show 2 < m; omega⟩) ?_ hk hj)
  show CartanMatrix.A m ⟨0, by omega⟩ ⟨2, by omega⟩ = 0
  simp [CartanMatrix.A, Fin.ext_iff]

theorem partner_POmegaPlus (hadm : StatedLieAdmissible .POmegaPlus n p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .POmegaPlus
        (modelUniv .POmegaPlus n p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .POmegaPlus
        (modelUniv .POmegaPlus n p e hp.out).D, Commutes R R' := by
  have hn : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hB := hasBruhatDatum .POmegaPlus n p e hp.out trivial hadm
  have hC := cartanOK .POmegaPlus n p e hp.out trivial hadm
  have hL := isLongestRoot_single .POmegaPlus n p e hp.out trivial hadm
  revert hB hC hL
  rw [modelUniv_POmegaPlus hn3]
  intro hB hC hL
  obtain ⟨nn, H, hct, hext⟩ := hB
  obtain ⟨hirr, hratio⟩ := hC
  refine partner_fund_of_longest (by decide) (by decide)
    (commutingPartner_nonadjacent hct hext hirr hratio
      (k := ⟨0, by show 0 < n; omega⟩) (j := ⟨2, by show 2 < n; omega⟩) ?_
      (hL ⟨0, by show 0 < n; omega⟩ trivial) (hL ⟨2, by show 2 < n; omega⟩ trivial))
  show cartanD n ⟨0, by omega⟩ ⟨2, by omega⟩ = 0
  simp [cartanD, Fin.ext_iff]
  omega

theorem partner_PSp (hadm : StatedLieAdmissible .PSp n p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSp
        (modelUniv .PSp n p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSp
        (modelUniv .PSp n p e hp.out).D, Commutes R R' := by
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .PSp n p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .PSp n p e hp.out trivial hadm
  have hk := isLongestRoot_single .PSp n p e hp.out trivial hadm ⟨n - 1, by show n - 1 < n; omega⟩
    (by show n - 1 + 1 = n; omega)
  refine partner_fund_of_longest (by decide) (by decide)
    (commutingPartner_double hct hext hirr hratio
      (k := ⟨n - 1, by show n - 1 < n; omega⟩) (j := ⟨n - 2, by show n - 2 < n; omega⟩) ?_ ?_ hk)
  · show cartanC n ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = 2
    simp [cartanC]
  · show cartanC n ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ * cartanC n ⟨n - 2, by omega⟩
      ⟨n - 1, by omega⟩ = 2
    simp only [cartanC, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem partner_POmegaOdd (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .POmegaOdd
        (modelUniv .POmegaOdd n p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .POmegaOdd
        (modelUniv .POmegaOdd n p e hp.out).D, Commutes R R' := by
  have hn : 3 ≤ n := hadm.2.2.1
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .POmegaOdd n p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .POmegaOdd n p e hp.out trivial hadm
  have hk := isLongestRoot_single .POmegaOdd n p e hp.out trivial hadm
    ⟨n - 2, by show n - 2 < n; omega⟩ (by show n - 2 + 1 < n; omega)
  refine partner_fund_of_longest (by decide) (by decide)
    (commutingPartner_double hct hext hirr hratio
      (k := ⟨n - 2, by show n - 2 < n; omega⟩) (j := ⟨n - 1, by show n - 1 < n; omega⟩) ?_ ?_ hk)
  · show cartanB n ⟨n - 2, by omega⟩ ⟨n - 2, by omega⟩ = 2
    simp [cartanB]
  · show cartanB n ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ * cartanB n ⟨n - 1, by omega⟩
      ⟨n - 2, by omega⟩ = 2
    simp only [cartanB, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem partner_POmegaMinus (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .POmegaMinus
        (modelUniv .POmegaMinus n p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .POmegaMinus
        (modelUniv .POmegaMinus n p e hp.out).D, Commutes R R' := by
  have hn : 4 ≤ n := hadm.2.2
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .POmegaMinus n p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .POmegaMinus n p e hp.out trivial hadm
  have hk := isLongestRoot_single .POmegaMinus n p e hp.out trivial hadm
    ⟨n - 3, by show n - 3 < n - 1; omega⟩ (by show n - 3 + 2 < n; omega)
  refine partner_fund_of_longest (by decide) (by decide)
    (commutingPartner_double hct hext hirr hratio
      (k := ⟨n - 3, by show n - 3 < n - 1; omega⟩) (j := ⟨n - 2, by show n - 2 < n - 1; omega⟩)
      ?_ ?_ hk)
  · show cartanB (n - 1) ⟨n - 3, by omega⟩ ⟨n - 3, by omega⟩ = 2
    simp [cartanB]
  · show cartanB (n - 1) ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩ *
      cartanB (n - 1) ⟨n - 2, by omega⟩ ⟨n - 3, by omega⟩ = 2
    simp only [cartanB, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem cartanC_double (r : ℕ) (hr : 2 ≤ r) :
    cartanC r ⟨r - 1, by omega⟩ ⟨r - 1, by omega⟩ = 2 ∧
      cartanC r ⟨r - 1, by omega⟩ ⟨r - 2, by omega⟩ *
        cartanC r ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ = 2 := by
  refine ⟨by simp [cartanC], ?_⟩
  simp only [cartanC, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem partner_PSU (hadm : StatedLieAdmissible .PSU n p e) (hn : 4 ≤ n) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSU
        (modelUniv .PSU n p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSU
        (modelUniv .PSU n p e hp.out).D, Commutes R R' := by
  have hf : 1 ≤ e := hadm.2.1
  have hr : 2 ≤ n / 2 := by omega
  have hB := hasBruhatDatum .PSU n p e hp.out trivial hadm
  have hC := cartanOK .PSU n p e hp.out trivial hadm
  have hL := isLongestRoot_single .PSU n p e hp.out trivial hadm
  have hL2 := isLongestRoot_two_nsmul_single_PSU n p e hp.out hadm
  revert hB hC hL hL2
  rw [modelUniv_PSU hf]
  intro hB hC hL hL2
  obtain ⟨nn, H, hct, hext⟩ := hB
  obtain ⟨hirr, hratio⟩ := hC
  by_cases he : Even n
  · obtain ⟨hc, hd⟩ := unitary_even he
    obtain ⟨h1, h2⟩ := cartanC_double (n / 2) hr
    refine partner_fund_of_longest (by decide) (by decide)
      (commutingPartner_double hct hext hirr hratio
        (k := ⟨n / 2 - 1, by show n / 2 - 1 < n / 2; omega⟩)
        (j := ⟨n / 2 - 2, by show n / 2 - 2 < n / 2; omega⟩) ?_ ?_
        (hL ⟨n / 2 - 1, by show n / 2 - 1 < n / 2; omega⟩
          ⟨he, by show n / 2 - 1 + 1 = n / 2; omega⟩))
    · show Unitary.cartan n ⟨n / 2 - 1, by omega⟩ ⟨n / 2 - 1, by omega⟩ = 2
      rw [hc]
      exact h1
    · show Unitary.cartan n ⟨n / 2 - 1, by omega⟩ ⟨n / 2 - 2, by omega⟩ *
        Unitary.cartan n ⟨n / 2 - 2, by omega⟩ ⟨n / 2 - 1, by omega⟩ = 2
      rw [hc]
      exact h2
  · obtain ⟨hc, hd⟩ := unitary_odd he
    obtain ⟨h1, h2⟩ := cartanC_double (n / 2) hr
    have hkd : (⟨n / 2 - 1, by omega⟩ : Fin (n / 2)) ∈ Unitary.divisible n := by
      rw [hd]
      show n / 2 - 1 + 1 = n / 2
      omega
    refine partner_fund_of_longest (by decide) (by decide)
      (commutingPartner_double_two hct hext hirr hratio
        (k := ⟨n / 2 - 1, by show n / 2 - 1 < n / 2; omega⟩)
        (j := ⟨n / 2 - 2, by show n / 2 - 2 < n / 2; omega⟩) hkd ?_ ?_
        (hL2 he ⟨n / 2 - 1, by show n / 2 - 1 < n / 2; omega⟩
          (by show n / 2 - 1 + 1 = n / 2; omega)))
    · show Unitary.cartan n ⟨n / 2 - 1, by omega⟩ ⟨n / 2 - 1, by omega⟩ = 2
      rw [hc]
      simpa using h1
    · show Unitary.cartan n ⟨n / 2 - 1, by omega⟩ ⟨n / 2 - 2, by omega⟩ *
        Unitary.cartan n ⟨n / 2 - 2, by omega⟩ ⟨n / 2 - 1, by omega⟩ = 2
      rw [hc]
      simp only [Matrix.transpose_apply]
      rw [mul_comm]
      exact h2

theorem cartan_F4_double :
    Tag.cartan .F4 ⟨1, by decide⟩ ⟨1, by decide⟩ = 2 ∧
      Tag.cartan .F4 ⟨1, by decide⟩ ⟨2, by decide⟩ * Tag.cartan .F4 ⟨2, by decide⟩ ⟨1, by decide⟩ =
        2 := by
  decide

theorem cartan_E_nonadjacent :
    Tag.cartan .E6 ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 ∧
      Tag.cartan .E7 ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 ∧
      Tag.cartan .E8 ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
  decide

theorem cartan_G2_triple :
    Tag.cartan .G2 ⟨0, by decide⟩ ⟨0, by decide⟩ = 2 ∧
      Tag.cartan .G2 ⟨1, by decide⟩ ⟨1, by decide⟩ = 2 ∧
      Tag.cartan .G2 ⟨0, by decide⟩ ⟨1, by decide⟩ = -1 ∧
      Tag.cartan .G2 ⟨1, by decide⟩ ⟨0, by decide⟩ = -3 := by
  decide

theorem fin_G2_two : ∀ i : Fin (Tag.rank .G2), i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
  decide

theorem partner_F4 (hadm : StatedLieAdmissible .F4 0 p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .F4
        (modelUniv .F4 0 p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .F4
        (modelUniv .F4 0 p e hp.out).D, Commutes R R' := by
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .F4 0 p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .F4 0 p e hp.out trivial hadm
  have h1 : 1 < Tag.rank .F4 := by decide
  have h2 : 2 < Tag.rank .F4 := by decide
  have hk := isLongestRoot_single .F4 0 p e hp.out trivial hadm ⟨1, h1⟩ (by show 1 < 2; decide)
  exact partner_fund_of_longest (by decide) (by decide)
    (commutingPartner_double hct hext hirr hratio (k := ⟨1, h1⟩) (j := ⟨2, h2⟩)
      cartan_F4_double.1 cartan_F4_double.2 hk)

theorem partner_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .twistedE6
        (modelUniv .twistedE6 0 p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .twistedE6
        (modelUniv .twistedE6 0 p e hp.out).D, Commutes R R' := by
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .twistedE6 0 p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .twistedE6 0 p e hp.out trivial hadm
  have h1 : 1 < Tag.rank .F4 := by decide
  have h2 : 2 < Tag.rank .F4 := by decide
  have hk := isLongestRoot_single .twistedE6 0 p e hp.out trivial hadm ⟨1, h1⟩
    (by show 1 < 2; decide)
  exact partner_fund_of_longest (by decide) (by decide)
    (commutingPartner_double hct hext hirr hratio (k := ⟨1, h1⟩) (j := ⟨2, h2⟩)
      cartan_F4_double.1 cartan_F4_double.2 hk)

theorem partner_E6 (hadm : StatedLieAdmissible .E6 0 p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E6
        (modelUniv .E6 0 p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E6
        (modelUniv .E6 0 p e hp.out).D, Commutes R R' := by
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .E6 0 p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .E6 0 p e hp.out trivial hadm
  have h0 : 0 < Tag.rank .E6 := by decide
  have h1 : 1 < Tag.rank .E6 := by decide
  exact partner_fund_of_longest (by decide) (by decide)
    (commutingPartner_nonadjacent hct hext hirr hratio (k := ⟨0, h0⟩) (j := ⟨1, h1⟩)
      cartan_E_nonadjacent.1 (isLongestRoot_single .E6 0 p e hp.out trivial hadm ⟨0, h0⟩ trivial)
      (isLongestRoot_single .E6 0 p e hp.out trivial hadm ⟨1, h1⟩ trivial))

theorem partner_E7 (hadm : StatedLieAdmissible .E7 0 p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E7
        (modelUniv .E7 0 p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E7
        (modelUniv .E7 0 p e hp.out).D, Commutes R R' := by
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .E7 0 p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .E7 0 p e hp.out trivial hadm
  have h0 : 0 < Tag.rank .E7 := by decide
  have h1 : 1 < Tag.rank .E7 := by decide
  exact partner_fund_of_longest (by decide) (by decide)
    (commutingPartner_nonadjacent hct hext hirr hratio (k := ⟨0, h0⟩) (j := ⟨1, h1⟩)
      cartan_E_nonadjacent.2.1
      (isLongestRoot_single .E7 0 p e hp.out trivial hadm ⟨0, h0⟩ trivial)
      (isLongestRoot_single .E7 0 p e hp.out trivial hadm ⟨1, h1⟩ trivial))

theorem partner_E8 (hadm : StatedLieAdmissible .E8 0 p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E8
        (modelUniv .E8 0 p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E8
        (modelUniv .E8 0 p e hp.out).D, Commutes R R' := by
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .E8 0 p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .E8 0 p e hp.out trivial hadm
  have h0 : 0 < Tag.rank .E8 := by decide
  have h1 : 1 < Tag.rank .E8 := by decide
  exact partner_fund_of_longest (by decide) (by decide)
    (commutingPartner_nonadjacent hct hext hirr hratio (k := ⟨0, h0⟩) (j := ⟨1, h1⟩)
      cartan_E_nonadjacent.2.2
      (isLongestRoot_single .E8 0 p e hp.out trivial hadm ⟨0, h0⟩ trivial)
      (isLongestRoot_single .E8 0 p e hp.out trivial hadm ⟨1, h1⟩ trivial))

theorem partner_G2 (hadm : StatedLieAdmissible .G2 0 p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .G2
        (modelUniv .G2 0 p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .G2
        (modelUniv .G2 0 p e hp.out).D, Commutes R R' := by
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .G2 0 p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .G2 0 p e hp.out trivial hadm
  have h0 : 0 < Tag.rank .G2 := by decide
  have h1 : 1 < Tag.rank .G2 := by decide
  have hk := isLongestRoot_single .G2 0 p e hp.out trivial hadm ⟨0, h0⟩ rfl
  obtain ⟨c1, c2, c3, c4⟩ := cartan_G2_triple
  exact commutingPartner_triple (Or.inl rfl) hct hext hirr rfl (k := ⟨0, h0⟩) (j := ⟨1, h1⟩)
    fin_G2_two c1 c2 c3 c4 hk

theorem partner_trialityD4 (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .trialityD4
        (modelUniv .trialityD4 0 p e hp.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .trialityD4
        (modelUniv .trialityD4 0 p e hp.out).D, Commutes R R' := by
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .trialityD4 0 p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .trialityD4 0 p e hp.out trivial hadm
  have h0 : 0 < Tag.rank .G2 := by decide
  have h1 : 1 < Tag.rank .G2 := by decide
  have hk := isLongestRoot_single .trialityD4 0 p e hp.out trivial hadm ⟨0, h0⟩ rfl
  obtain ⟨c1, c2, c3, c4⟩ := cartan_G2_triple
  exact commutingPartner_triple (Or.inr rfl) hct hext hirr rfl (k := ⟨0, h0⟩) (j := ⟨1, h1⟩)
    fin_G2_two c1 c2 c3 c4 hk

end CFSG.ClassicalInvolution.RouteD.LieBridge
