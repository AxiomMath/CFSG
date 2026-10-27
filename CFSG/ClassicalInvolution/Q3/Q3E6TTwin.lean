module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6TwinModel
public import CFSG.ClassicalInvolution.Q3.Q3WAPow
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

section Twin

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  {n : ℕ}

omit [Finite F] in
theorem twinR0'_ne3 (hn : 3 ≤ n) : twinR0' hirr hn ≠ twinR0 (b := b) (c := c) hirr hn := by
  intro h
  have hle : (twinR0' hirr hn).map (spinAction (quadMinus n F b c)) ≤
      (twinFrame (b := b) (c := c) hn).swap.La.range := map_conj_shortWeyl_le hirr hn
  rw [h, map_rankOne_zero hirr hn] at hle
  have hmem : (twinFrame (b := b) (c := c) hn).La (upperSL2 1) ∈
      (twinFrame (b := b) (c := c) hn).swap.La.range := hle ⟨upperSL2 1, rfl⟩
  rcases (Frame.La_mem_swap_range_iff _ _).mp hmem with h1 | h1
  · have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simp at this
  · have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simp [Matrix.SpecialLinearGroup.coe_neg] at this

omit [Finite F] in
theorem eq_of_map_eq_fund_minus3
    (hpow : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), Q3W.Pow3 R)
    (hcop : ∀ x ∈ (spinAction (quadMinus n F b c)).ker, ¬ 3 ∣ orderOf x)
    {R R' : Subgroup (spinGroup (quadMinus n F b c))}
    (hR : R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr))
    (hR' : R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr))
    (h : R.map (spinAction (quadMinus n F b c)) = R'.map (spinAction (quadMinus n F b c))) :
    R = R' :=
  Q3W.eq_of_map_eq_of_pow3 (spinAction (quadMinus n F b c)) (ker_spinAction_le_center _) hcop
    (hpow R hR) (hpow R' hR') h

theorem eq_twinR0'_of_twin3 (hn : 5 ≤ n) (hodd : Odd (Nat.card F))
    (hperfK : Group.IsPerfect (spinGroup (quadMinus n F b c)))
    (hsc : FundamentalSingleClass .POmegaMinus (minusDatum n hirr))
    (hpow : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), Q3W.Pow3 R)
    (hcop : ∀ x ∈ (spinAction (quadMinus n F b c)).ker, ¬ 3 ∣ orderOf x)
    (hnc : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), ∀ x ∈ R,
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c))) → x = 1)
    {R' : Subgroup (spinGroup (quadMinus n F b c))}
    (hR' : R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr))
    (hne : R' ≠ twinR0 hirr (by omega : 3 ≤ n))
    (hcomm : Commutes (twinR0 hirr (by omega : 3 ≤ n)) R')
    {r r' : spinGroup (quadMinus n F b c)} (hr : r ∈ twinR0 hirr (by omega : 3 ≤ n))
    (hr1 : r ≠ 1) (hr' : r' ∈ R') (hr'1 : r' ≠ 1)
    (hcen : ∀ y, r * r' * y * (r * r')⁻¹ * y⁻¹ ∈
      Subgroup.center (spinGroup (quadMinus n F b c))) :
    R' = twinR0' hirr (by omega : 3 ≤ n) := by
  have hn3 : 3 ≤ n := by omega
  have hR₀mem : twinR0 hirr hn3 ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    rankOne_mem_fund_minus hirr (k := twIdx0 hn3) (by simp only [twIdx0]; omega)
  have hR₀'mem : twinR0' hirr hn3 ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    conjSub_mem_fundamentalSubgroups hR₀mem _
  obtain ⟨g, hg⟩ := hsc _ hR₀mem R' hR'
  have hF' := isFundamental_map_conj hirr hn3 g
  rw [← hg] at hF'
  have hinv := same_involution_of_twin hirr hn hodd hperfK (isFundamental_twinR0 hirr hn3) hF'
    hcomm (hnc _ hR₀mem) (hnc _ hR') hr hr1 hr' hr'1 hcen
  rw [← hinv] at hF'
  obtain ⟨L'', hL'', hneL, -, huniq⟩ :=
    IsFundamental.exists_twin hodd (isFundamental_twinR0 hirr hn3)
  have h1 := huniq _ hF'
  have h2 := huniq _ (isFundamental_twinR0' hirr hodd hn3)
  rcases h1 with h1 | h1
  · exact absurd (eq_of_map_eq_fund_minus3 hirr hpow hcop hR' hR₀mem h1) hne
  rcases h2 with h2 | h2
  · exact absurd (eq_of_map_eq_fund_minus3 hirr hpow hcop hR₀'mem hR₀mem h2) (twinR0'_ne3 hirr hn3)
  exact eq_of_map_eq_fund_minus3 hirr hpow hcop hR' hR₀'mem (h1.trans h2.symm)

theorem twin_partner_spin3 (hn : 5 ≤ n) (hodd : Odd (Nat.card F))
    (hperfK : Group.IsPerfect (spinGroup (quadMinus n F b c)))
    (hsc : FundamentalSingleClass .POmegaMinus (minusDatum n hirr))
    (hpow : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), Q3W.Pow3 R)
    (hcop : ∀ x ∈ (spinAction (quadMinus n F b c)).ker, ¬ 3 ∣ orderOf x)
    (hnc : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), ∀ x ∈ R,
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c))) → x = 1)
    {R R' : Subgroup (spinGroup (quadMinus n F b c))}
    (hR : R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr))
    (hR' : R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr)) (hne : R ≠ R')
    (hcomm : Commutes R R')
    (hant : ∃ r ∈ R, r ≠ 1 ∧ ∃ r' ∈ R', r' ≠ 1 ∧ ∀ y,
      r * r' * y * (r * r')⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c))) :
    ∃ R'' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr),
      (∃ W, LinearBlockStandardPair F W R R'') ∧ ∃ W, LinearBlockStandardPair F W R'' R' := by
  have hn3 : 3 ≤ n := by omega
  have hn4 : 4 ≤ n := by omega
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hR₀mem : twinR0 hirr hn3 ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    rankOne_mem_fund_minus hirr (k := twIdx0 hn3) (by simp only [twIdx0]; omega)
  have hR₁mem : twinR1 hirr hn4 ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    rankOne_mem_fund_minus hirr (k := twIdx1 hn3) (by simp only [twIdx1]; omega)
  obtain ⟨g, hg⟩ := hsc _ hR₀mem R hR
  obtain ⟨r, hr, hr1, r', hr', hr'1, hcen⟩ := hant
  have hR₁' : conjSub g⁻¹ R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    conjSub_mem_fundamentalSubgroups hR' g⁻¹
  have hRg : conjSub g⁻¹ R = twinR0 hirr hn3 := by
    rw [hg, conjSub_inv_conjSub]
  have hne₁ : conjSub g⁻¹ R' ≠ twinR0 hirr hn3 := by
    intro h
    apply hne
    rw [← hRg] at h
    have := congrArg (conjSub g) h
    rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
    exact this.symm
  have hcomm₁ : Commutes (twinR0 hirr hn3) (conjSub g⁻¹ R') := by
    rw [← hRg]
    exact (commutes_conjSub_iff g⁻¹).mpr hcomm
  have hr₁ : g⁻¹ * r * g ∈ twinR0 hirr hn3 := by
    rw [← hRg]
    exact mem_conjSub_iff.mpr (by simpa [mul_assoc] using hr)
  have hr₁' : g⁻¹ * r' * g ∈ conjSub g⁻¹ R' := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hr'
  have hcen₁ : ∀ y, (g⁻¹ * r * g) * (g⁻¹ * r' * g) * y * ((g⁻¹ * r * g) * (g⁻¹ * r' * g))⁻¹ *
      y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c)) := by
    intro y
    have h := hcen (g * y * g⁻¹)
    set w := r * r' * (g * y * g⁻¹) * (r * r')⁻¹ * (g * y * g⁻¹)⁻¹ with hw
    have hc : g⁻¹ * w = w * g⁻¹ := Subgroup.mem_center_iff.mp h g⁻¹
    have e : (g⁻¹ * r * g) * (g⁻¹ * r' * g) * y * ((g⁻¹ * r * g) * (g⁻¹ * r' * g))⁻¹ * y⁻¹ =
        g⁻¹ * w * g := by
      rw [hw]
      group
    rw [e, hc, mul_assoc, inv_mul_cancel, mul_one]
    exact h
  have hone : ∀ x : spinGroup (quadMinus n F b c), x ≠ 1 → g⁻¹ * x * g ≠ 1 := by
    intro x hx h
    apply hx
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]
    group
  have key := eq_twinR0'_of_twin3 hirr hn hodd hperfK hsc hpow hcop hnc hR₁' hne₁ hcomm₁ hr₁
    (hone r hr1) hr₁' (hone r' hr'1) hcen₁
  have hR'eq : R' = conjSub g (twinR0' hirr hn3) := by
    rw [← key, conjSub_conjSub_inv]
  refine ⟨conjSub g (twinR1 hirr hn4), conjSub_mem_fundamentalSubgroups hR₁mem g, ?_, ?_⟩
  · obtain ⟨W, hW⟩ := exists_standardPair_R0_R1 hirr hn4 h2
    rw [hg]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW g⟩
  · obtain ⟨W, hW⟩ := exists_standardPair_R1_twin hirr hn4 h2
    rw [hR'eq]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW g⟩

end Twin

section Main


theorem twinPartnerFactTwin_pOmegaMinus_five3 :
    TwinPartnerFactTwin 3 1 .POmegaMinus 5 1 := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaMinus 5 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hY := Q3W.yData3_minus (by norm_num : 4 ≤ 5) hadm
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [Q3W.card_gf3]
    decide
  have hnc := CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral 3 .POmegaMinus 5 1 trivial hadm
    (by decide)
  intro R hR R' hR' hne hcomm hant
  exact twin_partner_spin3 (minusCoeffs_irr 3 1) (by norm_num) hodd hY.perfK hY.sc hY.pow3
    (fun x hx => hY.cop x (ker_spinAction_le_center _ hx)) hnc hR hR' hne hcomm hant

end Main

end CFSG.ClassicalInvolution.Q3.Q3E6T
