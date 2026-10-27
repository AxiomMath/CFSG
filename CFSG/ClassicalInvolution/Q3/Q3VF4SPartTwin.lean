module

public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinModel
public import CFSG.ClassicalInvolution.Q3.Q3WAPow

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {F : Type} [Field F] {n : ℕ}

theorem oddTwR0'_ne3 (hn : 3 ≤ n) : oddTwR0' (F := F) hn ≠ oddTwR0 hn := by
  intro h
  have hle : (oddTwR0' (F := F) hn).map (spinAction (quadOdd n F)) ≤
      (oddTwFrame (F := F) hn).swap.La.range := oddTw_map_conj_le hn
  rw [h, oddTw_map_rankOne_zero] at hle
  have hmem : (oddTwFrame (F := F) hn).La (upperSL2 1) ∈
      (oddTwFrame (F := F) hn).swap.La.range := hle ⟨upperSL2 1, rfl⟩
  rcases (Frame.La_mem_swap_range_iff _ _).mp hmem with h1 | h1
  · have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simp at this
  · have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simp [Matrix.SpecialLinearGroup.coe_neg] at this

theorem eq_of_map_eq_fund_odd3
    (hpow : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F), Q3W.Pow3 R)
    (hker2 : ∀ x ∈ (spinAction (quadOdd n F)).ker, x * x = 1)
    {R R' : Subgroup (spinGroup (quadOdd n F))}
    (hR : R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F))
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F))
    (h : R.map (spinAction (quadOdd n F)) = R'.map (spinAction (quadOdd n F))) : R = R' :=
  Q3W.eq_of_map_eq_of_pow3 (spinAction (quadOdd n F)) (ker_spinAction_le_center _)
    (fun z hz h3 =>
      absurd (h3.trans (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hker2 z hz)))
        (by norm_num))
    (hpow R hR) (hpow R' hR') h

variable [Finite F]

theorem eq_oddTwR0'_of_twin3 (hn : 4 ≤ n) (hodd : Odd (Nat.card F))
    (hsc : FundamentalSingleClass .POmegaOdd (oddDatum n F))
    (hpow : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F), Q3W.Pow3 R)
    (hker2 : ∀ x ∈ (spinAction (quadOdd n F)).ker, x * x = 1)
    (hnc : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F), ∀ x ∈ R,
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) → x = 1)
    {R' : Subgroup (spinGroup (quadOdd n F))}
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F))
    (hne : R' ≠ oddTwR0 (F := F) (by omega : 3 ≤ n))
    (hcomm : Commutes (oddTwR0 (F := F) (by omega : 3 ≤ n)) R')
    {r r' : spinGroup (quadOdd n F)} (hr : r ∈ oddTwR0 (F := F) (by omega : 3 ≤ n))
    (hr1 : r ≠ 1) (hr' : r' ∈ R') (hr'1 : r' ≠ 1)
    (hcen : ∀ y, r * r' * y * (r * r')⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) :
    R' = oddTwR0' (F := F) (by omega : 3 ≤ n) := by
  have hn3 : 3 ≤ n := by omega
  have hR₀mem : oddTwR0 (F := F) hn3 ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    rankOne_mem_fundamentalSubgroups_oddDatum hn3 (i := oddTwIdx0 hn3)
      (by simp only [oddTwIdx0]; omega)
  have hR₀'mem : oddTwR0' (F := F) hn3 ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    conjSub_mem_fundamentalSubgroups hR₀mem _
  obtain ⟨g, hg⟩ := hsc _ hR₀mem R' hR'
  have hF' := isFundamental_map_conj_odd (isFundamental_oddTwR0 (F := F) hn3) g
  rw [← hg] at hF'
  have hinv := same_involution_of_twin_odd hodd hn (isFundamental_oddTwR0 (F := F) hn3) hF' hcomm
    (hnc _ hR₀mem) (hnc _ hR') hr hr1 hr' hr'1 hcen
  rw [← hinv] at hF'
  obtain ⟨L'', hL'', hneL, -, huniq⟩ :=
    IsFundamental.exists_twin hodd (isFundamental_oddTwR0 (F := F) hn3)
  have h1 := huniq _ hF'
  have h2 := huniq _ (isFundamental_oddTwR0' (F := F) hodd hn3)
  rcases h1 with h1 | h1
  · exact absurd (eq_of_map_eq_fund_odd3 hpow hker2 hR' hR₀mem h1) hne
  rcases h2 with h2 | h2
  · exact absurd (eq_of_map_eq_fund_odd3 hpow hker2 hR₀'mem hR₀mem h2) (oddTwR0'_ne3 hn3)
  exact eq_of_map_eq_fund_odd3 hpow hker2 hR' hR₀'mem (h1.trans h2.symm)

theorem twin_partner_spin_odd3 (hn : 4 ≤ n) (hodd : Odd (Nat.card F))
    (hsc : FundamentalSingleClass .POmegaOdd (oddDatum n F))
    (hpow : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F), Q3W.Pow3 R)
    (hker2 : ∀ x ∈ (spinAction (quadOdd n F)).ker, x * x = 1)
    (hnc : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F), ∀ x ∈ R,
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) → x = 1)
    {R R' : Subgroup (spinGroup (quadOdd n F))}
    (hR : R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F))
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F)) (hne : R ≠ R')
    (hcomm : Commutes R R')
    (hant : ∃ r ∈ R, r ≠ 1 ∧ ∃ r' ∈ R', r' ≠ 1 ∧ ∀ y,
      r * r' * y * (r * r')⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) :
    ∃ R'' ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F),
      (∃ W, LinearBlockStandardPair F W R R'') ∧ ∃ W, LinearBlockStandardPair F W R'' R' := by
  have hn3 : 3 ≤ n := by omega
  have hR₀mem : oddTwR0 (F := F) hn3 ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    rankOne_mem_fundamentalSubgroups_oddDatum hn3 (i := oddTwIdx0 hn3)
      (by simp only [oddTwIdx0]; omega)
  have hR₁mem : oddTwR1 (F := F) hn3 ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    rankOne_mem_fundamentalSubgroups_oddDatum hn3 (i := oddTwIdx1 hn3)
      (by simp only [oddTwIdx1]; omega)
  obtain ⟨g, hg⟩ := hsc _ hR₀mem R hR
  obtain ⟨r, hr, hr1, r', hr', hr'1, hcen⟩ := hant
  have hR₁' : conjSub g⁻¹ R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    conjSub_mem_fundamentalSubgroups hR' g⁻¹
  have hRg : conjSub g⁻¹ R = oddTwR0 (F := F) hn3 := by
    rw [hg, conjSub_inv_conjSub]
  have hne₁ : conjSub g⁻¹ R' ≠ oddTwR0 (F := F) hn3 := by
    intro h
    apply hne
    rw [← hRg] at h
    have := congrArg (conjSub g) h
    rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
    exact this.symm
  have hcomm₁ : Commutes (oddTwR0 (F := F) hn3) (conjSub g⁻¹ R') := by
    rw [← hRg]
    exact (commutes_conjSub_iff g⁻¹).mpr hcomm
  have hr₁ : g⁻¹ * r * g ∈ oddTwR0 (F := F) hn3 := by
    rw [← hRg]
    exact mem_conjSub_iff.mpr (by simpa [mul_assoc] using hr)
  have hr₁' : g⁻¹ * r' * g ∈ conjSub g⁻¹ R' := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hr'
  have hcen₁ : ∀ y, (g⁻¹ * r * g) * (g⁻¹ * r' * g) * y * ((g⁻¹ * r * g) * (g⁻¹ * r' * g))⁻¹ *
      y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F)) := by
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
  have hone : ∀ x : spinGroup (quadOdd n F), x ≠ 1 → g⁻¹ * x * g ≠ 1 := by
    intro x hx h
    apply hx
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]
    group
  have key := eq_oddTwR0'_of_twin3 hn hodd hsc hpow hker2 hnc hR₁' hne₁ hcomm₁ hr₁
    (hone r hr1) hr₁' (hone r' hr'1) hcen₁
  have hR'eq : R' = conjSub g (oddTwR0' (F := F) hn3) := by
    rw [← key, conjSub_conjSub_inv]
  refine ⟨conjSub g (oddTwR1 (F := F) hn3), conjSub_mem_fundamentalSubgroups hR₁mem g, ?_, ?_⟩
  · obtain ⟨W, hW⟩ := exists_standardPair_oddTw_R0_R1 (F := F) hn3
    rw [hg]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW g⟩
  · obtain ⟨W, hW⟩ := exists_standardPair_oddTw_R1_twin (F := F) hn3
    rw [hR'eq]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW g⟩

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
