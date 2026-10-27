module

public import CFSG.ClassicalInvolution.Q3.Q3TD3Orth
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem _root_.CFSG.ClassicalInvolution.Q3.Q3TY.DNodes3.mem_loc {m : ℕ} {K : Subgroup G}
    (nd : DNodes3 m Ω K) (b : Fin m) {L : Subgroup G} (hL : L ∈ Ω) (hc : Commutes L (nd.J b)) :
    L ∈ centralizingMembers Ω {nd.w b} :=
  mem_centralizingMembers_of_commutes hL (nd.cl b).mem hc

section Scenarios

variable {m : ℕ} {K : Subgroup G} {z : G}

theorem scenario_A3
    (hF : OrthGeom (Subgroup.center (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    (c : TCtx3 .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (nd : DNodes3 m Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {pp a₀ a₁ e b : Fin m} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (h0 : DNodes3.Adj pp a₀) (h1 : DNodes3.Adj pp a₁) (h01 : a₀ ≠ a₁) (h01' : ¬ DNodes3.Adj a₀ a₁)
    (hea₀ : e ≠ a₀) (hea₁ : e ≠ a₁)
    (hdis : (DNodes3.Adj e a₀ ∧ ¬ DNodes3.Adj e a₁) ∨ (¬ DNodes3.Adj e a₀ ∧ DNodes3.Adj e a₁))
    (hbpp : b ≠ pp) (hb0 : b ≠ a₀) (hb1 : b ≠ a₁) (hbe : b ≠ e)
    (hbpp' : ¬ DNodes3.Adj b pp) (hb0' : ¬ DNodes3.Adj b a₀) (hb1' : ¬ DNodes3.Adj b a₁)
    (hbe' : ¬ DNodes3.Adj b e) : False := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle (nd.mem b) (nd.cl b)
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t := by
    have := standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
    exact this
  have hKJ : ∀ a, K ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact not_commutes_self3 c.hz this
  have hβJ : ∀ a, β ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact hnKβ this
  have hKw : ∀ a, Commute z (nd.w a) := fun a =>
    (nd.commK a) z c.hz.mem (nd.w a) (nd.cl a).mem
  have mxJ : ∀ a, a ≠ b → ¬ DNodes3.Adj a b → nd.J a ∈ centralizingMembers Ω {nd.w b} :=
    fun a hab hadj => nd.mem_loc b (nd.mem a) (nd.commutes_of_not_adj hab hadj)
  have mxK : K ∈ centralizingMembers Ω {nd.w b} := nd.mem_loc b c.hK (nd.commK b)
  have mxβ : β ∈ centralizingMembers Ω {nd.w b} := nd.mem_loc b hβ (hfix b hbpp)
  have hppne : ∀ a, DNodes3.Adj pp a → a ≠ pp := fun a h => (DNodes3.Adj.ne h).symm
  have hfix0 : Commutes β (nd.J a₀) := hfix a₀ (hppne a₀ h0)
  have hfix1 : Commutes β (nd.J a₁) := hfix a₁ (hppne a₁ h1)
  have hcomm0β : Commutes (nd.J a₀) β := commutes_symm hfix0
  have hcomm1β : Commutes (nd.J a₁) β := commutes_symm hfix1
  refine star_config3 cx hF (c := nd.J pp) (wc := nd.w pp)
    (l := ![nd.J a₀, nd.J a₁, β]) (w := ![nd.w a₀, nd.w a₁, t]) ?_ (nd.cl pp) ?_ ?_ ?_ ?_ ?_
  · exact mxJ pp hbpp.symm (fun h => hbpp' h.symm)
  · intro i
    fin_cases i
    · exact mxJ a₀ hb0.symm (fun h => hb0' h.symm)
    · exact mxJ a₁ hb1.symm (fun h => hb1' h.symm)
    · exact mxβ
  · intro i
    fin_cases i
    · exact nd.cl a₀
    · exact nd.cl a₁
    · exact ht
  · intro i
    fin_cases i
    · exact ⟨nd.ne_J (DNodes3.Adj.ne h0), nd.not_commutes_of_adj h0, nd.commute_w _ _,
        nd.conjSub_w h0⟩
    · exact ⟨nd.ne_J (DNodes3.Adj.ne h1), nd.not_commutes_of_adj h1, nd.commute_w _ _,
        nd.conjSub_w h1⟩
    · exact ⟨(hβJ pp).symm, fun h => hmov (commutes_symm h),
        (commute_of_conjSub_eq3 (nd.cl pp) hnorm).symm, hnorm⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact ⟨nd.ne_J h01, nd.commutes_of_not_adj h01 h01'⟩
    · exact ⟨(hβJ a₀).symm, hcomm0β⟩
    · exact ⟨nd.ne_J h01.symm, nd.commutes_of_not_adj h01.symm (fun h => h01' h.symm)⟩
    · exact absurd rfl hij
    · exact ⟨(hβJ a₁).symm, hcomm1β⟩
    · exact ⟨hβJ a₀, hfix0⟩
    · exact ⟨hβJ a₁, hfix1⟩
    · exact absurd rfl hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd hij (by decide) | skip
    ·
      refine ⟨nd.J e, nd.w e, mxJ e hbe.symm (fun h => hbe' h.symm), nd.cl e, nd.ne_J hea₀,
        nd.ne_J hea₁, nd.commute_w _ _, nd.commute_w _ _, ?_⟩
      rcases hdis with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
      · intro hiff
        exact nd.not_commutes_of_adj ha (hiff.mpr (nd.commutes_of_not_adj hea₁ hb'))
      · intro hiff
        exact nd.not_commutes_of_adj hb' (hiff.mp (nd.commutes_of_not_adj hea₀ ha))
    ·
      exact ⟨K, z, mxK, c.hz, hKJ a₀, hKne, hKw a₀, hzt,
        fun hiff => hnKβ (hiff.mp (nd.commK a₀))⟩
    ·
      exact ⟨K, z, mxK, c.hz, hKJ a₁, hKne, hKw a₁, hzt,
        fun hiff => hnKβ (hiff.mp (nd.commK a₁))⟩

theorem scenario_B3
    (hF : OrthGeom (Subgroup.center (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    (c : TCtx3 .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (nd : DNodes3 m Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {pp q a₀ a₁ a₂ e b : Fin m} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (hpp : pp = a₁ ∨ pp = a₂)
    (hq0 : DNodes3.Adj q a₀) (hq1 : DNodes3.Adj q a₁) (hq2 : DNodes3.Adj q a₂)
    (h01 : a₀ ≠ a₁) (h02 : a₀ ≠ a₂) (h12 : a₁ ≠ a₂)
    (h01' : ¬ DNodes3.Adj a₀ a₁) (h02' : ¬ DNodes3.Adj a₀ a₂) (h12' : ¬ DNodes3.Adj a₁ a₂)
    (hea₀ : e ≠ a₀) (hea₁ : e ≠ a₁) (hea₂ : e ≠ a₂) (he0 : DNodes3.Adj e a₀)
    (he1 : ¬ DNodes3.Adj e a₁) (he2 : ¬ DNodes3.Adj e a₂)
    (hbq : b ≠ q) (hb0 : b ≠ a₀) (hb1 : b ≠ a₁) (hb2 : b ≠ a₂) (hbe : b ≠ e)
    (hbq' : ¬ DNodes3.Adj b q) (hb0' : ¬ DNodes3.Adj b a₀) (hb1' : ¬ DNodes3.Adj b a₁)
    (hb2' : ¬ DNodes3.Adj b a₂) (hbe' : ¬ DNodes3.Adj b e) : False := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle (nd.mem b) (nd.cl b)
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hKJ : ∀ a, K ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact not_commutes_self3 c.hz this
  have hβJ : ∀ a, β ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact hnKβ this
  have hbpp : b ≠ pp := by rcases hpp with rfl | rfl <;> assumption
  have hTw : ∀ a, Commute t (nd.w a) := fun a => by
    by_cases hap : a = pp
    · subst hap
      exact commute_of_conjSub_eq3 (nd.cl a) hnorm
    · exact (hfix a hap) t ht.mem (nd.w a) (nd.cl a).mem
  have mxJ : ∀ a, a ≠ b → ¬ DNodes3.Adj a b → nd.J a ∈ centralizingMembers Ω {nd.w b} :=
    fun a hab hadj => nd.mem_loc b (nd.mem a) (nd.commutes_of_not_adj hab hadj)
  have mxβ : β ∈ centralizingMembers Ω {nd.w b} := nd.mem_loc b hβ (hfix b hbpp)
  have hadjq : ∀ a, DNodes3.Adj q a → a ≠ q := fun a h => (DNodes3.Adj.ne h).symm
  refine star_config3 cx hF (c := nd.J q) (wc := nd.w q)
    (l := ![nd.J a₀, nd.J a₁, nd.J a₂]) (w := ![nd.w a₀, nd.w a₁, nd.w a₂])
    (mxJ q hbq.symm (fun h => hbq' h.symm)) (nd.cl q) ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact mxJ a₀ hb0.symm (fun h => hb0' h.symm)
    · exact mxJ a₁ hb1.symm (fun h => hb1' h.symm)
    · exact mxJ a₂ hb2.symm (fun h => hb2' h.symm)
  · intro i
    fin_cases i
    · exact nd.cl a₀
    · exact nd.cl a₁
    · exact nd.cl a₂
  · intro i
    fin_cases i
    · exact ⟨nd.ne_J (DNodes3.Adj.ne hq0), nd.not_commutes_of_adj hq0, nd.commute_w _ _,
        nd.conjSub_w hq0⟩
    · exact ⟨nd.ne_J (DNodes3.Adj.ne hq1), nd.not_commutes_of_adj hq1, nd.commute_w _ _,
        nd.conjSub_w hq1⟩
    · exact ⟨nd.ne_J (DNodes3.Adj.ne hq2), nd.not_commutes_of_adj hq2, nd.commute_w _ _,
        nd.conjSub_w hq2⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact ⟨nd.ne_J h01, nd.commutes_of_not_adj h01 h01'⟩
    · exact ⟨nd.ne_J h02, nd.commutes_of_not_adj h02 h02'⟩
    · exact ⟨nd.ne_J h01.symm, nd.commutes_of_not_adj h01.symm (fun h => h01' h.symm)⟩
    · exact absurd rfl hij
    · exact ⟨nd.ne_J h12, nd.commutes_of_not_adj h12 h12'⟩
    · exact ⟨nd.ne_J h02.symm, nd.commutes_of_not_adj h02.symm (fun h => h02' h.symm)⟩
    · exact ⟨nd.ne_J h12.symm, nd.commutes_of_not_adj h12.symm (fun h => h12' h.symm)⟩
    · exact absurd rfl hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd hij (by decide) | skip
    · refine ⟨nd.J e, nd.w e, mxJ e hbe.symm (fun h => hbe' h.symm), nd.cl e, nd.ne_J hea₀,
        nd.ne_J hea₁, nd.commute_w _ _, nd.commute_w _ _, ?_⟩
      intro hiff
      exact nd.not_commutes_of_adj he0 (hiff.mpr (nd.commutes_of_not_adj hea₁ he1))
    · refine ⟨nd.J e, nd.w e, mxJ e hbe.symm (fun h => hbe' h.symm), nd.cl e, nd.ne_J hea₀,
        nd.ne_J hea₂, nd.commute_w _ _, nd.commute_w _ _, ?_⟩
      intro hiff
      exact nd.not_commutes_of_adj he0 (hiff.mpr (nd.commutes_of_not_adj hea₂ he2))
    · refine ⟨β, t, mxβ, ht, (hβJ a₁), (hβJ a₂), hTw a₁, hTw a₂, ?_⟩
      intro hiff
      rcases hpp with rfl | rfl
      · exact hmov (hiff.mpr (hfix a₂ h12.symm))
      · exact hmov (hiff.mp (hfix a₁ h12))

theorem scenario_C3
    (hF : OrthFacts
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    (c : TCtx3 .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (nd : DNodes3 m Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {pp b : Fin m} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (hbpp : b ≠ pp) (hbpp' : ¬ DNodes3.Adj b pp) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W β (nd.J pp) := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle (nd.mem b) (nd.cl b)
  obtain ⟨W, hW⟩ := hKβ
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hβJ : β ≠ nd.J pp := fun h => by
    have := nd.commK pp
    rw [← h] at this
    exact hnKβ this
  have hnormK : conjSub t K = K :=
    conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  exact sign_config_orth3 cx hF (a := K) (b := β) (d := nd.J pp) (wa := z) (wb := t) (wd := nd.w pp)
    (nd.mem_loc b c.hK (nd.commK b)) (nd.mem_loc b hβ (hfix b hbpp))
    (nd.mem_loc b (nd.mem pp) (nd.commutes_of_not_adj hbpp.symm (fun h => hbpp' h.symm)))
    c.hz ht (nd.cl pp) hKne hβJ ⟨W, hW⟩ hmov (nd.commK pp) hzt
    (commute_of_conjSub_eq3 (nd.cl pp) hnorm).symm hnormK hnorm

local macro "idx_tac3" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (apply Gaps.fin_ne_of_val_ne; simp only; omega)
    | (left; apply Fin.ext; simp only; omega)
    | (right; apply Fin.ext; simp only; omega))

theorem adapted_pattern_D3 (hm : 7 ≤ m)
    (hF : OrthFacts
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    (c : TCtx3 .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (nd : DNodes3 m Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {pp : Fin m} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp) :
    pp.val = 0 ∧ ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W β (nd.J pp) := by
  have hpt : pp.val < m := pp.isLt
  have hp0 : pp.val = 0 := by
    by_contra hne
    have hp1 : 1 ≤ pp.val := Nat.one_le_iff_ne_zero.mpr hne
    have hcases : pp.val = 1 ∨ (2 ≤ pp.val ∧ pp.val + 5 ≤ m) ∨ pp.val + 4 = m ∨ pp.val + 3 = m ∨
        pp.val + 2 = m ∨ pp.val + 1 = m := by omega
    rcases hcases with h | h | h | h | h | h
    ·
      refine scenario_A3 hF.toOrthGeom c hsingle nd hβ ht hKβ (pp := pp) (a₀ := ⟨0, by omega⟩)
        (a₁ := ⟨2, by omega⟩) (e := ⟨3, by omega⟩) (b := ⟨m - 1, by omega⟩) hfix hmov hnorm
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      idx_tac3
    ·
      by_cases hs : pp.val ≤ 3
      · refine scenario_A3 hF.toOrthGeom c hsingle nd hβ ht hKβ (pp := pp)
          (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
          (e := ⟨pp.val - 2, by omega⟩) (b := ⟨m - 1, by omega⟩) hfix hmov hnorm
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        idx_tac3
      · refine scenario_A3 hF.toOrthGeom c hsingle nd hβ ht hKβ (pp := pp)
          (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
          (e := ⟨pp.val - 2, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        idx_tac3
    ·
      refine scenario_A3 hF.toOrthGeom c hsingle nd hβ ht hKβ (pp := pp)
        (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
        (e := ⟨m - 2, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      idx_tac3
    ·
      refine scenario_A3 hF.toOrthGeom c hsingle nd hβ ht hKβ (pp := pp)
        (a₀ := ⟨m - 4, by omega⟩) (a₁ := ⟨m - 2, by omega⟩)
        (e := ⟨m - 5, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      idx_tac3
    ·
      refine scenario_B3 hF.toOrthGeom c hsingle nd hβ ht hKβ (pp := pp) (q := ⟨m - 3, by omega⟩)
        (a₀ := ⟨m - 4, by omega⟩) (a₁ := ⟨m - 2, by omega⟩) (a₂ := ⟨m - 1, by omega⟩)
        (e := ⟨m - 5, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      idx_tac3
    ·
      refine scenario_B3 hF.toOrthGeom c hsingle nd hβ ht hKβ (pp := pp) (q := ⟨m - 3, by omega⟩)
        (a₀ := ⟨m - 4, by omega⟩) (a₁ := ⟨m - 2, by omega⟩) (a₂ := ⟨m - 1, by omega⟩)
        (e := ⟨m - 5, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      idx_tac3
  refine ⟨hp0, ?_⟩
  refine scenario_C3 hF c hsingle nd hβ ht hKβ (pp := pp) (b := ⟨2, by omega⟩) hfix hmov hnorm
    ?_ ?_ <;>
  idx_tac3

end Scenarios

end CFSG.ClassicalInvolution.Q3.Q3TD
