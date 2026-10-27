module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalCore1

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem Ps_inf_J_conj (Δ : Data σ r) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q) (i : Fin 3) :
    conjSub (Δ.a ^ (i : ℕ)) Δ.J ⊓ σ.Ps r i = ⊥ := by
  have h0 : Δ.J ⊓ σ.Ps r 0 = ⊥ := by
    rw [eq_bot_iff, ← J_inf_ON Δ hδq]
    exact inf_le_inf_left _ (Ps_zero_le_ON Δ)
  have hP : σ.Ps r i = conjSub (Δ.a ^ (i : ℕ)) (σ.Ps r 0) := by rw [conjSub_a_pow_Ps, zero_add]
  rw [hP, ← conjSub_inf, h0, conjSub_bot]

theorem odd_card_pCoreIn (Δ : Data σ r) (X : Subgroup G) : Odd (Nat.card (pCoreIn r X)) :=
  odd_card_of_isPGroup Δ.prime Δ.ne_two (isPGroup_pCoreIn r _)

namespace CoreHyp

variable {Δ : Data σ r} {V U : Subgroup G} {z : G} (h : CoreHyp Δ V U z)
include h

theorem T_le_normalizer_Ustar : σ.T ≤ Subgroup.normalizer (pCoreIn r (U ⊔ σ.C) : Set G) :=
  h.T_le_C'.trans (C_le_normalizer_pCoreIn_sup U)

theorem R0_le_Ustar : R Δ 0 ≤ pCoreIn r (U ⊔ σ.C) := fun u hu =>
  h.comp_U_subset_Ustar 0 (by rw [h.comp_U_zero]; exact hu)

theorem Rs1_le_Ustar : Rs Δ 1 ≤ pCoreIn r (U ⊔ σ.C) := fun u hu =>
  h.comp_U_subset_Ustar 1 (by rw [h.comp_U_one]; exact hu)

theorem Q2_subset_comp_U : (Δ.Q 2 : Set G) ⊆ comp σ U 2 :=
  fun _ hu => comp_mono h.V_le_U 2 (h.Q2_subset_comp hu)

theorem Y_le_Ustar : V ⊓ oddCoreIn (Kp σ r) ≤ pCoreIn r (U ⊔ σ.C) := by
  refine le_of_comp_subset h.valid h.odd_Y h.Y_T (by rw [h.Y_inf_C]; exact bot_le) ?_
  intro i
  match i with
  | 0 =>
    intro u hu
    have hP : u ∈ σ.Ps r 0 := V_inf_N_inf_oddCore_le Δ h.maxV
      ⟨⟨hu.1.1, Subgroup.mem_centralizer_singleton_iff.mpr hu.2.1.symm⟩, hu.1.2⟩
    exact h.R0_le_Ustar (Ps_le_R Δ 0 hP)
  | 1 => exact fun u hu => h.comp_U_subset_Ustar 1 ⟨h.V_le_U hu.1.1, hu.2⟩
  | 2 => exact fun u hu => h.comp_U_subset_Ustar 2 ⟨h.V_le_U hu.1.1, hu.2⟩

theorem comp_U_two_subset_R2 : ∃ W : Subgroup G, (W : Set G) = comp σ U 2 ∧
    σ.C ≤ Subgroup.normalizer (W : Set G) ∧ W ≤ R Δ 2 ∧ Δ.Q 2 ≤ W := by
  have hσ := h.valid
  have hδq := h.deltaEps
  obtain ⟨W, hW, hCW, hcases⟩ := h.U_omni.part_i_b 2
  have hQW : Δ.Q 2 ≤ W := fun u hu => by rw [← SetLike.mem_coe, hW]; exact h.Q2_subset_comp_U hu
  refine ⟨W, hW, hCW, ?_, hQW⟩
  rcases hcases with hWP | hWR | hWRs
  · exfalso
    apply Q_ne_bot Δ hδq hσ 2
    rw [eq_bot_iff, ← Q_inf_Ps Δ hδq 2]
    exact le_inf le_rfl (hQW.trans hWP)
  · exact hWR
  · exfalso
    have hQs : Δ.Q 2 ≤ Δ.Qs 2 := by
      have hD := inf_sup_eq_of_le_left (A := Δ.Qs 2) (B := σ.Ps r 2)
        (M := conjSub (Δ.a ^ ((2 : Fin 3) : ℕ)) Δ.J)
        ((Qs_le_Ns Δ hσ 2).trans (le_normalizer_pCoreIn r _)) (Qs_le_J_conj Δ 2)
      rw [Ps_inf_J_conj Δ hδq 2, sup_bot_eq] at hD
      rw [← hD]
      exact le_inf (Q_le_J_conj Δ 2) (hQW.trans hWRs)
    apply Q_ne_Qs Δ hδq 2
    exact Subgroup.eq_of_le_of_card_ge hQs (by rw [card_Q Δ hδq, card_Qs Δ hδq])

theorem Qs1_le_Zc : Δ.Qs 1 ≤ pCoreIn r (U ⊔ σ.C) ⊓
    Subgroup.centralizer (pCoreIn r (U ⊔ σ.C) : Set G) := by
  have hσ := h.valid
  have hδq := h.deltaEps
  have hF := h.facts
  have homni := h.omni
  have hI := h.inputs
  have : Fact r.Prime := ⟨Δ.prime⟩
  set Us := pCoreIn r (U ⊔ σ.C) with hUs
  set Zc : Subgroup G := Us ⊓ Subgroup.centralizer (Us : Set G) with hZc
  have hZcU : Zc ≤ U := inf_le_left.trans h.Ustar_le_U
  have hCZc : σ.C ≤ Subgroup.normalizer (Zc : Set G) := fun c hc =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨C_le_normalizer_pCoreIn_sup U hc,
      normalizer_le_normalizer_centralizer Us (C_le_normalizer_pCoreIn_sup U hc)⟩
  have hTZc : σ.T ≤ Subgroup.normalizer (Zc : Set G) := h.T_le_C'.trans hCZc
  have hZcodd : Odd (Nat.card Zc) :=
    (odd_card_pCoreIn Δ (U ⊔ σ.C)).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hZcC : Zc ⊓ σ.C = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_left).trans
    h.Ustar_inf_C.le)
  have hUsne : Us ≠ ⊥ := fun hb => Ps_zero_ne_bot Δ
    (eq_bot_iff.mpr ((Ps_le_R Δ 0).trans (hb ▸ h.R0_le_Ustar)))
  have hZcne : Zc ≠ ⊥ := by
    have hUsp : IsPGroup r Us := isPGroup_pCoreIn r _
    have : Nontrivial Us := by rw [Subgroup.nontrivial_iff_ne_bot]; exact hUsne
    have := hUsp.center_nontrivial
    obtain ⟨⟨w, hw⟩, hw1⟩ := exists_ne (1 : Subgroup.center Us)
    intro hb
    apply hw1
    have hwZ : (w : G) ∈ Zc := by
      refine ⟨w.2, ?_⟩
      show (w : G) ∈ Subgroup.centralizer (Us : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨x, hx⟩)
    rw [hb, Subgroup.mem_bot] at hwZ
    exact Subtype.ext (Subtype.ext hwZ)
  have hZcent : ∀ {X : Subgroup G}, X ≤ Us → Zc ≤ Subgroup.centralizer (X : Set G) :=
    fun hX => inf_le_right.trans (Subgroup.centralizer_le hX)
  have hA : Zc ⊓ R Δ 0 = ⊥ := by
    have hP : Zc ⊓ R Δ 0 ⊓ σ.Ps r 0 = ⊥ := by
      by_contra hne
      apply h.not_pGroupR
      apply pGroupR_of_centralizer_Ps0_Rs1 hσ hF Δ homni
      intro hb
      apply hne
      rw [eq_bot_iff, ← hb]
      exact fun g hg => ⟨hg.2, hZcent h.Rs1_le_Ustar hg.1.1⟩
    by_contra hne
    have hXQ := eq_Q_of_le_R Δ hδq hI.ii_4_10_iii 0 inf_le_right
      (fun c hc => Subgroup.inf_normalizer_le_normalizer_inf ⟨hCZc hc, C_le_normalizer_R Δ 0 hc⟩)
      hP hne
    have hQ0 : Δ.Q 0 ≤ Subgroup.centralizer ((V ⊓ oddCoreIn (Kp σ r) : Subgroup G) : Set G) :=
      hXQ ▸ inf_le_left.trans (hZcent h.Y_le_Ustar)
    have hQs0 : Δ.Qs 0 ≤
        Subgroup.centralizer ((V ⊓ oddCoreIn (Kp σ r) : Subgroup G) : Set G) := by
      have := conjSub_mono (g := z) hQ0
      rwa [h.swap.conj_Q, conjSub_centralizer, h.conjSub_z_Y] at this
    have hJ : Δ.J ≤ Subgroup.centralizer ((V ⊓ oddCoreIn (Kp σ r) : Subgroup G) : Set G) := by
      have hJeq := J_conj_eq Δ hδq 0
      rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, pow_zero, conjSub_one] at hJeq
      rw [hJeq]
      exact sup_le hQ0 hQs0
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp (Q_ne_bot Δ hδq hσ 2))
    have hc : σ.x * (u : G) = u * σ.x :=
      (Subgroup.mem_centralizer_iff.mp (hJ (x_mem_J hσ Δ (J_inf_ON Δ hδq))) u
        (h.Q2_le_Y u.2)).symm
    have hinv : σ.xs 0 * (u : G) * (σ.xs 0)⁻¹ = (u : G)⁻¹ :=
      R_inverted Δ hσ (i := 2) (j := 0) (by decide) (Q_le_R Δ 2 u.2)
    exact hu1 (Subtype.ext (eq_one_of_conj_eq_inv_of_commute
      (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two (Δ.Q_pgroup 2).1) u.2)
      hinv hc))
  have hC2 : Zc ⊓ R Δ 2 = ⊥ := by
    have hP : Zc ⊓ R Δ 2 ⊓ σ.Ps r 2 = ⊥ := by
      by_contra hne
      apply h.not_pGroupR
      apply pGroupR_of_centralizer_Ps2_R0 hσ hF Δ homni
      intro hb
      apply hne
      rw [eq_bot_iff, ← hb]
      exact fun g hg => ⟨hg.2, hZcent h.R0_le_Ustar hg.1.1⟩
    by_contra hne
    have hXQ := eq_Q_of_le_R Δ hδq hI.ii_4_10_iii 2 inf_le_right
      (fun c hc => Subgroup.inf_normalizer_le_normalizer_inf ⟨hCZc hc, C_le_normalizer_R Δ 2 hc⟩)
      hP hne
    have hRQ : R Δ 0 ≤ Subgroup.centralizer (Δ.Q 2 : Set G) :=
      Subgroup.le_centralizer_iff.mp (hXQ ▸ inf_le_left.trans (hZcent h.R0_le_Ustar))
    exact h.not_pGroupR (lemma11_1 hσ Δ homni (C_le_normalizer_Q Δ 2)
      (hRQ.trans (centralizer_le_normalizer _))
      (R_le_oddCore_normalizer_Q Δ hδq hσ hI.ii_4_4 2) (isPGroup_R Δ hσ 0)
      (isPGroup_R Δ hσ 2) (C_le_normalizer_R Δ 0) (C_le_normalizer_R Δ 2))
  have hB : Zc ⊓ Rs Δ 1 = ⊥ ∨ Zc ⊓ Rs Δ 1 = Δ.Qs 1 := by
    have hP : Zc ⊓ Rs Δ 1 ⊓ σ.Ps r 1 = ⊥ := by
      by_contra hne
      apply h.not_pGroupR
      apply pGroupR_of_centralizer_Ps1_R0 hσ hF Δ homni
      intro hb
      apply hne
      rw [eq_bot_iff, ← hb]
      exact fun g hg => ⟨hg.2, hZcent h.R0_le_Ustar hg.1.1⟩
    by_cases hne : Zc ⊓ Rs Δ 1 = ⊥
    · exact Or.inl hne
    · exact Or.inr (eq_Qs_of_le_Rs Δ hδq hI.ii_4_10_iii 1 inf_le_right
        (fun c hc => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hCZc hc, C_le_normalizer_Rs Δ 1 hc⟩) hP hne)
  obtain ⟨W₂, hW₂, -, hW₂R, -⟩ := h.comp_U_two_subset_R2
  have hZcle : Zc ≤ Zc ⊓ Rs Δ 1 := by
    refine le_of_comp_subset hσ hZcodd hTZc (by rw [hZcC]; exact bot_le) ?_
    intro i
    match i with
    | 0 =>
      intro u hu
      have hu' : u ∈ Zc ⊓ R Δ 0 := ⟨hu.1, by
        have := comp_mono hZcU 0 hu
        rwa [h.comp_U_zero] at this⟩
      rw [hA] at hu'
      rw [Subgroup.mem_bot.mp hu']
      exact Subgroup.one_mem _
    | 1 =>
      intro u hu
      exact ⟨hu.1, by
        have := comp_mono hZcU 1 hu
        rwa [h.comp_U_one] at this⟩
    | 2 =>
      intro u hu
      have hu' : u ∈ Zc ⊓ R Δ 2 := ⟨hu.1, hW₂R (by
        rw [← SetLike.mem_coe, hW₂]
        exact comp_mono hZcU 2 hu)⟩
      rw [hC2] at hu'
      rw [Subgroup.mem_bot.mp hu']
      exact Subgroup.one_mem _
  rcases hB with hB | hB
  · exact absurd (le_bot_iff.mp (hB ▸ hZcle)) hZcne
  · rw [← hB]
    exact inf_le_left

theorem Qs1_le_centralizer_Ustar :
    Δ.Qs 1 ≤ Subgroup.centralizer (pCoreIn r (U ⊔ σ.C) : Set G) :=
  h.Qs1_le_Zc.trans inf_le_right

theorem Q2_le_centralizer_Ps0 : Δ.Q 2 ≤ Subgroup.centralizer (σ.Ps r 0 : Set G) := fun u hu =>
  mem_centralizer_of_inverted
    (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two (Δ.Q_pgroup 2).1) hu)
    (R_inverted Δ h.valid (i := 2) (j := 0) (by decide) (Q_le_R Δ 2 hu))
    (fun a ha => (Subgroup.mem_centralizer_singleton_iff.mp (Δ.P_centralized 0 ha)).symm)
    (V_le_Kp h.maxV (h.Q2_le_V hu))

theorem Qs1_le_centralizer_Ps0 : Δ.Qs 1 ≤ Subgroup.centralizer (σ.Ps r 0 : Set G) :=
  fun u hu =>
  mem_centralizer_of_inverted
    (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two (Δ.Q_pgroup 1).2) hu)
    (Rs_inverted Δ h.valid (i := 1) (j := 0) (by decide) (Qs_le_Rs Δ 1 hu))
    (fun a ha => (Subgroup.mem_centralizer_singleton_iff.mp (Δ.P_centralized 0 ha)).symm)
    (V_le_Kp h.maxV (h.Qs1_le_V hu))

theorem comp_U_two : comp σ U 2 = (Δ.Q 2 : Set G) := by
  have hσ := h.valid
  have hδq := h.deltaEps
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨W, hW, -, hWR, hQW⟩ := h.comp_U_two_subset_R2
  have hD : W ⊓ σ.Ps r 2 = ⊥ := by
    by_contra hne
    have h1 : σ.Ps r 2 ⊓ Subgroup.centralizer (Δ.Qs 1 : Set G) ≠ ⊥ := by
      intro hb
      apply hne
      rw [eq_bot_iff, ← hb]
      intro g hg
      refine ⟨hg.2, ?_⟩
      have hgU : g ∈ pCoreIn r (U ⊔ σ.C) := by
        apply h.comp_U_subset_Ustar 2
        rw [← hW]
        exact hg.1
      show g ∈ Subgroup.centralizer (Δ.Qs 1 : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (Subgroup.mem_centralizer_iff.mp (h.Qs1_le_centralizer_Ustar hq) g hgU).symm
    have h2 : σ.Ps r 0 ⊓ Subgroup.centralizer (Δ.Qs 2 : Set G) ≠ ⊥ := by
      have h1' : conjSub (Δ.a ^ ((1 : Fin 3) : ℕ))
          (σ.Ps r 2 ⊓ Subgroup.centralizer (Δ.Qs 1 : Set G)) ≠ ⊥ := by
        rwa [Ne, conjSub_eq_bot_iff]
      rwa [conjSub_inf_centralizer, conjSub_a_pow_Ps, conjSub_a_pow_Qs] at h1'
    set R' : Subgroup G := σ.Ps r 0 ⊓ Subgroup.centralizer (Δ.Qs 2 : Set G) with hR'
    set H' : Subgroup G := Subgroup.normalizer (R' : Set G) with hH'
    have hR'P : R' ≤ σ.Ps r 0 := inf_le_left
    have hcentH : Subgroup.centralizer (R' : Set G) ≤ H' := centralizer_le_normalizer R'
    have hCH : σ.C ≤ H' := fun c hc => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨C_le_normalizer_Ps r 0 hc,
        normalizer_le_normalizer_centralizer _ (C_le_normalizer_Qs Δ 2 hc)⟩
    have hJH : Δ.J ≤ H' := fun j hj =>
      hcentH (Subgroup.centralizer_le hR'P (J_le_centralizer_Ps Δ hj))
    have hR'O : R' ≤ oddCoreIn H' := le_oddCoreIn Subgroup.le_normalizer le_rfl
      (odd_card_of_isPGroup Δ.prime Δ.ne_two ((isPGroup_Ps 0).to_le hR'P))
    have hO : oddCoreIn H' ≠ ⊥ := fun hb => h2 (eq_bot_iff.mpr (hb ▸ hR'O))
    have hQ2H : Δ.Q 2 ≤ H' := fun u hu =>
      hcentH (Subgroup.centralizer_le hR'P (h.Q2_le_centralizer_Ps0 hu))
    have hQs2H : Δ.Qs 2 ≤ H' := by
      refine (Subgroup.le_centralizer_iff.mp ?_).trans hcentH
      exact inf_le_right
    have hQ2O : Δ.Q 2 ≤ oddCoreIn H' := fun u hu =>
      mem_oddCoreIn_of_inverted_of_J_le hσ h.facts Δ hCH hO hJH (hQ2H hu)
        (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two (Δ.Q_pgroup 2).1) hu)
        (R_inverted Δ hσ (i := 2) (j := 0) (by decide) (Q_le_R Δ 2 hu))
    have hQs2O : Δ.Qs 2 ≤ oddCoreIn H' := fun u hu =>
      mem_oddCoreIn_of_inverted_of_J_le hσ h.facts Δ hCH hO hJH (hQs2H hu)
        (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two (Δ.Q_pgroup 2).2) hu)
        (Rs_inverted Δ hσ (i := 2) (j := 0) (by decide) (Qs_le_Rs Δ 2 hu))
    exact not_Q_sup_Qs_le hσ Δ hδq 2 (odd_card_oddCoreIn _) (sup_le hQ2O hQs2O)
  have hWeq : W = Δ.Q 2 := by
    have hD' := inf_sup_eq_of_le_left (A := Δ.Q 2) (B := σ.Ps r 2) (M := W)
      ((Q_le_Ns Δ hσ 2).trans (le_normalizer_pCoreIn r _)) hQW
    have hWR' : W ≤ Δ.Q 2 ⊔ σ.Ps r 2 := hWR
    rw [hD, sup_bot_eq, inf_eq_left.mpr hWR'] at hD'
    exact hD'
  rw [← hW, hWeq]

theorem comp_V_two : comp σ V 2 = (Δ.Q 2 : Set G) :=
  Set.Subset.antisymm (fun _ hu => h.comp_U_two ▸ comp_mono h.V_le_U 2 hu) h.Q2_subset_comp

theorem Y_inf_Ns_eq (i : Fin 3) (hi : i ≠ 0) :
    ((V ⊓ oddCoreIn (Kp σ r) ⊓ σ.Ns i : Subgroup G) : Set G) = comp σ V i := by
  rw [coe_inf_Ns_eq h.valid h.odd_Y h.Y_T, h.Y_inf_C, Subgroup.coe_bot, Set.singleton_one,
    one_mul]
  ext u
  rw [mem_comp_inf]
  constructor
  · exact fun hu => hu.1
  · intro hu
    refine ⟨hu, ?_⟩
    match i, hi with
    | 1, _ => exact comp_one_subset_oddCore h.valid h.facts Δ h.maxV hu
    | 2, _ => exact comp_two_subset_oddCore h.valid h.facts Δ h.maxV hu

theorem comp_V_one : comp σ V 1 = (Δ.Qs 1 : Set G) := by
  have hσ := h.valid
  have hδq := h.deltaEps
  obtain ⟨W₁, hW₁, -, -⟩ := h.V_omni.part_i_b 1
  have hY1 : V ⊓ oddCoreIn (Kp σ r) ⊓ σ.Ns 1 = W₁ := by
    apply SetLike.coe_injective
    rw [h.Y_inf_Ns_eq 1 (by decide), hW₁]
  have hY2 : V ⊓ oddCoreIn (Kp σ r) ⊓ σ.Ns 2 = Δ.Q 2 := by
    apply SetLike.coe_injective
    rw [h.Y_inf_Ns_eq 2 (by decide), h.comp_V_two]
  have hz12 : conjSub z (σ.Ns 1) = σ.Ns 2 := by
    rw [Setting.Ns, conjSub_centralizer_singleton]
    change Subgroup.centralizer {z * σ.x₂ * z⁻¹} = _
    rw [h.swap.conj_x₂ hδq hσ]
    rfl
  have hcard : Nat.card W₁ = Nat.card (Δ.Q 2) := by
    rw [← hY1, ← hY2, ← card_conjSub z, conjSub_inf, h.conjSub_z_Y, hz12]
  have hQsW : Δ.Qs 1 ≤ W₁ := fun u hu => by
    rw [← SetLike.mem_coe, hW₁]
    exact h.Qs1_subset hu
  have heq : Δ.Qs 1 = W₁ := Subgroup.eq_of_le_of_card_ge hQsW
    (by rw [hcard, card_Q Δ hδq, card_Qs Δ hδq])
  rw [← hW₁, ← heq]

end CoreHyp

end CFSG.ABGTheoremB.TotallyInverted.Sec11
