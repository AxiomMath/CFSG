module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalCore3

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

namespace CoreHyp

variable {Δ : Data σ r} {V U : Subgroup G} {z : G} (h : CoreHyp Δ V U z)
include h

theorem mem_Ps_of_mem_sup_of_comm {g : G} (hg : g ∈ Δ.Qs 1 ⊔ σ.Ps r 0)
    (hx : σ.x * g = g * σ.x) : g ∈ σ.Ps r 0 := by
  obtain ⟨q, hq, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer h.Qs1_le_normalizer_Ps).mp hg
  have hqinv : σ.x * q * σ.x⁻¹ = q⁻¹ :=
    Rs_inverted Δ h.valid (i := 1) (j := 0) (by decide) (Qs_le_Rs Δ 1 hq)
  have hpc : σ.x * p * σ.x⁻¹ = p := by
    have e : p * σ.x = σ.x * p := Subgroup.mem_centralizer_singleton_iff.mp (Δ.P_centralized 0 hp)
    rw [← e, mul_inv_cancel_right]
  have hconj : σ.x * (q * p) * σ.x⁻¹ = q * p := by rw [hx, mul_inv_cancel_right]
  have hq1 : q = 1 := by
    have e : σ.x * (q * p) * σ.x⁻¹ = q⁻¹ * p := by
      calc σ.x * (q * p) * σ.x⁻¹ = (σ.x * q * σ.x⁻¹) * (σ.x * p * σ.x⁻¹) := by group
        _ = q⁻¹ * p := by rw [hqinv, hpc]
    rw [hconj] at e
    have hqq : q = q⁻¹ := mul_right_cancel e
    exact eq_one_of_conj_eq_inv_of_commute
      (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two (Δ.Q_pgroup 1).2) hq)
      (t := 1) (by rw [one_mul, inv_one, mul_one]; exact hqq) (by rw [one_mul, mul_one])
  rw [hq1, one_mul]
  exact hp

theorem Ps0_le_centralizer_Ustar :
    σ.Ps r 0 ≤ Subgroup.centralizer (pCoreIn r (U ⊔ σ.C) : Set G) := by
  have hσ := h.valid
  have : Fact r.Prime := ⟨Δ.prime⟩
  set Us := pCoreIn r (U ⊔ σ.C) with hUs
  set Vs := pCoreIn r (V ⊔ σ.C) with hVs
  set Z₀ : Subgroup G := Δ.Qs 1 ⊔ σ.Ps r 0 with hZ₀
  set 𝓕 : Set (Subgroup G) := {F | σ.T ≤ Subgroup.normalizer (F : Set G) ∧ Vs ≤ F ∧ F ≤ Us ∧
    Z₀ ≤ Subgroup.centralizer (F : Set G)} with h𝓕
  have hV𝓕 : Vs ∈ 𝓕 :=
    ⟨h.T_le_normalizer_Vstar, le_rfl, h.Vstar_le_Ustar, h.le_Zv.trans inf_le_right⟩
  obtain ⟨F, hF, hVF⟩ := exists_le_mem_maximals hV𝓕
  obtain ⟨hTF, hVsF, hFU, hZF⟩ := hF.1
  have hUsp : IsPGroup r Us := isPGroup_pCoreIn r _
  have hTN : σ.T ≤ Subgroup.normalizer
      ((Subgroup.normalizer (F : Set G) : Subgroup G) : Set G) := fun t ht => by
    rw [← conjSub_eq_self_iff, ← normalizer_conjSub, conjSub_eq_self_iff.mpr (hTF ht)]
  set ZF : Subgroup G := F ⊓ Subgroup.centralizer (F : Set G) with hZFdef
  have hTZF : σ.T ≤ Subgroup.normalizer (ZF : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hTF ht, normalizer_le_normalizer_centralizer F (hTF ht)⟩
  have hZFodd : Odd (Nat.card ZF) :=
    (odd_card_pCoreIn Δ (U ⊔ σ.C)).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_left.trans hFU))
  have hZFC : ZF ⊓ σ.C = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right _ (inf_le_left.trans hFU)).trans
    h.Ustar_inf_C.le)
  have hZFU : ZF ≤ U := inf_le_left.trans (hFU.trans h.Ustar_le_U)
  have hZFZv : ∀ {w : G}, w ∈ ZF → w ∈ Vs → w ∈ Z₀ := by
    intro w hw hwV
    rw [hZ₀, ← h.Zv_eq]
    exact ⟨hwV, Subgroup.centralizer_le hVsF hw.2⟩
  have hkey : ∀ w ∈ ZF, σ.x₂ * w * σ.x₂⁻¹ = w⁻¹ → w ∈ σ.Ps r 0 := by
    intro w hw hinv
    obtain ⟨w₀, h₀, w₁, h₁, w₂, h₂, w₃, h₃, rfl⟩ := exists_mul_comp hσ hZFodd hTZF hw
    have hw₀ : w₀ = 1 := by
      have := hZFC.le h₀
      exact this
    have hw₁R : w₁ ∈ R Δ 0 := by
      have := comp_mono hZFU 0 h₁
      rw [h.comp_U_zero] at this
      exact this
    have hw₁P : w₁ ∈ σ.Ps r 0 := by
      apply h.mem_Ps_of_mem_sup_of_comm
      · exact hZFZv h₁.1 (h.comp_V_subset_Vstar 0 (by rw [h.comp_V_zero]; exact hw₁R))
      · exact h₁.2.1
    have hw₃ : w₃ = 1 := by
      have hw₃Q : w₃ ∈ Δ.Q 2 := by
        have := comp_mono hZFU 2 h₃
        rw [h.comp_U_two] at this
        exact this
      have hw₃Z : w₃ ∈ Z₀ := hZFZv h₃.1 (h.comp_V_subset_Vstar 2
        (by rw [h.comp_V_two]; exact hw₃Q))
      have := h.Qs1_sup_Ps_inf_Q2.le ⟨hw₃Z, hw₃Q⟩
      exact this
    have hw₂R : w₂ ∈ Rs Δ 1 := by
      have := comp_mono hZFU 1 h₂
      rw [h.comp_U_one] at this
      exact this
    have hcomm : w₁ * w₂ = w₂ * w₁ :=
      (Subgroup.mem_centralizer_iff.mp h₂.1.2 w₁ h₁.1.1)
    have hx₂w₁ : σ.x₂ * w₁ * σ.x₂⁻¹ = w₁⁻¹ := Δ.P_inverted 0 1 (by decide) w₁ hw₁P
    have hx₂w₂ : σ.x₂ * w₂ * σ.x₂⁻¹ = w₂ := by
      have e : σ.x₂ * w₂ = w₂ * σ.x₂ := Rs_centralized Δ hσ 1 hw₂R
      rw [e, mul_inv_cancel_right]
    rw [hw₀, hw₃, one_mul, mul_one] at hinv ⊢
    have e1 : σ.x₂ * (w₁ * w₂) * σ.x₂⁻¹ = w₁⁻¹ * w₂ := by
      calc σ.x₂ * (w₁ * w₂) * σ.x₂⁻¹ = (σ.x₂ * w₁ * σ.x₂⁻¹) * (σ.x₂ * w₂ * σ.x₂⁻¹) := by group
        _ = w₁⁻¹ * w₂ := by rw [hx₂w₁, hx₂w₂]
    rw [e1, mul_inv_rev] at hinv
    have hc' : w₂⁻¹ * w₁⁻¹ = w₁⁻¹ * w₂⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hcomm]
    have hw₂2 : w₂ = w₂⁻¹ := mul_left_cancel (hinv.trans hc')
    have hw₂1 : w₂ = 1 := eq_one_of_conj_eq_inv_of_commute
      (odd_orderOf_of_mem (odd_card_Rs Δ hσ 1) hw₂R) (t := 1)
      (by rw [one_mul, inv_one, mul_one]; exact hw₂2) (by rw [one_mul, mul_one])
    rw [hw₂1, mul_one]
    exact hw₁P
  by_contra hcon
  have hFne : F ≠ Us := by
    intro hFeq
    apply hcon
    rw [← hFeq]
    exact (le_sup_right : σ.Ps r 0 ≤ Z₀).trans hZF
  have hFlt : F < Us := lt_of_le_of_ne hFU hFne
  set Y₃ : Subgroup G := Us ⊓ Subgroup.normalizer (F : Set G) with hY₃
  have hFY : F < Y₃ := lt_inf_normalizer hUsp hFlt
  have hY₃U : Y₃ ≤ U := inf_le_left.trans h.Ustar_le_U
  have hTY : σ.T ≤ Subgroup.normalizer (Y₃ : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨h.T_le_normalizer_Ustar ht, hTN ht⟩
  have hY₃odd : Odd (Nat.card Y₃) := (odd_card_pCoreIn Δ (U ⊔ σ.C)).of_dvd_nat
    (Subgroup.card_dvd_of_le inf_le_left)
  have hY₃C : Y₃ ⊓ σ.C ≤ F ⊔ (Y₃ ⊓ σ.Ps r 1) := by
    rw [eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_left).trans h.Ustar_inf_C.le)]
    exact bot_le
  have hY₃le : Y₃ ≤ F ⊔ (Y₃ ⊓ σ.Ps r 1) := by
    refine le_of_comp_subset hσ hY₃odd hTY hY₃C ?_
    intro i
    match i with
    | 0 =>
      intro u hu
      have : u ∈ comp σ U 0 := comp_mono hY₃U 0 hu
      rw [h.comp_U_zero] at this
      exact (le_sup_left : F ≤ F ⊔ (Y₃ ⊓ σ.Ps r 1))
        (hVsF (h.comp_V_subset_Vstar 0 (by rw [h.comp_V_zero]; exact this)))
    | 1 =>
      intro u hu
      have huR : u ∈ comp σ U 1 := comp_mono hY₃U 1 hu
      rw [h.comp_U_one] at huR
      obtain ⟨q, hq, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer
        ((Qs_le_Ns Δ hσ 1).trans (le_normalizer_pCoreIn r _))).mp huR
      have hqF : q ∈ F := hVsF (h.comp_V_subset_Vstar 1 (by rw [h.comp_V_one]; exact hq))
      have hpY : p ∈ Y₃ := by
        have := Y₃.mul_mem (Y₃.inv_mem (hFY.le hqF)) hu.1
        rwa [inv_mul_cancel_left] at this
      exact Subgroup.mul_mem_sup hqF ⟨hpY, hp⟩
    | 2 =>
      intro u hu
      have : u ∈ comp σ U 2 := comp_mono hY₃U 2 hu
      rw [h.comp_U_two] at this
      exact (le_sup_left : F ≤ F ⊔ (Y₃ ⊓ σ.Ps r 1))
        (hVsF (h.comp_V_subset_Vstar 2 (by rw [h.comp_V_two]; exact this)))
  have hcent : F ⊔ (Y₃ ⊓ σ.Ps r 1) ≤ Subgroup.centralizer (Z₀ : Set G) := by
    refine sup_le (Subgroup.le_centralizer_iff.mp hZF) ?_
    rintro u ⟨huY, huP⟩
    have huN : u ∈ Subgroup.normalizer (σ.Ps r 0 : Set G) := by
      apply mem_normalizer_of_conj_mem
      intro p hp
      have hpZF : p ∈ ZF := ⟨hVsF (h.comp_V_subset_Vstar 0 (by
        rw [h.comp_V_zero]; exact Ps_le_R Δ 0 hp)),
        hZF ((le_sup_right : σ.Ps r 0 ≤ Z₀) hp)⟩
      have huZF : u ∈ Subgroup.normalizer (ZF : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨huY.2, normalizer_le_normalizer_centralizer F huY.2⟩
      apply hkey
      · exact (Subgroup.mem_normalizer_iff.mp huZF p).mp hpZF
      · have hux : σ.x₂ * u = u * σ.x₂ :=
          (Subgroup.mem_centralizer_singleton_iff.mp (Ps_le_Ns 1 huP)).symm
        have hpx : σ.x₂ * p * σ.x₂⁻¹ = p⁻¹ := Δ.P_inverted 0 1 (by decide) p hp
        have hux' : σ.x₂ * u * σ.x₂⁻¹ = u := by rw [hux, mul_inv_cancel_right]
        calc σ.x₂ * (u * p * u⁻¹) * σ.x₂⁻¹ =
              (σ.x₂ * u * σ.x₂⁻¹) * (σ.x₂ * p * σ.x₂⁻¹) * (σ.x₂ * u * σ.x₂⁻¹)⁻¹ := by group
          _ = (u * p * u⁻¹)⁻¹ := by rw [hux', hpx]; group
    refine mem_centralizer_sup ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (Subgroup.mem_centralizer_iff.mp (Qs_le_centralizer_Ps Δ h.deltaEps 1 hq) u huP).symm
    · exact mem_centralizer_of_inverted
        (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two (isPGroup_Ps 1)) huP)
        (Δ.P_inverted 1 0 (by decide) u huP)
        (fun a ha => (Subgroup.mem_centralizer_singleton_iff.mp (Δ.P_centralized 0 ha)).symm)
        huN
  have hY𝓕 : Y₃ ∈ 𝓕 := ⟨hTY, hVsF.trans hFY.le, inf_le_left,
    Subgroup.le_centralizer_iff.mpr (hY₃le.trans hcent)⟩
  exact hFY.ne (hF.2 Y₃ hY𝓕 hFY.le).symm

theorem false : False := by
  apply h.not_pGroupR
  apply pGroupR_of_centralizer_Ps0_Rs1 h.valid h.facts Δ h.omni
  have hle : σ.Ps r 0 ≤ σ.Ps r 0 ⊓ Subgroup.centralizer (Rs Δ 1 : Set G) :=
    le_inf le_rfl (h.Ps0_le_centralizer_Ustar.trans (Subgroup.centralizer_le h.Rs1_le_Ustar))
  intro hb
  exact Ps_zero_ne_bot Δ (eq_bot_iff.mpr (hb ▸ hle))

end CoreHyp

theorem core (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r) (homni : Omnibus Δ)
    (hI : Inputs Δ) (h91 : ConjugateMaximalTC σ r) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q)
    {V : Subgroup G} (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r))
    (hRV : R Δ 0 ≤ V)
    (hX : (Δ.Qs 1 : Set G) = comp σ V 1 ∩ Subgroup.centralizer (R Δ 0 : Set G))
    (hRRs : IsPGroup r (R Δ 0 ⊔ Rs Δ 1 : Subgroup G)) : PGroupR Δ := by
  by_contra hnot
  obtain ⟨z, hz⟩ := exists_isSwap Δ hδq
  have hVmem : V ∈ signalizersPerm ⊤ σ.T σ.C r := ⟨⟨le_top, hV.1.1.2⟩, hV.1.2⟩
  obtain ⟨U, hU, hVU⟩ := exists_le_mem_maximals hVmem
  exact (CoreHyp.mk hσ hF homni hI h91 hδq hV hRV hX hRRs hnot hU hVU hz).false

end CFSG.ABGTheoremB.TotallyInverted.Sec11
