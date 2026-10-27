module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.ConjugacyBasic

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

namespace Conjugacy

theorem conj_of_inf_ne_bot (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ) :
    ∀ V₁ ∈ maximals (signalizers ⊤ σ.C r), ∀ V₂ ∈ maximals (signalizers ⊤ σ.C r),
      V₁ ⊓ V₂ ≠ ⊥ → ∃ m ∈ σ.M, conjSub m V₁ = V₂ := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  suffices h : ∀ n : ℕ, ∀ V₁ ∈ maximals (signalizers ⊤ σ.C r),
      ∀ V₂ ∈ maximals (signalizers ⊤ σ.C r),
        Nat.card G - Nat.card (V₁ ⊓ V₂ : Subgroup G) = n → V₁ ⊓ V₂ ≠ ⊥ →
          ∃ m ∈ σ.M, conjSub m V₁ = V₂ from
    fun V₁ hV₁ V₂ hV₂ hne => h _ V₁ hV₁ V₂ hV₂ rfl hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V₁ hV₁ V₂ hV₂ hn hne
  by_cases h12 : V₁ ≤ V₂
  · exact ⟨1, σ.M.one_mem, by rw [conjSub_one]; exact (hV₁.2 V₂ hV₂.1 h12).symm⟩
  by_cases h21 : V₂ ≤ V₁
  · exact ⟨1, σ.M.one_mem, by rw [conjSub_one]; exact hV₂.2 V₁ hV₁.1 h21⟩
  set Y := V₁ ⊓ V₂ with hY
  have hY₁ : Y < V₁ := lt_of_le_of_ne inf_le_left fun h => h12 (h ▸ inf_le_right)
  have hY₂ : Y < V₂ := lt_of_le_of_ne inf_le_right fun h => h21 (h ▸ inf_le_left)
  set H := Subgroup.normalizer (Y : Set G) with hH
  have hYodd : Odd (Nat.card Y) :=
    odd_card_of_isPGroup Δ.prime Δ.ne_two (hV₁.1.2.1.to_le inf_le_left)
  have hYO : Y ≤ oddCoreIn H := le_oddCoreIn Subgroup.le_normalizer le_rfl hYodd
  have hOH : oddCoreIn H ≠ ⊥ := fun h => hne (eq_bot_iff.mpr (h ▸ hYO))
  have hCH : σ.C ≤ H := fun c hc => mem_normalizer_inf (hV₁.1.2.2.1 hc) (hV₂.1.2.2.1 hc)
  have hsig : ∀ V ∈ maximals (signalizers ⊤ σ.C r), V ⊓ H ∈ signalizers H σ.C r :=
    fun V hV => ⟨inf_le_right, hV.1.2.1.to_le inf_le_left,
      fun c hc => mem_normalizer_inf (hV.1.2.2.1 hc) (Subgroup.le_normalizer (hCH hc)),
      eq_bot_iff.mpr ((inf_le_inf_right σ.C inf_le_left).trans hV.1.2.2.2.le)⟩
  have hlt₁ : Y < V₁ ⊓ H := lt_inf_normalizer hV₁.1.2.1 hY₁
  have hlt₂ : Y < V₂ ⊓ H := lt_inf_normalizer hV₂.1.2.1 hY₂
  obtain ⟨X₁, hX₁, hVX₁⟩ := exists_le_mem_maximals
    (mem_signalizersPerm_of_mem_signalizers (σ.T_le_C hσ) (hsig V₁ hV₁))
  obtain ⟨X₂, hX₂, hVX₂⟩ := exists_le_mem_maximals
    (mem_signalizersPerm_of_mem_signalizers (σ.T_le_C hσ) (hsig V₂ hV₂))
  have hA := homni H hCH X₁ hX₁
  obtain ⟨m, hm, hmX⟩ := hA.part_iv hOH X₂ hX₂
  obtain ⟨hY₁max, hY₁all⟩ := hA.part_vi
  have hmM : m ∈ σ.M := hm.1
  have hmH : conjSub m H = H := conjSub_eq_self_of_mem hm.2
  have hW₁ : V₁ ⊓ H ≤ pCoreIn r (X₁ ⊔ σ.C) := hY₁all _ (hsig V₁ hV₁) hVX₁
  have hW₂ : conjSub m (V₂ ⊓ H) ≤ pCoreIn r (X₁ ⊔ σ.C) :=
    hY₁all _ (conjSub_mem_signalizers hmH hmM (hsig V₂ hV₂)) ((conjSub_mono hVX₂).trans hmX.le)
  obtain ⟨R₁, hR₁, hYR₁⟩ := exists_le_mem_maximals (signalizers_mono le_top hY₁max.1)
  obtain ⟨R₂, hR₂, hVR₂⟩ := exists_le_mem_maximals (signalizers_mono le_top (hsig V₂ hV₂))
  have hR₂' : conjSub m R₂ ∈ maximals (signalizers ⊤ σ.C r) :=
    conjSub_mem_maximals_signalizers (conjSub_top m) hmM hR₂
  have key : ∀ A ∈ maximals (signalizers ⊤ σ.C r), ∀ B ∈ maximals (signalizers ⊤ σ.C r),
      ∀ W : Subgroup G, W ≤ A ⊓ B → Nat.card Y < Nat.card W →
        ∃ m ∈ σ.M, conjSub m A = B := by
    intro A hA B hB W hW hcard
    have hcard' : Nat.card Y < Nat.card (A ⊓ B : Subgroup G) :=
      lt_of_lt_of_le hcard (Subgroup.card_le_of_le hW)
    have hle : Nat.card (A ⊓ B : Subgroup G) ≤ Nat.card G := Subgroup.card_le_card_group _
    refine ih (Nat.card G - Nat.card (A ⊓ B : Subgroup G)) (by omega) A hA B hB rfl ?_
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard'
    have : 0 < Nat.card Y := Nat.card_pos
    omega
  obtain ⟨m₁, hm₁, h₁⟩ :=
    key V₁ hV₁ R₁ hR₁ (V₁ ⊓ H) (le_inf inf_le_left (hW₁.trans hYR₁)) (Subgroup.card_lt_of_lt hlt₁)
  obtain ⟨m₂, hm₂, h₂⟩ := key R₁ hR₁ (conjSub m R₂) hR₂' (conjSub m (V₂ ⊓ H))
    (le_inf (hW₂.trans hYR₁) (conjSub_mono hVR₂))
    (by rw [card_conjSub]; exact Subgroup.card_lt_of_lt hlt₂)
  obtain ⟨m₃, hm₃, h₃⟩ :=
    key R₂ hR₂ V₂ hV₂ (V₂ ⊓ H) (le_inf hVR₂ inf_le_left) (Subgroup.card_lt_of_lt hlt₂)
  refine ⟨m₃ * m⁻¹ * m₂ * m₁,
    σ.M.mul_mem (σ.M.mul_mem (σ.M.mul_mem hm₃ (σ.M.inv_mem hmM)) hm₂) hm₁, ?_⟩
  rw [← conjSub_conjSub, ← conjSub_conjSub, ← conjSub_conjSub, h₁, h₂, conjSub_inv_conjSub, h₃]

theorem conj_of_inf_N_le (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ)
    {V₁ V₂ R : Subgroup G} (hV₁ : V₁ ∈ maximals (signalizers ⊤ σ.C r))
    (hV₂ : V₂ ∈ maximals (signalizers ⊤ σ.C r)) (h₁ : V₁ ⊓ σ.Ns 0 ≠ ⊥)
    (h₂ : V₂ ⊓ σ.Ns 0 ≠ ⊥) (hR : R ∈ signalizers (σ.Ns 0) σ.C r) (hR₁ : V₁ ⊓ σ.Ns 0 ≤ R)
    (hR₂ : V₂ ⊓ σ.Ns 0 ≤ R) : ∃ m ∈ σ.M, conjSub m V₁ = V₂ := by
  have hCN : ∀ V ∈ maximals (signalizers ⊤ σ.C r),
      σ.C ≤ Subgroup.normalizer ((V ⊓ σ.Ns 0 : Subgroup G) : Set G) := fun V hV c hc =>
    mem_normalizer_inf (hV.1.2.2.1 hc) (Subgroup.le_normalizer (C_le_Ns 0 hc))
  have hWR : (V₁ ⊓ σ.Ns 0) ⊔ (V₂ ⊓ σ.Ns 0) ≤ R := sup_le hR₁ hR₂
  have hW : (V₁ ⊓ σ.Ns 0) ⊔ (V₂ ⊓ σ.Ns 0) ∈ signalizers ⊤ σ.C r :=
    ⟨le_top, hR.2.1.to_le hWR, fun c hc => mem_normalizer_sup (hCN V₁ hV₁ hc) (hCN V₂ hV₂ hc),
      eq_bot_iff.mpr ((inf_le_inf_right _ hWR).trans hR.2.2.2.le)⟩
  obtain ⟨V, hV, hWV⟩ := exists_le_mem_maximals hW
  obtain ⟨m₁, hm₁, e₁⟩ := conj_of_inf_ne_bot hσ Δ homni V₁ hV₁ V hV
    (ne_bot_of_le_ne_bot h₁ (le_inf inf_le_left (le_sup_left.trans hWV)))
  obtain ⟨m₂, hm₂, e₂⟩ := conj_of_inf_ne_bot hσ Δ homni V₂ hV₂ V hV
    (ne_bot_of_le_ne_bot h₂ (le_inf inf_le_left (le_sup_right.trans hWV)))
  refine ⟨m₂⁻¹ * m₁, σ.M.mul_mem (σ.M.inv_mem hm₂) hm₁, ?_⟩
  rw [← conjSub_conjSub, e₁, ← e₂, conjSub_inv_conjSub]

theorem conj_of_inf_N_ne_bot (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ)
    {V₁ V₂ : Subgroup G} (hV₁ : V₁ ∈ maximals (signalizers ⊤ σ.C r))
    (hV₂ : V₂ ∈ maximals (signalizers ⊤ σ.C r)) (h₁ : V₁ ⊓ σ.Ns 0 ≠ ⊥)
    (h₂ : V₂ ⊓ σ.Ns 0 ≠ ⊥) : ∃ m ∈ σ.M, conjSub m V₁ = V₂ := by
  have hsig : ∀ V ∈ maximals (signalizers ⊤ σ.C r), V ⊓ σ.Ns 0 ∈ signalizers (σ.Ns 0) σ.C r :=
    fun V hV => ⟨inf_le_right, hV.1.2.1.to_le inf_le_left,
      fun c hc => mem_normalizer_inf (hV.1.2.2.1 hc) (Subgroup.le_normalizer (C_le_Ns 0 hc)),
      eq_bot_iff.mpr ((inf_le_inf_right σ.C inf_le_left).trans hV.1.2.2.2.le)⟩
  obtain ⟨R₁, hR₁, hVR₁⟩ := exists_le_mem_maximals (hsig V₁ hV₁)
  obtain ⟨R₂, hR₂, hVR₂⟩ := exists_le_mem_maximals (hsig V₂ hV₂)
  have hR₁s := hR₁.1
  have hR₂s := hR₂.1
  have h71 := Δ.lemma71 0
  by_cases hq : σ.DeltaEpsMinus ∧ r ∣ σ.q
  · rw [ite_eq_left hq] at h71
    rw [h71] at hR₁ hR₂
    obtain ⟨-, -, -, -, ⟨z, hz, hzQ⟩, -⟩ := Δ.Q_cases hq 0
    have hzD : z ∈ σ.D := by simpa [conjSub_one] using hz
    have hzM : z ∈ σ.M := D_le_M hzD
    have hzN : z ∈ σ.Ns 0 := σ.D_le_N hσ hzD
    have hzP : conjSub z (σ.Ps r 0 ⊔ Δ.Q 0) = σ.Ps r 0 ⊔ Δ.Qs 0 := by
      rw [conjSub_sup, hzQ, conjSub_Ps_of_mem hzN]
    have hzV : ∀ V : Subgroup G, conjSub z V ⊓ σ.Ns 0 = conjSub z (V ⊓ σ.Ns 0) := fun V => by
      rw [conjSub_inf, conjSub_eq_self_of_mem hzN]
    rcases hR₁ with rfl | rfl <;> rcases hR₂ with rfl | rfl
    · exact conj_of_inf_N_le hσ Δ homni hV₁ hV₂ h₁ h₂ hR₁s hVR₁ hVR₂
    · obtain ⟨m, hm, e⟩ := conj_of_inf_N_le hσ Δ homni
        (conjSub_mem_maximals_signalizers (conjSub_top z) hzM hV₁) hV₂
        (by rw [hzV]; exact conjSub_eq_bot_iff.not.mpr h₁) h₂ hR₂s
        (by rw [hzV, ← hzP]; exact conjSub_mono hVR₁) hVR₂
      exact ⟨m * z, σ.M.mul_mem hm hzM, by rw [← conjSub_conjSub, e]⟩
    · obtain ⟨m, hm, e⟩ := conj_of_inf_N_le hσ Δ homni hV₁
        (conjSub_mem_maximals_signalizers (conjSub_top z) hzM hV₂) h₁
        (by rw [hzV]; exact conjSub_eq_bot_iff.not.mpr h₂) hR₁s hVR₁
        (by rw [hzV, ← hzP]; exact conjSub_mono hVR₂)
      exact ⟨z⁻¹ * m, σ.M.mul_mem (σ.M.inv_mem hzM) hm,
        by rw [← conjSub_conjSub, e, conjSub_inv_conjSub]⟩
    · exact conj_of_inf_N_le hσ Δ homni hV₁ hV₂ h₁ h₂ hR₁s hVR₁ hVR₂
  · rw [ite_eq_right hq] at h71
    rw [h71, Set.mem_singleton_iff] at hR₁ hR₂
    subst hR₁ hR₂
    exact conj_of_inf_N_le hσ Δ homni hV₁ hV₂ h₁ h₂ hR₁s hVR₁ hVR₂

theorem exists_conj_inf_N_ne_bot (hσ : σ.IsValid) (Δ : Data σ r) {V : Subgroup G}
    (hV : V ∈ maximals (signalizers ⊤ σ.C r)) (hV1 : V ≠ ⊥) :
    ∃ m ∈ σ.M, conjSub m V ⊓ σ.Ns 0 ≠ ⊥ := by
  obtain ⟨j, hj⟩ := exists_inf_Ns_ne_bot hσ (odd_card_of_isPGroup Δ.prime Δ.ne_two hV.1.2.1)
    ((σ.T_le_C hσ).trans hV.1.2.2.1) hV1
  have step : ∀ (m : G) (i : Fin 3), conjSub m V ⊓ σ.Ns i ≠ ⊥ →
      conjSub (Δ.a * m) V ⊓ σ.Ns (i + 1) ≠ ⊥ := by
    intro m i h
    rw [← conjSub_conjSub, ← conjSub_a_Ns Δ i, ← conjSub_inf]
    exact conjSub_eq_bot_iff.not.mpr h
  have h0 : conjSub 1 V ⊓ σ.Ns j ≠ ⊥ := by rwa [conjSub_one]
  have ha := Δ.a_mem
  have hcases : j = 0 ∨ j + 1 = 0 ∨ j + 1 + 1 = 0 := by
    fin_cases j <;> decide
  rcases hcases with hj0 | hj1 | hj2
  · rw [hj0] at h0
    exact ⟨1, σ.M.one_mem, h0⟩
  · have h := step 1 j h0
    rw [hj1] at h
    exact ⟨Δ.a * 1, σ.M.mul_mem ha σ.M.one_mem, h⟩
  · have h := step _ _ (step 1 j h0)
    rw [hj2] at h
    exact ⟨Δ.a * (Δ.a * 1), σ.M.mul_mem ha (σ.M.mul_mem ha σ.M.one_mem), h⟩

theorem decomp_of_mem_maximals (Δ : Data σ r) (homni : Omnibus Δ) {U : Subgroup G}
    (hU : U ∈ maximals (signalizersPerm ⊤ σ.T σ.C r)) :
    pCoreIn r (U ⊔ σ.C) ∈ maximals (signalizers ⊤ σ.C r) ∧
      U = pCoreIn r (U ⊔ σ.C) ⊔ (U ⊓ σ.C) ∧ IsSylowOf r (U ⊓ σ.C) σ.C := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  have hA := homni ⊤ le_top U hU
  have hVmax := hA.part_vi.1
  have hV1 : pCoreIn r (U ⊔ σ.C) ≠ ⊥ := by
    intro h
    apply Ps_ne_bot Δ
    exact (hVmax.2 _ (Ps_mem_signalizers Δ 0) (by rw [h]; exact bot_le)).trans h
  have hUCH : U ⊔ σ.C ≤ Subgroup.normalizer (pCoreIn r (U ⊔ σ.C) : Set G) :=
    le_normalizer_pCoreIn r _
  have hCH := le_sup_right.trans hUCH
  have hUH' : U ∈ maximals (signalizersPerm (Subgroup.normalizer (pCoreIn r (U ⊔ σ.C) : Set G))
      σ.T σ.C r) :=
    mem_maximals_of_subset (signalizersPerm_mono le_top) hU
      ⟨⟨le_sup_left.trans hUCH, hU.1.1.2⟩, hU.1.2⟩
  have hOH : oddCoreIn (Subgroup.normalizer (pCoreIn r (U ⊔ σ.C) : Set G)) ≠ ⊥ := by
    intro h
    apply hV1
    have hVO := le_oddCoreIn Subgroup.le_normalizer le_rfl
      (odd_card_of_isPGroup Δ.prime Δ.ne_two (isPGroup_pCoreIn r (U ⊔ σ.C)))
    exact eq_bot_iff.mpr (h ▸ hVO)
  refine ⟨hVmax, (homni _ hCH U hUH').part_iii_a hOH, ?_⟩
  obtain ⟨R₀, hR₀, hR₀U⟩ := hA.part_ii_a
  rw [hR₀.eq_of_le (le_inf hR₀U hR₀.le) inf_le_right (hU.1.1.2.1.to_le inf_le_left)]
  exact hR₀

end Conjugacy

open Conjugacy

theorem conjugateMaximalC (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ) :
    ∀ V₁ ∈ maximals (signalizers ⊤ σ.C r), ∀ V₂ ∈ maximals (signalizers ⊤ σ.C r),
      ∃ m ∈ σ.M, conjSub m V₁ = V₂ := by
  intro V₁ hV₁ V₂ hV₂
  by_cases h1 : V₁ = ⊥
  · subst h1
    exact ⟨1, σ.M.one_mem, by rw [conjSub_one]; exact (hV₁.2 V₂ hV₂.1 bot_le).symm⟩
  by_cases h2 : V₂ = ⊥
  · subst h2
    exact ⟨1, σ.M.one_mem, by rw [conjSub_one]; exact hV₂.2 V₁ hV₁.1 bot_le⟩
  obtain ⟨m₁, hm₁, e₁⟩ := exists_conj_inf_N_ne_bot hσ Δ hV₁ h1
  obtain ⟨m₂, hm₂, e₂⟩ := exists_conj_inf_N_ne_bot hσ Δ hV₂ h2
  obtain ⟨m, hm, e⟩ := conj_of_inf_N_ne_bot hσ Δ homni
    (conjSub_mem_maximals_signalizers (conjSub_top _) hm₁ hV₁)
    (conjSub_mem_maximals_signalizers (conjSub_top _) hm₂ hV₂) e₁ e₂
  refine ⟨m₂⁻¹ * m * m₁, σ.M.mul_mem (σ.M.mul_mem (σ.M.inv_mem hm₂) hm) hm₁, ?_⟩
  rw [← conjSub_conjSub, ← conjSub_conjSub, e, conjSub_inv_conjSub]

theorem conjugateMaximalTC (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ) :
    ConjugateMaximalTC σ r := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  intro U₁ hU₁ U₂ hU₂
  obtain ⟨hV₁, e₁, hS₁⟩ := decomp_of_mem_maximals Δ homni hU₁
  obtain ⟨hV₂, e₂, hS₂⟩ := decomp_of_mem_maximals Δ homni hU₂
  obtain ⟨m, hm, hmV⟩ := conjugateMaximalC hσ Δ homni _ hV₁ _ hV₂
  have hS : IsSylowOf r (conjSub m (U₁ ⊓ σ.C)) σ.C := by
    have h := isSylowOf_conjSub hS₁ m
    rwa [conjSub_eq_self_iff.mpr hm] at h
  obtain ⟨c, hc, hcS⟩ := exists_conjSub_eq_of_isSylowOf hS hS₂
  have hcV : conjSub c (pCoreIn r (U₂ ⊔ σ.C)) = pCoreIn r (U₂ ⊔ σ.C) :=
    conjSub_eq_self_iff.mpr (hV₂.1.2.2.1 hc)
  refine ⟨c * m, σ.M.mul_mem (C_le_M hc) hm, ?_⟩
  rw [← conjSub_conjSub, e₁, conjSub_sup, conjSub_sup, hmV, hcV, hcS]
  exact e₂.symm

end CFSG.ABGTheoremB.TotallyInverted
