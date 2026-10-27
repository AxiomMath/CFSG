module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510A
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510C
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57K

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sq_eq_one_of_mem_sup {X Y : Subgroup G} (hX : ∀ x ∈ X, x * x = 1)
    (hY : ∀ y ∈ Y, y * y = 1) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {z : G}
    (hz : z ∈ X ⊔ Y) : z * z = 1 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup_commute hXY hz
  rw [show x * y * (x * y) = x * (y * x) * y by group, ← hXY x hx y hy,
    show x * (x * y) * y = (x * x) * (y * y) by group, hX x hx, hY y hy, one_mul]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem conj_mem_S_of_max
    (h𝕊 : FooteSimpleType 𝕊)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hCt : ∀ y ∈ T, y * t = t * y → y ∈ S)
    {M : ℕ} (hM : M = 16 ∨ M = 32)
    (hmax : ∀ E : Subgroup G, E ≤ S → (∀ e ∈ E, e * e = 1) → Nat.card E ≤ M)
    {S₁ : Subgroup G} (hSS₁ : S ≤ S₁) (hS₁T : S₁ ≤ T) (hS₁N : S₁ ≤ normalizer (S : Set G))
    (hcard₁ : Nat.card S₁ = 2 * Nat.card S) {s : G} (hs : ∀ x ∈ S, s * x * s⁻¹ ∈ S₁)
    {E : Subgroup G} (hES : E ≤ S) (hEsq : ∀ e ∈ E, e * e = 1) (hEM : Nat.card E = M) :
    ∀ x ∈ E, s * x * s⁻¹ ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  obtain ⟨x₀, hx₀, ha⟩ := hno
  set Es := conjugate E s⁻¹ with hEs
  have hmemEs : ∀ y, y ∈ Es ↔ s⁻¹ * y * s ∈ E := fun y => by
    rw [hEs, mem_conjugate_iff, inv_inv]
  have hEsS₁ : Es ≤ S₁ := fun y hy => by
    have h1 := hs _ (hES ((hmemEs y).mp hy))
    rwa [show s * (s⁻¹ * y * s) * s⁻¹ = y by group] at h1
  have hEssq : ∀ y ∈ Es, y * y = 1 := fun y hy => by
    have h1 := hEsq _ ((hmemEs y).mp hy)
    calc y * y = s * ((s⁻¹ * y * s) * (s⁻¹ * y * s)) * s⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hEsc : ∀ a ∈ Es, ∀ b ∈ Es, a * b = b * a := fun a ha b hb =>
    commute_of_sq_eq_one hEssq ha hb
  have hEsM : Nat.card Es = M := by rw [hEs, card_conjugate_eq_card, hEM]
  set a := s * x₀ * s⁻¹ with hadef
  have haEs : a ∈ Es := (hmemEs a).mpr (by rw [hadef]; group; exact hx₀)
  have haS₁ := hEsS₁ haEs
  have haT := hS₁T haS₁
  have haN := hS₁N haS₁
  have hQa : Q ⊓ conjugate Q a = ⊥ :=
    h.inf_conjugate_Q_eq_bot_of_ne haT fun h1 =>
      h.not_mem_normalizer_Q haT ha (mem_normalizer_of_conjugate_eq h1)
  set E₁ := Es ⊓ S with hE₁
  have hE₁Q : E₁ ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyEs := (mem_inf.mp (mem_inf.mp hy).1).1
    have hyQ := (mem_inf.mp hy).2
    have h1 : y ∈ Q ⊓ conjugate Q a := by
      refine mem_inf.mpr ⟨hyQ, ?_⟩
      rw [mem_conjugate_iff, hEsc a haEs y hyEs, mul_inv_cancel_right]
      exact hyQ
    rwa [hQa] at h1
  have hE₁card : M ≤ 2 * Nat.card E₁ := by
    rw [← hEsM]
    refine card_le_two_mul_of_cover (h := a) fun y hy => ?_
    by_cases hyS : y ∈ S
    · exact Or.inl (mem_inf.mpr ⟨hy, hyS⟩)
    · right
      refine mem_inf.mpr ⟨mul_mem (inv_mem haEs) hy, ?_⟩
      exact mul_mem_of_card_eq_two_mul hSS₁ hcard₁ (inv_mem haS₁) (hEsS₁ hy)
        (fun h1 => ha (by simpa using inv_mem h1)) hyS
  have hE₁S : E₁ ≤ S := inf_le_right
  have hE₁sq : ∀ y ∈ E₁, y * y = 1 := fun y hy => hEssq y (mem_inf.mp hy).1
  have hE₁N : E₁ ≤ normalizer (L : Set G) := hE₁S.trans h.S_le
  have himg : Nat.card E₁ = Nat.card (actImage L ε E₁) := by
    have h1 := card_eq_card_inf_mul_card_actImage ε hE₁N
    have h2 : E₁ ⊓ coreActionKernel L = ⊥ := by
      have h0 : E₁ ⊓ coreActionKernel L = E₁ ⊓ Q := by
        rw [← h.inf_coreActionKernel, ← inf_assoc, inf_of_le_left hE₁S]
      rw [h0, hE₁Q]
    rwa [h2, card_bot, one_mul] at h1
  rcases hM with rfl | rfl
  swap
  ·
    have h1 := AutL2Facts.footeAutRankThree 𝕊 h𝕊 (actImage L ε E₁) (by
      intro α hα
      obtain ⟨e, he, rfl⟩ := (mem_actImage ε hE₁N).mp hα
      rw [← actG_mul ε (hE₁N he) (hE₁N he), hE₁sq e he, actG_one])
    omega
  obtain ⟨r₁, hr₁, r₂, hr₂, hr₁2, hr₂2, hr₁₂, hr₁1, hr₂1, hne, hEr⟩ :=
    h.exists_fourgroup_R_of_image ε h𝕊 hE₁S hE₁sq (by omega)
  set W := kleinFourOfCommutingInvolutions r₁ r₂ hr₁2 hr₂2 hr₁₂ with hW
  have hW4 : Nat.card W = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions r₁ r₂ hr₁2 hr₂2 hr₁1 hr₂1 hne hr₁₂).card_four
  have hWR : W ≤ S ⊓ L := fun w hw => by
    rcases (mem_kleinFour_iff hr₁2 hr₂2 hr₁₂).mp hw with rfl | rfl | rfl | rfl
    · exact mul_mem hr₁ hr₂
    · exact hr₁
    · exact hr₂
    · exact one_mem _
  have hWsq : ∀ w ∈ W, w * w = 1 := fun w hw => by
    rcases (mem_kleinFour_iff hr₁2 hr₂2 hr₁₂).mp hw with rfl | rfl | rfl | rfl
    · rw [show r₁ * r₂ * (r₁ * r₂) = r₁ * (r₂ * r₁) * r₂ by group, ← hr₁₂,
        show r₁ * (r₁ * r₂) * r₂ = (r₁ * r₁) * (r₂ * r₂) by group, hr₁2, hr₂2, one_mul]
    · exact hr₁2
    · exact hr₂2
    · exact one_mul 1
  have hE₁W : ∀ e ∈ E₁, ∀ w ∈ W, e * w = w * e := fun e he w hw => by
    rcases (mem_kleinFour_iff hr₁2 hr₂2 hr₁₂).mp hw with rfl | rfl | rfl | rfl
    · rw [← mul_assoc, (hEr e he).1, mul_assoc, (hEr e he).2, mul_assoc]
    · exact (hEr e he).1
    · exact (hEr e he).2
    · rw [mul_one, one_mul]
  have hat : a * t * a⁻¹ ≠ t := fun h1 => ha (hCt a haT (by
    calc a * t = a * t * a⁻¹ * a := by group
      _ = t * a := by rw [h1]))
  have hRa := h.inf_conjugate_R_eq_bot hna haN hat
  set Wa := conjugate W a with hWa
  have hWaR : Wa ≤ conjugate (S ⊓ L) a := fun w hw => by
    rw [mem_conjugate_iff] at hw ⊢
    exact hWR hw
  have hWaS : Wa ≤ S := hWaR.trans (conjugate_le_of_mem_normalizer haN inf_le_left)
  have hWWa : ∀ w ∈ W, ∀ w' ∈ Wa, w * w' = w' * w := fun w hw w' hw' =>
    (h.commute_of_inf_conjugate_eq_bot haN hRa (hWR hw) (hWaR hw')).symm
  have hWWabot : W ⊓ Wa = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h1 : w ∈ S ⊓ L ⊓ conjugate (S ⊓ L) a :=
      mem_inf.mpr ⟨hWR (mem_inf.mp hw).1, hWaR (mem_inf.mp hw).2⟩
    rwa [hRa] at h1
  have hWasq : ∀ w ∈ Wa, w * w = 1 := fun w hw => conjugate_sq_eq_one hWsq hw
  have hF16 : Nat.card ↥(W ⊔ Wa) = 16 := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer W Wa (le_normalizer_of_commute hWWa)
      (disjoint_iff.mpr hWWabot), hW4, hWa, card_conjugate_eq_card, hW4]
  have hFS : W ⊔ Wa ≤ S := sup_le (hWR.trans inf_le_left) hWaS
  have hFsq : ∀ w ∈ W ⊔ Wa, w * w = 1 := fun w hw => sq_eq_one_of_mem_sup hWsq hWasq hWWa hw
  have hE₁Wa : ∀ e ∈ E₁, ∀ w ∈ Wa, e * w = w * e := by
    intro e he w hw
    have hea := hEsc a haEs e (mem_inf.mp he).1
    have h1 := hE₁W e he _ (mem_conjugate_iff.mp hw)
    calc e * w = a⁻¹ * (a * e * a⁻¹ * (a * w * a⁻¹)) * a := by group
      _ = a⁻¹ * (e * (a * w * a⁻¹)) * a := by rw [show a * e * a⁻¹ = e by rw [hea]; group]
      _ = a⁻¹ * ((a * w * a⁻¹) * e) * a := by rw [h1]
      _ = w * (a⁻¹ * e * a) := by group
      _ = w * e := by rw [show a⁻¹ * e * a = e by rw [mul_assoc, ← hea]; group]
  have hE₁F : ∀ e ∈ E₁, ∀ f ∈ W ⊔ Wa, e * f = f * e := by
    intro e he f hf
    obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_of_mem_sup_commute hWWa hf
    rw [← mul_assoc, hE₁W e he w hw, mul_assoc, hE₁Wa e he w' hw', ← mul_assoc]
  have hE₁leF : E₁ ≤ W ⊔ Wa := by
    intro e he
    by_contra heF
    have hdisj : (W ⊔ Wa) ⊓ zpowers e = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases eq_one_or_eq_of_mem_zpowers_sq (hE₁sq e he) (mem_inf.mp hy).2 with rfl | rfl
      · exact one_mem _
      · exact absurd (mem_inf.mp hy).1 heF
    have hcz : ∀ f ∈ W ⊔ Wa, ∀ y ∈ zpowers e, f * y = y * f := by
      intro f hf y hy
      rcases eq_one_or_eq_of_mem_zpowers_sq (hE₁sq e he) hy with rfl | rfl
      · rw [mul_one, one_mul]
      · exact (hE₁F y he f hf).symm
    have he1 : e ≠ 1 := fun h1 => heF (h1 ▸ one_mem _)
    have heo : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact hE₁sq e he) he1
    have h1 := hmax ((W ⊔ Wa) ⊔ zpowers e) (sup_le hFS (zpowers_le.mpr (hE₁S he)))
      (fun y hy => sq_eq_one_of_mem_sup hFsq (fun y hy => by
        rcases eq_one_or_eq_of_mem_zpowers_sq (hE₁sq e he) hy with rfl | rfl
        · exact one_mul 1
        · exact hE₁sq _ he) hcz hy)
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (W ⊔ Wa) (zpowers e)
      (le_normalizer_of_commute hcz) (disjoint_iff.mpr hdisj), hF16, Nat.card_zpowers, heo] at h1
    omega
  have hE₁Wne : E₁ ⊓ W ≠ ⊥ := by
    intro hbot
    have h1 := card_le_of_le (sup_le hE₁leF le_sup_left : E₁ ⊔ W ≤ W ⊔ Wa)
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer E₁ W
      (le_normalizer_of_commute hE₁W) (disjoint_iff.mpr hbot), hF16, hW4] at h1
    omega
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE₁Wne
  have hy1' : y ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
  have hyWa : y ∈ Wa := by
    rw [hWa, mem_conjugate_iff, hEsc a haEs y (mem_inf.mp (mem_inf.mp hy).1).1,
      mul_inv_cancel_right]
    exact (mem_inf.mp hy).2
  have h1 : y ∈ W ⊓ Wa := mem_inf.mpr ⟨(mem_inf.mp hy).2, hyWa⟩
  rw [hWWabot, mem_bot] at h1
  exact hy1' h1

end Sec5

end CFSG.ComponentClassification.Foote5
