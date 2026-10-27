module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ClassCount

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup

variable {G : Type*} [Group G]

theorem le_or_le_of_forall_mem_or {H X Y : Subgroup G} (h : ∀ a ∈ H, a ∈ X ∨ a ∈ Y) :
    H ≤ X ∨ H ≤ Y := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨a, haH, haX⟩ := IsConcreteLE.not_le_iff_exists.1 hne.1
  obtain ⟨b, hbH, hbY⟩ := IsConcreteLE.not_le_iff_exists.1 hne.2
  have haY : a ∈ Y := (h a haH).resolve_left haX
  have hbX : b ∈ X := (h b hbH).resolve_right hbY
  rcases h (a * b) (H.mul_mem haH hbH) with hab | hab
  · exact haX (by simpa using X.mul_mem hab (X.inv_mem hbX))
  · exact hbY (by simpa using Y.mul_mem (Y.inv_mem haY) hab)

theorem exists_ne_one_commute_of_mem_normalizer {p : ℕ} [Fact p.Prime] [Finite G]
    {X : Subgroup G} (hX : IsPGroup p X) (hX1 : X ≠ ⊥) {g : G}
    (hgN : g ∈ normalizer (X : Set G)) (hg : IsPGroup p (zpowers g)) :
    ∃ a ∈ X, a ≠ 1 ∧ Commute g a := by
  set ĝ : normalizer (X : Set G) := ⟨g, hgN⟩
  have hK : IsPGroup p (zpowers ĝ) := by
    obtain ⟨k, hk⟩ := hg.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, ← hk, Nat.card_zpowers]
    exact (Subgroup.orderOf_mk g hgN)
  have hdvd : p ∣ Nat.card X := by
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hX1
      rw [pow_zero] at hk
      exact (Subgroup.card_eq_one).1 hk
    rw [hk]
    exact dvd_pow_self p hk0
  have h1 : (1 : X) ∈ MulAction.fixedPoints (zpowers ĝ) X := fun k => smul_one k
  obtain ⟨b, hb, hb1⟩ := hK.exists_fixed_point_of_prime_dvd_card_of_fixed_point X hdvd h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), ?_⟩
  have := hb ⟨ĝ, mem_zpowers ĝ⟩
  have h2 : g * (b : G) * g⁻¹ = b := congrArg Subtype.val this
  calc g * (b : G) = g * b * g⁻¹ * g := by group
    _ = b * g := by rw [h2]

theorem mem_normalizer_of_conj_le [Finite G] {X : Subgroup G} {g : G}
    (h : ∀ c ∈ X, g * c * g⁻¹ ∈ X) : g ∈ normalizer (X : Set G) := by
  let f : X → X := fun c => ⟨g * c * g⁻¹, h c c.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hs := Finite.surjective_of_injective hf
  rw [mem_normalizer_iff]
  intro c
  refine ⟨fun hc => h c hc, fun hc => ?_⟩
  obtain ⟨d, hd⟩ := hs ⟨g * c * g⁻¹, hc⟩
  have := congrArg Subtype.val hd
  simp only [f, mul_left_inj, mul_right_inj] at this
  exact this ▸ d.2

theorem mem_zpowers_sq_of_isPGroup {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) [Finite G] {g : G}
    (hg : IsPGroup p (zpowers g)) : g ∈ zpowers (g ^ 2) := by
  obtain ⟨k, hk⟩ := hg.exists_card_eq
  rw [Nat.card_zpowers] at hk
  have hodd : Odd (orderOf g) := by
    rw [hk]
    exact (Nat.Prime.odd_of_ne_two (Fact.out) hp).pow
  obtain ⟨m, hm⟩ := hodd
  refine ⟨((m + 1 : ℕ) : ℤ), ?_⟩
  change (g ^ 2) ^ ((m + 1 : ℕ) : ℤ) = g
  rw [zpow_natCast, ← pow_mul]
  calc g ^ (2 * (m + 1)) = g ^ (orderOf g) * g := by rw [hm, ← pow_succ]; ring_nf
    _ = g := by rw [pow_orderOf_eq_one, one_mul]

section TwoFactors

variable {p : ℕ} [Fact p.Prime] [Finite G] {X Y V : Subgroup G}

theorem conj_mem_left_of_two_factors (hp : p ≠ 2) (hX1 : X ≠ ⊥) (hXY : X ⊓ Y = ⊥)
    (hXV : X ≤ V) (hYV : Y ≤ V) (hfac : ∀ v ∈ V, ∃ a ∈ X, ∃ b ∈ Y, v = a * b)
    (hconj : ∀ g : G, ∀ c : G, (c ∈ X ∨ c ∈ Y) → c ≠ 1 → ∀ a ∈ X, a ≠ 1 → ∀ b ∈ Y, b ≠ 1 →
      g * c * g⁻¹ ≠ a * b)
    {g : G} (hgN : g ∈ normalizer (V : Set G)) (hg : IsPGroup p (zpowers g)) :
    ∀ c ∈ X, g * c * g⁻¹ ∈ X := by
  have hor : ∀ h : G, h ∈ normalizer (V : Set G) → ∀ c : G, (c ∈ X ∨ c ∈ Y) →
      h * c * h⁻¹ ∈ X ∨ h * c * h⁻¹ ∈ Y := by
    intro h hhN c hc
    by_cases hc1 : c = 1
    · left; rw [hc1, mul_one, mul_inv_cancel]; exact X.one_mem
    have hcV : c ∈ V := hc.elim (fun h => hXV h) (fun h => hYV h)
    obtain ⟨a, ha, b, hb, hab⟩ := hfac _ ((mem_normalizer_iff.1 hhN c).1 hcV)
    by_cases ha1 : a = 1
    · right; rw [hab, ha1, one_mul]; exact hb
    by_cases hb1 : b = 1
    · left; rw [hab, hb1, mul_one]; exact ha
    exact absurd hab (hconj h c hc hc1 a ha ha1 b hb hb1)
  have hsplit : ∀ h : G, h ∈ normalizer (V : Set G) → ∀ H : Subgroup G, (H = X ∨ H = Y) →
      (∀ c ∈ H, h * c * h⁻¹ ∈ X) ∨ (∀ c ∈ H, h * c * h⁻¹ ∈ Y) := by
    intro h hhN H hH
    have := le_or_le_of_forall_mem_or (H := H.map (MulAut.conj h).toMonoidHom) (X := X) (Y := Y)
      (by
        rintro _ ⟨c, hc, rfl⟩
        exact hor h hhN c (hH.elim (fun e => Or.inl (e ▸ hc)) (fun e => Or.inr (e ▸ hc))))
    rcases this with h1 | h1
    · exact Or.inl fun c hc => h1 ⟨c, hc, rfl⟩
    · exact Or.inr fun c hc => h1 ⟨c, hc, rfl⟩
  rcases hsplit g hgN X (Or.inl rfl) with hXX | hXY'
  · exact hXX
  exfalso
  have hginv : g⁻¹ ∈ normalizer (V : Set G) := inv_mem hgN
  rcases hsplit g hgN Y (Or.inr rfl) with hYX | hYY
  · have hg2 : g ^ 2 ∈ normalizer (X : Set G) := by
      apply mem_normalizer_of_conj_le
      intro c hc
      have := hYX _ (hXY' c hc)
      simpa [pow_two, mul_assoc] using this
    have hgX : g ∈ normalizer (X : Set G) :=
      (zpowers_le.2 hg2) (mem_zpowers_sq_of_isPGroup hp hg)
    apply hX1
    rw [eq_bot_iff]
    intro c hc
    have h1 : g * c * g⁻¹ ∈ X ⊓ Y := ⟨(mem_normalizer_iff.1 hgX c).1 hc, hXY' c hc⟩
    rw [hXY, mem_bot] at h1
    rw [mem_bot]
    have h2 := congrArg (fun w => g⁻¹ * w * g) h1
    simp only [inv_mul_cancel, mul_one] at h2
    rw [← h2]
    group
  ·
    apply hX1
    rw [eq_bot_iff]
    intro c hc
    have hcV' : g⁻¹ * c * g ∈ V := by
      have := (mem_normalizer_iff.1 hginv c).1 (hXV hc)
      simpa using this
    obtain ⟨a, ha, b, hb, hab⟩ := hfac _ hcV'
    have hcY : c ∈ Y := by
      have e : c = (g * a * g⁻¹) * (g * b * g⁻¹) := by
        calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
          _ = g * (a * b) * g⁻¹ := by rw [hab]
          _ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact Y.mul_mem (hXY' a ha) (hYY b hb)
    have : c ∈ X ⊓ Y := ⟨hc, hcY⟩
    rwa [hXY] at this

end TwoFactors

theorem eq_of_isPGroup_of_two_factors {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) [Finite G]
    {X Y V : Subgroup G} (hXp : IsPGroup p X) (hYp : IsPGroup p Y) (hX1 : X ≠ ⊥) (hY1 : Y ≠ ⊥)
    (hXY : X ⊓ Y = ⊥) (hXV : X ≤ V) (hYV : Y ≤ V)
    (hfac : ∀ v ∈ V, ∃ a ∈ X, ∃ b ∈ Y, v = a * b) (hVab : ∀ v ∈ V, ∀ w ∈ V, Commute v w)
    (hmax : ∀ a ∈ X, a ≠ 1 → ∀ b ∈ Y, b ≠ 1 → ∀ Q : Subgroup G, IsPGroup p Q → V ≤ Q →
      Q ≤ centralizer ({a * b} : Set G) → Q = V)
    (hconj : ∀ g : G, ∀ c : G, (c ∈ X ∨ c ∈ Y) → c ≠ 1 → ∀ a ∈ X, a ≠ 1 → ∀ b ∈ Y, b ≠ 1 →
      g * c * g⁻¹ ≠ a * b)
    {Q : Subgroup G} (hQ : IsPGroup p Q) (hVQ : V ≤ Q) : Q = V := by
  set S : Set G := {v | ∃ a ∈ X, a ≠ 1 ∧ ∃ b ∈ Y, b ≠ 1 ∧ v = a * b} with hS
  refine eq_of_isPGroup_of_centralizer (S := S) ?_ ?_ ?_ hQ hVQ
  · rintro v ⟨a, ha, -, b, hb, -, rfl⟩ w hw
    rw [mem_centralizer_singleton_iff]
    exact (hVab w hw _ (V.mul_mem (hXV ha) (hYV hb))).eq
  · rintro v ⟨a, ha, ha1, b, hb, hb1, rfl⟩
    exact hmax a ha ha1 b hb hb1
  · intro g hgN hg
    have hX : ∀ c ∈ X, g * c * g⁻¹ ∈ X :=
      conj_mem_left_of_two_factors hp hX1 hXY hXV hYV hfac hconj hgN hg
    have hY : ∀ c ∈ Y, g * c * g⁻¹ ∈ Y := by
      refine conj_mem_left_of_two_factors (X := Y) (Y := X) hp hY1 (by rw [inf_comm, hXY]) hYV hXV
        (fun v hv => ?_) (fun g' c hc hc1 a ha ha1 b hb hb1 => ?_) hgN hg
      · obtain ⟨a, ha, b, hb, rfl⟩ := hfac v hv
        exact ⟨b, hb, a, ha, (hVab _ (hXV ha) _ (hYV hb)).eq⟩
      · rw [(hVab _ (hYV ha) _ (hXV hb)).eq]
        exact hconj g' c hc.symm hc1 b hb hb1 a ha ha1
    obtain ⟨a, ha, ha1, hga⟩ :=
      exists_ne_one_commute_of_mem_normalizer hXp hX1 (mem_normalizer_of_conj_le hX) hg
    obtain ⟨b, hb, hb1, hgb⟩ :=
      exists_ne_one_commute_of_mem_normalizer hYp hY1 (mem_normalizer_of_conj_le hY) hg
    exact ⟨a * b, ⟨a, ha, ha1, b, hb, hb1, rfl⟩, hga.mul_right hgb⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
