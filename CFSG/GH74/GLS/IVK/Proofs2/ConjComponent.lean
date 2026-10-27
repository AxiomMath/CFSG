module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open scoped commutatorElement

namespace ConjComponent

variable {H : Type*} [Group H]

theorem exists_mul_of_mem_sup {A B : Subgroup H} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : H}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup H :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        have := hc a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← this]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem A, 1, one_mem B, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, hc a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  exact (sup_le (fun a ha => ⟨a, ha, 1, one_mem B, by simp⟩)
    (fun b hb => ⟨1, one_mem A, b, hb, by simp⟩) : A ⊔ B ≤ S) hx

theorem mem_zpowers_of_central {A : Subgroup H} {z : H} (hperf : ⁅A, A⁆ = A)
    (hn : ∀ N : Subgroup H, N ≤ A → (∀ x ∈ A, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      N ≤ Subgroup.zpowers z ∨ N = A)
    (hA : ¬ A ≤ Subgroup.zpowers z) {b : H} (hb : b ∈ A) (hcb : ∀ c ∈ A, b * c = c * b) :
    b ∈ Subgroup.zpowers z := by
  have hinv : ∀ x ∈ A, ∀ n ∈ A ⊓ Subgroup.centralizer (A : Set H),
      x * n * x⁻¹ ∈ A ⊓ Subgroup.centralizer (A : Set H) := by
    intro x hx n hn'
    rw [Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hn').2 x hx, mul_assoc, mul_inv_cancel,
      mul_one]
    exact hn'
  rcases hn _ inf_le_left hinv with h | h
  · exact h (Subgroup.mem_inf.2 ⟨hb, Subgroup.mem_centralizer_iff.2 fun c hc => (hcb c hc).symm⟩)
  · refine absurd ?_ hA
    have hAcent : A ≤ Subgroup.centralizer (A : Set H) := fun x hx => by
      have : x ∈ A ⊓ Subgroup.centralizer (A : Set H) := by rw [h]; exact hx
      exact (Subgroup.mem_inf.1 this).2
    have hbot : ⁅A, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hAcent
    rw [hperf] at hbot
    rw [hbot]
    exact bot_le

theorem mem_of_commute_sup {A B : Subgroup H} {z : H} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hzA : Subgroup.zpowers z ≤ A)
    (hZ : ∀ b ∈ B, (∀ c ∈ B, b * c = c * b) → b ∈ Subgroup.zpowers z)
    {x : H} (hx : x ∈ A ⊔ B) (hxB : ∀ c ∈ B, x * c = c * x) : x ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hx
  have hbZ : b ∈ Subgroup.zpowers z := by
    refine hZ b hb fun c hcB => ?_
    have h1 := hxB c hcB
    have h2 := hc a ha c hcB
    calc b * c = a⁻¹ * (a * b * c) := by group
      _ = a⁻¹ * (c * (a * b)) := by rw [h1]
      _ = a⁻¹ * (c * a * b) := by group
      _ = a⁻¹ * (a * c * b) := by rw [h2]
      _ = c * b := by group
  exact mul_mem ha (hzA hbZ)

theorem conj_mem_of_mem_sup {A B : Subgroup H} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : H}
    (hx : x ∈ A ⊔ B) {y : H} (hy : y ∈ B) : x * y * x⁻¹ ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hx
  have h1 := hc a ha (b * y * b⁻¹) (mul_mem (mul_mem hb hy) (inv_mem hb))
  have : a * b * y * (a * b)⁻¹ = b * y * b⁻¹ :=
    calc a * b * y * (a * b)⁻¹ = (a * (b * y * b⁻¹)) * a⁻¹ := by group
      _ = (b * y * b⁻¹ * a) * a⁻¹ := by rw [h1]
      _ = b * y * b⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hb hy) (inv_mem hb)

theorem commutatorElement_mul_left {u a y : H} (hua : Commute u a) (huy : Commute u y) :
    ⁅u * a, y⁆ = ⁅a, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : Commute u (a * y * a⁻¹) := (hua.mul_right huy).mul_right hua.inv_right
  calc u * a * y * (u * a)⁻¹ * y⁻¹ = (u * (a * y * a⁻¹)) * u⁻¹ * y⁻¹ := by group
    _ = ((a * y * a⁻¹) * u) * u⁻¹ * y⁻¹ := by rw [h1.eq]
    _ = a * y * a⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_right {v a b : H} (hva : Commute v a) (hvb : Commute v b) :
    ⁅a, v * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv (v * b) a, commutatorElement_mul_left hvb hva,
    commutatorElement_inv]

theorem commutatorElement_mul_mul {u v a b : H} (hua : Commute u a) (hub : Commute u b)
    (huv : Commute u v) (hva : Commute v a) (hvb : Commute v b) :
    ⁅u * a, v * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left hua (huv.mul_right hub), commutatorElement_mul_right hva hvb]

theorem eq_or_eq_of_commute [Finite H] {K₁ K₂ : Subgroup H} {z : H}
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinter : K₁ ⊓ K₂ = Subgroup.zpowers z)
    (hperf₁ : ⁅K₁, K₁⁆ = K₁) (hperf₂ : ⁅K₂, K₂⁆ = K₂)
    (hn₁ : ∀ N : Subgroup H, N ≤ K₁ → (∀ x ∈ K₁, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      N ≤ Subgroup.zpowers z ∨ N = K₁)
    (hn₂ : ∀ N : Subgroup H, N ≤ K₂ → (∀ x ∈ K₂, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      N ≤ Subgroup.zpowers z ∨ N = K₂)
    (hK₁ : ¬ K₁ ≤ Subgroup.zpowers z) (hK₂ : ¬ K₂ ≤ Subgroup.zpowers z)
    {L N : Subgroup H} (hNK : N ≤ K₁ ⊔ K₂) (hLK : L ≤ K₁ ⊔ K₂)
    (hNinv : ∀ k ∈ K₁ ⊔ K₂, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hLN : ∀ l ∈ L, ∀ n ∈ N, l * n = n * l)
    (hcardN : Nat.card N = Nat.card K₂) (hcardL : Nat.card L = Nat.card K₁) :
    L = K₁ ∨ L = K₂ := by
  have hzK₁ : Subgroup.zpowers z ≤ K₁ := by rw [← hinter]; exact inf_le_left
  have hzK₂ : Subgroup.zpowers z ≤ K₂ := by rw [← hinter]; exact inf_le_right
  have hcomm' : ∀ b ∈ K₂, ∀ a ∈ K₁, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hZ₁ : ∀ b ∈ K₁, (∀ c ∈ K₁, b * c = c * b) → b ∈ Subgroup.zpowers z :=
    fun b hb hcb => mem_zpowers_of_central hperf₁ hn₁ hK₁ hb hcb
  have hZ₂ : ∀ b ∈ K₂, (∀ c ∈ K₂, b * c = c * b) → b ∈ Subgroup.zpowers z :=
    fun b hb hcb => mem_zpowers_of_central hperf₂ hn₂ hK₂ hb hcb
  have hC₂ : ∀ x ∈ K₁ ⊔ K₂, (∀ c ∈ K₂, x * c = c * x) → x ∈ K₁ :=
    fun x hx hxc => mem_of_commute_sup hcomm hzK₁ hZ₂ hx hxc
  have hC₁ : ∀ x ∈ K₁ ⊔ K₂, (∀ c ∈ K₁, x * c = c * x) → x ∈ K₂ :=
    fun x hx hxc => mem_of_commute_sup hcomm' hzK₂ hZ₁ (by rwa [sup_comm]) hxc
  have hzK : ∀ w ∈ Subgroup.zpowers z, ∀ k ∈ K₁ ⊔ K₂, w * k = k * w := by
    intro w hw k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    refine (Commute.zpow_left ?_ m).eq
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hk
    have h1 := hcomm a ha z (hzK₂ (Subgroup.mem_zpowers z))
    have h2 := hcomm z (hzK₁ (Subgroup.mem_zpowers z)) b hb
    show z * (a * b) = a * b * z
    calc z * (a * b) = (z * a) * b := by group
      _ = (a * z) * b := by rw [h1]
      _ = a * (z * b) := by group
      _ = a * (b * z) := by rw [h2]
      _ = a * b * z := by group
  have hP := hn₂ (N ⊓ K₂) inf_le_right fun x hx n hn' =>
    Subgroup.mem_inf.2 ⟨hNinv x (Subgroup.mem_sup_right hx) n (Subgroup.mem_inf.1 hn').1,
      mul_mem (mul_mem hx (Subgroup.mem_inf.1 hn').2) (inv_mem hx)⟩
  rcases hP with hP | hP
  · have hzmem : ∀ n ∈ N, ∀ c ∈ K₂, ⁅n, c⁆ ∈ Subgroup.zpowers z := by
      intro n hn c hc
      apply hP
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have : ⁅n, c⁆ = n * (c * n⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
        rw [this]
        exact mul_mem hn (hNinv c (Subgroup.mem_sup_right hc) n⁻¹ (inv_mem hn))
      · rw [commutatorElement_def]
        exact mul_mem (conj_mem_of_mem_sup hcomm (hNK hn) hc) (inv_mem hc)
    have hcentral : ∀ n ∈ N, ∀ c ∈ K₂, n * c = c * n := by
      intro n hn
      have hle : ⁅K₂, K₂⁆ ≤ K₂ ⊓ Subgroup.centralizer ({n} : Set H) := by
        rw [Subgroup.commutator_le]
        intro c₁ hc₁ c₂ hc₂
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem hc₁ hc₂) (inv_mem hc₁)) (inv_mem hc₂)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have e₁ : n * c₁ * n⁻¹ = ⁅n, c₁⁆ * c₁ := by rw [commutatorElement_def]; group
          have e₂ : n * c₂ * n⁻¹ = ⁅n, c₂⁆ * c₂ := by rw [commutatorElement_def]; group
          have hw₁ := hzmem n hn c₁ hc₁
          have hw₂ := hzmem n hn c₂ hc₂
          have key : n * ⁅c₁, c₂⁆ * n⁻¹ = ⁅c₁, c₂⁆ := by
            have := map_commutatorElement (MulAut.conj n) c₁ c₂
            simp only [MulAut.conj_apply] at this
            rw [this, e₁, e₂]
            exact commutatorElement_mul_mul (hzK _ hw₁ c₁ (Subgroup.mem_sup_right hc₁))
              (hzK _ hw₁ c₂ (Subgroup.mem_sup_right hc₂))
              (hzK _ hw₁ _ (Subgroup.mem_sup_right (hzK₂ hw₂)))
              (hzK _ hw₂ c₁ (Subgroup.mem_sup_right hc₁))
              (hzK _ hw₂ c₂ (Subgroup.mem_sup_right hc₂))
          exact (mul_inv_eq_iff_eq_mul.1 key).symm
      intro c hc
      exact (Subgroup.mem_centralizer_singleton_iff.1
        (Subgroup.mem_inf.1 (hle (hperf₂.ge hc))).2).symm
    have hNK₁ : N ≤ K₁ := fun n hn => hC₂ n (hNK hn) fun c hc => hcentral n hn c hc
    rcases hn₁ N hNK₁ (fun x hx n hn' => hNinv x (Subgroup.mem_sup_left hx) n hn') with hN | hN
    · exfalso
      have h1 := Subgroup.card_le_of_le hN
      rw [hcardN] at h1
      exact hK₂ (Subgroup.eq_of_le_of_card_ge hzK₂ h1).ge
    · have hLK₂ : L ≤ K₂ := fun l hl =>
        hC₁ l (hLK hl) fun c hc => hLN l hl c (by rw [hN]; exact hc)
      refine Or.inr (Subgroup.eq_of_le_of_card_ge hLK₂ ?_)
      have h3 : Nat.card N = Nat.card K₁ := by rw [hN]
      omega
  · have hK₂N : K₂ ≤ N := fun x hx => (Subgroup.mem_inf.1 (hP.ge hx)).1
    have hLK₁ : L ≤ K₁ := fun l hl => hC₂ l (hLK hl) fun c hc => hLN l hl c (hK₂N hc)
    exact Or.inl (Subgroup.eq_of_le_of_card_ge hLK₁ hcardL.ge)

end ConjComponent

theorem conj_component {H : Type*} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H}
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hz2 : orderOf z = 2)
    (hinter : K₁ ⊓ K₂ = Subgroup.zpowers z) (hnorm : (K₁ ⊔ K₂).Normal)
    (hperf₁ : ⁅K₁, K₁⁆ = K₁) (hperf₂ : ⁅K₂, K₂⁆ = K₂)
    (hn₁ : ∀ N : Subgroup H, N ≤ K₁ → (∀ x ∈ K₁, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      N ≤ Subgroup.zpowers z ∨ N = K₁)
    (hn₂ : ∀ N : Subgroup H, N ≤ K₂ → (∀ x ∈ K₂, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      N ≤ Subgroup.zpowers z ∨ N = K₂)
    (hK₁ : ¬ K₁ ≤ Subgroup.zpowers z) (hK₂ : ¬ K₂ ≤ Subgroup.zpowers z) (h : H) :
    K₁.map (MulAut.conj h).toMonoidHom = K₁ ∨ K₁.map (MulAut.conj h).toMonoidHom = K₂ := by
  have _ := hz2
  have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  have hφ : ∀ x, (MulAut.conj h).toMonoidHom x = h * x * h⁻¹ := fun x => rfl
  have hconj : ∀ k ∈ K₁ ⊔ K₂, h⁻¹ * k * h ∈ K₁ ⊔ K₂ := fun k hk => by
    simpa using hnorm.conj_mem k hk h⁻¹
  refine ConjComponent.eq_or_eq_of_commute hcomm hinter hperf₁ hperf₂ hn₁ hn₂ hK₁ hK₂
    (L := K₁.map (MulAut.conj h).toMonoidHom) (N := K₂.map (MulAut.conj h).toMonoidHom)
    ?_ ?_ ?_ ?_ (Subgroup.card_map_of_injective hinj) (Subgroup.card_map_of_injective hinj)
  · rintro _ ⟨b, hb, rfl⟩
    rw [hφ]
    exact hnorm.conj_mem b (Subgroup.mem_sup_right hb) h
  · rintro _ ⟨a, ha, rfl⟩
    rw [hφ]
    exact hnorm.conj_mem a (Subgroup.mem_sup_left ha) h
  · rintro k hk _ ⟨b, hb, rfl⟩
    refine ⟨h⁻¹ * k * h * b * (h⁻¹ * k * h)⁻¹,
      ConjComponent.conj_mem_of_mem_sup hcomm (hconj k hk) hb, ?_⟩
    simp only [hφ]
    group
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [hφ]
    calc h * a * h⁻¹ * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group
      _ = h * (b * a) * h⁻¹ := by rw [hcomm a ha b hb]
      _ = h * b * h⁻¹ * (h * a * h⁻¹) := by group

end CFSG.GH74.GLS.IVK.Proofs2
