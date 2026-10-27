module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Block

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_of_commute {P Q : Subgroup G}
    (hc : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) {x : G} (hx : x ∈ P ⊔ Q) :
    ∃ a ∈ P, ∃ b ∈ Q, x = a * b := by
  let X : Subgroup G :=
    { carrier := {y | ∃ a ∈ P, ∃ b ∈ Q, y = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', P.mul_mem ha ha', b * b', Q.mul_mem hb hb', ?_⟩
        have h1 : b * a' = a' * b := (hc a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h1]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, P.inv_mem ha, b⁻¹, Q.inv_mem hb, ?_⟩
        have h1 : a * b = b * a := hc a ha b hb
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [h1]
          _ = a⁻¹ * b⁻¹ := by group }
  have hPX : P ≤ X := fun a ha => ⟨a, ha, 1, Q.one_mem, by simp⟩
  have hQX : Q ≤ X := fun b hb => ⟨1, P.one_mem, b, hb, by simp⟩
  exact (sup_le hPX hQX) hx

theorem le_or_le_of_forall_mem {P U V : Subgroup G} (h : ∀ p ∈ P, p ∈ U ∨ p ∈ V) :
    P ≤ U ∨ P ≤ V := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hPU, hPV⟩ := hcon
  obtain ⟨p₁, hp₁P, hp₁U⟩ : ∃ p ∈ P, p ∉ U := by
    by_contra h'
    push Not at h'
    exact hPU h'
  obtain ⟨p₂, hp₂P, hp₂V⟩ : ∃ p ∈ P, p ∉ V := by
    by_contra h'
    push Not at h'
    exact hPV h'
  have hp₁V : p₁ ∈ V := (h p₁ hp₁P).resolve_left hp₁U
  have hp₂U : p₂ ∈ U := (h p₂ hp₂P).resolve_right hp₂V
  rcases h (p₁ * p₂) (P.mul_mem hp₁P hp₂P) with h1 | h1
  · exact hp₁U (by simpa using U.mul_mem h1 (U.inv_mem hp₂U))
  · exact hp₂V (by simpa using V.mul_mem (V.inv_mem hp₁V) h1)

section Blocks

variable [Finite G]

theorem IsA4Block.exists_conj {L U : Subgroup G} (h : IsA4Block L U) {a b : G} (ha : a ∈ U)
    (hb : b ∈ U) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : ∃ g ∈ L, b = g⁻¹ * a * g := by
  obtain ⟨c, hcL, hc, hcN, hcfp, -⟩ := h.exists_c
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  obtain ⟨n, hn⟩ := klein_conj_transitive h.card_U hc3 hcN hcfp ha hb ha1 hb1
  exact ⟨c ^ n, pow_mem hcL n, hn⟩

theorem IsA4Block.conj_mixed {L₁ L₂ U₁ U₂ : Subgroup G} (h₁ : IsA4Block L₁ U₁)
    (h₂ : IsA4Block L₂ U₂) (hc : ∀ l ∈ L₁, ∀ l' ∈ L₂, l * l' = l' * l) {a a' b b' : G}
    (ha : a ∈ U₁) (ha' : a' ∈ U₁) (hb : b ∈ U₂) (hb' : b' ∈ U₂) (ha1 : a ≠ 1) (ha'1 : a' ≠ 1)
    (hb1 : b ≠ 1) (hb'1 : b' ≠ 1) : ∃ g : G, a' * b' = g⁻¹ * (a * b) * g := by
  obtain ⟨g₁, hg₁, hg₁'⟩ := h₁.exists_conj ha ha' ha1 ha'1
  obtain ⟨g₂, hg₂, hg₂'⟩ := h₂.exists_conj hb hb' hb1 hb'1
  have h1b : g₁ * b = b * g₁ := hc g₁ hg₁ b (h₂.le hb)
  have h2a : a' * g₂ = g₂ * a' := hc a' (h₁.le ha') g₂ hg₂
  refine ⟨g₁ * g₂, ?_⟩
  have e1 : g₁⁻¹ * b * g₁ = b := by
    calc g₁⁻¹ * b * g₁ = g₁⁻¹ * (b * g₁) := by group
      _ = g₁⁻¹ * (g₁ * b) := by rw [h1b]
      _ = b := by group
  have e2 : g₂⁻¹ * a' * g₂ = a' := by
    calc g₂⁻¹ * a' * g₂ = g₂⁻¹ * (a' * g₂) := by group
      _ = g₂⁻¹ * (g₂ * a') := by rw [h2a]
      _ = a' := by group
  calc a' * b' = (g₂⁻¹ * a' * g₂) * (g₂⁻¹ * b * g₂) := by rw [e2, ← hg₂']
    _ = g₂⁻¹ * (a' * b) * g₂ := by group
    _ = g₂⁻¹ * ((g₁⁻¹ * a * g₁) * (g₁⁻¹ * b * g₁)) * g₂ := by rw [e1, ← hg₁']
    _ = (g₁ * g₂)⁻¹ * (a * b) * (g₁ * g₂) := by group

omit [Finite G] in
theorem IsA4Block.inf_eq_bot {L₁ L₂ U₁ U₂ : Subgroup G} (h₁ : IsA4Block L₁ U₁)
    (h₂ : IsA4Block L₂ U₂) (hc : ∀ l ∈ L₁, ∀ l' ∈ L₂, l * l' = l' * l) : U₁ ⊓ U₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg₁, hg₂⟩
  have := h₁.center_L g (h₁.le hg₁) (fun l hl => (hc l hl g (h₂.le hg₂)).symm)
  rw [this]
  exact one_mem _

theorem no_mixed_mem_conjClass {L₁ L₂ U₁ U₂ P N : Subgroup G} {z z₂ : G} (h₁ : IsA4Block L₁ U₁)
    (h₂ : IsA4Block L₂ U₂) (hc : ∀ l ∈ L₁, ∀ l' ∈ L₂, l * l' = l' * l) (hz : z ∈ U₁ ⊔ U₂)
    (hzU₁ : z ∉ U₁) (hzU₂ : z ∉ U₂) (hzZ : z ∉ conjClass z₂)
    (hP : P ≤ U₁ ⊔ U₂) (hN : N ≤ U₁ ⊔ U₂) (hP4 : Nat.card P = 4) (hN4 : Nat.card N = 4)
    (hPN : P ⊓ N = ⊥) (hPZ : ∀ p ∈ P, p ≠ 1 → p ∈ conjClass z₂)
    (hNZ : ∀ n ∈ N, n ≠ 1 → n ∈ conjClass z₂) :
    ∀ p ∈ P, ∀ n ∈ N, p ≠ 1 → n ≠ 1 → p * n ∉ conjClass z₂ := by
  have hcU : ∀ a ∈ U₁, ∀ b ∈ U₂, a * b = b * a := fun a ha b hb =>
    hc a (h₁.le ha) b (h₂.le hb)
  obtain ⟨a₀, ha₀, b₀, hb₀, hzab⟩ := exists_mul_of_mem_sup_of_commute hcU hz
  have ha₀1 : a₀ ≠ 1 := by
    rintro rfl
    exact hzU₂ (by rw [hzab, one_mul]; exact hb₀)
  have hb₀1 : b₀ ≠ 1 := by
    rintro rfl
    exact hzU₁ (by rw [hzab, mul_one]; exact ha₀)
  have hmix : ∀ a ∈ U₁, ∀ b ∈ U₂, a ≠ 1 → b ≠ 1 → a * b ∉ conjClass z₂ := by
    intro a ha b hb ha1 hb1 hcl
    obtain ⟨g, hg⟩ := h₁.conj_mixed h₂ hc ha₀ ha hb₀ hb ha₀1 ha1 hb₀1 hb1
    apply hzZ
    rw [hzab]
    obtain ⟨k, hk⟩ := hcl
    refine ⟨k * g⁻¹, ?_⟩
    have : a * b = g⁻¹ * (a₀ * b₀) * g := hg
    calc a₀ * b₀ = g * (a * b) * g⁻¹ := by rw [this]; group
      _ = g * (k⁻¹ * z₂ * k) * g⁻¹ := by rw [← hk]
      _ = (k * g⁻¹)⁻¹ * z₂ * (k * g⁻¹) := by group
  have hpure : ∀ y ∈ U₁ ⊔ U₂, y ∈ conjClass z₂ → y ∈ U₁ ∨ y ∈ U₂ := by
    intro y hy hycl
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcU hy
    by_cases ha1 : a = 1
    · right
      rw [ha1, one_mul]
      exact hb
    · by_cases hb1 : b = 1
      · left
        rw [hb1, mul_one]
        exact ha
      · exact absurd hycl (hmix a ha b hb ha1 hb1)
  have hsub : ∀ Q : Subgroup G, Q ≤ U₁ ⊔ U₂ → (∀ q ∈ Q, q ≠ 1 → q ∈ conjClass z₂) →
      Q ≤ U₁ ∨ Q ≤ U₂ := by
    intro Q hQ hQZ
    refine le_or_le_of_forall_mem fun q hq => ?_
    by_cases hq1 : q = 1
    · left
      rw [hq1]
      exact one_mem _
    · exact hpure q (hQ hq) (hQZ q hq hq1)
  have hU₁4 := h₁.card_U
  have hU₂4 := h₂.card_U
  have hPe : P = U₁ ∨ P = U₂ := by
    rcases hsub P hP hPZ with h | h
    · left
      exact Subgroup.eq_of_le_of_card_ge h (le_of_eq (hU₁4.trans hP4.symm))
    · right
      exact Subgroup.eq_of_le_of_card_ge h (le_of_eq (hU₂4.trans hP4.symm))
  have hNe : N = U₁ ∨ N = U₂ := by
    rcases hsub N hN hNZ with h | h
    · left
      exact Subgroup.eq_of_le_of_card_ge h (le_of_eq (hU₁4.trans hN4.symm))
    · right
      exact Subgroup.eq_of_le_of_card_ge h (le_of_eq (hU₂4.trans hN4.symm))
  intro p hp n hn hp1 hn1
  have hne : P ≠ N := by
    intro h
    have hmem : p ∈ P ⊓ N := ⟨hp, h ▸ hp⟩
    rw [hPN] at hmem
    exact hp1 (Subgroup.mem_bot.mp hmem)
  rcases hPe with hPe | hPe <;> rcases hNe with hNe | hNe
  · exact absurd (hPe.trans hNe.symm) hne
  · rw [hPe] at hp
    rw [hNe] at hn
    exact hmix p hp n hn hp1 hn1
  · rw [hPe] at hp
    rw [hNe] at hn
    rw [← hcU n hn p hp]
    exact hmix n hn p hp hn1 hp1
  · exact absurd (hPe.trans hNe.symm) hne

end Blocks

end CFSG.QuasithinUnique.DoubleA3
