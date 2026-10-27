module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNEModel

public section

namespace CFSG.ComponentClassification.GMS78.RuNE

open Subgroup CFSG.ComponentClassification.GMS78.RuPi7 CFSG.ComponentClassification.GMS78.RuAsm

theorem w_pow_seven
    {G : Type} [Group G] {z : G}
    {A : Subgroup G} {f₁ : ↥ruM1 ≃* ↥(centralizer ({z} : Set G))} (hf₁ : IsNormCz f₁ A)
    (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (hag : ∀ (m : Pi7) (h₁ : m ∈ ruM1) (h₂ : m ∈ ruM2), m ∈ ruB0 →
      ((f₁ ⟨m, h₁⟩ : ↥(centralizer ({z} : Set G))) : G) = (f₂ ⟨m, h₂⟩ : G)) :
    ((f₁ ⟨PresentedGroup.of 5, mem_letterSub (by decide)⟩ : G) *
        f₁ ⟨PresentedGroup.of 0, mem_letterSub (by decide)⟩ *
        f₁ ⟨PresentedGroup.of 2, mem_letterSub (by decide)⟩ *
        f₂ ⟨PresentedGroup.of 6, mem_letterSub (by decide)⟩) ^ 7 = 1 := by
  classical
  let Φ : Pi7 → G := fun m =>
    if h : m ∈ ruM1 then ((f₁ ⟨m, h⟩ : ↥(centralizer ({z} : Set G))) : G) else 1
  let Ψ : Pi7 → G := fun m =>
    if h : m ∈ ruM2 then ((f₂ ⟨m, h⟩ : ↥(normalizer (A : Set G))) : G) else 1
  have hΦ : ∀ m (h : m ∈ ruM1), Φ m = f₁ ⟨m, h⟩ := fun m h => dite_eq_left h
  have hΨ : ∀ m (h : m ∈ ruM2), Ψ m = f₂ ⟨m, h⟩ := fun m h => dite_eq_left h
  have hΦmul : ∀ a b, a ∈ ruM1 → b ∈ ruM1 → Φ (a * b) = Φ a * Φ b := fun a b ha hb => by
    rw [hΦ _ (mul_mem ha hb), hΦ a ha, hΦ b hb]
    exact congrArg Subtype.val (map_mul f₁ ⟨a, ha⟩ ⟨b, hb⟩)
  have hΦconj : ∀ a b, a ∈ ruM1 → b ∈ ruM1 → Φ (a * b * a⁻¹) = Φ a * Φ b * (Φ a)⁻¹ :=
    fun a b ha hb => by
      rw [hΦmul _ _ (mul_mem ha hb) (inv_mem ha), hΦmul _ _ ha hb, hΦ _ (inv_mem ha), hΦ a ha]
      exact congrArg (fun x => _ * Subtype.val x) (map_inv f₁ ⟨a, ha⟩)
  have hΨmul : ∀ a b, a ∈ ruM2 → b ∈ ruM2 → Ψ (a * b) = Ψ a * Ψ b := fun a b ha hb => by
    rw [hΨ _ (mul_mem ha hb), hΨ a ha, hΨ b hb]
    exact congrArg Subtype.val (map_mul f₂ ⟨a, ha⟩ ⟨b, hb⟩)
  have hΨconj : ∀ a b, a ∈ ruM2 → b ∈ ruM2 → Ψ (a * b * a⁻¹) = Ψ a * Ψ b * (Ψ a)⁻¹ :=
    fun a b ha hb => by
      rw [hΨmul _ _ (mul_mem ha hb) (inv_mem ha), hΨmul _ _ ha hb, hΨ _ (inv_mem ha), hΨ a ha]
      exact congrArg (fun x => _ * Subtype.val x) (map_inv f₂ ⟨a, ha⟩)
  have hΦinj : ∀ a b, a ∈ ruM1 → b ∈ ruM1 → Φ a = Φ b → a = b := fun a b ha hb h => by
    rw [hΦ a ha, hΦ b hb] at h
    exact congrArg Subtype.val (f₁.injective (Subtype.ext h))
  have hE1 : ∀ {e : Pi7}, e ∈ ruE0 → e ∈ ruM1 := fun he => ruE0_le_ruM1 he
  have hag' : ∀ e ∈ ruE0, Φ e = Ψ e := fun e he => by
    have hB := ruE0_le_ruB0 he
    rw [hΦ e (ruB0_le_ruM1 hB), hΨ e (ruB0_le_ruM2 hB)]
    exact hag e _ _ hB
  have h5 : (PresentedGroup.of 5 : Pi7) ∈ ruM1 := mem_letterSub (by decide)
  have h0 : (PresentedGroup.of 0 : Pi7) ∈ ruM1 := mem_letterSub (by decide)
  have h2 : (PresentedGroup.of 2 : Pi7) ∈ ruM1 := mem_letterSub (by decide)
  have h6 : (PresentedGroup.of 6 : Pi7) ∈ ruM2 := mem_letterSub (by decide)
  let u₁ : Pi7 := PresentedGroup.of 5 * PresentedGroup.of 0 * PresentedGroup.of 2
  have hu₁ : u₁ ∈ ruM1 := mul_mem (mul_mem h5 h0) h2
  have hn₁ : u₁ ∈ normalizer (ruE0 : Set Pi7) :=
    mul_mem (mul_mem (of_mem_normalizer (by decide)) (of_mem_normalizer (by decide)))
      (of_mem_normalizer (by decide))
  have hn₂ : (PresentedGroup.of 6 : Pi7) ∈ normalizer (ruE0 : Set Pi7) :=
    of_mem_normalizer (by decide)
  have hn₀ : u₁ * PresentedGroup.of 6 ∈ normalizer (ruE0 : Set Pi7) := mul_mem hn₁ hn₂
  have hw : ((f₁ ⟨PresentedGroup.of 5, h5⟩ : G) * f₁ ⟨PresentedGroup.of 0, h0⟩ *
      f₁ ⟨PresentedGroup.of 2, h2⟩ * f₂ ⟨PresentedGroup.of 6, h6⟩) =
      Φ u₁ * Ψ (PresentedGroup.of 6) := by
    rw [hΦmul _ _ (mul_mem h5 h0) h2, hΦmul _ _ h5 h0, hΦ _ h5, hΦ _ h0, hΦ _ h2, hΨ _ h6]
  rw [hw]
  have hK : ∀ e ∈ ruE0, Φ u₁ * Ψ (PresentedGroup.of 6) * Φ e *
      (Φ u₁ * Ψ (PresentedGroup.of 6))⁻¹ =
      Φ (u₁ * PresentedGroup.of 6 * e * (u₁ * PresentedGroup.of 6)⁻¹) := by
    intro e he
    have he₂ : PresentedGroup.of 6 * e * (PresentedGroup.of 6)⁻¹ ∈ ruE0 :=
      (mem_normalizer_iff.1 hn₂ e).1 he
    rw [conj_mul_conj (Φ u₁) (Ψ (PresentedGroup.of 6)) (Φ e), hag' e he,
      ← hΨconj _ _ h6 (ruB0_le_ruM2 (ruE0_le_ruB0 he)), ← hag' _ he₂,
      ← hΦconj _ _ hu₁ (hE1 he₂), conj_mul_conj u₁ (PresentedGroup.of 6) e]
  have hK' : ∀ k : ℕ, ∀ e ∈ ruE0, (Φ u₁ * Ψ (PresentedGroup.of 6)) ^ k * Φ e *
      ((Φ u₁ * Ψ (PresentedGroup.of 6)) ^ k)⁻¹ =
      Φ ((u₁ * PresentedGroup.of 6) ^ k * e * ((u₁ * PresentedGroup.of 6) ^ k)⁻¹) := by
    intro k
    induction k with
    | zero => intro e _; simp only [pow_zero, one_mul, inv_one, mul_one]
    | succ k ih =>
      intro e he
      have he' : (u₁ * PresentedGroup.of 6) ^ k * e * ((u₁ * PresentedGroup.of 6) ^ k)⁻¹ ∈ ruE0 :=
        (mem_normalizer_iff.1 (pow_mem hn₀ k) e).1 he
      rw [pow_succ', pow_succ',
        conj_mul_conj (Φ u₁ * Ψ (PresentedGroup.of 6)) ((Φ u₁ * Ψ (PresentedGroup.of 6)) ^ k),
        ih e he, hK _ he',
        conj_mul_conj (u₁ * PresentedGroup.of 6) ((u₁ * PresentedGroup.of 6) ^ k) e]
  have h7 : ∀ e ∈ ruE0, (Φ u₁ * Ψ (PresentedGroup.of 6)) ^ 7 * Φ e =
      Φ e * (Φ u₁ * Ψ (PresentedGroup.of 6)) ^ 7 := by
    intro e he
    have h := hK' 7 e he
    have hw₀ : (u₁ * PresentedGroup.of 6) ^ 7 = 1 := w0_pow_seven
    rw [hw₀, one_mul, inv_one, mul_one, mul_inv_eq_iff_eq_mul] at h
    exact h
  have hz : Φ ruZ0 = z := by
    rw [hΦ _ (hE1 ruZ0_mem_ruE0)]
    exact hf₁.1 ⟨ruZ0, hE1 ruZ0_mem_ruE0⟩ rfl
  have hzc : (Φ u₁ * Ψ (PresentedGroup.of 6)) ^ 7 ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hz]
    exact h7 _ ruZ0_mem_ruE0
  obtain ⟨m, hm⟩ : ∃ m : ↥ruM1, ((f₁ m : ↥(centralizer ({z} : Set G))) : G) =
      (Φ u₁ * Ψ (PresentedGroup.of 6)) ^ 7 := ⟨f₁.symm ⟨_, hzc⟩, by simp⟩
  have hmΦ : Φ (m : Pi7) = (Φ u₁ * Ψ (PresentedGroup.of 6)) ^ 7 := by
    rw [hΦ _ m.2]
    exact hm
  have hmc : (m : Pi7) ∈ centralizer (ruE0 : Set Pi7) := by
    refine mem_centralizer_iff.2 fun e he => hΦinj _ _ (mul_mem (hE1 he) m.2)
      (mul_mem m.2 (hE1 he)) ?_
    rw [hΦmul _ _ (hE1 he) m.2, hΦmul _ _ m.2 (hE1 he), hmΦ]
    exact (h7 e he).symm
  have hmE : (m : Pi7) ∈ ruE0 := mem_ruE0_of_mem_centralizer m.2 hmc
  have hcomm : u₁ * PresentedGroup.of 6 * (m : Pi7) = (m : Pi7) * (u₁ * PresentedGroup.of 6) := by
    have hconj : u₁ * PresentedGroup.of 6 * (m : Pi7) * (u₁ * PresentedGroup.of 6)⁻¹ ∈ ruE0 :=
      (mem_normalizer_iff.1 hn₀ _).1 hmE
    have h := hK _ hmE
    rw [hmΦ, show ∀ x : G, x * x ^ 7 * x⁻¹ = x ^ 7 from fun x => by group, ← hmΦ] at h
    have h' := hΦinj _ _ m.2 (hE1 hconj) h
    rw [eq_mul_inv_iff_mul_eq] at h'
    exact h'.symm
  have hm1 : (m : Pi7) = 1 := eq_one_of_commute_w0 hmE hcomm
  rw [← hmΦ, hm1, hΦ 1 (one_mem _)]
  exact congrArg Subtype.val (map_one f₁)

end CFSG.ComponentClassification.GMS78.RuNE
