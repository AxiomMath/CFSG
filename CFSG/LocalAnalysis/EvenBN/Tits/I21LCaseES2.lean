module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Subgroup

section Odd

variable {Y : Type*} [Group Y]

theorem caseES_eq_one_of_odd (C : Subgroup Y) (hC : Odd (Nat.card C)) {c : Y} (hc : c ∈ C)
    (hc2 : c * c = 1) : c = 1 := by
  by_contra hne
  have h2 : orderOf c = 2 := orderOf_eq_prime (by rwa [pow_two]) hne
  have h3 := Subgroup.orderOf_dvd_natCard C hc
  rw [h2] at h3
  exact (Nat.not_even_iff_odd.mpr hC) (even_iff_two_dvd.mpr h3)

theorem caseES_relIndex_dvd_two (Y₀ F : Subgroup Y)
    (h : ∀ a b : Y, a ∉ Y₀ → b ∉ Y₀ → a * b ∈ Y₀) : Y₀.relIndex F ∣ 2 := by
  rw [Subgroup.relIndex_dvd_two_iff]
  by_cases hF : ∃ a ∈ F, a ∉ Y₀
  · obtain ⟨a, haF, haY⟩ := hF
    refine ⟨a, haF, fun b _ => ?_⟩
    by_cases hb : b ∈ Y₀
    · exact Or.inr hb
    · exact Or.inl (h b a hb haY)
  · push Not at hF
    exact ⟨1, F.one_mem, fun b hb => Or.inr (hF b hb)⟩

theorem caseES_index_dvd_two (Y₀ : Subgroup Y)
    (h : ∀ a b : Y, a ∉ Y₀ → b ∉ Y₀ → a * b ∈ Y₀) : Y₀.index ∣ 2 := by
  rw [← Subgroup.relIndex_top_right]
  exact caseES_relIndex_dvd_two Y₀ ⊤ h

end Odd

section P3

variable {Y : Type*} [Group Y] [Finite Y]

theorem caseES_p3_of_odd_normal (C : Subgroup Y) [C.Normal] (hC : Odd (Nat.card C))
    (hidx : ∃ n : ℕ, C.index = 2 ^ n) (S : Sylow 2 Y) {t : Y} (ht : t ∈ S) {g : Y}
    (hg : g * t * g⁻¹ ∈ S) : ∃ s ∈ S, s * t * s⁻¹ = g * t * g⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCS : C ⊓ (S : Subgroup Y) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card ↥(C ⊓ (S : Subgroup Y)) ∣ Nat.card C :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(C ⊓ (S : Subgroup Y)) ∣ Nat.card (S : Subgroup Y) :=
      Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp S.isPGroup'
    rw [hn] at h2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    rw [hj] at h1 ⊢
    cases j with
    | zero => rfl
    | succ j =>
      exfalso
      exact (Nat.not_even_iff_odd.mpr hC)
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h1))
  have hSC : (S : Subgroup Y) ⊔ C = ⊤ := by
    rw [← Subgroup.index_eq_one]
    have h1 : ((S : Subgroup Y) ⊔ C).index ∣ C.index := Subgroup.index_dvd_of_le le_sup_right
    have h2 : ((S : Subgroup Y) ⊔ C).index ∣ (S : Subgroup Y).index :=
      Subgroup.index_dvd_of_le le_sup_left
    obtain ⟨n, hn⟩ := hidx
    rw [hn] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hS2 : ¬ 2 ∣ (S : Subgroup Y).index := Sylow.not_dvd_index S
    cases j with
    | zero => simpa using hj
    | succ j =>
      exfalso
      apply hS2
      rw [hj] at h2
      exact (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h2
  have hgmem : g ∈ (↑((S : Subgroup Y) ⊔ C) : Set Y) := by
    rw [hSC]
    trivial
  rw [Subgroup.mul_normal] at hgmem
  obtain ⟨s₀, hs₀, c, hc, rfl⟩ := hgmem
  refine ⟨s₀, hs₀, ?_⟩
  have e1 : s₀ * c * t * (s₀ * c)⁻¹ = s₀ * (c * t * c⁻¹) * s₀⁻¹ := by group
  rw [e1] at hg ⊢
  have hP : ∀ {a : Y}, a ∈ S → a ∈ (S : Subgroup Y) := fun h => h
  have ht'' : c * t * c⁻¹ ∈ (S : Subgroup Y) := by
    have h3 := (S : Subgroup Y).mul_mem ((S : Subgroup Y).mul_mem
      ((S : Subgroup Y).inv_mem (hP hs₀)) (hP hg)) (hP hs₀)
    have e2 : s₀⁻¹ * (s₀ * (c * t * c⁻¹) * s₀⁻¹) * s₀ = c * t * c⁻¹ := by group
    rwa [e2] at h3
  have hCm : c * t * c⁻¹ * t⁻¹ ∈ C := by
    have e3 : c * t * c⁻¹ * t⁻¹ = c * (t * c⁻¹ * t⁻¹) := by group
    rw [e3]
    exact C.mul_mem hc (Normal.conj_mem (inferInstance : C.Normal) c⁻¹ (C.inv_mem hc) t)
  have hSm : c * t * c⁻¹ * t⁻¹ ∈ (S : Subgroup Y) :=
    (S : Subgroup Y).mul_mem ht'' ((S : Subgroup Y).inv_mem (hP ht))
  have h5 : c * t * c⁻¹ * t⁻¹ ∈ C ⊓ (S : Subgroup Y) := ⟨hCm, hSm⟩
  rw [hCS, Subgroup.mem_bot, mul_inv_eq_one] at h5
  rw [h5]

end P3

section Kernel

variable {Y : Type*} [Group Y]

theorem caseES_card_units_sq : Nat.card ((ZMod 5)ˣ × (ZMod 5)ˣ) = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem caseES_card_sq_units : Nat.card {b : (ZMod 5)ˣ × (ZMod 5)ˣ // b * b = 1} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem caseES_index_dvd_of_hom {C Y₀ : Subgroup Y} (hCY : C ≤ Y₀) {B : Type*} [Group B] [Finite B]
    (φ : Y₀ →* B) (hker : ∀ y : Y₀, φ y = 1 ↔ (y : Y) ∈ C) :
    C.index ∣ Nat.card B * Y₀.index := by
  have h1 : C.subgroupOf Y₀ = φ.ker := by
    ext y
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hker]
  have h2 : C.relIndex Y₀ = Nat.card φ.range := by
    rw [Subgroup.relIndex, h1, Subgroup.index_ker]
  rw [← Subgroup.relIndex_mul_index hCY, h2]
  exact Nat.mul_dvd_mul_right (Subgroup.card_subgroup_dvd_card φ.range) _

theorem caseES_index_dvd_two_pow_five {C Y₀ : Subgroup Y} (hCY : C ≤ Y₀)
    (hY₀ : ∀ a b : Y, a ∉ Y₀ → b ∉ Y₀ → a * b ∈ Y₀) (φ : Y₀ →* (ZMod 5)ˣ × (ZMod 5)ˣ)
    (hker : ∀ y : Y₀, φ y = 1 ↔ (y : Y) ∈ C) : C.index ∣ 2 ^ 5 := by
  have h1 := caseES_index_dvd_of_hom hCY φ hker
  rw [caseES_card_units_sq] at h1
  have h2 : 16 * Y₀.index ∣ 16 * 2 := Nat.mul_dvd_mul_left 16 (caseES_index_dvd_two Y₀ hY₀)
  exact h1.trans h2

theorem caseES_card_dvd {C : Subgroup Y} (hc : Nat.card C ∣ 3 ^ 2 * 5 ^ 2)
    (hidx : C.index ∣ 2 ^ 5) : Nat.card Y ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2 := by
  rw [← Subgroup.card_mul_index C]
  have h := Nat.mul_dvd_mul hc hidx
  rwa [show 3 ^ 2 * 5 ^ 2 * 2 ^ 5 = 2 ^ 5 * 3 ^ 2 * 5 ^ 2 by ring] at h

theorem caseES_card_elemAb_le_eight {C Y₀ : Subgroup Y} (hC : Odd (Nat.card C))
    (hY₀ : ∀ a b : Y, a ∉ Y₀ → b ∉ Y₀ → a * b ∈ Y₀) (φ : Y₀ →* (ZMod 5)ˣ × (ZMod 5)ˣ)
    (hker : ∀ y : Y₀, φ y = 1 → (y : Y) ∈ C) (F : Subgroup Y) (hF : ∀ f ∈ F, f * f = 1) :
    Nat.card F ≤ 8 := by
  have h1 := Subgroup.relIndex_mul_card Y₀ F
  have h2 : Y₀.relIndex F ≤ 2 :=
    Nat.le_of_dvd two_pos (caseES_relIndex_dvd_two Y₀ F hY₀)
  have hsq : ∀ z : ↥(Y₀ ⊓ F), φ ⟨z, z.2.1⟩ * φ ⟨z, z.2.1⟩ = 1 := by
    intro z
    rw [← map_mul]
    have : (⟨z, z.2.1⟩ : Y₀) * ⟨z, z.2.1⟩ = 1 := Subtype.ext (hF z z.2.2)
    rw [this, map_one]
  have hinj : Function.Injective (fun z : ↥(Y₀ ⊓ F) =>
      (⟨φ ⟨z, z.2.1⟩, hsq z⟩ : {b : (ZMod 5)ˣ × (ZMod 5)ˣ // b * b = 1})) := by
    intro z z' hzz
    have hφ : φ ⟨z, z.2.1⟩ = φ ⟨z', z'.2.1⟩ := congrArg Subtype.val hzz
    have h3 : φ ((⟨z, z.2.1⟩ : Y₀)⁻¹ * ⟨z', z'.2.1⟩) = 1 := by
      rw [map_mul, map_inv, hφ, inv_mul_cancel]
    have h4 : (z : Y)⁻¹ * z' ∈ C := hker _ h3
    have h5 : ((z : Y)⁻¹ * z') * ((z : Y)⁻¹ * z') = 1 :=
      hF _ (F.mul_mem (F.inv_mem z.2.2) z'.2.2)
    exact Subtype.ext (inv_mul_eq_one.mp (caseES_eq_one_of_odd C hC h4 h5))
  have h6 : Nat.card ↥(Y₀ ⊓ F) ≤ 4 := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [caseES_card_sq_units] at this
  calc Nat.card F = Y₀.relIndex F * Nat.card ↥(Y₀ ⊓ F) := h1.symm
    _ ≤ 2 * 4 := Nat.mul_le_mul h2 h6
    _ = 8 := rfl

end Kernel

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
