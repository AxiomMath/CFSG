module

public import CFSG.GroupTheory.GL52.ExcludedOrders
public import CFSG.GroupTheory.GL52.SylowFive
public import CFSG.GroupTheory.GL52.SylowSeven
public import CFSG.GroupTheory.GL52.SylowThirtyOne
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Subgroup Module CFSG.GroupTheory.GL52

@[expose] def SylowOK (p M N : ℕ) : Prop :=
  p ∣ N → ∃ d ∈ Nat.divisors M, p ∣ d ∧ d ∣ N ∧ (N / d) % p = 1

theorem sylowOK_of_dvd (H : Subgroup (GL (Fin 5) (ZMod 2))) {p M : ℕ} [Fact p.Prime]
    (hp : ∀ P : Sylow p (GL (Fin 5) (ZMod 2)), Nat.card P = p)
    (hN : ∀ P : Sylow p (GL (Fin 5) (ZMod 2)),
      Nat.card (Subgroup.normalizer (P : Set (GL (Fin 5) (ZMod 2)))) = M)
    (hM : M ≠ 0) (hp2 : ¬ p ^ 2 ∣ Nat.card (GL (Fin 5) (ZMod 2))) : SylowOK p M (Nat.card H) := by
  intro hpH
  obtain ⟨m, hm⟩ := hpH
  have hmp : ¬ p ∣ m := by
    intro h
    obtain ⟨k, rfl⟩ := h
    apply hp2
    have : p ^ 2 ∣ Nat.card H := ⟨k, by rw [hm]; ring⟩
    exact this.trans (Subgroup.card_subgroup_dvd_card H)
  obtain ⟨Q⟩ : Nonempty (Sylow p H) := inferInstance
  have hQ : Nat.card Q = p := card_sylow_of_card_eq_prime_mul hm hmp Q
  have hd := card_normalizer_sylow_subgroup_dvd hp hN Q hQ
  obtain ⟨hmul, hmod⟩ := card_sylow_mul_card_normalizer Q
  have hpd : p ∣ Nat.card (Subgroup.normalizer (Q : Set H)) := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (Q : Subgroup H)))
    rwa [hQ] at this
  refine ⟨Nat.card (Subgroup.normalizer (Q : Set H)), Nat.mem_divisors.2 ⟨hd, hM⟩, hpd, ?_, ?_⟩
  · exact Dvd.intro_left _ hmul
  · have h1 : Nat.card H / Nat.card (Subgroup.normalizer (Q : Set H)) = Nat.card (Sylow p H) := by
      rw [← hmul]
      exact Nat.mul_div_cancel _ (Nat.card_pos)
    rw [h1]
    rw [Nat.one_mod_eq_one.2 (Fact.out : p.Prime).ne_one] at hmod
    exact hmod

@[expose] def survivorOrders : Finset ℕ :=
  {1, 2, 4, 5, 7, 8, 10, 14, 16, 20, 31, 32, 56, 64, 80, 112, 128, 155, 160, 256, 320, 448, 512,
    896, 992, 1024, 1280, 2560, 3584, 4960, 5120, 7168, 8680, 31744, 158720}

instance (p M N : ℕ) : Decidable (SylowOK p M N) := by unfold SylowOK; infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem arith_survivors_aux :
    ∀ a < 11, ∀ e < 2, ∀ f < 2, ∀ g < 2,
      SylowOK 5 60 (2 ^ a * 5 ^ e * 7 ^ f * 31 ^ g) →
      SylowOK 7 126 (2 ^ a * 5 ^ e * 7 ^ f * 31 ^ g) →
      SylowOK 31 155 (2 ^ a * 5 ^ e * 7 ^ f * 31 ^ g) →
      (2 ^ a * 5 ^ e * 7 ^ f * 31 ^ g) ∈ survivorOrders := by
  decide +kernel

theorem dvd_eq_pow {N : ℕ} (h : N ∣ 2 ^ 10 * 5 * 7 * 31) :
    ∃ a < 11, ∃ e < 2, ∃ f < 2, ∃ g < 2, N = 2 ^ a * 5 ^ e * 7 ^ f * 31 ^ g := by
  obtain ⟨N1, N2, h1, h2, rfl⟩ := Nat.dvd_mul.1 h
  obtain ⟨N3, N4, h3, h4, rfl⟩ := Nat.dvd_mul.1 h1
  obtain ⟨N5, N6, h5, h6, rfl⟩ := Nat.dvd_mul.1 h3
  obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).1 h5
  have h6' : N6 = 1 ∨ N6 = 5 := (Nat.dvd_prime (by norm_num)).1 h6
  have h4' : N4 = 1 ∨ N4 = 7 := (Nat.dvd_prime (by norm_num)).1 h4
  have h2' : N2 = 1 ∨ N2 = 31 := (Nat.dvd_prime (by norm_num)).1 h2
  refine ⟨a, by omega, ?_⟩
  rcases h6' with rfl | rfl
  · rcases h4' with rfl | rfl
    · rcases h2' with rfl | rfl
      · exact ⟨0, by norm_num, 0, by norm_num, 0, by norm_num, by simp⟩
      · exact ⟨0, by norm_num, 0, by norm_num, 1, by norm_num, by simp⟩
    · rcases h2' with rfl | rfl
      · exact ⟨0, by norm_num, 1, by norm_num, 0, by norm_num, by simp⟩
      · exact ⟨0, by norm_num, 1, by norm_num, 1, by norm_num, by simp⟩
  · rcases h4' with rfl | rfl
    · rcases h2' with rfl | rfl
      · exact ⟨1, by norm_num, 0, by norm_num, 0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, 0, by norm_num, 1, by norm_num, by simp⟩
    · rcases h2' with rfl | rfl
      · exact ⟨1, by norm_num, 1, by norm_num, 0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, 1, by norm_num, 1, by norm_num, by simp⟩

theorem orders_of_threePrime (H : Subgroup (GL (Fin 5) (ZMod 2))) (h3 : ¬ 3 ∣ Nat.card H) :
    Nat.card H ∈ survivorOrders := by
  have hG := card_G52
  have hd : Nat.card H ∣ 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := hG ▸ Subgroup.card_subgroup_dvd_card H
  have hcop : Nat.Coprime (Nat.card H) (3 ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  have hd' : Nat.card H ∣ 2 ^ 10 * 5 * 7 * 31 := by
    have : 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 = 3 ^ 2 * (2 ^ 10 * 5 * 7 * 31) := by ring
    rw [this] at hd
    exact hcop.dvd_of_dvd_mul_left hd
  have h5 : SylowOK 5 60 (Nat.card H) := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact sylowOK_of_dvd H syl5_card_sylow (fun P => (syl5_structure P).2.2) (by norm_num)
      (by rw [hG]; norm_num)
  have h7 : SylowOK 7 126 (Nat.card H) := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact sylowOK_of_dvd H syl7_card_sylow (fun P => (syl7_structure P).1) (by norm_num)
      (by rw [hG]; norm_num)
  have h31 : SylowOK 31 155 (Nat.card H) := by
    have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    exact sylowOK_of_dvd H syl31_card_sylow (fun P => (syl31_structure P).1) (by norm_num)
      (by rw [hG]; norm_num)
  obtain ⟨a, ha, e, he, f, hf, g, hg, hN⟩ := dvd_eq_pow hd'
  rw [hN] at h5 h7 h31 ⊢
  exact arith_survivors_aux a ha e he f hf g hg h5 h7 h31

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
