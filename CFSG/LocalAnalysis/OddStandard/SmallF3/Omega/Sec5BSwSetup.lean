module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwPocket
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

structure SwSetup {Λ : Type} [Group Λ] (A₁ A₂ : Subgroup Λ) (z : Λ) : Prop where
  pocket₁ : SwPocket A₁ z
  pocket₂ : SwPocket A₂ z
  comm : ∀ u ∈ A₁, ∀ v ∈ A₂, u * v = v * u
  odd_mem : ∀ o ∈ centralizer ({z} : Set Λ), Odd (orderOf o) → o ∈ A₁ ⊔ A₂

namespace SwSetup

variable {Λ : Type} [Group Λ] {A₁ A₂ : Subgroup Λ} {z : Λ}

private lemma commute_zpowers (S : SwSetup A₁ A₂ z) {a : Λ} (ha : a ∈ A₁) {w : Λ}
    (hw : w ∈ zpowers z) : a * w = w * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hz : Commute a z := Subgroup.mem_centralizer_singleton_iff.mp (S.pocket₁.le_cent ha)
  exact (hz.zpow_right k).eq

private lemma exists_orderOf_eq_two_pow {u : Λ} {n : ℕ} (hu : u ^ (2 ^ n) = 1) :
    ∃ k : ℕ, orderOf u = 2 ^ k := by
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hu)
  exact ⟨k, hk⟩

private lemma sq_eq_one_of_two_pow (S : SwSetup A₁ A₂ z) {w : Λ} (hw : w ∈ zpowers z) {n : ℕ}
    (hn : w ^ (2 ^ n) = 1) : w * w = 1 := by
  have hwA : w ∈ A₁ := (Subgroup.zpowers_le.mpr S.pocket₁.mem) hw
  have hwwA : w * w ∈ A₁ := A₁.mul_mem hwA hwA
  have hcent : ∀ a ∈ A₁, a * w = w * a := fun a ha => S.commute_zpowers ha hw
  have hcentww : ∀ a ∈ A₁, a * (w * w) = (w * w) * a := by
    intro a ha
    calc a * (w * w) = (a * w) * w := by rw [mul_assoc]
      _ = (w * a) * w := by rw [hcent a ha]
      _ = w * (a * w) := by rw [mul_assoc]
      _ = w * (w * a) := by rw [hcent a ha]
      _ = (w * w) * a := by rw [mul_assoc]
  have hww_pow : (w * w) ^ (2 ^ n) = 1 := by
    calc (w * w) ^ (2 ^ n) = (w ^ 2) ^ (2 ^ n) := by rw [pow_two]
      _ = w ^ (2 * 2 ^ n) := by rw [← pow_mul]
      _ = w ^ (2 ^ n * 2) := by rw [mul_comm]
      _ = (w ^ (2 ^ n)) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [hn, one_pow]
  have horder_w : ∃ k : ℕ, orderOf w = 2 ^ k := exists_orderOf_eq_two_pow hn
  have horder_ww : ∃ k : ℕ, orderOf (w * w) = 2 ^ k := exists_orderOf_eq_two_pow hww_pow
  rcases S.pocket₁.two_center w hwA hcent horder_w (w * w) hwwA hcentww horder_ww with
    h1 | h2 | h3
  · rw [h1, one_mul]
  · exact h2
  · have hw1 : w = 1 := by
      have hmul : w * 1 = w * w := by rw [mul_one, ← h3]
      exact (mul_left_cancel hmul).symm
    rw [hw1, one_mul]

theorem sq_of_two_power (S : SwSetup A₁ A₂ z) {w : Λ} (hw : w ∈ zpowers z) {n : ℕ}
    (hn : w ^ (2 ^ n) = 1) : w * w = 1 :=
  S.sq_eq_one_of_two_pow hw hn

private lemma card_inf_le_two [Finite Λ] (S : SwSetup A₁ A₂ z) {S₁ S₂ : Subgroup Λ}
    (hS₁A : S₁ ≤ A₁) (hS₂A : S₂ ≤ A₂) (hS₁p : IsPGroup 2 S₁) :
    Nat.card ↥(S₁ ⊓ S₂) ≤ 2 := by
  let T : Subgroup Λ := S₁ ⊓ S₂
  have hcentral : ∀ w ∈ T, ∀ a ∈ A₁, a * w = w * a :=
    fun w hw a ha => S.comm a ha w (hS₂A hw.2)
  have horder : ∀ w ∈ T, ∃ k : ℕ, orderOf w = 2 ^ k := by
    intro w hw
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hS₁p ⟨w, hw.1⟩
    exact ⟨k, (Subgroup.orderOf_coe (⟨w, hw.1⟩ : S₁)).trans hk⟩
  have hsub_exists : ∃ v ∈ T, (T : Set Λ) ⊆ ({1, v} : Set Λ) := by
    by_cases hbot : T = ⊥
    · refine ⟨1, T.one_mem, fun w hwT => ?_⟩
      have hw1 : w = 1 := (Subgroup.eq_bot_iff_forall T).mp hbot w hwT
      rw [hw1]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · have hex : ∃ v ∈ T, v ≠ 1 := by
        by_contra h
        have h' : ∀ x ∈ T, x = 1 := by
          intro x hx
          by_contra hx1
          exact h ⟨x, hx, hx1⟩
        exact hbot ((Subgroup.eq_bot_iff_forall T).mpr h')
      obtain ⟨v, hvT, hvne⟩ := hex
      refine ⟨v, hvT, fun w hwT => ?_⟩
      rcases eq_or_ne w 1 with hw1 | hw1
      · exact Set.mem_insert_iff.mpr (Or.inl hw1)
      · refine Set.mem_insert_iff.mpr (Or.inr ?_)
        rcases S.pocket₁.two_center w (hS₁A hwT.1) (hcentral w hwT) (horder w hwT)
          v (hS₁A hvT.1) (hcentral v hvT) (horder v hvT) with h1 | h2 | h3
        · exact absurd h1 hw1
        · exact absurd h2 hvne
        · simpa using h3
  obtain ⟨v, hvT, hsub⟩ := hsub_exists
  have hle : Nat.card T ≤ Nat.card ({1, v} : Set Λ) :=
    Nat.card_le_card_of_injective (fun w : T => (⟨(w : Λ), hsub w.2⟩ : ({1, v} : Set Λ)))
      (fun a b hab => Subtype.ext (by
        have h := congrArg (fun x : ({1, v} : Set Λ) => (x : Λ)) hab
        simpa using h))
  have hpair : Nat.card ({1, v} : Set Λ) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    simpa using Set.ncard_insert_le (1 : Λ) ({v} : Set Λ)
  exact hle.trans hpair

theorem exists_big_two [Finite Λ] (S : SwSetup A₁ A₂ z) :
    ∃ P : Subgroup Λ, IsPGroup 2 P ∧ 32 ≤ Nat.card P ∧ P ≤ A₁ ⊔ A₂ := by
  obtain ⟨S₁, hS₁A, hS₁p, hS₁card⟩ := S.pocket₁.sylow
  obtain ⟨S₂, hS₂A, hS₂p, hS₂card⟩ := S.pocket₂.sylow
  have hcomm : ∀ u ∈ S₁, ∀ v ∈ S₂, u * v = v * u :=
    fun u hu v hv => S.comm u (hS₁A hu) v (hS₂A hv)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute S₁ S₂ hcomm).1
  have h64 : Nat.card ↥(S₁ ⊔ S₂) * Nat.card ↥(S₁ ⊓ S₂) = 64 := by
    rw [hcard, hS₁card, hS₂card]
  have hinf : Nat.card ↥(S₁ ⊓ S₂) ≤ 2 := S.card_inf_le_two hS₁A hS₂A hS₁p
  have h2a : 64 ≤ 2 * Nat.card ↥(S₁ ⊔ S₂) := by
    calc 64 = Nat.card ↥(S₁ ⊔ S₂) * Nat.card ↥(S₁ ⊓ S₂) := h64.symm
      _ ≤ Nat.card ↥(S₁ ⊔ S₂) * 2 := Nat.mul_le_mul_left _ hinf
      _ = 2 * Nat.card ↥(S₁ ⊔ S₂) := by ring
  have h32 : 32 ≤ Nat.card ↥(S₁ ⊔ S₂) := by omega
  refine ⟨S₁ ⊔ S₂, ?_, h32, sup_le_sup hS₁A hS₂A⟩
  have hdvd : Nat.card ↥(S₁ ⊔ S₂) ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num]
    exact ⟨Nat.card ↥(S₁ ⊓ S₂), h64.symm⟩
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact IsPGroup.of_card hk

end SwSetup

end CFSG.OddStandard.SmallF3.Omega
