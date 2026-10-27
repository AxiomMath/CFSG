module

public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.EightCycles

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

variable {V : Type*} [CommGroup V] [Finite V]

theorem card_modEq_card_inf_fixV {q : ℕ} [Fact q.Prime] {Y : Subgroup (MulAut V)}
    (hY : IsPGroup q Y) {M : Subgroup V} (hYM : Y ≤ stabSub M) :
    Nat.card M ≡ Nat.card ↥(M ⊓ fixV Y) [MOD q] := by
  have hY' : IsPGroup q (autSub Y M) :=
    (hY.comap_of_injective (stabSub M).subtype (stabSub M).subtype_injective).map (resHom M)
  have h1 := card_modEq_card_fixV (V := ↥M) hY'
  have h2 : Nat.card (fixV (autSub Y M)) = Nat.card ↥(M ⊓ fixV Y) := by
    rw [← map_subtype_fixV_autSub hYM, Subgroup.card_map_of_injective M.subtype_injective]
  rwa [h2] at h1

theorem fixV_zpowers_eq_bot_of_card_eq_sixteen (h16 : Nat.card V = 16) {L : Subgroup (MulAut V)}
    (ι : ↥L ≃* alternatingGroup (Fin 8)) {x : MulAut V} (hx : x ∈ L)
    (h3 : (ι ⟨x, hx⟩ : Perm (Fin 8)).IsThreeCycle) : fixV (Subgroup.zpowers x) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hx1 : x ≠ 1 := ne_one_of_isThreeCycle ι hx h3
  have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_isThreeCycle ι hx h3
  have hP3 : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one])
  obtain ⟨s, -, hs1, hs5, hsx⟩ := exists_mem_pow_five ι hx h3
  have hP5 : IsPGroup 5 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hs5 hs1, pow_one])
  have hsC : Subgroup.zpowers s ≤ stabSub (fixV (Subgroup.zpowers x)) := by
    refine B1.le_stabSub_of_invariant fun g hg c hc => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [mem_fixV_zpowers_iff] at hc ⊢
    have h1 : (s ^ k * x) c = (x * s ^ k) c := by rw [(Commute.zpow_left hsx k).eq]
    rw [MulAut.mul_apply, MulAut.mul_apply, hc] at h1
    exact h1.symm
  have hC := card_modEq_card_fixV hP3
  have hCs := card_modEq_card_inf_fixV hP5 hsC
  have hS := card_modEq_card_fixV hP5
  have dC : Nat.card (fixV (Subgroup.zpowers x)) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← h16]
    exact Subgroup.card_subgroup_dvd_card _
  have dS : Nat.card (fixV (Subgroup.zpowers s)) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← h16]
    exact Subgroup.card_subgroup_dvd_card _
  have lCs : Nat.card ↥(fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers s)) ≤
      Nat.card (fixV (Subgroup.zpowers x)) := Subgroup.card_le_of_le inf_le_left
  have lCs' : Nat.card ↥(fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers s)) ≤
      Nat.card (fixV (Subgroup.zpowers s)) := Subgroup.card_le_of_le inf_le_right
  have pCs : 0 < Nat.card ↥(fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers s)) :=
    Nat.card_pos
  have hCtop : Nat.card (fixV (Subgroup.zpowers x)) ≠ 16 := fun h =>
    hx1 (eq_one_of_fixV_eq_top (Subgroup.eq_top_of_card_eq _ (h.trans h16.symm)))
  have hStop : Nat.card (fixV (Subgroup.zpowers s)) ≠ 16 := fun h =>
    hs1 (eq_one_of_fixV_eq_top (Subgroup.eq_top_of_card_eq _ (h.trans h16.symm)))
  rw [← Subgroup.card_eq_one]
  obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 dC
  obtain ⟨j, hj, hcj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 dS
  rw [Nat.ModEq, h16] at hC hS
  rw [Nat.ModEq] at hCs
  rw [hai] at hC hCs hCtop lCs ⊢
  rw [hcj] at hS hStop lCs'
  interval_cases i <;> interval_cases j <;> omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
