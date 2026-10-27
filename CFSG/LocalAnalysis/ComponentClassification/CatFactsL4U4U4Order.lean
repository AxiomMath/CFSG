module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Order
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

theorem not_int_dvd_pow_sub_neg_one_pow {q s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hsq : s ∣ q ^ 2 + 1) {i : ℕ} (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    ¬ (s : ℤ) ∣ (q : ℤ) ^ i - (-1) ^ i := by
  have : Fact (1 < s) := ⟨hs.one_lt⟩
  intro hdiv
  have h0 : ((q : ZMod s)) ^ 2 + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ s).2 hsq
    push_cast at h
    exact h
  have hx : ((q : ZMod s)) ^ 2 = -1 := eq_neg_of_add_eq_zero_left h0
  have hz : ((q : ZMod s)) ^ i - (-1) ^ i = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ s).2 hdiv
    push_cast at h
    exact h
  have key : ((q : ZMod s)) ^ i = (-1) ^ i := sub_eq_zero.1 hz
  suffices hneg : (-1 : ZMod s) = 1 by
    have := neg_one_eq_one_iff.1 hneg
    rw [ZMod.ringChar_zmod_n] at this
    exact hs2 this
  interval_cases i
  · rw [pow_one, pow_one] at key
    rw [key, neg_one_sq] at hx
    exact hx.symm
  · rw [hx, neg_one_sq] at key
    exact key
  · have h3 : ((q : ZMod s)) ^ 3 = -(q : ZMod s) := by
      rw [pow_succ, hx, neg_one_mul]
    rw [h3, show ((-1 : ZMod s)) ^ 3 = -1 by rw [pow_succ, neg_one_sq, one_mul]] at key
    have hq : (q : ZMod s) = 1 := neg_inj.1 key
    rw [hq, one_pow] at hx
    exact hx.symm

theorem not_dvd_card_sesqUnitaryGroup {p f : ℕ} {K : Type*} [Field K]
    (h : UnitaryFieldData p f K) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) {d : ℕ}
    (hd : Module.finrank K V = d) (hd1 : 1 ≤ d) (hd3 : d ≤ 3) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsq : s ∣ (p ^ f) ^ 2 + 1) :
    ¬ s ∣ Nat.card (sesqUnitaryGroup B) := by
  intro hdiv
  have hcard := (unitary_full_group_order h hB hBl hd hd1).1
  have hdivZ : (s : ℤ) ∣ (Nat.card (sesqUnitaryGroup B) : ℤ) := Int.natCast_dvd_natCast.2 hdiv
  rw [hcard] at hdivZ
  have hsp : Prime (s : ℤ) := Nat.prime_iff_prime_int.1 hs
  rcases hsp.dvd_or_dvd hdivZ with h1 | h1
  · have h2 := hsp.dvd_of_dvd_pow h1
    have h3 : s ∣ p ^ f := Int.natCast_dvd_natCast.1 h2
    exact not_dvd_of_dvd_pow_add_one (e := 1) hs (by simpa using hsq) h3
  · obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hsp _).1 h1
    rw [Finset.mem_Icc] at hi
    exact not_int_dvd_pow_sub_neg_one_pow hs hs2 hsq hi.1 (by omega) hdi

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (n : ℕ)

@[expose] noncomputable def toSesq :
    ClassicalGroups.UnitaryFlag.unitarySU p f K n →* sesqUnitaryGroup (stdHermForm h n) :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* _).toMonoidHom.comp
    (ClassicalGroups.UnitaryFlag.unitarySU p f K n).subtype).codRestrict _ fun A x y =>
      ((ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry h).1 A.2).2 x y

theorem toSesq_apply (A : ClassicalGroups.UnitaryFlag.unitarySU p f K n) (x : Fin n → K) :
    (((toSesq h n A : sesqUnitaryGroup (stdHermForm h n)) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : (Fin n → K) →ₗ[K] Fin n → K) x =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x :=
  rfl

theorem toSesq_injective : Function.Injective (toSesq h n) := by
  intro A B hAB
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.toLin.injective
  exact congrArg Subtype.val hAB

end CFSG.ComponentClassification.CatFactsL4U4
