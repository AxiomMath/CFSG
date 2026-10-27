module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.GF2Thm1311.ConjugatePair
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.Seven

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.GF2Thm1311
open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

section Dihedral

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem inv_conj_pair {a : G} (ha : a * a = 1) (g : G) :
    a * (a * (g * a * g⁻¹)) * a⁻¹ = (a * (g * a * g⁻¹))⁻¹ := by
  have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [this]
  simp only [mul_inv_rev, inv_inv, this, mul_assoc]
  rw [← mul_assoc a a, ha, one_mul]

theorem exists_conj_pair_of_prime_dvd_orderOf {a : G} (ha : a * a = 1) (g : G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ orderOf (a * (g * a * g⁻¹))) :
    ∃ c : G, orderOf (a * (c * a * c⁻¹)) = p := by
  set w := a * (g * a * g⁻¹) with hw
  have hM : orderOf w ≠ 0 := (orderOf_pos w).ne'
  have hu : orderOf (w ^ (orderOf w / p)) = p := orderOf_pow_orderOf_div hM hdvd
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  set m := orderOf w / p * (k + 1) with hm
  have hu2 : w ^ (2 * m) = w ^ (orderOf w / p) := by
    have h1 : (w ^ (orderOf w / p)) ^ p = 1 := by
      have := pow_orderOf_eq_one (w ^ (orderOf w / p))
      rwa [hu] at this
    calc w ^ (2 * m) = (w ^ (orderOf w / p)) ^ (2 * (k + 1)) := by rw [hm, ← pow_mul]; ring_nf
      _ = (w ^ (orderOf w / p)) ^ (p + 1) := by congr 1; omega
      _ = w ^ (orderOf w / p) := by rw [pow_succ, h1, one_mul]
  refine ⟨(w ^ m)⁻¹, ?_⟩
  have hinv := inv_conj_pair ha g
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hconj : a * w ^ m * a = (w ^ m)⁻¹ := by
    have := conj_pow (a := a) (b := w) (i := m)
    rw [hai] at this hinv
    rw [← this, hinv, inv_pow]
  have key : a * ((w ^ m)⁻¹ * a * ((w ^ m)⁻¹)⁻¹) = w ^ (2 * m) := by
    have e : a * ((w ^ m)⁻¹ * a * ((w ^ m)⁻¹)⁻¹) = (a * (w ^ m)⁻¹ * a) * w ^ m := by
      simp only [inv_inv, mul_assoc]
    rw [e]
    have h2 : a * (w ^ m)⁻¹ * a = w ^ m := by
      have := congrArg (·⁻¹) hconj
      simpa [mul_inv_rev, hai, mul_assoc] using this
    rw [h2, ← pow_add, two_mul]
  rw [key, hu2, hu]

end Dihedral

section Engine

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_prime_dvd_orderOf_conj_pair (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (h : Nat.card V ≤ 4 * Nat.card {v : V | ∀ b ∈ A, b v = v}) {a : MulAut V} (haA : a ∈ A)
    (ha : a * a = 1) (g : MulAut V) {p : ℕ} (hp : p.Prime) (hbig : 11 ≤ p ∨ p = 7)
    (hdvd : p ∣ orderOf (a * (g * a * g⁻¹))) : False := by
  have hp2 : p ≠ 2 := by rcases hbig with h | h <;> omega
  obtain ⟨c, hc⟩ := exists_conj_pair_of_prime_dvd_orderOf ha g hp hp2 hdvd
  rcases hbig with h11 | h7
  swap
  · subst h7
    have hb : (c * a * c⁻¹) * (c * a * c⁻¹) = 1 := by
      have : (c * a * c⁻¹) * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      rw [this, ha]; group
    refine false_of_seven_pair (fun v => by simpa [pow_two] using hV v) ha hb hc ?_
    have h4 := index_fixV_zpowers_le_four haA h
    rw [index_fixV_conj]
    exact Nat.mul_le_mul h4 h4
  have : Fact p.Prime := ⟨hp⟩
  have h4 := orderOf_two_le_four_of_conj_pair hV h haA c hp2 hc
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hpos : 0 < orderOf (2 : ZMod p) :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one h20⟩).orderOf_pos
  have hpow : (2 : ZMod p) ^ orderOf (2 : ZMod p) = 1 := pow_orderOf_eq_one _
  set d := orderOf (2 : ZMod p) with hd
  have hdvd' : p ∣ 2 ^ d - 1 := by
    have h1 : ((2 ^ d : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using hpow
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
    have h2 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have h3 := (Nat.modEq_iff_dvd' h2).mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp h1).symm
    exact h3
  have h2d : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hpos
  have hle : p ≤ 2 ^ d - 1 := Nat.le_of_dvd (by omega) hdvd'
  have h16 : 2 ^ d ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h4
  have hfin : ∀ d ∈ Finset.Icc 1 4, ∀ q ∈ Finset.range 16, q.Prime → q ∣ 2 ^ d - 1 → q ≤ 7 := by decide
  have := hfin d (Finset.mem_Icc.mpr ⟨hpos, h4⟩) p (Finset.mem_range.mpr (by omega)) hp hdvd'
  omega

end Engine

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
