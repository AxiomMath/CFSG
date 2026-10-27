module

public import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6Two

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp12Lie

open Subgroup CFSG.RankThree.PerfectCover CFSG.LieType.Steinberg.CentralExt

theorem sq_eq_one_of_mem_ker {L X : Type} [Group L] [Group X] [Group.IsPerfect L] (q : L →* X)
    (hq : Function.Surjective q) (hker : q.ker ≤ center L)
    (hb : ∀ m ∈ hopfMultiplier X, m ^ 6 = 1) (h2 : IsPGroup 2 ↥q.ker) {z : L} (hz : z ∈ q.ker) :
    z ^ 2 = 1 := by
  obtain ⟨m, hm⟩ := hopfMultiplierToKer_surjective q hq hker ⟨z, hz⟩
  have h6 : z ^ 6 = 1 := by
    have h1 := congrArg (fun k : q.ker => (k : L) ^ 6) hm
    simp only at h1
    rw [← h1, ← Subgroup.coe_pow, ← map_pow]
    have : (m : ↥(hopfMultiplier X)) ^ 6 = 1 := Subtype.ext (hb m m.2)
    rw [this, map_one]
    rfl
  obtain ⟨n, hn⟩ := h2 ⟨z, hz⟩
  have hzn : z ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have hd1 : orderOf z ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hd2 : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hzn
  have hd : orderOf z ∣ 2 := by
    have : orderOf z ∣ Nat.gcd 6 (2 ^ n) := Nat.dvd_gcd hd1 hd2
    refine this.trans ?_
    rcases n with _ | n
    · simp
    · rw [pow_succ]
      calc Nat.gcd 6 (2 ^ n * 2) = 2 * Nat.gcd 3 (2 ^ n) := by
            rw [show (6 : ℕ) = 2 * 3 by norm_num, mul_comm (2 ^ n) 2, Nat.gcd_mul_left]
        _ = 2 := by
            have : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
            rw [this.gcd_eq_one, mul_one]
        _ ∣ 2 := dvd_rfl
  exact orderOf_dvd_iff_pow_eq_one.1 hd

theorem pow_six_eq_one (x : Multiplicative (ZMod 3 × ZMod 2 × ZMod 2)) : x ^ 6 = 1 := by
  revert x
  decide

theorem hopfMultiplier_pow_six (h : GriessTwistedE6Two.TwistedE6TwoMultiplier) {X : Type}
    [Group X] (hX : CFSG.Blueprint.LieModel X .twistedE6 0 2 1) :
    ∀ m ∈ hopfMultiplier X, m ^ 6 = 1 := by
  intro m hm
  obtain ⟨-, ⟨f⟩⟩ := h X hX
  let g : CFSG.Open.griessHopfMultiplier X := (hopfMultiplierEquivGriess X).symm ⟨m, hm⟩
  have h1 : f g ^ 6 = 1 := pow_six_eq_one _
  have h2 : g ^ 6 = 1 := f.injective (by rw [map_pow, map_one]; exact h1)
  have h3 : (⟨m, hm⟩ : ↥(hopfMultiplier X)) ^ 6 = 1 := by
    have := congrArg (hopfMultiplierEquivGriess X) h2
    rwa [map_pow, map_one, MulEquiv.apply_symm_apply] at this
  exact congrArg Subtype.val h3

theorem card_center_le_two_of_twistedE6 (h : GriessTwistedE6Two.TwistedE6TwoMultiplier)
    {L : Type} [Group L] [Group.IsPerfect L]
    (hX : CFSG.Blueprint.LieModel (L ⧸ center L) .twistedE6 0 2 1) (h2 : IsPGroup 2 ↥(center L))
    (hc : IsCyclic ↥(center L)) : Nat.card ↥(center L) ≤ 2 := by
  let q : L →* (L ⧸ center L) := QuotientGroup.mk' (center L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = center L := QuotientGroup.ker_mk' _
  have hsq : ∀ z : ↥(center L), z ^ 2 = 1 := fun z => by
    have hz : (z : L) ∈ q.ker := by rw [hker]; exact z.2
    have h2' : IsPGroup 2 ↥q.ker := by rw [hker]; exact h2
    exact Subtype.ext (sq_eq_one_of_mem_ker q hq hker.le (hopfMultiplier_pow_six h hX) h2' hz)
  obtain ⟨g, hg⟩ := hc.exists_generator
  have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq g)
  have hcard : orderOf g = Nat.card ↥(center L) := orderOf_eq_card_of_forall_mem_zpowers hg
  exact Nat.le_of_dvd (by norm_num) (hcard ▸ hord)

end CFSG.EvenSporadicStandard.Induction.Hyp12Lie
