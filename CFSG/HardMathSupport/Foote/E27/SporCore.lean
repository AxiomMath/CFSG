module

public import CFSG.HardMathSupport.Foote.E27.Defs
public import CFSG.HardMathSupport.Foote.E27.LocalBound
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.ComponentClassification.OuterAutomorphisms

theorem E27Config.mem_of_not_dvd_outer {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (hc : E27Config X K R T z) (hOut : ¬ 3 ∣ Nat.card (Outer ↥K)) : z ∈ K := by
  have := hc.normal
  let ψ : X →* MulAut ↥K := MulAut.conjNormal
  have hz3 : z ^ 3 = 1 := hc.elem.2 z hc.z_mem
  have hβ : (QuotientGroup.mk (ψ z) : Outer ↥K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ← map_pow, hz3, map_one]
    rfl
  have hq : (QuotientGroup.mk (ψ z) : Outer ↥K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hβ) with h1 | h1
    · exact orderOf_eq_one_iff.1 h1
    · exact absurd (h1 ▸ orderOf_dvd_natCard (QuotientGroup.mk (ψ z) : Outer ↥K)) hOut
  obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff _).1 hq
  have hcent : (k : X)⁻¹ * z ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun f : MulAut ↥K => (f ⟨y, hy⟩ : X)) hk
    simp only [ψ, MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    have h1 : (k : X) * y * (k : X)⁻¹ = z * y * z⁻¹ := by simpa using h1
    calc y * ((k : X)⁻¹ * z) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * z := by group
      _ = (k : X)⁻¹ * (z * y * z⁻¹) * z := by rw [h1]
      _ = (k : X)⁻¹ * z * y := by group
  rw [hc.faithful, Subgroup.mem_bot] at hcent
  have : z = k := by
    have := congrArg ((k : X) * ·) hcent
    simpa using this
  exact this ▸ k.2

theorem E27Config.three_pow_five_dvd_card_of_not_dvd_outer {X : Type} [Group X] [Finite X]
    {K R T : Subgroup X} {z : X} (hc : E27Config X K R T z)
    (hOut : ¬ 3 ∣ Nat.card (Outer ↥K)) : 3 ^ 5 ∣ Nat.card ↥K := by
  have := hc.normal
  have hD := three_pow_five_dvd_card_mulAut K hc.faithful R T z hc.elem hc.card_R hc.T_le_R
    hc.card_T hc.z_mem hc.z_not_mem hc.fus hc.sylow hc.central hc.dvd81
  have hmul : Nat.card (inner ↥K) * Nat.card (Outer ↥K) = Nat.card (MulAut ↥K) :=
    (inner ↥K).card_mul_index
  have hcop : Nat.Coprime (3 ^ 5) (Nat.card (Outer ↥K)) :=
    Nat.Coprime.pow_left 5 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hOut)
  rw [← hmul] at hD
  have h1 : 3 ^ 5 ∣ Nat.card (inner ↥K) := hcop.dvd_of_dvd_mul_right hD
  refine h1.trans ?_
  have hsurj : Function.Surjective ((MulAut.conj : ↥K →* MulAut ↥K).rangeRestrict) :=
    MonoidHom.rangeRestrict_surjective _
  exact Subgroup.card_dvd_of_surjective hsurj

end CFSG.HardMathSupport.Foote.E27
