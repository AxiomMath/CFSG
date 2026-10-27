module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31A
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.TwoGroups

section NoFour

variable {J : Type} [Group J] [Finite J]

theorem not_exists_four_of_quaternion {T : Subgroup J} {m : ℕ} [NeZero m]
    (ι : ↥T →* QuaternionGroup m) (hι : Function.Injective ι) :
    ¬ ∃ U : Subgroup J, U ≤ T ∧ IVK.IsFourSubgroup U := by
  rintro ⟨U, hUT, hUel, hUcard⟩
  have := hUel
  have hsq : ∀ x ∈ U, x ^ 2 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hU1 : U ≠ ⊥ := by
    intro h
    rw [h] at hUcard
    simp at hUcard
  obtain ⟨a, haU, ha1⟩ : ∃ a ∈ U, a ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hU1)
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  obtain ⟨b, hbU, hbz⟩ : ∃ b ∈ U, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ Subgroup.zpowers a := fun x hx => hcon x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [hUcard, Nat.card_zpowers] at h1
    have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq a haU)
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ Subgroup.one_mem _)
  have hab : a ≠ b := fun h => hbz (h ▸ Subgroup.mem_zpowers a)
  set a' : ↥T := ⟨a, hUT haU⟩ with ha'
  set b' : ↥T := ⟨b, hUT hbU⟩ with hb'
  have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have ha'2 : a' ^ 2 = 1 := Subtype.ext (hsq a haU)
  have hb'2 : b' ^ 2 = 1 := Subtype.ext (hsq b hbU)
  have e1 : ι a' = QuaternionGroup.a (m : ZMod (2 * m)) :=
    eq_a_of_sq_eq_one (fun h => ha'1 (hι (h.trans (map_one ι).symm)))
      (by rw [← map_pow, ha'2, map_one])
  have e2 : ι b' = QuaternionGroup.a (m : ZMod (2 * m)) :=
    eq_a_of_sq_eq_one (fun h => hb'1 (hι (h.trans (map_one ι).symm)))
      (by rw [← map_pow, hb'2, map_one])
  exact hab (congrArg Subtype.val (hι (e1.trans e2.symm)))

end NoFour

section Central

variable {J : Type} [Group J] [Finite J]

theorem sq_mem_center_of_quaternion (hq : IsQuasisimple J) (hev : 2 ∣ Nat.card J)
    (T : Sylow 2 J) (hnc : ¬ IsCyclic ↥(T : Subgroup J)) {m : ℕ} [NeZero m]
    (ι : ↥(T : Subgroup J) →* QuaternionGroup m) (hι : Function.Injective ι)
    {u : ↥(T : Subgroup J)}
    (hu : ι u ∉ Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup m)) :
    (u : J) ^ 2 ∈ Subgroup.center J := by
  rcases l31_isCyclic_or_isQuat_of_no_four T.isPGroup' (not_exists_four_of_quaternion ι hι) with
    hc | ⟨n, hn3, ⟨e⟩⟩
  · exact absurd hc hnc
  ·
    have hmne : ¬ QuaternionGroup.a (m : ZMod (2 * m)) = 1 := fun h =>
      zmod_natCast_ne_zero (by
        rw [QuaternionGroup.one_def] at h
        exact (QuaternionGroup.a.injEq _ _).mp h)
    obtain ⟨j, hj⟩ : ∃ j, ι u = QuaternionGroup.xa j := by
      cases hu' : ι u with
      | a j => exact absurd (by rw [hu']; exact (mem_zpowers_a_one_iff _).2 ⟨j, rfl⟩) hu
      | xa j => exact ⟨j, rfl⟩
    have hsq : ι (u ^ 2) = QuaternionGroup.a (m : ZMod (2 * m)) := by
      rw [map_pow, hj, QuaternionGroup.xa_sq]
    have h4 : u ^ 4 = 1 := hι (by rw [map_pow, hj, QuaternionGroup.xa_pow_four, map_one])
    have hu21 : u ^ 2 ≠ 1 := fun h => hmne (by rw [← hsq, h, map_one])
    set t : J := (u : J) ^ 2 with ht
    have htT : t ∈ (T : Subgroup J) := T.pow_mem u.2 2
    have ht2 : orderOf t = 2 := by
      have h42 : t ^ 2 = 1 := by
        rw [ht, ← pow_mul]
        exact congrArg Subtype.val h4
      have ht1 : t ≠ 1 := fun h => hu21 (Subtype.ext h)
      exact orderOf_eq_prime h42 ht1
    have hbs := CFSG.BrauerSuzuki.brauer_suzuki n hn3 T ⟨e⟩ t htT ht2
    have hA : CFSG.oddCore J ≤ Subgroup.center J := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (CFSG.oddCore_normal (G := J)) with
        h | h
      · exfalso
        have hodd : Odd (Nat.card (CFSG.oddCore J)) := CFSG.ABGDGroups.odd_card_oddCore J
        rw [h, Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hev)
      · exact h
    have hcen := (CFSG.LocalCores.quasisimple_central_quotient hq (CFSG.oddCore J) hA).2.2
    rw [hcen] at hbs
    obtain ⟨c, hc, hct⟩ := hbs
    have h1 : c⁻¹ * t ∈ CFSG.oddCore J := QuotientGroup.eq.mp hct
    have h2 : t = c * (c⁻¹ * t) := by group
    rw [h2]
    exact Subgroup.mul_mem _ hc (hA h1)

end Central

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2
