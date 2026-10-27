module

public import CFSG.GH74.Generic.BProg.B3.S1IdentSl2
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalSl2

open CFSG Subgroup
open scoped MatrixGroups

theorem eq_one_of_sq_of_mem_odd {X : Type} [Group X] (N : Subgroup X) (hN : Odd (Nat.card N))
    {x : X} (hx : x ∈ N) (hx2 : x * x = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : ↥N) ∣ Nat.card ↥N := orderOf_dvd_natCard _
  have h2 : orderOf (⟨x, hx⟩ : ↥N) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [pow_two] using hx2
  have h3 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hN.coprime_two_right] at h3
  have := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  exact congrArg Subtype.val this

theorem eq_one_of_pow_two_pow_of_mem_odd {X : Type} [Group X] (N : Subgroup X)
    (hN : Odd (Nat.card N)) {x : X} (hx : x ∈ N) (k : ℕ) (hxk : x ^ (2 ^ k) = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : ↥N) ∣ Nat.card ↥N := orderOf_dvd_natCard _
  have h2 : orderOf (⟨x, hx⟩ : ↥N) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hxk
  have h3 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k hN.coprime_two_right)] at h3
  have := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  exact congrArg Subtype.val this

theorem eq_one_of_central_of_simple {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hn : ∃ a b : Y, a * b ≠ b * a) {z : Y} (hz : ∀ g : Y, g * z = z * g) : z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with hb | ht
  · have : z ∈ Subgroup.center Y := Subgroup.mem_center_iff.2 hz
    rw [hb] at this
    exact this
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    apply hab
    have : a ∈ Subgroup.center Y := by rw [ht]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem odd_card_of_no_involution {X : Type} [Group X] [Finite X] (N : Subgroup X)
    (h : ∀ x ∈ N, x * x = 1 → x = 1) : Odd (Nat.card N) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card N := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2
  have hz2 : (z : X) * z = 1 := by
    have := pow_orderOf_eq_one (z : X)
    rwa [Subgroup.orderOf_coe, hz, pow_two] at this
  have hz1 : z = 1 := Subtype.ext (h z z.2 hz2)
  rw [hz1, orderOf_one] at hz
  omega

theorem sq_eq_one_of_mem_center {F : Type} [CommRing F] {x : SL(2, F)}
    (hx : x ∈ Subgroup.center SL(2, F)) : x ^ 2 = 1 := by
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow, hr, map_one]
  rfl

theorem normal_odd_le_ker {H : Type} [Group H] {F : Type} [Field F] [Fintype F]
    (hodd : Odd (Fintype.card F)) (hF : 5 ≤ Fintype.card F) (θ : H →* SL(2, F))
    (hθ : Function.Surjective θ) (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N)) :
    N ≤ θ.ker := by
  classical
  have hk : ringChar F ≠ 2 := S1IdentSl2.ringChar_ne_two hodd
  have h4 : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ]; omega)
    exact ⟨t, ht⟩
  intro z hz
  have hn : (N.map θ).Normal := Subgroup.Normal.map inferInstance θ hθ
  have hqs : CFSG.IsQuasisimple SL(2, F) := CFSG.RankThree.Classical.isQuasisimple_SL2 h4
  have hord : ∀ w ∈ N, orderOf (θ w) ∣ Nat.card N := fun w hw =>
    (orderOf_map_dvd θ w).trans (by
      have := orderOf_dvd_natCard (⟨w, hw⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at this)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs hn with htop | hcen
  · exfalso
    have hm1 : (-1 : SL(2, F)) ∈ N.map θ := by rw [htop]; trivial
    obtain ⟨w, hw, hwθ⟩ := hm1
    have h3 : orderOf (θ w) = 2 := by
      rw [hwθ]
      exact (CFSG.LocalAnalysis.ComponentInitial.sl2_orderOf_eq_two_iff hk _).2 rfl
    have h5 := hord w hw
    rw [h3] at h5
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h5)
  · have hz' : θ z ∈ center SL(2, F) := hcen ⟨z, hz, rfl⟩
    have h2 : (θ z) ^ 2 = 1 := sq_eq_one_of_mem_center hz'
    have h5 := hord z hz
    have h6 : orderOf (θ z) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h7 := Nat.dvd_gcd h5 h6
    rw [Nat.Coprime.gcd_eq_one hN.coprime_two_right] at h7
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h7)

end S1FinalSl2

end CFSG.GH74.Generic.BProg.B3
