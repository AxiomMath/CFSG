module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.KleinBound
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open Subgroup

private lemma card_le_25_of_isPGroup_five_dvd_100 {L : Type*} [Group L] [Finite L]
    (h5 : IsPGroup 5 L) (hdvd : Nat.card L ∣ 100) : Nat.card L ≤ 25 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨j, hj⟩ := h5.exists_card_eq
  rw [hj]
  have hdvd' : 5 ^ j ∣ 100 := by rwa [hj] at hdvd
  have hcop : Nat.Coprime (5 ^ j) 4 := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; simp
    · rw [Nat.coprime_pow_left_iff hjpos]; norm_num
  have h25 : 5 ^ j ∣ 25 := by
    apply hcop.dvd_of_dvd_mul_right
    rw [show (25 : ℕ) * 4 = 100 by norm_num]
    exact hdvd'
  exact Nat.le_of_dvd (by norm_num) h25

private lemma card_le_25_of_isPGroup_five_dvd_card_z {L : Type*} [Group L] [Finite L]
    (h5 : IsPGroup 5 L) (hdvd : Nat.card L ∣ 2 ^ 14 * 3 ^ 2 * 5 ^ 2) : Nat.card L ≤ 25 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨j, hj⟩ := h5.exists_card_eq
  rw [hj]
  have hdvd' : 5 ^ j ∣ 2 ^ 14 * 3 ^ 2 * 5 ^ 2 := by rwa [hj] at hdvd
  have hcop : Nat.Coprime (5 ^ j) (2 ^ 14 * 3 ^ 2) := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; simp
    · rw [Nat.coprime_pow_left_iff hjpos]; norm_num
  have h25 : 5 ^ j ∣ 25 := by
    apply hcop.dvd_of_dvd_mul_right
    rw [show (25 : ℕ) = 5 ^ 2 by norm_num, mul_comm]
    exact hdvd'
  exact Nat.le_of_dvd (by norm_num) h25

theorem five_odd_core_bound (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z z' : G}
    (h : IsF5Type a z) (hz' : IsConj z z') (haz' : IsConj z (a * z')) {ρ : G} (hρ : ρ ∈ Gx a)
    (h5 : orderOf ρ = 5) (hshape : IsShapeCentralizerFiveB ↥(Gxy a ρ)) (hz'ρ : z' ∈ Gxy a ρ)
    {N : Subgroup G} (hNK : N ≤ Gx ρ) (hNn : (N.subgroupOf (Gx ρ)).Normal) (hN5 : IsPGroup 5 ↥N)
    (hρN : ρ ∈ N) : Nat.card ↥N ≤ 5 ^ 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have haK : a ∈ Gx ρ := (mem_Gx (x := ρ) (g := a)).mpr (mem_Gx.mp hρ).symm
  have hz'K : z' ∈ Gx ρ := (mem_Gxy.mp hz'ρ).2
  have haz'_comm : a * z' = z' * a := mem_Gx.mp (mem_Gxy.mp hz'ρ).1
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rw [h.orderOf_a] at this
    simpa [pow_two] using this
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z] at this
  have hz'2 : z' * z' = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hz'
    have hpow : z' ^ 2 = 1 := by
      rw [← hc, conj_pow, hz2]
      simp
    simpa [pow_two] using hpow
  have hNa : ∀ x ∈ N, a * x * a⁻¹ ∈ N :=
    fun x hx => (normal_subgroupOf_iff hNK).mp hNn x a hx haK
  have hNz' : ∀ x ∈ N, z' * x * z'⁻¹ ∈ N :=
    fun x hx => (normal_subgroupOf_iff hNK).mp hNn x z' hx hz'K
  obtain ⟨n, hn⟩ := hN5.exists_card_eq
  have hNcard : Nat.card ↥N = 5 ^ n := hn
  have hodd : ¬ 2 ∣ Nat.card ↥N := by
    rw [hNcard]
    intro hd
    have h25 : 2 ∣ 5 := Nat.prime_two.dvd_of_dvd_pow hd
    norm_num at h25
  have hid := card_mul_sq_eq_prod_of_klein (G := G) hodd ha2 hz'2 haz'_comm hNa hNz'
  have hGxy_card : Nat.card ↥(Gxy a ρ) = 100 := by
    obtain ⟨e⟩ := hshape
    have he : Nat.card ↥(Gxy a ρ) =
        Nat.card (Multiplicative (ZMod 5) × Multiplicative (ZMod 2) × DihedralGroup 5) :=
      Nat.card_congr e.toEquiv
    rw [he]
    have hZ5 : Nat.card (Multiplicative (ZMod 5)) = 5 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hZ2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hD5 : Nat.card (DihedralGroup 5) = 10 := DihedralGroup.nat_card (n := 5)
    rw [Nat.card_prod, Nat.card_prod, hZ5, hZ2, hD5]
  have hcard_z : Nat.card ↥(Gx z) = 2 ^ 9 * 7200 := card_centralizer_z_of_isF5Type h
  have hcard_z' : Nat.card ↥(Gx z') = 2 ^ 14 * 3 ^ 2 * 5 ^ 2 := by
    rw [← card_centralizer_eq_of_isConj hz', hcard_z]
    norm_num
  have hcard_az' : Nat.card ↥(Gx (a * z')) = 2 ^ 14 * 3 ^ 2 * 5 ^ 2 := by
    rw [← card_centralizer_eq_of_isConj haz', hcard_z]
    norm_num
  have hA25 : Nat.card ↥(N ⊓ Gx a) ≤ 25 := by
    refine card_le_25_of_isPGroup_five_dvd_100 ?_ ?_
    · exact IsPGroup.of_card_dvd_pow (n := n) (by
        rw [← hNcard]
        exact Subgroup.card_dvd_of_le inf_le_left)
    · have h : Nat.card ↥(N ⊓ Gx a) ∣ Nat.card ↥(Gxy a ρ) :=
        Subgroup.card_dvd_of_le (by
          intro x hx
          obtain ⟨hxN, hxa⟩ := Subgroup.mem_inf.mp hx
          rw [mem_Gxy]
          exact ⟨hxa, hNK hxN⟩)
      rwa [hGxy_card] at h
  have hZ25 : Nat.card ↥(N ⊓ Gx z') ≤ 25 := by
    refine card_le_25_of_isPGroup_five_dvd_card_z ?_ ?_
    · exact IsPGroup.of_card_dvd_pow (n := n) (by
        rw [← hNcard]
        exact Subgroup.card_dvd_of_le inf_le_left)
    · have h : Nat.card ↥(N ⊓ Gx z') ∣ Nat.card ↥(Gx z') :=
        Subgroup.card_dvd_of_le inf_le_right
      rwa [hcard_z'] at h
  have hAZ25 : Nat.card ↥(N ⊓ Gx (a * z')) ≤ 25 := by
    refine card_le_25_of_isPGroup_five_dvd_card_z ?_ ?_
    · exact IsPGroup.of_card_dvd_pow (n := n) (by
        rw [← hNcard]
        exact Subgroup.card_dvd_of_le inf_le_left)
    · have h : Nat.card ↥(N ⊓ Gx (a * z')) ∣ Nat.card ↥(Gx (a * z')) :=
        Subgroup.card_dvd_of_le inf_le_right
      rwa [hcard_az'] at h
  have hρmem : ρ ∈ N ⊓ Gxy a z' := by
    refine Subgroup.mem_inf.mpr ⟨hρN, ?_⟩
    rw [mem_Gxy]
    exact ⟨hρ, (mem_Gx (x := z') (g := ρ)).mpr (mem_Gx.mp (mem_Gxy.mp hz'ρ).2).symm⟩
  have hCge5 : 5 ≤ Nat.card ↥(N ⊓ Gxy a z') := by
    have := Subgroup.orderOf_le_card (N ⊓ Gxy a z') (Set.toFinite _) hρmem
    rwa [h5] at this
  have hC25 : 25 ≤ Nat.card ↥(N ⊓ Gxy a z') ^ 2 := by
    have h := Nat.mul_le_mul hCge5 hCge5
    simpa [pow_two] using h
  have hmain : Nat.card ↥N * 25 ≤ 25 * 625 := by
    calc Nat.card ↥N * 25
        ≤ Nat.card ↥N * Nat.card ↥(N ⊓ Gxy a z') ^ 2 := Nat.mul_le_mul_left _ hC25
      _ = Nat.card ↥(N ⊓ Gx a) * Nat.card ↥(N ⊓ Gx z') *
            Nat.card ↥(N ⊓ Gx (a * z')) := hid
      _ ≤ 25 * 25 * 25 := Nat.mul_le_mul (Nat.mul_le_mul hA25 hZ25) hAZ25
      _ = 25 * 625 := by norm_num
  have hN625 : Nat.card ↥N ≤ 625 := by omega
  rwa [show (5 : ℕ) ^ 4 = 625 by norm_num]

end CFSG.EvenSporadicStandard.HNRecog.Section3
