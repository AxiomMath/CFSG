module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.CardSq
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Qz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem oddInv_natCard_Z (n : ℕ) [NeZero n] : Nat.card (Z n) = n := by
  rw [Nat.card_congr (Multiplicative.toAdd : Z n ≃ ZMod n), Nat.card_zmod]

private theorem oddInv_card_of_isShapeZpTimesA5_three {X : Type*} [Group X]
    (h : IsShapeZpTimesA5 3 X) : Nat.card X = 180 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, oddInv_natCard_Z, nat_card_alternatingGroup,
    Nat.card_fin]
  norm_num

theorem oddInv_three_plus {G : Type} [Group G] {a z : G} (hSGz : StructGzFacts a z)
    (σ : ↥(Gx z)) (h3 : orderOf σ = 3) (hcard : Nat.card ↥(CbarCent z σ) = 18) :
    IsPlusExtraspecial 2 (Qz z ⊓ Gx (σ : G)) := by
  rcases hSGz.three.1 σ h3 with ⟨hA5, -⟩ | ⟨-, hplus⟩
  · have h180 := oddInv_card_of_isShapeZpTimesA5_three hA5
    rw [hcard] at h180
    norm_num at h180
  · exact hplus

theorem oddInv_three_card {G : Type} [Group G] [Finite G] {a z x : G} (h : IsF5Type a z)
    (hx : IsConj a x) (haz : a ∈ Gx z) (hnc : ¬ IsConj a (a * z))
    (hT : IsPlusExtraspecial 2 (Qz z ⊓ Gx (a * x))) :
    8 ≤ Nat.card ↥(Qz z ⊓ Gx (a * x) ⊓ Gx a) := by
  have ha2 : a ^ 2 = 1 := by
    rw [← h.orderOf_a]
    exact pow_orderOf_eq_one a
  have hz2 : z ^ 2 = 1 := by
    rw [← h.orderOf_z]
    exact pow_orderOf_eq_one z
  have hx2 : x ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hx
    rw [← hc, conj_pow, ha2]
    group
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha2)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx2)
  have hza : z * a = a * z := mem_Gx.mp haz
  have hle := oddInv_card_le_sq (Qz z ⊓ Gx (a * x)) ha2 hz2 ?_ ?_ ?_
  · have hcard : Nat.card ↥(Qz z ⊓ Gx (a * x)) = 32 := by
      have h32 := hT.2.1
      norm_num at h32
      exact h32
    have hdvd : Nat.card ↥(Qz z ⊓ Gx (a * x) ⊓ Gx a) ∣ 32 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rw [hcard] at hle
    generalize Nat.card ↥(Qz z ⊓ Gx (a * x) ⊓ Gx a) = n at hle hdvd ⊢
    have hn32 : n ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n <;> first | omega | norm_num at hle hdvd ⊢
  ·
    intro u hu
    obtain ⟨huQ, huc⟩ := Subgroup.mem_inf.mp hu
    refine Subgroup.mem_inf.mpr ⟨gzNo_conj_mem_Qz haz huQ, ?_⟩
    have huc' : a * x * u = u * (a * x) := mem_Gx.mp huc
    have hxa : x * a * u = u * (x * a) := by
      have h1 : (a * x)⁻¹ * u = u * (a * x)⁻¹ := by
        calc (a * x)⁻¹ * u = (a * x)⁻¹ * (u * (a * x)) * (a * x)⁻¹ := by group
          _ = (a * x)⁻¹ * (a * x * u) * (a * x)⁻¹ := by rw [huc']
          _ = u * (a * x)⁻¹ := by group
      rwa [mul_inv_rev, hxinv, hainv] at h1
    rw [mem_Gx]
    calc a * x * (a * u * a⁻¹) = a * (x * a * u) * a⁻¹ := by group
      _ = a * (u * (x * a)) * a⁻¹ := by rw [hxa]
      _ = a * u * a⁻¹ * (a * x) := by group
  ·
    intro u hu
    exact (gzNo_mem_zpowers_iff h.orderOf_z).mp
      (gzNo_sq_mem_zpowers h (Subgroup.mem_inf.mp hu).1)
  ·
    intro u _ heq
    apply hnc
    have h1 : a * u = u * z * a := by
      calc a * u = a * u * a⁻¹ * a := by group
        _ = u * z * a := by rw [heq]
    refine isConj_iff.mpr ⟨u⁻¹, ?_⟩
    calc u⁻¹ * a * u⁻¹⁻¹ = u⁻¹ * (a * u) := by group
      _ = u⁻¹ * (u * z * a) := by rw [h1]
      _ = z * a := by group
      _ = a * z := hza

end CFSG.EvenSporadicStandard.HNRecog.Section3
