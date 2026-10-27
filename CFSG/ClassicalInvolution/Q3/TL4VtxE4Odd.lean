module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Model
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLeaves

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution

namespace Vtx

variable {Y : Type} [Group Y]

theorem conj_mem_centralizer_of_mk {t m : Y}
    (hm : (QuotientGroup.mk m : Y ⧸ Subgroup.center Y) ∈
      Subgroup.centralizer ({(QuotientGroup.mk t : Y ⧸ Subgroup.center Y)} : Set _))
    {x : Y} (hx : x ∈ Subgroup.centralizer ({t} : Set Y)) :
    m * x * m⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx hm ⊢
  have hz : t⁻¹ * (m * t * m⁻¹) ∈ Subgroup.center Y := by
    rw [← QuotientGroup.eq]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hm]
    group
  obtain ⟨z, hzZ, hw⟩ : ∃ z ∈ Subgroup.center Y, m * t * m⁻¹ = t * z :=
    ⟨_, hz, by group⟩
  have hyw : m * x * m⁻¹ * (t * z) = t * z * (m * x * m⁻¹) := by
    rw [← hw]
    calc m * x * m⁻¹ * (m * t * m⁻¹) = m * (x * t) * m⁻¹ := by group
      _ = m * (t * x) * m⁻¹ := by rw [hx]
      _ = m * t * m⁻¹ * (m * x * m⁻¹) := by group
  have hzc : m * x * m⁻¹ * z = z * (m * x * m⁻¹) := Subgroup.mem_center_iff.mp hzZ _
  calc m * x * m⁻¹ * t = m * x * m⁻¹ * (t * z) * z⁻¹ := by group
    _ = t * z * (m * x * m⁻¹) * z⁻¹ := by rw [hyw]
    _ = t * (z * (m * x * m⁻¹)) * z⁻¹ := by group
    _ = t * (m * x * m⁻¹ * z) * z⁻¹ := by rw [hzc]
    _ = t * (m * x * m⁻¹) := by group

variable [Finite Y]

theorem oddCent_le_center_of_mk {t : Y}
    (h : Balance.oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk t : Y ⧸ Subgroup.center Y)} : Set _)) = ⊥) :
    oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤ Subgroup.center Y := by
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  set X := Subgroup.centralizer ({(QuotientGroup.mk t : Y ⧸ Subgroup.center Y)} : Set _)
    with hXdef
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
  set S := (oddCoreImg C).map π with hS
  have hSX : S ≤ X := by
    rintro _ ⟨o, ho, rfl⟩
    have hoC := Subgroup.mem_centralizer_singleton_iff.mp (oddCoreImg_le C ho)
    rw [hXdef, Subgroup.mem_centralizer_singleton_iff]
    change QuotientGroup.mk o * QuotientGroup.mk t = QuotientGroup.mk t * QuotientGroup.mk o
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hoC]
  have hconj : ∀ m ∈ X, ∀ y ∈ S, m * y * m⁻¹ ∈ S := by
    rintro m hm _ ⟨o, ho, rfl⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective m
    have hmN : m ∈ Subgroup.normalizer (C : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => conj_mem_centralizer_of_mk hm hx, fun hx => ?_⟩
      have hm' : (QuotientGroup.mk m⁻¹ : Y ⧸ Subgroup.center Y) ∈ X := by
        rw [QuotientGroup.mk_inv]
        exact X.inv_mem hm
      have := conj_mem_centralizer_of_mk hm' hx
      rwa [inv_inv, show m⁻¹ * (m * x * m⁻¹) * m = x by group] at this
    exact ⟨m * o * m⁻¹, conj_mem_oddCoreImg hmN ho, by simp [hπ]⟩
  have hnorm : X ≤ Subgroup.normalizer (S : Set (Y ⧸ Subgroup.center Y)) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj m hm y, fun hy => ?_⟩
    have := hconj m⁻¹ (X.inv_mem hm) _ hy
    rwa [inv_inv, show m⁻¹ * (m * y * m⁻¹) * m = y by group] at this
  have hodd : Odd (Nat.card S) :=
    (odd_natCard_oddCoreImg C).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hle := Balance.le_oddCoreIn_of_normalizes hSX hnorm hodd
  rw [h] at hle
  intro o ho
  have h1 : π o ∈ S := ⟨o, ho, rfl⟩
  have h2 := hle h1
  rw [Subgroup.mem_bot] at h2
  exact (QuotientGroup.eq_one_iff o).mp h2

end Vtx

theorem secIdE4OddCent_proved : SecIdE4OddCent := by
  intro Y _ _ R S t hd hc hO2 _ hM
  have hs : IsSimpleGroup (Y ⧸ Subgroup.center Y) := Vtx.isSimpleGroup_of_exLie hM
  have hZM := Vtx.center_quot_center_eq_bot hs
  have htZ : t ∉ Subgroup.center Y := by
    intro htZ
    refine hO2 ⟨Subgroup.zpowers t, ⟨fun x hx g => ?_⟩, ?_, Subgroup.mem_zpowers t⟩
    · have hxZ : x ∈ Subgroup.center Y := Subgroup.zpowers_le.mpr htZ hx
      rw [Subgroup.mem_center_iff.mp hxZ g, mul_inv_cancel_right]
      exact hx
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order, pow_one])
  have ht : orderOf (QuotientGroup.mk t : Y ⧸ Subgroup.center Y) = 2 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← hd.order, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      exact htZ ((QuotientGroup.eq_one_iff t).mp h1)
  have hle := Vtx.oddCent_le_center_of_mk (Vtx.oddCoreIn_centralizer_eq_bot_of_exLie hM hZM ht)
  have hnormal : (oddCoreImg (Subgroup.centralizer ({t} : Set Y))).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_center_iff.mp (hle hx) g, mul_inv_cancel_right]
      exact hx⟩
  have hO : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤ classicalInvolutionOddCore Y :=
    le_sSup ⟨hnormal, odd_natCard_oddCoreImg _⟩
  have hY : classicalInvolutionOddCore Y = ⊥ := hc.2.2
  rw [hY] at hO
  exact le_bot_iff.mp hO

end CFSG.ClassicalInvolution.Q3.TL4
