module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Quat

variable {G : Type} [Group G] [Finite G]

theorem sq_eq_of_mem_quat {K A : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) (hAK : A ≤ K)
    (h8 : Nat.card ↥A = 8) (hnc : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) {x : G} (hx : x ∈ A)
    (hx1 : x ≠ 1) (hxz : x ≠ z) : x * x = z := by
  have hdvd : orderOf x ∣ 8 := h8 ▸ Subgroup.orderOf_dvd_natCard A hx
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf x ∣ 2 ^ 3 by simpa using hdvd)
  interval_cases m
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using hm')) hx1
  · exfalso
    have h2 : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rw [hm'] at this
      simpa [pow_two] using this
    rcases hz.unique x (hAK hx) h2 with h | h
    · exact hx1 h
    · exact hxz h
  · exact Q3.PhilipHall.Frame.TwinPerp.sq_eq_of_orderOf_four hz (hAK hx) (by simpa using hm')
  · exfalso
    have hxo : orderOf x = 8 := by simpa using hm'
    have hle : Subgroup.zpowers x ≤ A := (Subgroup.zpowers_le).mpr hx
    have hcard : Nat.card ↥(Subgroup.zpowers x) = Nat.card ↥A := by
      rw [Nat.card_zpowers, hxo, h8]
    have heq : Subgroup.zpowers x = A := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    rw [← heq] at ha hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hab ((Commute.zpow_zpow_self x i j).eq)

end Quat

end CFSG.ClassicalInvolution.Q8P.Asc77
