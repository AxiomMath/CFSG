module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensus
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ConstrainedGen
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeRk

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Th CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

section Z


theorem card_centralizer_zJ_dvd :
    Nat.card (Subgroup.centralizer ({ThCent.zJ} : Set ↥CFSG.Sporadic.Th.J)) ∣ 2 ^ 3 * 3 ^ 10 := by
  haveI : Finite ↥CFSG.Sporadic.Th.J := finite_J
  obtain ⟨Q, hQ, -, hz3, hQz, ⟨u, hu, huz⟩, -⟩ := Certificates.certificate13650
  set C := Subgroup.centralizer ({ThCent.zJ} : Set ↥CFSG.Sporadic.Th.J) with hCdef
  have hle : Nat.card C ≤ 472392 := Certificates.certificate13651
  have hQC : Q ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hQz x hx)
  have h3 : 3 ^ 10 ∣ Nat.card C := hQ ▸ Subgroup.card_dvd_of_le hQC
  have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.2 huz
  have h2 : 2 ∣ Nat.card C := by
    have := Subgroup.orderOf_dvd_natCard C huC
    rwa [hu] at this
  have hJ : Nat.card C ∣ 90745943887872000 := by
    rw [← CFSG.Sporadic.Th.Max3.natCard_J]
    exact Subgroup.card_subgroup_dvd_card C
  have hpos : 0 < Nat.card C := Nat.card_pos
  obtain ⟨r, hr⟩ := h3
  have h59 : (3 : ℕ) ^ 10 = 59049 := by norm_num
  have hr8 : r ≤ 8 := by
    rw [hr, h59] at hle
    omega
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [hr, h0, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h0
  have hr2 : 2 ∣ r := by
    rw [hr] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h) (by norm_num)
    · exact h
  have hr3 : ¬ 3 ∣ r := by
    rintro ⟨r', rfl⟩
    rw [hr] at hJ
    have : 3 ^ 11 ∣ 90745943887872000 := (Dvd.intro r' (by ring)).trans hJ
    norm_num at this
  have hr' : r ∣ 8 := by
    interval_cases r <;> omega
  rw [hr, mul_comm (3 ^ 10), mul_comm (2 ^ 3)]
  exact Nat.mul_dvd_mul_right hr' _

end Z

section ShapeZ


theorem th_shape_Z : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) thZ := by
  unfold ShapeRkAt
  left
  have hz : orderOf thZ = 3 := th_orderOf.2.1
  have hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({thZ} : Set ↥CFSG.Sporadic.Th.J)) = ⊥ :=
    oPrimeCoreTrivialAt_Th_three_of_residual thThreeResidual_holds thZ hz
  haveI : Finite ↥CFSG.Sporadic.Th.J := finite_J
  exact pConstrainedShape_of_solvable Nat.prime_three
    (isSolvable_of_card_dvd_two_three card_centralizer_zJ_dvd) hO

end ShapeZ

end CFSG.HardMathSupport.Dickson.I271
