module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll
import CFSG.LocalAnalysis.GLTheoremA.PartI.I112Ctx
import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
import CFSG.Adapters.LinearCatalogStated
import CFSG.Open.StatedCenterThree
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance

private theorem l227_ordA : CFSG.Open.ordA 1 27 = 9828 := by decide +kernel

theorem card_of_catalogIs_L227 {S : Type} [Group S] (h : catalogIs S (onLie (isL2 27))) :
    Nat.card S = 9828 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hv⟩⟩ | s
  · exact hi.elim
  · exact hi.elim
  · rcases d with ⟨r, q⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
      try exact hi.elim
    rcases r with _ | _ | r
    · exact hi.elim
    · have hq : q.card = 27 := hi
      have hp2 : q.p ≠ 2 := by
        intro h2
        have h2d : 2 ∣ q.card := by
          rw [TauCeti.PrimePower.card_def, h2]
          exact dvd_pow_self 2 q.exponent_pos.ne'
        rw [hq] at h2d
        omega
      have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
      have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hm).1 rfl
      rw [hc]
      have : q.p ^ q.exponent = 27 := (TauCeti.PrimePower.card_def q).symm.trans hq
      rw [this]
      exact l227_ordA
    · exact hi.elim
  · exact hi.elim

private theorem l227_card_eq_mul_center (Y : Type) [Group Y] :
    Nat.card Y = Nat.card (Y ⧸ Subgroup.center Y) * Nat.card (Subgroup.center Y) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)

private theorem l227_not_isHatSix {Y : Type} [Group Y]
    (h : Nat.card (Y ⧸ Subgroup.center Y) = 9828) : ¬ IsHatSix Y := by
  rintro ⟨-, -, ⟨e⟩⟩
  have := Nat.card_congr e.toEquiv
  rw [h, Nat.card_eq_fintype_card, card_alternatingGroup] at this
  simp [Nat.factorial] at this

private theorem l227_not_isHatSeven {Y : Type} [Group Y]
    (h : Nat.card (Y ⧸ Subgroup.center Y) = 9828) : ¬ IsHatSeven Y := by
  rintro ⟨-, -, ⟨e⟩⟩
  have := Nat.card_congr e.toEquiv
  rw [h, Nat.card_eq_fintype_card, card_alternatingGroup] at this
  simp [Nat.factorial] at this

private theorem l227_card_m22 : Nat.card TauCeti.SporadicName.M22.Group = 443520 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M22.tauCeti_finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M22.le_card_native
  rw [Nat.card_congr e.toEquiv] at h2
  omega

private theorem l227_not_isHatMTwentyTwo {Y : Type} [Group Y]
    (h : Nat.card (Y ⧸ Subgroup.center Y) = 9828) : ¬ IsHatMTwentyTwo Y := by
  rintro ⟨-, -, ⟨e⟩⟩
  have := Nat.card_congr e.toEquiv
  have h22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520 :=
    l227_card_m22
  rw [h, h22] at this
  omega

private theorem l227_not_isSLThreeExc {Y : Type} [Group Y]
    (h : Nat.card (Y ⧸ Subgroup.center Y) = 9828) : ¬ IsSLThreeExc Y := by
  rintro ⟨F, hF, hfin, h9, ⟨e⟩⟩
  have h3 : 3 ∣ Nat.card F - 1 := by omega
  have hZ : Nat.card (Subgroup.center Y) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.Open.StatedCenterThree.card_center_statedSL_three h3
  have hY : Nat.card Y = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, mul_assoc]
  have key := l227_card_eq_mul_center Y
  rw [hY, h, hZ] at key
  have hq4 : 4 ≤ Nat.card F := by omega
  generalize Nat.card F = Q at key hq4
  have h1 : 64 ≤ Q ^ 3 := (show 64 = 4 ^ 3 by norm_num) ▸ Nat.pow_le_pow_left hq4 3
  have h2 : 16 ≤ Q ^ 2 := (show 16 = 4 ^ 2 by norm_num) ▸ Nat.pow_le_pow_left hq4 2
  have := Nat.mul_le_mul (Nat.mul_le_mul h1 (show 15 ≤ Q ^ 2 - 1 by omega))
    (show 63 ≤ Q ^ 3 - 1 by omega)
  omega

private theorem l227_not_isSUThreeExc {Y : Type} [Group Y]
    (h : Nat.card (Y ⧸ Subgroup.center Y) = 9828) : ¬ IsSUThreeExc Y := by
  rintro ⟨F, hF, hfin, q, hFq, hq9, ⟨e⟩⟩
  have h3 : 3 ∣ q + 1 := by omega
  have hZ : Nat.card (Subgroup.center Y) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.Open.StatedCenterThree.card_center_statedSU_three hFq h3
  have hY : Nat.card Y = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hFq
  have key := l227_card_eq_mul_center Y
  rw [hY, h, hZ] at key
  rcases (by omega : q = 2 ∨ 5 ≤ q) with rfl | hq5
  · norm_num at key
  · have h1 : 125 ≤ q ^ 3 := (show 125 = 5 ^ 3 by norm_num) ▸ Nat.pow_le_pow_left hq5 3
    have h2 : 25 ≤ q ^ 2 := (show 25 = 5 ^ 2 by norm_num) ▸ Nat.pow_le_pow_left hq5 2
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 (show 24 ≤ q ^ 2 - 1 by omega))
      (show 126 ≤ q ^ 3 + 1 by omega)
    omega

private theorem l227_not_isLTwoOddPow {Y : Type} [Group Y]
    (h : Nat.card (Y ⧸ Subgroup.center Y) = 9828) : ¬ IsLTwoOddPow Y := by
  intro hL
  have hc : Subgroup.center Y = ⊥ := (isL2TwoPowOdd_of_isLTwoOddPow hL).center_eq_bot
  obtain ⟨F, hF, hfin, n, hn, hn1, hcard, ⟨e⟩⟩ := hL
  have hY : Nat.card Y = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hcard]
  have hZ : Nat.card (Subgroup.center Y) = 1 := by
    rw [hc]
    exact Subgroup.card_bot
  have key := l227_card_eq_mul_center Y
  rw [hY, h, hZ] at key
  have h8 : 8 ∣ 2 ^ n := (show 8 = 2 ^ 3 by norm_num) ▸ pow_dvd_pow 2 (by omega : 3 ≤ n)
  have := Dvd.dvd.mul_right h8 ((2 ^ n) ^ 2 - 1)
  rw [key] at this
  omega

theorem not_isL227_of_weakExc {Y : Type} [Group Y]
    (h : catalogIs (Y ⧸ Subgroup.center Y) (onLie (isL2 27))) :
    ¬ (IsLTwoOddPow Y ∨ IsHatSix Y ∨ IsHatSeven Y ∨ IsHatMTwentyTwo Y ∨ IsSLThreeExc Y ∨
      IsSUThreeExc Y ∨ IsSUThreeTwoPow Y) := by
  have h9828 := card_of_catalogIs_L227 h
  rintro (h | h | h | h | h | h | h)
  · exact l227_not_isLTwoOddPow h9828 h
  · exact l227_not_isHatSix h9828 h
  · exact l227_not_isHatSeven h9828 h
  · exact l227_not_isHatMTwentyTwo h9828 h
  · exact l227_not_isSLThreeExc h9828 h
  · exact l227_not_isSUThreeExc h9828 h
  · exact l227_not_isSUThreeExc h9828 (isSUThreeExc_of_isSUThreeTwoPow h)


theorem i112L227At_holds
    {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hKP : CFSG.Open.IsKProper G) : I112L227At G := by
  intro X B L _ hBX hB hr hL hcat
  by_contra hnL
  obtain ⟨-, -, -, htype⟩ := i112c_types
    CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
    CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds
    hsimple hKP Nat.prime_three (by norm_num) hB hBX hr hL hnL
  exact not_isL227_of_weakExc (Y := barOf 3 L) hcat htype

end CFSG.LocalAnalysis.GLTheoremA
