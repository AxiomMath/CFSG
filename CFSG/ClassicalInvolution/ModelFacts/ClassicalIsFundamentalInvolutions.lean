module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem false_of_two_commuting_involutions_sl2 {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {L : Type} [Group L] [Finite L]
    (e : L ⧸ classicalInvolutionOddCore L ≃* SL(2, F)) {a b : L} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b) : False := by
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have hnot : ∀ x : L, orderOf x = 2 → x ∉ classicalInvolutionOddCore L := fun x hx hxO => by
    have h1 := Subgroup.orderOf_dvd_natCard (classicalInvolutionOddCore L) hxO
    rw [hx] at h1
    obtain ⟨k, hk⟩ := hOodd
    omega
  have himg : ∀ x : L, orderOf x = 2 →
      e (QuotientGroup.mk' (classicalInvolutionOddCore L) x) = -1 := fun x hx => by
    refine (sl2_orderOf_eq_two_iff hodd _).mp ?_
    rw [MulEquiv.orderOf_eq]
    have hx2 : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx, pow_two] at this
    have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore L) x) ^ 2 = 1 := by
      rw [← map_pow, pow_two, hx2, map_one]
    have h2 : QuotientGroup.mk' (classicalInvolutionOddCore L) x ≠ 1 := fun h => hnot x hx (by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h)
    exact orderOf_eq_prime h1 h2
  have h1 := himg a ha
  have h2 := himg b hb
  have hq : QuotientGroup.mk' (classicalInvolutionOddCore L) a =
      QuotientGroup.mk' (classicalInvolutionOddCore L) b := e.injective (h1.trans h2.symm)
  have hmem : a⁻¹ * b ∈ classicalInvolutionOddCore L := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hq
    exact hq
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, pow_two] at this
  have hb2 : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb, pow_two] at this
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  rw [hainv] at hmem
  apply hnot (a * b) _ hmem
  have hsq : (a * b) ^ 2 = 1 := by
    calc (a * b) ^ 2 = a * b * (a * b) := pow_two _
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hne1 : a * b ≠ 1 := fun h => hne (by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rwa [inv_eq_of_mul_eq_one_right hb2] at this)
  exact orderOf_eq_prime hsq hne1

end CFSG.ClassicalInvolution.ModelFacts
