module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaStep1A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaStep1B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverModel
import CFSG.ClassicalInvolution.Balance.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82FactOutZeta6_of_zetaInv (hS : Asc82SchurU43) (hζ : Asc82FactZetaInv6) :
    Asc82FactOutZeta6 := by
  intro G _ _ L hL y₁ c hy₁N hcN hyType hc1 hc2 hcent
  obtain ⟨α, V, i1, i2, i3, Q, hQ, e, x, hdim, hs, hy₁ind, hxType⟩ := hyType
  letI := i1
  letI := i2
  letI := i3
  obtain ⟨φ, hcov, he⟩ := t5_cover_of_model hS hL hdim hs e
  let h6 : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) :=
    Or.inr ⟨hdim, Or.inr hs⟩
  have hperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  obtain ⟨y, hxy, hyType⟩ := hxType
  obtain ⟨-, t, htt, htType, htProj⟩ := hyType
  have ht1 : invDim t = 1 := congrArg Prod.fst htType
  have hx1 : x = projOrthToProjSim Q (toProj Q t) := by
    rw [← hxy, ← htProj]
  let cN : ↥(Subgroup.normalizer (L : Set G)) := ⟨c, hcN⟩
  let yN : ↥(Subgroup.normalizer (L : Set G)) := ⟨y₁, hy₁N⟩
  let cYN : ↥(Subgroup.normalizer (L : Set G)) := ⟨c * y₁, mul_mem hcN hy₁N⟩
  let ccN : ↥(Subgroup.normalizer (L : Set G)) := ⟨c * c, mul_mem hcN hcN⟩
  let cYCN : ↥(Subgroup.normalizer (L : Set G)) :=
    ⟨(c * y₁) * (c * y₁), mul_mem (mul_mem hcN hy₁N) (mul_mem hcN hy₁N)⟩
  let z : ProjSim Q := ffTheta hQ h6 e cN
  have hθc : ffTheta hQ h6 e cN = z := rfl
  have hθy : ffTheta hQ h6 e yN = x :=
    (ffTheta_eq_iff hQ h6 e yN x).mpr hy₁ind
  have hθcy : ffTheta hQ h6 e cYN = z * projOrthToProjSim Q (toProj Q t) := by
    have hcYN : cYN = cN * yN := Subtype.ext rfl
    rw [hcYN, map_mul, hθc, hθy, hx1]
  have hθcc : ffTheta hQ h6 e ccN = z ^ 2 := by
    have hccN : ccN = cN * cN := Subtype.ext rfl
    rw [hccN, map_mul, hθc, pow_two]
  have hθcycy :
      ffTheta hQ h6 e cYCN = (z * projOrthToProjSim Q (toProj Q t)) ^ 2 := by
    have hcYCN : cYCN = cYN * cYN := Subtype.ext rfl
    rw [hcYCN, map_mul, hθcy, pow_two]
  have hz : ¬ SimInOmegaStar hQ z := by
    intro h
    rw [← hθc] at h
    exact hc1 (fg_oz_mem_sup_of_theta hQ h6 e hperf cN h)
  have hzt : ¬ SimInOmegaStar hQ (z * projOrthToProjSim Q (toProj Q t)) := by
    intro h
    rw [← hθcy] at h
    exact hc2 (fg_oz_mem_sup_of_theta hQ h6 e hperf cYN h)
  have key : ∀ (w : G) (hw : w ∈ Subgroup.normalizer (L : Set G)),
      (∀ x ∈ oddCoreIn L, w * x = x * w) →
      FGOZIsZeta hQ (ffTheta hQ h6 e ⟨w, hw⟩) → oddCoreIn L = ⊥ := by
    intro w hw hcomm hZeta
    let wN : ↥(Subgroup.normalizer (L : Set G)) := ⟨w, hw⟩
    obtain ⟨o, hθeq, hdet, hsn⟩ := hZeta
    have hInd : InducesViaP L (Subgroup.center ↥L) hQ e w
        (projOrthToProjSim Q (toProj Q o)) :=
      (ffTheta_eq_iff hQ h6 e wN _).mp hθeq
    have hact : CoverAct L φ w (orthToSim Q o) :=
      t5_coverAct_of_inducesViaP hL hcov he hInd rfl
    have hinv : ∀ x ∈ oddCoreIn L, w * x * w⁻¹ = x⁻¹ :=
      hζ G L hL φ hcov w o hact hdet hsn
    have hOddO : Odd (Nat.card (oddCoreIn L)) :=
      CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn L
    refine (Subgroup.eq_bot_iff_forall (H := oddCoreIn L)).mpr (fun x hx => ?_)
    have h1 := hinv x hx
    have h2 : w * x * w⁻¹ = x := by
      rw [hcomm x hx]
      group
    have hxinv : x = x⁻¹ := h2.symm.trans h1
    have hx2 : x * x = 1 := (eq_inv_iff_mul_eq_one).mp hxinv
    have hxord : orderOf x ∣ Nat.card (oddCoreIn L) :=
      Subgroup.orderOf_dvd_natCard (oddCoreIn L) hx
    have hxodd : Odd (orderOf x) := hOddO.of_dvd_nat hxord
    have hx2dvd : orderOf x ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hx2
    have hx1dvd : orderOf x ∣ 1 := by
      rw [show (2 : ℕ) = 2 * 1 by norm_num] at hx2dvd
      exact hxodd.coprime_two_right.dvd_of_dvd_mul_left hx2dvd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hx1dvd)
  have hcommC : ∀ x ∈ oddCoreIn L, c * x = x * c := fun x hx => (hcent x hx).2
  have hcommCY : ∀ x ∈ oddCoreIn L, (c * y₁) * x = x * (c * y₁) := by
    intro x hx
    obtain ⟨hy, hc⟩ := hcent x hx
    calc (c * y₁) * x = c * (y₁ * x) := by rw [mul_assoc]
      _ = c * (x * y₁) := by rw [hy]
      _ = (c * x) * y₁ := by rw [← mul_assoc]
      _ = (x * c) * y₁ := by rw [hc]
      _ = x * (c * y₁) := by rw [mul_assoc]
  have hcommCC : ∀ x ∈ oddCoreIn L, (c * c) * x = x * (c * c) := by
    intro x hx
    obtain ⟨-, hc⟩ := hcent x hx
    calc (c * c) * x = c * (c * x) := by rw [mul_assoc]
      _ = c * (x * c) := by rw [hc]
      _ = (c * x) * c := by rw [← mul_assoc]
      _ = (x * c) * c := by rw [hc]
      _ = x * (c * c) := by rw [mul_assoc]
  have hcommCYCY : ∀ x ∈ oddCoreIn L,
      ((c * y₁) * (c * y₁)) * x = x * ((c * y₁) * (c * y₁)) := by
    intro x hx
    have hw := hcommCY x hx
    calc ((c * y₁) * (c * y₁)) * x = (c * y₁) * ((c * y₁) * x) := by rw [mul_assoc]
      _ = (c * y₁) * (x * (c * y₁)) := by rw [hw]
      _ = ((c * y₁) * x) * (c * y₁) := by rw [← mul_assoc]
      _ = (x * (c * y₁)) * (c * y₁) := by rw [hw]
      _ = x * ((c * y₁) * (c * y₁)) := by rw [mul_assoc]
  rcases fg_oz_core hQ htt ht1 hz hzt with h | h | h | h
  · exact key c hcN hcommC (by rwa [hθc])
  · exact key (c * y₁) (mul_mem hcN hy₁N) hcommCY (by rwa [hθcy])
  · exact key (c * c) (mul_mem hcN hcN) hcommCC (by rwa [hθcc])
  · exact key ((c * y₁) * (c * y₁)) (mul_mem (mul_mem hcN hy₁N) (mul_mem hcN hy₁N))
      hcommCYCY (by rwa [hθcycy])

end CFSG.OddStandard.SmallF3.Omega
