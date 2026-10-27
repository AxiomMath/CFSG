module

public import CFSG.GH74.Generic.BProg.B3.LocBalL3Lin
public import CFSG.GH74.Generic.BProg.B3.LocBalL3Uni
public import CFSG.GH74.Generic.BProg.B1.Stage3aRank
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.GH74.Generic.JMaxShapes

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg Subgroup

namespace LocBalL3

theorem modelData_of_qShape3 {Kt : Type} [Group Kt] (hK : QShape3 Kt) :
    LocBalL3Abs.ModelData Kt := by
  obtain ⟨p, f, hp, hp2, hq, hmod⟩ := hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hmod with hL | hU
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
    have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq hp hp2 hF
    have h2 : (2 : F) ≠ 0 := fun h0 => hF2 (by
      have : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h0)
      exact ringChar.eq F 2)
    exact (LocBalL3Lin.modelData_projectiveSL h2 (by omega)).of_mulEquiv e.symm
  · obtain ⟨-, -, F, _, _, hF, ⟨e₀⟩⟩ := lieModel_psu_data hU
    have hUF : UnitaryFieldData p f F := B2.GenLocDiagU.unitaryFieldData_of_card hp hF
    have : Fact p.Prime := ⟨hp⟩
    have := hUF.charP
    obtain ⟨θ, hθ⟩ := KGroups.L3Eps.Uni.exists_cover_of_equiv hUF e₀
    exact LocBalL3Uni.modelData_cover hUF hp2 h5 hodd hθ (isSimpleGroup_of_lieModel_L3' (Or.inr hU))
      (S3.SingleInv.of_mulEquiv e₀.symm (S3.singleInv_psu hUF hp2))

end LocBalL3

theorem locBal32_L3_gen {Kt : Type} [Group Kt] [Finite Kt] (hK : QShape3 Kt) (B : Subgroup Kt)
    (hB : ∀ b ∈ B, b * b = 1) : IsLocBal32 Kt (B.map (MulAut.conj : Kt →* MulAut Kt)) := by
  refine LocBalL3Abs.locBal32_of_modelData (LocBalL3.modelData_of_qShape3 hK) ?_ B hB
  intro E E' hE2 hE4 hE2' hE4'
  have hel : ∀ {U : Subgroup Kt}, (∀ e ∈ U, e * e = 1) → CFSG.IsElementaryAbelian 2 ↥U := by
    intro U hU
    refine B2.WeakSigGen.isElementaryAbelian_of_forall (fun a ha b hb => ?_) hU
    have h1 := hU _ (U.mul_mem ha hb)
    have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hU a ha)
    have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hU b hb)
    have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
    calc a * b = (a * b)⁻¹ := e3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [e1, e2]
  exact B2.FixFourS3.fourConj_shape3 Kt hK E E' (hel hE2) hE4 (hel hE2') hE4'

theorem locBal32_L3_inner {L : Type} [Group L] [Finite L] (hL : B1.QShape3SD L) (B : Subgroup L)
    (hB : ∀ b ∈ B, b * b = 1) : IsLocBal32 L (B.map (MulAut.conj : L →* MulAut L)) :=
  locBal32_L3_gen hL.qShape3 B hB

end CFSG.GH74.Generic.BProg.B3
