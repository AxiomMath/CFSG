module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocGL2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3.TA3
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open scoped MatrixGroups

theorem socleCyc4_l3 {F : Type} [Group F] [Finite F] (h : SmallL3Ne3 F) : SocleCyc4 F := by
  obtain ⟨p, f, hp, hp2, hf, h3, -, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  obtain ⟨hodd, h5⟩ := Q5L5U5.five_le hp hp2 hf h3
  have hK' : Odd (Nat.card K) := by
    rw [hK]
    exact hodd
  have hF₀ : ringChar K ≠ 2 := CFSG.GH74.Generic.S3.ringChar_ne_two_of_card_pow hp hp2 hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    omega
  let e0 : F ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 K))
  intro z hz
  let e' : ↥(⊤ : Subgroup F) ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    Subgroup.topEquiv.trans e0
  obtain ⟨-, π, hπr, hk, -⟩ := Q5L3.exists_frame hK' e' (Subgroup.mem_top z) hz
  have hrange : π.range = Subgroup.centralizer ({z} : Set F) := by
    rw [hπr, top_inf_eq]
  exact socleCyc4_of_gl2 hz π hrange hk Q5L3.slCentScalar_top hF₀ h4 Q5L3.slPartTopEquiv

theorem socleCyc4_u3 {F : Type} [Group F] [Finite F] (h : SmallU3Ne3 F) : SocleCyc4 F := by
  obtain ⟨p, f, hp, hp2, hf, h3, -, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  obtain ⟨-, h5⟩ := Q5L5U5.five_le hp hp2 hf h3
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := hU.charP
  have hcardF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) = p ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield hK
  have hF₀ : ringChar (CFSG.LieType.Steinberg.fixedSubfield K p f) ≠ 2 :=
    CFSG.GH74.Generic.S3.ringChar_ne_two_of_card_pow hp hp2 hcardF
  have h4 : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) := by
    rw [hcardF]
    omega
  obtain ⟨eJ⟩ := Q5U3.nonempty_slPart_equiv hU
  intro z hz
  let e' : ↥(⊤ : Subgroup F) ≃* StatedProj (StatedSU 3 (p ^ f) K) :=
    Subgroup.topEquiv.trans e
  obtain ⟨π, hπr, hk, -⟩ := Q5U3.exists_frame hU hp2 e' (Subgroup.mem_top z) hz
  have hrange : π.range = Subgroup.centralizer ({z} : Set F) := by
    rw [hπr, top_inf_eq]
  exact socleCyc4_of_gl2 hz π hrange hk (Q5U3.slCentScalar_GU2 hU) hF₀ h4 eJ

end CFSG.CGT.PushingUpLit.SolKNA.R4
