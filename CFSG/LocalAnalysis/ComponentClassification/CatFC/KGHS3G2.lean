module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ClassicalLift
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenRep
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley



open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.RankTwo CFSG.RankThree.PartOne.SEITZ11.G2Seven in
theorem rep7_injective_of_simple (k : Type) [Field k] [Finite k]
    (hs : IsSimpleGroup ↥(adjointGroup Tag.G2 k)) :
    Function.Injective (CFSG.RankThree.PartOne.SEITZ11.G2Seven.rep7 k) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hs.eq_bot_or_eq_top_of_normal (rep7 k).ker with h | h
  · exact h
  · exfalso
    have hx : xPar (rootOperatorFamily .G2) (g2CommRoot 0) (1 : k) ∈ (rep7 k).ker :=
      h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hx
    have h1 := rep7_xPar_pos k (a := 0) (by norm_num) (1 : k)
    rw [hx, Units.val_one] at h1
    have h21 := congrFun (congrFun h1 2) 1
    simp [rootMat, opMat, opMatSq, entMat, ent7, ent7sq] at h21

theorem no_hsType_chevalley_G2 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) {p f : ℕ}
    (hp3 : p ≠ 3) (hM : ChevalleyExceptionalModel S .G2 p f) (K : Subgroup S)
    (hK : HSType ↥K) : False := by
  obtain ⟨hadm, K', _, _, hcard, ⟨e⟩⟩ := hM
  obtain ⟨hp, hf, -⟩ := hadm
  haveI := hS
  have hcen : Subgroup.center ↥(adjointGroup Tag.G2 K') = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have e1 : ↥(adjointGroup Tag.G2 K') ⧸ Subgroup.center ↥(adjointGroup Tag.G2 K') ≃*
      ↥(adjointGroup Tag.G2 K') :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hsA : IsSimpleGroup ↥(adjointGroup Tag.G2 K') := (e.trans e1).symm.isSimpleGroup
  obtain ⟨Yh, hYh⟩ := exists_hsType_of_quotient (Subgroup.center ↥(adjointGroup Tag.G2 K'))
    le_rfl e K hK
  have hinj : Function.Injective
      ((CFSG.RankThree.PartOne.SEITZ11.G2Seven.rep7 K').comp Yh.subtype) :=
    (rep7_injective_of_simple K' hsA).comp Yh.subtype_injective
  have hHS := hsType_range_of_injective _ hinj hYh
  have hchar : ringChar K' = p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hcard
  exact no_hsType_card_lt_eight (F := K') (ι := Fin 7) (by rw [hchar]; exact hp3) (by simp)
    ((CFSG.RankThree.PartOne.SEITZ11.G2Seven.rep7 K').comp Yh.subtype).range hHS

end CFSG.ComponentClassification.CatFC.KGHS3
