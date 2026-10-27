module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10TwE6
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10G2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10F4
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Ree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Tri
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LieType.Simplicity.ExceptionalConverse

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def TwE6T1NoPSp4Input
    : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k), D.χ = signMaskChar .E6 20 →
    (∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ)) →
    ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
      NoPSp4Odd p (D.withOrbit J').orbitGroup

theorem twE6TwentyP_of_input
    (hO : LieOrderFormulasInput) (h : TwE6T1NoPSp4Input) :
    TwE6TwentyP (CompPred.noPSp4Odd hO) :=
  h

theorem familyNoPSp4Odd_exc
    (hO : LieOrderFormulasInput) (hLin : GSThmB.CF81X10RowLin) (hT1 : TwE6T1NoPSp4Input)
    {t : StatedLieTag} (ht : t ∈ chevalleyExceptionalTags ∨ t = .twistedG2) :
    FamilyP (CompPred.noPSp4Odd hO) t := by
  have hexc : ∀ (L : Type) [Group L], LieModel L .PSL 2 2 3 → (CompPred.noPSp4Odd hO).P 3 L :=
    fun _ _ h8 => noPSp4Odd_of_lieModel_psl_two_two_three hO h8
  rcases ht with ht | rfl
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact FamilyP.of_model _ excFamilyModel_G2_holds hexc
    · exact FamilyP.of_model _ excFamilyModel_F4_holds hexc
    · exact FamilyP.of_model _ excFamilyModel_E6_holds hexc
    · exact familyNoPSp4Odd_E7 hO hLin
    · exact FamilyP.of_model _ excFamilyModel_E8_holds hexc
    · exact familyNoPSp4Odd_twistedE6 hO hLin (twE6TwentyP_of_input hO hT1)
    · exact FamilyP.of_model _ excFamilyModel_trialityD4 hexc
  · exact FamilyP.of_model _ excFamilyModel_twistedG2 hexc

theorem simple_nonabelian_of_lieModel_exc
    (hO : LieOrderFormulasInput) {N : Type} [Group N] {τ : StatedLieTag} {p f : ℕ}
    (hτ : τ ∈ chevalleyExceptionalTags ∨ τ = .twistedG2) (hadm : StatedLieAdmissible τ 0 p f)
    (hN : LieModel N τ 0 p f) : IsSimpleGroup N ∧ ∃ a b : N, a * b ≠ b * a := by
  have hrep : ExceptionalRep N := by
    rcases hN with ⟨ht, -⟩ | ⟨-, ht, h⟩ | ⟨-, ht, h⟩ | ⟨-, ht, h⟩
    · exfalso
      rcases hτ with hτ | rfl
      · simp only [chevalleyExceptionalTags, classicalTags, Finset.mem_insert,
          Finset.mem_singleton] at hτ ht
        rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at ht
      · simp [classicalTags] at ht
    · exact Or.inl ⟨τ, p, f, ht, h⟩
    · exact Or.inr (Or.inl ⟨τ, p, f, ht, h⟩)
    · exact Or.inr (Or.inr ⟨p, f, h⟩)
  obtain ⟨hfin, -, hsimple⟩ := LieType.Simplicity.fam_exceptional_converse N hrep
  refine ⟨hsimple, ?_⟩
  obtain ⟨-, -, hfac⟩ := hO N τ 0 p f hadm hN
  have hf : 1 ≤ f := hadm.2.1
  have h3 : 3 ≤ lieSylowExponent τ 0 := by
    rcases hτ with hτ | rfl
    · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
      rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [lieSylowExponent]
    · simp [lieSylowExponent]
  by_contra hc
  push Not at hc
  let _ : CommGroup N := { (inferInstance : Group N) with mul_comm := hc }
  have hpr : (Nat.card N).Prime := IsSimpleGroup.prime_card
  have hle : (Nat.card N).factorization p ≤ 1 := by
    rw [hpr.factorization, Finsupp.single_apply]
    split_ifs <;> omega
  have : 3 ≤ lieSylowExponent τ 0 * f := le_trans h3 (Nat.le_mul_of_pos_right _ hf)
  omega

theorem cf81X10RowExc_of_rowLin
    (hLin : GSThmB.CF81X10RowLin) (hT1 : TwE6T1NoPSp4Input) : GSThmB.CF81X10RowExc := by
  intro N _ _ τ p f' f hp hp2 hτ hadm hN hf h5 α hαα hα1 L hL hLm
  have hO : LieOrderFormulasInput := lieOrderFormulasInput
  obtain ⟨hsimple, hna⟩ := simple_nonabelian_of_lieModel_exc hO hτ hadm hN
  have hq : IsQuasisimple L := CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hna
    ⟨τ, 0, p, f', hp, hp2, hadm, hN⟩ α hαα hα1 L hL
  obtain ⟨-, -, hsub, -, -⟩ := hL
  have hs := GSThmB.X10Rec.isSimpleGroup_of_lieModel_psp h5 hLm
  have hZ := GSThmB.X10Rec.center_eq_pPrimeCore hq hs
  have hLZ : LieModel (↥L ⧸ center ↥L) .PSp 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ).symm hLm
  have hodd : Odd (Nat.card (center ↥L)) := by
    rw [hZ]
    exact Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥L))
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hαα) hα1
  exact familyNoPSp4Odd_exc hO hLin hT1 hτ N 0 p f' hp hp2 hadm hN α hα2 L ⟨hq, hsub⟩ f h5 hodd
    hLZ

end CFSG.ComponentClassification.Burgoyne.X10
