module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddRee
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddExc
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddExcE7
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddSpMat
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddUniMat
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddOrthFam
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma54Layer

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Open CFSG.ComponentClassification.CatFC.DS81

@[expose] noncomputable def centralizerEquivInf {G : Type*} [Group G] (H : Subgroup G) (a : H) :
    centralizer {a} ≃* ↥(H ⊓ centralizer {(a : G)}) :=
  (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, by rw [← Subgroup.coe_mul, hx, Subgroup.coe_mul]⟩
      · rintro ⟨hy, hya⟩
        exact ⟨⟨y, hy⟩, Subtype.ext hya, rfl⟩))

theorem oddDichotomy_holds'
    : OddDichotomy :=
  oddDichotomy_of_families fun t => by
    cases t
    · exact oddDichotomyFamily_PSL
    · exact oddDichotomyFamily_PSU
    · exact oddDichotomyFamily_PSp
    · exact oddDichotomyFamily_POmegaOdd
    · exact oddDichotomyFamily_POmegaPlus
    · exact oddDichotomyFamily_POmegaMinus
    · exact oddDichotomyFamily_G2
    · exact oddDichotomyFamily_F4
    · exact oddDichotomyFamily_E6
    · exact oddDichotomyFamily_E7
    · exact oddDichotomyFamily_E8
    · exact oddDichotomyFamily_twistedE6
    · exact oddDichotomyFamily_trialityD4
    · exact oddDichotomyFamily_twistedB2
    · exact oddDichotomyFamily_twistedG2
    · exact oddDichotomyFamily_twistedF4
    · exact oddDichotomyFamily_Tits

theorem ds81Lemma210_odd
    {B : Type} [Group B] [Finite B] (Y : Subgroup B) [IsSimpleGroup ↥Y]
    (hna : ∃ a b : ↥Y, a * b ≠ b * a) (hodd : CFSG.Blueprint.OddLieType ↥Y)
    (y : B) (hy : y ∈ Y) (hy2 : orderOf y = 2) (A : Subgroup B)
    (hA : A = TwoFi22.O2In (Y ⊓ centralizer ({y} : Set B)))
    (hcent : Y ⊓ centralizer ({y} : Set B) ⊓ centralizer (A : Set B) ≤ A)
    (hquot : ∃ (X : Type) (_ : Group X) (π : ↥(Y ⊓ centralizer ({y} : Set B)) →* X),
      Function.Surjective π ∧ π.ker = A.subgroupOf (Y ⊓ centralizer ({y} : Set B)) ∧
      (IsU42Two X ∨ StatedClassicalModel X .PSU 4 2 1)) : False := by
  subst hA
  obtain ⟨X, _, π, hπ, -, hX⟩ := hquot
  have hτ2 : orderOf (⟨y, hy⟩ : ↥Y) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hy2
  have hdich := oddDichotomy_holds' ↥Y hna hodd ⟨y, hy⟩ hτ2
  have hdich' : HasCompOrSolv ↥(Y ⊓ centralizer ({y} : Set B)) :=
    HasCompOrSolv.of_mulEquiv (centralizerEquivInf Y ⟨y, hy⟩) hdich
  have hchar : IsCharacteristicP 2 ↥(Y ⊓ centralizer ({y} : Set B)) :=
    CFSG.EvenSporadicStandard.TwoB.isCharacteristicP_of_isTwoConstrained _ hcent
  rcases hdich' with hsolv | ⟨K, hK⟩
  · have hXsolv : Group.IsSolvable X := Group.isSolvable_of_surjective (f := π) hπ
    rcases hX with hX | hX
    · exact hX.not_isSolvable hXsolv
    · exact not_isSolvable_of_statedPSU42 hX hXsolv
  · exact not_isComponent_of_isCharacteristicP hchar K hK

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
