module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7E5Lie
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Exit
public import CFSG.ClassicalInvolution.SmallCases.SectionalFourBranch
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf
  (GLS3OddLieAutComponentsInput fixedTwoComponentsQuasisimple_of_oddLieType)
open CFSG.ComponentClassification.CatLeafProof (GLS3OddFamilyInput lieOrderFormulasInput)

@[expose] def A7ExitGLS3 : Prop :=
  GLS3OddFamilyInput .G2 ∧ GLS3OddFamilyInput .trialityD4 ∧ GLS3OddFamilyInput .PSp ∧
    GLS3OddFamilyInput .PSL ∧ GLS3OddFamilyInput .PSU ∧ GLS3OddFamilyInput .twistedG2

theorem statedLieAdmissible_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (_ht : t ≠ .twistedB2) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem false_of_lieModel_clause {t : StatedLieTag} (hF : GLS3OddFamilyInput t) {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ≠ .twistedB2) (h : LieModel G t n p f) {K : Subgroup G}
    {z : G} (hK : Hat2A7.IsClassical2A7 ⊤ K z) : False :=
  Hat2A7E5.false_of_lieModel_of_classical2A7 hF lieOrderFormulasInput
    (fixedTwoComponentsQuasisimple_of_oddLieType hnab (oddLieType_of_lieModel h hp hp2 ht)) hnab hp
    hp2 (statedLieAdmissible_of_lieModel h ht) h hK

theorem a7ExitTF4_of_gh74 (hLy : NoNonsolvableClassical (NativeSporadic.Carrier .Ly))
    (hGH : GH74SectionalModels) (hLie : A7ExitGLS3) : A7ExitTF4 := by
  obtain ⟨hG2, hD4, hSp, hSL, hSU, hRee⟩ := hLie
  intro G _ _ _ hnab hrank hF K z hK
  have hex : NoNonsolvableClassical G → False := fun hN => by
    have hsub : CFSG.Open.IsSubnormal K (Subgroup.centralizer ({z} : Set G)) := by
      have h1 := hK.subnormal
      rwa [top_inf_eq] at h1
    refine hN z hK.orderOf_eq_two K hK.mem hsub (Or.inr hK.witness) fun hsolv => ?_
    have hs : Group.IsSolvable (↥K ⧸ CFSG.Open.classicalInvolutionOddCore ↥K) :=
      Group.isSolvable_of_surjective
        (f := QuotientGroup.mk' (CFSG.Open.classicalInvolutionOddCore ↥K))
        (QuotientGroup.mk'_surjective _)
    exact not_isSolvable_of_open_isQuasisimple hK.witness.1 hs
  rcases hGH G hnab hrank hF with ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
    ⟨p, f, hp, hp2, hf, -, h⟩ | ⟨p, f, hp, hp2, hf, -, h⟩ | ⟨p, f, hp, hf, hm, h⟩ |
    ⟨p, f, hp, hf, hm, h⟩ | h | ⟨n, -, -, ⟨e⟩⟩ | h
  · rcases h with h | h
    · exact false_of_lieModel_clause hG2 hnab hp hp2 (by decide) h hK
    · exact false_of_lieModel_clause hD4 hnab hp hp2 (by decide) h hK
  · exact false_of_lieModel_clause hSp hnab hp hp2 (by decide) h hK
  · exact false_of_lieModel_clause hRee hnab Nat.prime_three (by norm_num) (by decide) h hK
  · exact false_of_lieModel_clause hSL hnab hp hp2 (by decide) h hK
  · exact false_of_lieModel_clause hSU hnab hp hp2 (by decide) h hK
  · exact false_of_lieModel_clause hSL hnab hp (ne_two_of_pow_mod_four hf (Or.inl hm))
      (by decide) h hK
  · exact false_of_lieModel_clause hSU hnab hp (ne_two_of_pow_mod_four hf (Or.inr hm))
      (by decide) h hK
  · rcases h with h | h | h | h
    · exact hex (noNonsolvableClassical_of_lieModel_two h (by decide) (by decide))
    · exact hex (noNonsolvableClassical_of_lieModel_two h (by decide) (by decide))
    · exact hex (noNonsolvableClassical_of_lieModel_two h (by decide) (by decide))
    · exact hex (noNonsolvableClassical_of_lieModel_two h (by decide) (by decide))
  · exact hex (NoNonsolvableClassical.of_mulEquiv e (noNonsolvableClassical_alternating n))
  · exact hex (noNonsolvableClassical_of_gh74_models hLy h)

end CFSG.ClassicalInvolution.Hat2A7S
