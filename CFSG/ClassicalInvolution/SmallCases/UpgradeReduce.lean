module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalExc
public import CFSG.ClassicalInvolution.SmallCases.UpgradeM11
public import CFSG.ClassicalInvolution.SmallCases.UpgradeRee

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank

@[expose] def LieModelCentralCover : Prop :=
  ∀ (t : StatedLieTag) (n r e : ℕ) (hr : r.Prime), r ≠ 2 → IsFundTag t →
    StatedLieAdmissible t n r e → ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
      CFSG.Blueprint.LieModel X t n r e →
      ∃ ψ : (modelUniv t n r e hr).K →* X,
        Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center (modelUniv t n r e hr).K

@[expose] def ClassicalMemberParametersAt (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (n r e : ℕ) (hr : r.Prime), r ≠ 2 → StatedLieAdmissible t n r e →
    ∀ (L : Subgroup (modelUniv t n r e hr).K) (z : (modelUniv t n r e hr).K),
      IsClassicalMember p f L z → r = p ∧ (e = f ∨ (t = .trialityD4 ∧ 3 * e = f))

@[expose] def ClassicalMemberParameters (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ t : StatedLieTag, IsFundTag t → ClassicalMemberParametersAt p f t

variable {p f : ℕ} [Fact p.Prime]

theorem isFundTag_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n r e : ℕ} (hr2 : r ≠ 2)
    (hadm : StatedLieAdmissible t n r e) (hmodel : CFSG.Blueprint.LieModel G t n r e)
    {K : Subgroup G} {z : G} (hK : IsClassicalMember p f K z) : IsFundTag t := by
  rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, hree⟩ | ⟨-, -, hsz⟩
  · simp only [CFSG.Blueprint.classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp only [CFSG.Blueprint.chevalleyExceptionalTags, Finset.mem_insert,
      Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp only [CFSG.Blueprint.reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact (false_of_isClassicalMember_of_reeTitsModel hree hK).elim
    · exact absurd hadm.2.2.2.1 hr2
    · exact absurd hadm.2.2.2.1 hr2
  · exact absurd hsz.1 hr2

theorem smallUpgrade_of_model (hfund : ClassicalIsFundamental p f) (hcover : LieModelCentralCover)
    (hpar : ClassicalMemberParameters p f) : SmallUpgrade p f := by
  intro G _ _ _ hnab hp2 hq K z hK hG
  rcases hG with ⟨t, n, r, e, hr, hr2, hadm, hmodel⟩ | hm11
  · have hFT : IsFundTag t := isFundTag_of_lieModel hr2 hadm hmodel hK
    obtain ⟨ψ, hsurj, hker⟩ := hcover t n r e hr hr2 hFT hadm G hmodel
    have : Finite (modelUniv t n r e hr).K :=
      CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 hr hFT hadm
    obtain ⟨L, z', hL, -, -⟩ := ModelFacts.IsClassicalMember.exists_lift hp2 hq ψ hsurj hker hK
    obtain ⟨rfl, hef⟩ := hpar t hFT hp2 hq n r e hr hr2 hadm L z' hL
    obtain ⟨R, hR, hKR⟩ := hfund hp2 hq t n e hr hFT hadm hef G ψ hsurj hker K z hK
    rw [hKR]
    exact lieSystem_range_conj_of_model hr hFT hadm hef ψ hsurj hker hR
  · exact (not_isClassicalMember_of_isSporadic_m11 hm11 hq hK).elim

theorem smallUpgrade_of_exc_cover
    (hexc : CFSG.ClassicalInvolution.ModelFacts.ClassicalMembersFundamentalExc p f)
    (hcover : LieModelCentralCover) (hpar : ClassicalMemberParameters p f) : SmallUpgrade p f :=
  smallUpgrade_of_model (CFSG.ClassicalInvolution.ModelFacts.classicalIsFundamental_of_exc hexc)
    hcover hpar

end CFSG.ClassicalInvolution.Upgrade
