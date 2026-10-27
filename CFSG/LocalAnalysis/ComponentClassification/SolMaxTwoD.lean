module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveT
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Props
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11Q
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9K
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCK
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveP
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36Y
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallN
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoA
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem exists_fixed_layer_seven_of_two (S : Sig36 X t J 9 e E D)
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin 9)} (hρJ : IsPermAction e ρJ) {f : X}
    (hfJ : f ∈ normalizer (J : Set X)) (hf2 : f * f = 1)
    (h2 : (ρJ ⟨f, hfJ⟩).support.card = 2) :
    ∃ (L₀ F : Subgroup X) (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7))
      (DY : Finset (Fin 7)), L₀ ≤ J ∧
      L₀ ≤ centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X) ∧
      IsPComponent 2 (L₀.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X))) ∧
      F ≤ L₀ ∧ F ≤ J ∧ Nat.card F = 4 ∧ (∀ x ∈ F, x * x = 1) ∧
      (∃ DF : Finset (Fin 9), DF.card = 4 ∧ ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 9)) : Perm (Fin 9)) ω = ω) ∧
      DY.card = 4 ∧
      ∀ x : ↥L₀, (x : X) ∈ F → ∀ y ∉ DY,
        ((χ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) y = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L₀, hL₀J, hL₀pc, -, -, χ₀, hχ₀⟩ :=
    exists_fixed_component_of_perm S.pair.1.2.1 S.pair.1.2.2.1 hρJ hfJ hf2 (by rw [h2]; norm_num)
  have hL₀J' : L₀ ≤ J := hL₀J.trans inf_le_left
  have hL₀C : L₀ ≤ centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X) :=
    le_inf (hL₀J'.trans S.pair.1.2.1) (hL₀J.trans inf_le_right)
  have hβ : Fintype.card ↥((ρJ ⟨f, hfJ⟩).supportᶜ : Finset (Fin 9)) = 7 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, h2]
  set π := Fintype.equivFinOfCardEq hβ with hπdef
  set χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7) := χ₀.trans π.altCongrHom
    with hχdef
  set q : ↥L₀ →* alternatingGroup (Fin 7) :=
    χ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L₀)) with hqdef
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨b, rfl⟩ := χ.surjective a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L₀) b
    exact ⟨x, rfl⟩
  have hqker : q.ker = pPrimeCore 2 ↥L₀ := by
    ext x
    rw [MonoidHom.mem_ker, hqdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ χ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hqodd : Odd (Nat.card q.ker) := by
    rw [hqker]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨F, hFL₀, hFk, DY, hDY4, hFY⟩ :=
    exists_four_subgroup_of_surjective (by norm_num) q hq hqodd
  obtain ⟨hF4, hFsq'⟩ := card_sq_of_klein hFk
  have hFsq : ∀ x ∈ F, x * x = 1 := fun x hx => by rw [← sq]; exact hFsq' x hx
  have hFJ : F ≤ J := hFL₀.trans hL₀J'
  set κ : Fin 7 → Fin 9 := fun i =>
    ((π.symm i : ↥((ρJ ⟨f, hfJ⟩).supportᶜ : Finset (Fin 9))) : Fin 9) with hκdef
  have hκ : Function.Injective κ := fun i j hij => π.symm.injective (Subtype.ext hij)
  set DF : Finset (Fin 9) := DY.map ⟨κ, hκ⟩ with hDFdef
  have hDF : DF.card = 4 := by rw [hDFdef, Finset.card_map, hDY4]
  refine ⟨L₀, F, χ, DY, hL₀J', hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, ⟨DF, hDF, ?_⟩, hDY4, hFY⟩
  intro x hxF ω hω
  set x₀ : ↥L₀ := ⟨x, hFL₀ hxF⟩ with hx₀def
  have hx₀ := hχ₀ x₀ x.2
  have hcore : ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
      coreImage e (show (x₀ : X) ∈ J from x.2) := rfl
  rw [hcore, ← hx₀]
  by_cases hωF : ω ∈ (ρJ ⟨f, hfJ⟩).supportᶜ
  ·
    set i := π ⟨ω, hωF⟩ with hidef
    have hiω : κ i = ω := by
      rw [hκdef]
      simp [hidef]
    have hiY : i ∉ DY := by
      intro hi
      apply hω
      rw [hDFdef, Finset.mem_map]
      exact ⟨i, hi, hiω⟩
    have h1 := hFY x₀ hxF i hiY
    change ((χ (x₀ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = i
      at h1
    have h2 : ((χ (x₀ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        π.permCongr ((χ₀ (x₀ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup _) : Perm _) := rfl
    rw [h2, Equiv.permCongr_apply] at h1
    have h3 := congrArg π.symm h1
    rw [Equiv.symm_apply_apply] at h3
    rw [← hiω, Perm.ofSubtype_apply_of_mem _ (π.symm i).2]
    simp only [hκdef]
    rw [h3]
  · exact Perm.ofSubtype_apply_of_not_mem _ hωF

end Sig36

end CFSG.ComponentClassification.SolMax
