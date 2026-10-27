module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SharedRankTwoControlledNoncentralLine
import CFSG.FeitThompson.Local.LowRankSylowCentralProduct
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.PrimeCubeNoncentralLineTransitivity
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PrimeExtensionMaximalInvariantSubgroup
import CFSG.FeitThompson.Local.ConjugationUniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise

universe u

variable {G : Type u} [Group G]

theorem exists_plane_le_of_natCard_eq_pow_three [Finite G] {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {Q : Subgroup G} (hQcard : Nat.card ↥Q = p ^ 3) (hQnab : ¬ IsMulCommutative ↥Q) :
    ∃ A : Subgroup G, A ≤ Q ∧ _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A := by
  have hQp : IsPGroup p ↥Q := IsPGroup.of_card (n := 3) hQcard
  have hnc : ¬ IsCyclic ↥Q := fun h => hQnab h.isMulCommutative
  have hnc' : ¬ IsCyclic ↥(⊤ : Subgroup ↥Q) := fun h =>
    hnc (isCyclic_of_surjective (⊤ : Subgroup ↥Q).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩)
  obtain ⟨E, -, -, ⟨f⟩⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hpodd hQp ⊤ hnc'
  exact ⟨E.map Q.subtype, Subgroup.map_subtype_le _,
    ⟨(E.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans f⟩⟩

theorem exists_conj_smul_eq_of_le_of_natCard [Finite G] {p : ℕ} (hp : p.Prime)
    {Q A A₀ A₁ : Subgroup G} (hQcard : Nat.card ↥Q = p ^ 3) (hQnab : ¬ IsMulCommutative ↥Q)
    (hAQ : A ≤ Q) (hAcard : Nat.card ↥A = p ^ 2) (hA₀ : A₀ ≤ A) (hA₁ : A₁ ≤ A)
    (hA₀card : Nat.card ↥A₀ = p) (hA₁card : Nat.card ↥A₁ = p)
    (hA₀Z : A₀ ≠ Q ⊓ centralizer (Q : Set G)) (hA₁Z : A₁ ≠ Q ⊓ centralizer (Q : Set G)) :
    ∃ y ∈ Q, MulAut.conj y • A₀ = A₁ := by
  have hA₀Q : A₀ ≤ Q := hA₀.trans hAQ
  have hA₁Q : A₁ ≤ Q := hA₁.trans hAQ
  have hmap : ∀ {X : Subgroup G}, X ≤ Q → (X.subgroupOf Q).map Q.subtype = X := by
    intro X h; rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h]
  have hcard : ∀ {X : Subgroup G}, X ≤ Q → Nat.card ↥(X.subgroupOf Q) = Nat.card ↥X := by
    intro X h; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have hne : ∀ {X : Subgroup G}, X ≤ Q → X ≠ Q ⊓ centralizer (Q : Set G) →
      X.subgroupOf Q ≠ center ↥Q := by
    intro X h hX hEq
    exact hX (by rw [← hmap h, hEq, map_center_subtype])
  have hAc : Nat.card ↥(A.subgroupOf Q) = p ^ 2 := by rw [hcard hAQ, hAcard]
  have h0c : Nat.card ↥(A₀.subgroupOf Q) = p := by rw [hcard hA₀Q, hA₀card]
  have h1c : Nat.card ↥(A₁.subgroupOf Q) = p := by rw [hcard hA₁Q, hA₁card]
  have h0le : A₀.subgroupOf Q ≤ A.subgroupOf Q := Subgroup.comap_mono hA₀
  have h1le : A₁.subgroupOf Q ≤ A.subgroupOf Q := Subgroup.comap_mono hA₁
  obtain ⟨y, hy⟩ := exists_conj_smul_eq_of_card_eq_prime_sq (A := A.subgroupOf Q) hp hQcard hQnab
    hAc h0le h1le h0c h1c (hne hA₀Q hA₀Z) (hne hA₁Q hA₁Z)
  refine ⟨(y : G), y.2, ?_⟩
  have h := congrArg (fun K : Subgroup ↥Q => K.map Q.subtype) hy
  simpa [map_subtype_conj_smul, hmap hA₀Q, hmap hA₁Q] using h

theorem FNI_shared_rank_two_maxima_contradiction
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₄ : Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₅ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FNI_shared_rank_two_maxima_contradiction.{u} := by
  intro G _ _ hG p M T R hM hT hMT hp hpodd hRMT hRnab hRsyl hrank hNR
  have hfact := Fact.mk hp
  have hfin : Fintype G := Fintype.ofFinite G
  have hG6 : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hRsyl6 : _root_.CFSG.FeitThompson.Prep06.IsSylowIn p R ⊤ :=
    ⟨le_top, by
      rw [Subgroup.card_top]
      exact (_root_.CFSG.FeitThompson.isSylowSubgroup_iff_natCard hp).1 hRsyl⟩
  obtain ⟨Q, -, hQR, -, -, hQcard, hQnab, hQexp, -, -, -, -, -, -⟩ :=
    FPL_low_rank_sylow_central_product h₅ G hG6 p hp hpodd R hRsyl6 hrank.le hRnab
  obtain ⟨A, hAQ, hAplane⟩ := exists_plane_le_of_natCard_eq_pow_three hp hpodd hQcard hQnab
  obtain ⟨A₀, hA₀A, hA₀card, hA₀Z, hA₀uniq⟩ :=
    FNI_shared_rank_two_controlled_noncentral_line h₁ h₂ h₃ h₄ h₅ G hG p M T R Q A hM hT hMT hp
      hpodd hRMT hRnab hRsyl hrank hNR hQR hQnab hQcard hQexp hAQ hAplane
  obtain ⟨A₁, hA₁A, hA₁card, hA₁Z, hA₁uniq⟩ :=
    FNI_shared_rank_two_controlled_noncentral_line h₁ h₂ h₃ h₄ h₅ G hG p T M R Q A hT hM hMT.symm
      hp hpodd (inf_comm M T ▸ hRMT) hRnab hRsyl hrank (inf_comm M T ▸ hNR) hQR hQnab hQcard hQexp
      hAQ hAplane
  obtain ⟨y, hyQ, hy⟩ := exists_conj_smul_eq_of_le_of_natCard hp hQcard hQnab hAQ hAplane.natCard'
    hA₀A hA₁A hA₀card hA₁card hA₀Z hA₁Z
  have hconjuniq : IsUniqueMaximalOvergroup (normalizer (A₁ : Set G)) (MulAut.conj y • M) := by
    have h := hA₀uniq.smul y
    rwa [← normalizer_pointwise_smul, hy] at h
  have hyM : y ∈ M := (hQR.trans (hRMT.trans inf_le_left)) hyQ
  have hMy : MulAut.conj y • M = M := by
    rw [conj_smul_eq_map_conj]
    exact map_conj_eq_self hyM
  exact (hA₁uniq.unique (hMy ▸ hconjuniq)).symm

end

end CFSG.FeitThompson.Proofs
