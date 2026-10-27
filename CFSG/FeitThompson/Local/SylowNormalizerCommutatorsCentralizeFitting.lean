module

public import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
public import CFSG.FeitThompson.Local.SubgroupIndicatorElementaryPlane
import CFSG.FeitThompson.Local.NonuniqueScnControlsNormalizers
import CFSG.FeitThompson.Local.NonuniqueAbelianEscapingCentralizer
import CFSG.FeitThompson.Local.MixedFittingIntersectionRankTwo
import CFSG.FeitThompson.Local.CoprimeDerivedCentralizesSmallRank
import CFSG.FeitThompson.Local.RankThreeCoprimePlaneGeneration
import CFSG.FeitThompson.Local.CentralRankThreeConstrainedTransitivity
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Local.SelfCentralizingAbelianSylowConstraint
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Local.SylowNormalizerNotCentralizing

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem le_centralizer_iSup {ι : Sort*} {A : Subgroup G} {K : ι → Subgroup G}
    (h : ∀ i, A ≤ centralizer (K i : Set G)) :
    A ≤ centralizer ((⨆ i, K i : Subgroup G) : Set G) :=
  Subgroup.le_centralizer_iff.2 (iSup_le fun i => Subgroup.le_centralizer_iff.1 (h i))

theorem le_normalizer_pComplCoreIn_mixedFitting [Finite G] (p : ℕ) (M : Subgroup G) :
    M ≤ normalizer ((pComplCoreIn p (mixedFitting M) : Subgroup G) : Set G) := by
  rw [pComplCoreIn_eq]
  exact le_normalizer_map_subtype_of_characteristic _ (le_normalizer_mixedFitting M)

theorem iSup_inf_centralizer_plane_eq [Finite G] {E D : Subgroup G} [Group.IsSolvable ↥D]
    (hp : p.Prime) (hEcard : Nat.card ↥E = p ^ 3) (hEexp : ∀ x ∈ E, x ^ p = 1)
    (hEcomm : IsMulCommutative ↥E) (hEN : E ≤ normalizer (D : Set G))
    (hcop : p.Coprime (Nat.card ↥D)) :
    (⨆ S ∈ subgroupsOfCard ↥E (p ^ 2), D ⊓ centralizer ((S.map E.subtype : Subgroup G) : Set G))
      = D := by
  have hexp' : ∀ x : ↥E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hEexp x x.2)
  have h1 := iSup_fixedPoints_subgroupsOfCard_eq_top (V := ↥D) hp hEcard hexp'
    (conjOnNormalized D hEN) hcop
  have h2 : Subgroup.map D.subtype
      (⨆ S ∈ subgroupsOfCard ↥E (p ^ 2),
        FixedPoints.subgroup ↥((conjOnNormalized D hEN).comp S.subtype).range ↥D)
      = D := by rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simp only [Subgroup.map_iSup] at h2
  have h3 : (⨆ S ∈ subgroupsOfCard ↥E (p ^ 2),
      D ⊓ centralizer ((S.map E.subtype : Subgroup G) : Set G))
      = ⨆ S ∈ subgroupsOfCard ↥E (p ^ 2), Subgroup.map D.subtype
        (FixedPoints.subgroup ↥((conjOnNormalized D hEN).comp S.subtype).range ↥D) :=
    iSup_congr fun S => iSup_congr fun _ =>
      (map_subtype_fixedPoints_conjOnNormalized hEN S).symm
  rw [h3, h2]

theorem commutator_eq_bot_of_le_commutator_inf_of_le_mixedFitting_inf [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X) (hp : p.Prime)
    {M L P₀ N : Subgroup G} (hM : IsCoatom M) (hL : IsCoatom L) (hML : M ≠ L)
    (hP₀ : IsPGroup p ↥P₀) (hP₀X : P₀ ≤ ⁅M ⊓ L, M ⊓ L⁆)
    (hN : N ≤ mixedFitting M ⊓ L) (hNp : ¬ p ∣ Nat.card ↥N)
    (hNnorm : M ⊓ L ≤ normalizer (N : Set G)) :
    ⁅P₀, N⁆ = ⊥ := by
  have := Fact.mk hp
  set X : Subgroup G := M ⊓ L with hX
  have hXM : X ≤ M := inf_le_left
  have hXtop : X ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hXM))
  have : Group.IsSolvable ↥X := hsolv X hXtop
  have hoddX : Odd (Nat.card ↥X) := odd_natCard_subgroup hodd X
  have hNX : N ≤ X := hN.trans (inf_le_inf_right L (mixedFitting_le M))
  have hP₀X' : P₀ ≤ X := hP₀X.trans (Subgroup.commutator_le_self X)
  have hNnormal : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hNnorm
  have hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(N.subgroupOf X) ≤ 2 := by
    intro q hq
    have h1 : elementaryAbelianPRank q ↥(N.subgroupOf X) = elementaryAbelianPRank q ↥N :=
      elementaryAbelianPRank_eq_of_mulEquiv hq.one_lt (Subgroup.subgroupOfEquivOfLe hNX)
    rw [h1]
    exact (elementaryAbelianPRank_le_of_le hq.one_lt hN).trans
      (elementaryAbelianPRank_mixedFitting_inf_le_two hna hodd hsolv hM hL hML hq)
  have hDcomm : P₀.subgroupOf X ≤ _root_.commutator ↥X := by
    rw [commutator_eq_subgroupOf_commutator]
    exact Subgroup.comap_mono hP₀X
  have hcard1 : Nat.card ↥(P₀.subgroupOf X) = Nat.card ↥P₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀X').toEquiv
  have hcard2 : Nat.card ↥(N.subgroupOf X) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
  obtain ⟨k, hk⟩ := hP₀.exists_card_eq
  have hcop : (Nat.card ↥(P₀.subgroupOf X)).Coprime (Nat.card ↥(N.subgroupOf X)) := by
    rw [hcard1, hcard2, hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hNp)
  have hmain := commutator_eq_bot_of_le_commutator_of_coprime hoddX hrank hDcomm hcop
  rw [commutator_subgroupOf hP₀X' hNX, Subgroup.subgroupOf_eq_bot] at hmain
  have hle : ⁅P₀, N⁆ ≤ X :=
    (Subgroup.commutator_mono hP₀X' hNX).trans (Subgroup.commutator_le_self X)
  have h2 := disjoint_iff.1 hmain
  rwa [inf_eq_left.2 hle] at h2

theorem commutator_pComplCoreIn_mixedFitting_eq_bot [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hp : p.Prime) (P : Sylow p G) {A M : Subgroup G}
    (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hAtwo : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ A ≤ M₁ ∧ A ≤ M₂ ∧ M₁ ≠ M₂)
    (hM : IsCoatom M) (hCM : centralizer (A : Set G) ≤ M) :
    ⁅⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆,
      pComplCoreIn p (mixedFitting M)⁆ = ⊥ := by
  have := Fact.mk hp
  obtain ⟨M₁, M₂, hM₁, hM₂, hAM₁, hAM₂, hM₁₂⟩ := hAtwo
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_inf_centralizer_eq hAself
  have hAM : A ≤ M := (Subgroup.le_centralizer A).trans hCM
  have hDF : pComplCoreIn p (mixedFitting M) ≤ mixedFitting M := pComplCoreIn_le p (mixedFitting M)
  have hDM : pComplCoreIn p (mixedFitting M) ≤ M := hDF.trans (mixedFitting_le M)
  have hMD : M ≤ normalizer ((pComplCoreIn p (mixedFitting M) : Subgroup G) : Set G) :=
    le_normalizer_pComplCoreIn_mixedFitting p M
  have hDp : ¬ p ∣ Nat.card ↥(pComplCoreIn p (mixedFitting M)) :=
    not_dvd_natCard_pComplCoreIn hp (mixedFitting M)
  have : Group.IsSolvable ↥M := hsolv M hM.1
  have hDsolv : Group.IsSolvable ↥(pComplCoreIn p (mixedFitting M)) := isSolvable_of_le hDM
  obtain ⟨E, hEA, hEcomm', hEexp, hEcard⟩ :=
    (mem_elementaryAbelianRanks_subgroup_iff (H := A) (d := 3) hp).1
      ((le_elementaryAbelianPRank_iff hp.one_lt).1 hArank)
  have hEcomm : IsMulCommutative ↥E :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (hEcomm' a a.2 b b.2)
  have hEN : E ≤ normalizer ((pComplCoreIn p (mixedFitting M) : Subgroup G) : Set G) :=
    (hEA.trans hAM).trans hMD
  have hcop : p.Coprime (Nat.card ↥(pComplCoreIn p (mixedFitting M))) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hDp
  have hgen := iSup_inf_centralizer_plane_eq hp hEcard hEexp hEcomm hEN hcop
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hgen]
  refine le_centralizer_iSup fun S => le_centralizer_iSup fun hS => ?_
  have hBE : S.map E.subtype ≤ E := Subgroup.map_subtype_le S
  have hBA : S.map E.subtype ≤ A := hBE.trans hEA
  have hBcard : Nat.card ↥(S.map E.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact mem_subgroupsOfCard.1 hS
  have hBea : IsElementaryAbelian p (S.map E.subtype) := isElementaryAbelian_iff.2
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hEcomm' a (hBE a.2) b (hBE b.2)),
      fun x hx => hEexp x (hBE hx)⟩
  obtain ⟨b, hbB, _, L, hL, hLM, hCbL, hCAL⟩ :=
    exists_escaping_centralizer_of_isElementaryAbelian hp hna hodd hsolv hAcomm hM₁ hM₂ hM₁₂
      hAM₁ hAM₂ hBA hBea hBcard hM hCM
  have hNPX : normalizer ((P : Subgroup G) : Set G) ≤ M ⊓ L :=
    le_inf
      (normalizer_sylow_le_of_scn hna hodd hsolv hp P hAnormal hAself hArank
        ⟨M₁, M₂, hM₁, hM₂, hAM₁, hAM₂, hM₁₂⟩ hM hCM)
      (normalizer_sylow_le_of_scn hna hodd hsolv hp P hAnormal hAself hArank
        ⟨M₁, M₂, hM₁, hM₂, hAM₁, hAM₂, hM₁₂⟩ hL hCAL)
  have hP₀X : ⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆ ≤ ⁅M ⊓ L, M ⊓ L⁆ :=
    Subgroup.commutator_mono (Subgroup.le_normalizer.trans hNPX) hNPX
  have hP₀pg : IsPGroup p ↥⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆ :=
    P.isPGroup'.to_le (commutator_normalizer_le (P : Subgroup G))
  have hNle : pComplCoreIn p (mixedFitting M) ⊓ L ≤ mixedFitting M ⊓ L := inf_le_inf_right L hDF
  have hNp : ¬ p ∣ Nat.card ↥(pComplCoreIn p (mixedFitting M) ⊓ L) := fun h =>
    hDp (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hNnorm : M ⊓ L ≤ normalizer
      ((pComplCoreIn p (mixedFitting M) ⊓ L : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans hMD) (inf_le_right.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hkey := commutator_eq_bot_of_le_commutator_inf_of_le_mixedFitting_inf hna hodd hsolv hp
    hM hL (fun h => hLM h.symm) hP₀pg hP₀X hNle hNp hNnorm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hkey
  refine hkey.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (le_inf inf_le_left ?_)))
  exact (inf_le_right.trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbB))).trans hCbL

theorem le_centralizer_pComplCoreIn_mixedFitting [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hp : p.Prime) (P : Sylow p G) {A M : Subgroup G}
    (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hAtwo : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ A ≤ M₁ ∧ A ≤ M₂ ∧ M₁ ≠ M₂)
    (hM : IsCoatom M) (hCM : centralizer (A : Set G) ≤ M) :
    ⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆
      ≤ centralizer ((pComplCoreIn p (mixedFitting M) : Subgroup G) : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.1
    (commutator_pComplCoreIn_mixedFitting_eq_bot hna hodd hsolv hp P hAnormal hAself hArank hAtwo
      hM hCM)

end

end CFSG.FeitThompson
