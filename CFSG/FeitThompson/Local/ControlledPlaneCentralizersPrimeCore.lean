module

public import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
public import CFSG.FeitThompson.Local.PLengthOneNormalComplementElementSubgroup
public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
public import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.Local.NormalAbelianSylowInPrimeCore
import CFSG.FeitThompson.Local.NormalPlaneElementCentralizerIndex
import CFSG.FeitThompson.Local.NormalComplementSylowDerivedIntersection
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.SelfCentralizingAbelianSylowConstraint
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.PComplCoreCentralizerInAmbient
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
import CFSG.FeitThompson.Foundations.HallImageQuotient
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {p : ℕ}

theorem subgroupOf_normalizer_le_normalizer_subgroupOf {K H : Subgroup G} :
    (normalizer (H : Set G)).subgroupOf K
      ≤ normalizer ((H.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_subgroupOf]
  exact mem_normalizer_iff.1 (Subgroup.mem_subgroupOf.1 hg) (h : G)

theorem normalizer_inf_le_normalizer_inf (H K : Subgroup G) :
    normalizer (H : Set G) ⊓ normalizer (K : Set G)
      ≤ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_inf]
  rw [mem_normalizer_iff.1 hg.1 h, mem_normalizer_iff.1 hg.2 h]

theorem isMulCommutative_subgroupOf_of_isMulCommutative {H K : Subgroup G}
    (hH : IsMulCommutative ↥H) : IsMulCommutative ↥(H.subgroupOf K) := by
  refine Subgroup.le_centralizer_iff_isMulCommutative.1 fun x hx => mem_centralizer_iff.2 ?_
  intro y hy
  have h := Subgroup.le_centralizer_iff_isMulCommutative.2 hH (Subgroup.mem_subgroupOf.1 hx)
  exact Subtype.ext (mem_centralizer_iff.1 h (y : G) (Subgroup.mem_subgroupOf.1 hy))

theorem le_pComplCoreIn_iff_subgroupOf_le_pComplCore [Finite G] {X Y : Subgroup G} (hYX : Y ≤ X) :
    Y ≤ pComplCoreIn p X ↔ Y.subgroupOf X ≤ pComplCore p ↥X := by
  rw [pComplCoreIn_eq]
  constructor
  · intro h y hy
    obtain ⟨w, hw, hwy⟩ := h (Subgroup.mem_subgroupOf.1 hy)
    exact (Subtype.ext hwy : w = y) ▸ hw
  · intro h
    rw [← Subgroup.map_subgroupOf_eq_of_le hYX]
    exact Subgroup.map_mono h

theorem inf_centralizer_self_eq_map_center (H : Subgroup G) :
    H ⊓ centralizer (H : Set G) = (Subgroup.center ↥H).map H.subtype := by
  rw [← inf_centralizer_self_subgroupOf H, Subgroup.map_subgroupOf_eq_of_le inf_le_left]

theorem isMulCommutative_inf_centralizer_self (H : Subgroup G) :
    IsMulCommutative ↥(H ⊓ centralizer (H : Set G)) := by
  rw [inf_centralizer_self_eq_map_center]
  exact Subgroup.map_isMulCommutative _ _

theorem le_normalizer_inf_centralizer_self_of_le_normalizer {H L : Subgroup G}
    (h : L ≤ normalizer (H : Set G)) :
    L ≤ normalizer ((H ⊓ centralizer (H : Set G) : Subgroup G) : Set G) := by
  rw [inf_centralizer_self_eq_map_center]
  exact le_normalizer_map_subtype_of_characteristic _ h

theorem le_pComplCoreIn_of_le_centralizer_of_le_normalizer [Finite G] (hp : p.Prime)
    {X R D : Subgroup G} (hXsolv : Group.IsSolvable ↥X) (hRX : R ≤ X) (hDX : D ≤ X)
    (hR : IsPGroup p ↥R) (hDC : D ≤ centralizer (R : Set G))
    (hCD : X ⊓ centralizer (R : Set G) ≤ normalizer (D : Set G))
    (hDp : ¬ p ∣ Nat.card ↥D) : D ≤ pComplCoreIn p X := by
  have := hXsolv
  refine (le_pComplCoreIn_iff_subgroupOf_le_pComplCore hDX).2 ?_
  refine le_pComplCore_of_le_normalizer hp (R := R.subgroupOf X) (D := D.subgroupOf X)
    (hR.comap_of_injective X.subtype X.subtype_injective) ?_ ?_ ?_
  · intro x hx
    refine mem_centralizer_iff.2 fun r hr => Subtype.ext ?_
    exact mem_centralizer_iff.1 (hDC (Subgroup.mem_subgroupOf.1 hx)) (r : G)
      (Subgroup.mem_subgroupOf.1 hr)
  · intro x hx
    refine subgroupOf_normalizer_le_normalizer_subgroupOf
      (Subgroup.mem_subgroupOf.2 (hCD ⟨x.2, ?_⟩))
    refine mem_centralizer_iff.2 fun r hr => ?_
    exact congrArg Subtype.val (mem_centralizer_iff.1 hx ⟨r, hRX hr⟩ (Subgroup.mem_subgroupOf.2 hr))
  · rwa [natCard_subgroupOf_of_le hDX]

theorem pComplCoreIn_inf_centralizer_le_pComplCoreIn [Finite G] (hp : p.Prime) {X R : Subgroup G}
    (hXsolv : Group.IsSolvable ↥X) (hRX : R ≤ X) (hR : IsPGroup p ↥R) :
    pComplCoreIn p (X ⊓ centralizer (R : Set G)) ≤ pComplCoreIn p X :=
  le_pComplCoreIn_of_le_centralizer_of_le_normalizer hp hXsolv hRX
    ((pComplCoreIn_le p _).trans inf_le_left) hR
    ((pComplCoreIn_le p _).trans inf_le_right) (le_normalizer_pComplCoreIn p _)
    (not_dvd_natCard_pComplCoreIn hp _)

theorem le_pComplCoreIn_inf_of_le_pComplCoreIn [Finite G] (hp : p.Prime) {X W D : Subgroup G}
    (hDX : D ≤ X) (hDW : D ≤ W) (hD : D ≤ pComplCoreIn p W) : D ≤ pComplCoreIn p (X ⊓ W) := by
  set D₀ := pComplCoreIn p W ⊓ (X ⊓ W) with hD₀
  have hnorm : X ⊓ W ≤ normalizer ((D₀ : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    simp only [hD₀, Subgroup.mem_inf]
    rw [mem_normalizer_iff.1 (le_normalizer_pComplCoreIn p W (Subgroup.mem_inf.1 hg).2) h]
    have h2 := mem_normalizer_iff.1 (Subgroup.le_normalizer hg) h
    simp only [Subgroup.mem_inf] at h2 ⊢
    rw [h2]
  have hcard : ¬ p ∣ Nat.card ↥D₀ := fun h =>
    not_dvd_natCard_pComplCoreIn hp W (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  exact (le_inf hD (le_inf hDX hDW)).trans (le_pComplCoreIn inf_le_right hnorm hcard)

theorem le_of_commutator_le_of_inf_centralizer_le_of_coprime [Finite G] {Y Z N : Subgroup G}
    [Group.IsSolvable ↥(Y ⊔ Z)] (hZY : Z ≤ normalizer (Y : Set G))
    (hcop : (Nat.card ↥Z).Coprime (Nat.card ↥Y)) (hcomm : (⁅Y, Z⁆ : Subgroup G) ≤ N)
    (hcent : Y ⊓ centralizer (Z : Set G) ≤ N) : Y ≤ N := by
  set L := Y ⊔ Z with hL
  have hYL : Y ≤ L := le_sup_left
  have hZL : Z ≤ L := le_sup_right
  have hYnormal : ((Y.subgroupOf L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYL, hL, sup_le_iff]
    exact ⟨Subgroup.le_normalizer, hZY⟩
  have hcop' : (Nat.card ↥(Z.subgroupOf L)).Coprime (Nat.card ↥(Y.subgroupOf L)) := by
    rwa [natCard_subgroupOf_of_le hZL, natCard_subgroupOf_of_le hYL]
  intro y hy
  obtain ⟨w, hw, c, hc, hyc⟩ := exists_mem_commutator_mul_mem_inf_centralizer
    (Y.subgroupOf L) (Z.subgroupOf L) hcop' (x := ⟨y, hYL hy⟩) (Subgroup.mem_subgroupOf.2 hy)
  have hwG : (w : G) ∈ (⁅Y, Z⁆ : Subgroup G) := by
    rw [commutator_subgroupOf hYL hZL] at hw
    exact Subgroup.mem_subgroupOf.1 hw
  have hcG : (c : G) ∈ Y ⊓ centralizer (Z : Set G) := by
    obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.1 hc
    refine ⟨Subgroup.mem_subgroupOf.1 hc1, mem_centralizer_iff.2 fun z hz => ?_⟩
    exact congrArg Subtype.val (mem_centralizer_iff.1 hc2 ⟨z, hZL hz⟩
      (Subgroup.mem_subgroupOf.2 hz))
  have hyG : y = (w : G) * (c : G) := by simpa using congrArg Subtype.val hyc
  rw [hyG]
  exact N.mul_mem (hcomm hwG) (hcent hcG)

theorem subgroupOf_le_tCore_of_le_normalizer [Finite G] (hp : p.Prime) {X A P₂ : Subgroup G}
    (hXsolv : Group.IsSolvable ↥X) (hXodd : Odd (Nat.card ↥X)) (hP₂X : P₂ ≤ X)
    (hP₂ : Nat.card ↥P₂ = p ^ (Nat.card ↥X).factorization p) (hA : A ≤ P₂)
    (hAcomm : IsMulCommutative ↥A) (hnorm : P₂ ≤ normalizer (A : Set G)) :
    A.subgroupOf X ≤ tCore p ↥X := by
  have := hXsolv
  refine le_tCore_of_normal_abelian_of_natCard_eq (S := P₂.subgroupOf X) hp hXodd ?_
    (Subgroup.comap_mono hA)
    (normal_subgroupOf_of_le_normalizer_set (Subgroup.comap_mono hA)
      ((Subgroup.comap_mono hnorm).trans subgroupOf_normalizer_le_normalizer_subgroupOf))
    (isMulCommutative_subgroupOf_of_isMulCommutative hAcomm)
  rwa [natCard_subgroupOf_of_le hP₂X]

theorem commutator_le_pComplCoreIn_of_subgroupOf_le_tCore [Finite G] (hp : p.Prime)
    {X Y Z : Subgroup G} (hYX : Y ≤ X) (hZX : Z ≤ X) (hZT : Z.subgroupOf X ≤ tCore p ↥X)
    (hYp : ¬ p ∣ Nat.card ↥Y) (hZY : Z ≤ normalizer (Y : Set G)) :
    (⁅Y, Z⁆ : Subgroup G) ≤ pComplCoreIn p X := by
  have := Fact.mk hp
  have hcomm : (⁅Y, Z⁆ : Subgroup G) ≤ X :=
    Subgroup.commutator_le.2 fun a ha b hb =>
      X.mul_mem (X.mul_mem (X.mul_mem (hYX ha) (hZX hb)) (X.inv_mem (hYX ha))) (X.inv_mem (hZX hb))
  refine (le_pComplCoreIn_iff_subgroupOf_le_pComplCore hcomm).2 ?_
  set N := pComplCore p ↥X with hN
  have hNnormal : N.Normal := pComplCore_normal p ↥X
  set f := QuotientGroup.mk' N with hf
  set Y' := Y.subgroupOf X with hY'
  set Z' := Z.subgroupOf X with hZ'
  have hQ : Z'.map f ≤ pCore p (↥X ⧸ N) := le_tCore_iff.1 hZT
  have hYbp : ¬ p ∣ Nat.card ↥(Y'.map f) := fun h =>
    hYp ((h.trans (natCard_map_mk'_dvd Y' N)).trans (dvd_of_eq (natCard_subgroupOf_of_le hYX)))
  have hinf : Y'.map f ⊓ pCore p (↥X ⧸ N) = ⊥ :=
    inf_eq_bot_of_not_dvd_natCard_of_isPGroup hp hYbp (isPGroup_pCore hp _)
  have hZbY : Z'.map f ≤ normalizer ((Y'.map f : Subgroup (↥X ⧸ N)) : Set (↥X ⧸ N)) :=
    (Subgroup.map_mono
      ((Subgroup.comap_mono hZY).trans subgroupOf_normalizer_le_normalizer_subgroupOf)).trans
      (Subgroup.le_normalizer_map f)
  have hbot : (⁅Y'.map f, Z'.map f⁆ : Subgroup (↥X ⧸ N)) = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact le_inf (Subgroup.le_normalizer_iff_commutator_le_left.1 hZbY)
      ((Subgroup.commutator_mono le_rfl hQ).trans (Subgroup.commutator_le_right _ _))
  rw [← commutator_subgroupOf hYX hZX]
  have h2 : (⁅Y', Z'⁆ : Subgroup ↥X).map f = ⊥ := by rw [Subgroup.map_commutator, hbot]
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h2
  exact h2

theorem centralizer_singleton_ne_top_of_isPGroup [Finite G] [IsSimpleGroup G]
    (hGnc : ¬ IsMulCommutative G) (hp : p.Prime) {b : G} (hb1 : b ≠ 1)
    (hb : IsPGroup p ↥(zpowers b)) : centralizer ({b} : Set G) ≠ ⊤ := by
  have hlt : normalizer ((zpowers b : Subgroup G) : Set G) < ⊤ :=
    normalizer_lt_top_of_isPGroup hGnc hp (by simpa using hb1) hb
  have hle : centralizer ({b} : Set G) ≤ normalizer ((zpowers b : Subgroup G) : Set G) := by
    rw [show centralizer ({b} : Set G) = centralizer ((zpowers b : Subgroup G) : Set G) by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]]
    exact Subgroup.centralizer_le_normalizer _
  exact ne_top_of_le_ne_top hlt.ne hle

theorem le_pComplCoreIn_centralizer_of_mem_center [Finite G] [IsSimpleGroup G]
    (hGnc : ¬ IsMulCommutative G) (hGodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) (hp : p.Prime) (P : Sylow p G)
    {A : Subgroup G} (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A) {z : G} (hzP : z ∈ (P : Subgroup G))
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hz1 : z ≠ 1) {Y : Subgroup G}
    (hYz : Y ≤ centralizer ({z} : Set G)) (hYp : ¬ p ∣ Nat.card ↥Y)
    (hYA : A ≤ normalizer (Y : Set G)) :
    Y ≤ pComplCoreIn p (centralizer ({z} : Set G)) := by
  have := Fact.mk hp
  set X : Subgroup G := centralizer ({z} : Set G) with hXdef
  have hPX : (P : Subgroup G) ≤ X := by
    intro x hx
    refine mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ((mem_centralizer_iff.1 hzc) x hx).symm
  have hAP : A ≤ (P : Subgroup G) := hAself ▸ inf_le_right
  have hAX : A ≤ X := hAP.trans hPX
  have hzpow : IsPGroup p ↥(zpowers z) := P.isPGroup'.to_le (by rwa [Subgroup.zpowers_le])
  have hXtop : X ≠ ⊤ := centralizer_singleton_ne_top_of_isPGroup hGnc hp hz1 hzpow
  have hXsolv : Group.IsSolvable ↥X := hsolv X hXtop
  have hXodd : Odd (Nat.card ↥X) := (odd_natCard_lt_natCard_of_ne_top hGodd hXtop).2
  set S : Sylow p ↥X := P.subtype hPX with hSdef
  have hScoe : (S : Subgroup ↥X) = (P : Subgroup G).subgroupOf X := P.coe_subtype hPX
  have hAS : A.subgroupOf X ≤ (S : Subgroup ↥X) := by
    rw [hScoe]; exact Subgroup.comap_mono hAP
  have hPnormA : (P : Subgroup G) ≤ normalizer (A : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (hK := hAnormal) hAP
  have hAnormal' : ((A.subgroupOf X).subgroupOf (S : Subgroup ↥X)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAS, hScoe]
    exact (Subgroup.comap_mono hPnormA).trans subgroupOf_normalizer_le_normalizer_subgroupOf
  have hAself' : centralizer ((A.subgroupOf X : Subgroup ↥X) : Set ↥X) ⊓ (S : Subgroup ↥X)
      = A.subgroupOf X := by
    have key : (X ⊓ centralizer (A : Set G)) ⊓ (P : Subgroup G) = A := by
      rw [inf_comm X, inf_assoc, inf_comm X, ← inf_assoc, hAself, inf_eq_left.2 hAX]
    rw [centralizer_subgroupOf hAX, hScoe]
    simp only [Subgroup.subgroupOf, ← Subgroup.comap_inf, key]
  have hYX : Y ≤ X := hYz
  have hYp' : ¬ p ∣ Nat.card ↥(Y.subgroupOf X) := by rwa [natCard_subgroupOf_of_le hYX]
  have hYA' : A.subgroupOf X ≤ normalizer ((Y.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
    (Subgroup.comap_mono hYA).trans subgroupOf_normalizer_le_normalizer_subgroupOf
  exact (le_pComplCoreIn_iff_subgroupOf_le_pComplCore hYX).2
    (le_pComplCore_of_normal_selfCentralizing_of_le_normalizer hp hXodd S hAS hAnormal' hAself'
      hYp' hYA')

theorem le_pComplCoreIn_of_mem_controlledPlane [Finite G] [IsSimpleGroup G]
    (hGnc : ¬ IsMulCommutative G) (hGodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) (hp : p.Prime) (P : Sylow p G)
    {A : Subgroup G} (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A) {B : Subgroup G} (hBA : B ≤ A)
    (hBnormal : (B.subgroupOf (P : Subgroup G)).Normal) (hBcard : Nat.card ↥B = p ^ 2)
    (hBZ : B ≤ subgroupCenterTorsionBy (P : Subgroup G) p ∨
      (Nat.card ↥(subgroupCenterTorsionBy (P : Subgroup G) p) = p ∧
        subgroupCenterTorsionBy (P : Subgroup G) p ≤ B))
    {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) {Y : Subgroup G} (hYb : Y ≤ centralizer ({b} : Set G))
    (hYp : ¬ p ∣ Nat.card ↥Y) (hYA : A ≤ normalizer (Y : Set G)) :
    Y ≤ pComplCoreIn p (centralizer ({b} : Set G)) := by
  have := Fact.mk hp
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_inf_centralizer_eq hAself
  have hAP : A ≤ (P : Subgroup G) := hAself ▸ inf_le_right
  have hBP : B ≤ (P : Subgroup G) := hBA.trans hAP
  set Z : Subgroup G := subgroupCenterTorsionBy (P : Subgroup G) p with hZdef
  rcases hBZ with hBZ | ⟨hZcard, hZB⟩
  ·
    exact le_pComplCoreIn_centralizer_of_mem_center hGnc hGodd hsolv hp P hAnormal hAself
      (subgroupCenterTorsionBy_le (hBZ hbB)) (subgroupCenterTorsionBy_le_centralizer (hBZ hbB))
      hb1 hYb hYp hYA
  ·
    set X : Subgroup G := centralizer ({b} : Set G) with hXdef
    have hbP : b ∈ (P : Subgroup G) := hBP hbB
    have hbpow : IsPGroup p ↥(zpowers b) := P.isPGroup'.to_le (by rwa [Subgroup.zpowers_le])
    have hXtop : X ≠ ⊤ := centralizer_singleton_ne_top_of_isPGroup hGnc hp hb1 hbpow
    have hXsolv : Group.IsSolvable ↥X := hsolv X hXtop
    have hXodd : Odd (Nat.card ↥X) := (odd_natCard_lt_natCard_of_ne_top hGodd hXtop).2
    set P₁ : Subgroup G := (P : Subgroup G) ⊓ centralizer ({b} : Set G) with hP₁def
    have hP₁X : P₁ ≤ X := inf_le_right
    have hP₁P : P₁ ≤ (P : Subgroup G) := inf_le_left
    have hP₁p : IsPGroup p ↥(P₁.subgroupOf X) :=
      (P.isPGroup'.to_le hP₁P).comap_of_injective X.subtype X.subtype_injective
    obtain ⟨Q, hQ⟩ := hP₁p.exists_le_sylow
    set P₂ : Subgroup G := (Q : Subgroup ↥X).map X.subtype with hP₂def
    have hP₂X : P₂ ≤ X := Subgroup.map_subtype_le _
    have hP₂card : Nat.card ↥P₂ = p ^ (Nat.card ↥X).factorization p := by
      rw [hP₂def, Subgroup.card_map_of_injective X.subtype_injective, Q.card_eq_multiplicity]
    have hP₂p : IsPGroup p ↥P₂ := Q.isPGroup'.map _
    have hP₁P₂ : P₁ ≤ P₂ := by
      rw [hP₂def, ← Subgroup.map_subgroupOf_eq_of_le hP₁X]
      exact Subgroup.map_mono hQ
    have hPsylow : ∀ R : Sylow p G, Nat.card ↥(R : Subgroup G) ≤ Nat.card ↥(P : Subgroup G) := by
      intro R
      rw [R.card_eq_multiplicity, P.card_eq_multiplicity]
    have hP₁norm : ((P₁.subgroupOf P₂).Normal) :=
      normal_subgroupOf_of_isPGroup_sylow hp hPsylow P.isPGroup' hP₂p hBP hBnormal hBcard hbB hb1
        hP₁P₂
    have hP₂normP₁ : P₂ ≤ normalizer (P₁ : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf (hK := hP₁norm) hP₁P₂
    have hZP : Z ≤ (P : Subgroup G) := subgroupCenterTorsionBy_le
    have hZcP : Z ≤ centralizer ((P : Subgroup G) : Set G) := subgroupCenterTorsionBy_le_centralizer
    have hZP₁ : Z ≤ P₁ := by
      refine le_inf hZP fun z hz => mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact mem_centralizer_iff.1 (hZcP hz) b hbP
    have hZZP₁ : Z ≤ P₁ ⊓ centralizer (P₁ : Set G) :=
      le_inf hZP₁ (hZcP.trans (Subgroup.centralizer_le (by exact_mod_cast hP₁P)))
    have hZX : Z ≤ X := hZP₁.trans hP₁X
    have hZT : Z.subgroupOf X ≤ tCore p ↥X :=
      (Subgroup.comap_mono hZZP₁).trans (subgroupOf_le_tCore_of_le_normalizer hp hXsolv hXodd
        hP₂X hP₂card (le_trans inf_le_left hP₁P₂) (isMulCommutative_inf_centralizer_self P₁)
        (le_normalizer_inf_centralizer_self_of_le_normalizer hP₂normP₁))
    have hYX : Y ≤ X := hYb
    have hZA : Z ≤ A := hZB.trans hBA
    have hZY : Z ≤ normalizer (Y : Set G) := hZA.trans hYA
    have hcomm : (⁅Y, Z⁆ : Subgroup G) ≤ pComplCoreIn p X :=
      commutator_le_pComplCoreIn_of_subgroupOf_le_tCore hp hYX hZX hZT hYp hZY
    have hZbot : Z ≠ ⊥ := by
      intro h
      rw [h, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩] at hZcard
      exact hp.one_lt.ne hZcard
    obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
      rw [Ne, Subgroup.eq_bot_iff_forall] at hZbot
      simp only [not_forall] at hZbot
      obtain ⟨z, hz, hz1⟩ := hZbot
      exact ⟨z, hz, hz1⟩
    set C : Subgroup G := Y ⊓ centralizer (Z : Set G) with hCdef
    have hCz : C ≤ centralizer ({z} : Set G) :=
      inf_le_right.trans (Subgroup.centralizer_le (by simpa using hzZ))
    have hCp : ¬ p ∣ Nat.card ↥C := fun h =>
      hYp (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hCA : A ≤ normalizer (C : Set G) := by
      refine le_trans (le_inf hYA ?_) (normalizer_inf_le_normalizer_inf _ _)
      exact le_trans (le_trans (Subgroup.le_centralizer_iff_isMulCommutative.2 hAcomm)
        (Subgroup.centralizer_le (by exact_mod_cast hZA)))
        (Subgroup.le_normalizer (H := centralizer (Z : Set G)))
    have hCcentral : C ≤ pComplCoreIn p (centralizer ({z} : Set G)) :=
      le_pComplCoreIn_centralizer_of_mem_center hGnc hGodd hsolv hp P hAnormal hAself (hZP hzZ)
        (hZcP hzZ) hz1 hCz hCp hCA
    have hzpowX : (zpowers z : Subgroup G) ≤ X := by
      rw [Subgroup.zpowers_le]; exact hZX hzZ
    have hzpow : IsPGroup p ↥(zpowers z) :=
      P.isPGroup'.to_le (by rw [Subgroup.zpowers_le]; exact hZP hzZ)
    have hcentEq : X ⊓ centralizer ((zpowers z : Subgroup G) : Set G)
        = X ⊓ centralizer ({z} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hCcore : C ≤ pComplCoreIn p X := by
      refine le_trans (le_pComplCoreIn_inf_of_le_pComplCoreIn hp (inf_le_left.trans hYX) hCz
        hCcentral) ?_
      rw [← hcentEq]
      exact pComplCoreIn_inf_centralizer_le_pComplCoreIn hp hXsolv hzpowX hzpow
    have : Group.IsSolvable ↥(Y ⊔ Z) := by
      have := hXsolv
      exact isSolvable_of_le (sup_le hYX hZX)
    have hcop : (Nat.card ↥Z).Coprime (Nat.card ↥Y) := by
      rw [hZcard]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hYp
    exact le_of_commutator_le_of_inf_centralizer_le_of_coprime hZY hcop hcomm hCcore

theorem subgroupOf_le_pComplCore_of_mem_controlledPlane [Finite G] [IsSimpleGroup G]
    (hGnc : ¬ IsMulCommutative G) (hGodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) (hp : p.Prime) (P : Sylow p G)
    {A : Subgroup G} (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A) {B : Subgroup G} (hBA : B ≤ A)
    (hBnormal : (B.subgroupOf (P : Subgroup G)).Normal) (hBcard : Nat.card ↥B = p ^ 2)
    (hBZ : B ≤ subgroupCenterTorsionBy (P : Subgroup G) p ∨
      (Nat.card ↥(subgroupCenterTorsionBy (P : Subgroup G) p) = p ∧
        subgroupCenterTorsionBy (P : Subgroup G) p ≤ B))
    {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) {Y : Subgroup G} (hYb : Y ≤ centralizer ({b} : Set G))
    (hYp : ¬ p ∣ Nat.card ↥Y) (hYA : A ≤ normalizer (Y : Set G)) :
    Y.subgroupOf (centralizer ({b} : Set G)) ≤ pComplCore p ↥(centralizer ({b} : Set G)) :=
  (le_pComplCoreIn_iff_subgroupOf_le_pComplCore hYb).1
    (le_pComplCoreIn_of_mem_controlledPlane hGnc hGodd hsolv hp P hAnormal hAself hBA hBnormal
      hBcard hBZ hbB hb1 hYb hYp hYA)

theorem le_pComplCoreIn_of_mem_controlledPlane' [Finite G] [IsSimpleGroup G]
    (hGnc : ¬ IsMulCommutative G) (hGodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) (hp : p.Prime) (P : Sylow p G)
    {A : Subgroup G} (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A) {B : Subgroup G} (hBA : B ≤ A)
    (hBnormal : (B.subgroupOf (P : Subgroup G)).Normal)
    (hBiso : ↥B ≃* (Fin 2 → Multiplicative (ZMod p)))
    (hBZ : B ≤ subgroupCenterTorsionBy (P : Subgroup G) p ∨
      (Nat.card ↥(subgroupCenterTorsionBy (P : Subgroup G) p) = p ∧
        subgroupCenterTorsionBy (P : Subgroup G) p ≤ B))
    {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) {Y : Subgroup G} (hYb : Y ≤ centralizer ({b} : Set G))
    (hYp : ¬ p ∣ Nat.card ↥Y) (hYA : A ≤ normalizer (Y : Set G)) :
    Y ≤ pComplCoreIn p (centralizer ({b} : Set G)) :=
  le_pComplCoreIn_of_mem_controlledPlane hGnc hGodd hsolv hp P hAnormal hAself hBA hBnormal
    (natCard_of_mulEquiv_pi hBiso) hBZ hbB hb1 hYb hYp hYA

end

end CFSG.FeitThompson
