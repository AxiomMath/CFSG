module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF6
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF7
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25SixLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2 (imgX)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin (TwinT4Hyp)
open scoped commutatorElement

section Setting


structure FSet (r n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K' W : Subgroup Y) (S₁ : Sylow 2 Y) (R₁ R₂ : Subgroup Y) (t₁ u₁ u₂ b : Y) : Prop where
  hr : 4 ≤ r
  hP : PerpHypR r n Y R S t
  hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t t₁
    u₁ u₂
  h11 : (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
    Subgroup.zpowers t
  hbS : b ∈ (S₁ : Subgroup Y)
  hb2 : b * b = 1
  hF₁ : IsFAut R₁ b

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ b : Y}

theorem FSet.base (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b) :
    FBase (CoreAssembly.conjClass (tightCore R)) b (tightCore R) t :=
  fBase_of_isFAut F.hr F.hP F.hyp F.hbS F.hF₁

theorem FSet.htC (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b) :
    t ∈ Subgroup.centralizer ({b} : Set Y) :=
  Subgroup.mem_centralizer_singleton_iff.mpr F.base.comm

theorem FSet.h2K (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b) :
    IsPGroup 2 (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
  TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) F.hP.core.datum.twoGroup

theorem FSet.h2 (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
  TwinADescent3.isPGroup_two_quotient_conjClass F.h2K

theorem FSet.hT4 (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b)
    (X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) :
    TwinT4Hyp (r - 1) (↥X ⧸ classicalInvolutionOddCore ↥X) (famF b (tightCore R) X) :=
  twinT4Hyp_famF F.base F.h2 (fBase_quat F.hr F.hP F.hyp F.hbS F.hF₁)
    (aEmpty_fFam F.hr F.hP F.hyp F.h11 F.hbS F.hb2 F.hF₁) X

theorem FSet.exists_datum (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b) :
    ∃ S' : Sylow 2 ↥((coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y))),
      Q8TwinDatum ((coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y))) S'
        (⟨t, F.htC⟩ : Subgroup.centralizer ({b} : Set Y)) ∧
      Nonempty (↥(S' : Subgroup ↥((coreAt b (tightCore R)).subgroupOf
        (Subgroup.centralizer ({b} : Set Y)))) ≃* QuaternionGroup (2 ^ (r - 1 - 2))) := by
  classical
  have hbase := F.base
  obtain ⟨Q, hQ, ⟨e⟩⟩ := fBase_quat F.hr F.hP F.hyp F.hbS F.hF₁
  have hQ2 : IsPGroup 2 ↥Q := hQ.2.1
  have hQcard : 2 ≤ Nat.card ↥Q := by
    haveI : NeZero (2 ^ (r - 1 - 2)) := ⟨by positivity⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have : 1 ≤ 2 ^ (r - 1 - 2) := Nat.one_le_two_pow
    omega
  have htQ : t ∈ Q := hbase.inv_core.mem_of_le hQ.1 hQ2 hQcard
  have hS'map : ((TwinEdge.sylowOf hQ : Sylow 2 ↥(coreAt b (tightCore R))) :
      Subgroup ↥(coreAt b (tightCore R))).map (coreAt b (tightCore R)).subtype = Q :=
    Subgroup.map_subgroupOf_eq_of_le hQ.1
  have hdf : Q8TwinDatum (coreAt b (tightCore R)) (TwinEdge.sylowOf hQ) t := by
    refine ⟨⟨r - 1, by have := F.hr; omega,
      ⟨(Subgroup.subgroupOfEquivOfLe hQ.1).trans e⟩⟩, ?_, ?_, ?_, ?_⟩
    · rw [hS'map]
      exact htQ
    · exact orderOf_eq_prime (by rw [pow_two]; exact hbase.inv.sq) hbase.inv.ne_one
    · exact (TwinADescent.coreAt_le_left b _).trans (isUniqueInvolution_le_centralizer hbase.inv)
    · exact TwinEdge.isPGroup_two_quotient_of_le (TwinADescent.coreAt_le_left b _) F.h2K
  have hSC : ((TwinEdge.sylowOf hQ : Sylow 2 ↥(coreAt b (tightCore R))) :
      Subgroup ↥(coreAt b (tightCore R))).map (coreAt b (tightCore R)).subtype ≤
      Subgroup.centralizer ({b} : Set Y) := by
    rw [hS'map]
    exact hQ.1.trans (TwinADescent.coreAt_le_centralizer b _)
  obtain ⟨S₁', hd₁, ⟨eS⟩⟩ := TwinEdge.restrict hdf hSC
  exact ⟨S₁', hd₁, ⟨eS.trans ((Subgroup.subgroupOfEquivOfLe hQ.1).trans e)⟩⟩

theorem isUniqueInvolution_imgF_X {r' : ℕ} {K : Subgroup Y}
    {X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))}
    (hT4 : TwinT4Hyp r' (↥X ⧸ classicalInvolutionOddCore ↥X) (famF b K X))
    {J : Subgroup Y} (hJ : imgX b X J ∈ famF b K X) {w : Y}
    (hw : IsUniqueInvolution (coreAt b J) w) (hwC : w ∈ Subgroup.centralizer ({b} : Set Y))
    (hwX : (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ X) :
    IsUniqueInvolution (imgX b X J)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)
        (⟨(⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), hwX⟩ : ↥X)) := by
  obtain ⟨⟨u, hu⟩, -⟩ := hT4.hyp.omega1 _ hJ
  have hwmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥X)
      (⟨(⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), hwX⟩ : ↥X) ∈ imgX b X J :=
    Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hw.mem), rfl⟩
  have hsq : (⟨(⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), hwX⟩ : ↥X) *
      ⟨(⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), hwX⟩ = 1 :=
    Subtype.ext (Subtype.ext hw.sq)
  have hne : (⟨(⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), hwX⟩ : ↥X) ≠ 1 := by
    intro h
    have h1 := congrArg (fun t : ↥X => (((t : ↥(Subgroup.centralizer ({b} : Set Y)))) : Y)) h
    exact hw.ne_one (by simpa using h1)
  have hodd := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have h1 := mk_ne_one_of_involution_of_odd hodd hsq hne
  have h2 : QuotientGroup.mk' (classicalInvolutionOddCore ↥X)
      (⟨(⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), hwX⟩ : ↥X) *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X)
      (⟨(⟨w, hwC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), hwX⟩ : ↥X) = 1 := by
    rw [← map_mul, hsq, map_one]
  rcases hu.unique _ hwmem h2 with h | h
  · exact absurd h h1
  · rw [h]
    exact hu

end Setting

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
