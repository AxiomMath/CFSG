module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU23

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement



section U24

open CFSG.ClassicalInvolution.Balance

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_card8 (hc : P23Cfg n Y R S t K' W u e g) :
    ∀ P : Subgroup Y, IsSylow2In P (tightCore R) → Nat.card ↥P = 8 := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hmem : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  intro P hP
  have hS' : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := hC.datum.sylow_core
  have hc8 : Nat.card ↥((S : Subgroup R).map R.subtype) = 8 := by
    obtain ⟨e⟩ := hC.q8
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
      R.subtype_injective).toEquiv, Nat.card_congr e.toEquiv]
    simp [QuaternionGroup.card]
  rw [← hc8]
  exact hΩ.omega3 _ hmem _ hmem P _ hP hS'

theorem p23_oddCore_centralizes_core (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∀ q ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), ∀ k ∈ tightCore R, q * k = k * q := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  intro q hq
  have : tightCore R ≤ Subgroup.centralizer ({q} : Set Y) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (oddCore_centralizes_twoElt_gen hΩ (CoreAssembly.mem_conjClass_self _) hc.std.hK'.1
      hc.std.hne hz hz' (p23_card8 hc) (p23_oddCore_comm_xy hP hc hno hα)
      (Subgroup.subset_closure hx) hx.2 q hq).symm
  intro k hk
  exact (Subgroup.mem_centralizer_singleton_iff.mp (this hk)).symm

theorem p23_members_isPGroup (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∀ J ∈ Om R, IsPGroup 2 ↥J := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hmem : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hθ := p23_oddCore_centralizes_core hP hc hno hα
  have hcent : classicalInvolutionOddCore ↥(tightCore R) ≤ Subgroup.center ↥(tightCore R) := by
    intro m hm
    have hsub : Balance.oddCoreIn (tightCore R) ≤
        Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
      Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_of_hypOmegaGen hΩ hmem hU)
    have hmem' : (m : Y) ∈ Balance.oddCoreIn (tightCore R) := ⟨m, hm, rfl⟩
    have hmθ := hsub hmem'
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hθ _ hmθ k k.2).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2q : IsPGroup 2 (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
    TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup
  have : Group.IsNilpotent (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
    h2q.isNilpotent
  have : Group.IsNilpotent ↥(tightCore R) :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (classicalInvolutionOddCore ↥(tightCore R)))
      (by rw [QuotientGroup.ker_mk']; exact hcent)
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(tightCore R)) := inferInstance
  have : Subsingleton (Sylow 2 ↥(tightCore R)) := (Sylow.unique_of_normal P inferInstance).instSubsingleton
  have hP2 : ∀ x : ↥(tightCore R), IsPGroup 2 (Subgroup.zpowers x) → x ∈ P := by
    intro x hx
    obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
    rw [Subsingleton.elim Q P] at hQ
    exact hQ (Subgroup.mem_zpowers x)
  have hK2 : IsPGroup 2 ↥(tightCore R) := by
    have hle : tightCore R ≤ (P : Subgroup ↥(tightCore R)).map (tightCore R).subtype := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      have hxK : x ∈ tightCore R := Subgroup.subset_closure hx
      refine ⟨⟨x, hxK⟩, hP2 _ ?_, rfl⟩
      obtain ⟨m, hm⟩ := hx.2 ⟨x, Subgroup.mem_zpowers x⟩
      have : (⟨x, hxK⟩ : ↥(tightCore R)) ^ 2 ^ m = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hm
        simpa using this
      exact OddQuot.isPGroup_zpowers_of_pow this
    intro k
    obtain ⟨p, hp, hpk⟩ := hle k.2
    have hpk' : p = k := Subtype.ext hpk
    subst hpk'
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨p, hp⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  rintro _ ⟨g', rfl⟩
  exact isPGroup_conjSub g' hK2

end U24

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
