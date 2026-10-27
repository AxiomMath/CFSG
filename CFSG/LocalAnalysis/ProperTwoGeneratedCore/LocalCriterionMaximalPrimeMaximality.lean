module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeClass
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G] [Finite G]

@[expose] def IsMaximalPrimeMotion (H : Subgroup G) (z : G) (p : ℕ) (M : Subgroup G) : Prop :=
  ∀ Q : Subgroup G, IsPGroup p Q → M < Q → 3 ≤ Nat.card (pointFixedSet H Q) →
    ¬ ∃ r ∈ involutionPointClass z, r ∈ Subgroup.normalizer (Q : Set G) ∧
      Nat.card (conjugacyWithin Q r) = p ^ (Nat.card (conjugacyWithin H z)).factorization p

omit [Finite G] in
theorem maximalPrimeMotion_larger_fixed_card_le_two
    {H M Q : Subgroup G} {z : G} {p : ℕ}
    (hmax : IsMaximalPrimeMotion H z p M) (hQ : IsPGroup p Q) (hMQ : M < Q)
    {r : G} (hr : r ∈ involutionPointClass z)
    (hrQ : r ∈ Subgroup.normalizer (Q : Set G))
    (hmotion : Nat.card (conjugacyWithin Q r) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p) :
    Nat.card (pointFixedSet H Q) ≤ 2 := by
  by_contra hlarge
  exact hmax Q hQ hMQ (by omega) ⟨r, hr, hrQ, hmotion⟩

theorem maximalPrimeMotion_normalizer_class_pair_flips
    {H M : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hM : IsPGroup p M)
    (hs : s ∈ involutionPointClass z)
    (hsM : s ∈ Subgroup.normalizer (M : Set G))
    (hmotion : Nat.card (conjugacyWithin M s) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p)
    (hmax : IsMaximalPrimeMotion H z p M)
    (hno : ∀ a ∈ pointFixedSet H M, pointRightCosetMul H a s ≠ a)
    (a b : pointRightCosetSpace H) (ha : a ∈ pointFixedSet H M)
    (hb : b ∈ pointFixedSet H M) (hab : a ≠ b) :
    ∃ r ∈ conjugacyWithin (Subgroup.normalizer (M : Set G)) s,
      pointRightCosetMul H a r = b := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let N := Subgroup.normalizer (M : Set G)
  let B := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  have hMB : M ≤ B := le_inf ((mem_pointFixedSet_iff H M a).mp ha)
    ((mem_pointFixedSet_iff H M b).mp hb)
  obtain ⟨hclass, hcentral, hpropagate⟩ := no_fixed_point_odd_normalizer_full_class
    h p hp hodd hM hs hsM hno
  by_contra hnot
  have hnoPair : ∀ r ∈ involutionPointClass z, r ∈ N → pointRightCosetMul H a r ≠ b := by
    intro r hr hrN hrflip
    apply hnot
    exact ⟨r, hclass ▸ (show r ∈ involutionPointClass z ∩ (N : Set G) from ⟨hr, hrN⟩), hrflip⟩
  have hMinternal : IsPGroup p (M.subgroupOf B) :=
    hM.of_injective (Subgroup.subgroupOfEquivOfLe hMB).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hMB).injective
  obtain ⟨Q, hMQinternal⟩ := hMinternal.exists_le_sylow
  let QG := (Q : Subgroup B).map B.subtype
  have hMQ : M ≤ QG := by
    have hm := Subgroup.map_mono (f := B.subtype) hMQinternal
    rw [Subgroup.map_subgroupOf_eq_of_le hMB] at hm
    exact hm
  have hQp : IsPGroup p QG := Q.isPGroup'.map B.subtype
  have hQB : QG ≤ B := Subgroup.map_subtype_le _
  obtain ⟨q, hq, hqa, _, hqnorm, hqmotion⟩ := pair_specified_sylow_flip
    h S hzS hzcenter a b hab p hp Q
  have hMltQ : M < QG := by
    apply lt_of_le_of_ne hMQ
    intro heq
    have hqM : q ∈ N := by
      change q ∈ Subgroup.normalizer (M : Set G)
      rw [heq]
      exact hqnorm
    exact hnoPair q hq hqM hqa
  have hQcard := maximalPrimeMotion_larger_fixed_card_le_two hmax hQp hMltQ
    hq hqnorm hqmotion
  have haQ : a ∈ pointFixedSet H QG := (mem_pointFixedSet_iff H QG a).mpr
    (hQB.trans inf_le_left)
  have hbQ : b ∈ pointFixedSet H QG := (mem_pointFixedSet_iff H QG b).mpr
    (hQB.trans inf_le_right)
  have hQpair := pointFixedSet_eq_pair_of_card_le_two H QG a b hab haQ hbQ hQcard
  have hQtwo : Nat.card (pointFixedSet H QG) = 2 := by
    rw [hQpair]
    change ({a, b} : Set (pointRightCosetSpace H)).ncard = 2
    exact Set.ncard_pair hab
  have hDeltaMod : Nat.card (pointFixedSet H M) ≡ 2 [MOD p] := by
    have hh := (pointFixedSet_card_modEq p hp H M hM).symm.trans
      (pointFixedSet_card_modEq p hp H QG hQp)
    rwa [hQtwo] at hh
  let U := QG ⊓ N
  have hMltU : M < U := pSubgroup_lt_normalizer_intersection p hp M QG hQp hMltQ
  have hUN : U ≤ N := inf_le_right
  have hUp : IsPGroup p U := hQp.of_injective
    (Subgroup.inclusion (show U ≤ QG from inf_le_left))
    (Subgroup.inclusion_injective _)
  have hUinternal : IsPGroup p (U.subgroupOf N) := hUp.of_injective
    (Subgroup.subgroupOfEquivOfLe hUN).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hUN).injective
  obtain ⟨R, hURinternal⟩ := hUinternal.exists_le_sylow
  let RG := (R : Subgroup N).map N.subtype
  have hUR : U ≤ RG := by
    have hh := Subgroup.map_mono (f := N.subtype) hURinternal
    rw [Subgroup.map_subgroupOf_eq_of_le hUN] at hh
    exact hh
  have hMR : M ≤ RG := hMltU.le.trans hUR
  have hRN : RG ≤ N := Subgroup.map_subtype_le _
  have hRp : IsPGroup p RG := R.isPGroup'.map N.subtype
  let sN : N := ⟨s, hsM⟩
  have hsNorder : orderOf sN = 2 := (Subgroup.orderOf_coe sN).symm.trans
    (order_two_of_mem_pointClass h.distinguished_order hs)
  obtain ⟨rN, hrNclass, hrNnorm⟩ := odd_central_quotient_class_normalizes_specified_sylow
    (CFSG.oddCore N) (CFSG.ComponentClassification.OddCore.odd_card N) sN hsNorder
    hcentral p hp R
  let r : G := rN
  have hrclassN : r ∈ conjugacyWithin N s := by
    obtain ⟨n, hn⟩ := hrNclass
    exact ⟨n, congrArg Subtype.val hn⟩
  have hrclass : r ∈ involutionPointClass z := (hclass ▸ hrclassN).1
  have hrnorm : r ∈ Subgroup.normalizer (RG : Set G) :=
    (normalizer_in_subgroup_iff_ambient_image N (R : Subgroup N) rN).mp hrNnorm
  have hrno := (hpropagate r hrclassN).1
  have hrMmotion : Nat.card (conjugacyWithin M r) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p :=
    (hpropagate r hrclassN).2.trans hmotion
  have hfixedMod : Nat.card (pointFixedSet H RG) ≡ 2 [MOD p] := by
    have hh := (pointFixedSet_restricted_card_modEq p hp H M RG hRp hRN).symm.trans hDeltaMod
    have hinter : pointFixedSet H M ∩ pointFixedSet H RG = pointFixedSet H RG :=
      Set.inter_eq_right.mpr (pointFixedSet_antitone hMR)
    rwa [hinter] at hh
  have hfixedCard : 2 ≤ Nat.card (pointFixedSet H RG) := two_le_of_modEq_two p _ hp hodd hfixedMod
  have hfixedNonzero : Nat.card (pointFixedSet H RG) ≠ 0 := by omega
  have : Nonempty (pointFixedSet H RG) := (Nat.card_ne_zero.mp hfixedNonzero).1
  let sigma := (Classical.choice this : pointFixedSet H RG)
  let tau := pointRightCosetMul H sigma.val r
  have htau : tau ∈ pointFixedSet H RG := normalizer_preserves_pointFixedSet hrnorm sigma.property
  have hsigmaDelta := pointFixedSet_antitone hMR sigma.property
  have hsigmatau : sigma.val ≠ tau := Ne.symm (hrno sigma.val hsigmaDelta)
  have hRpair : RG ≤ rightCosetStabilizer H sigma.val ⊓ rightCosetStabilizer H tau :=
    le_inf ((mem_pointFixedSet_iff H RG sigma.val).mp sigma.property)
      ((mem_pointFixedSet_iff H RG tau).mp htau)
  have hRbound := pair_invariant_subgroup_flip_card_le h S hzS hzcenter sigma.val tau
    hsigmatau r hrclass rfl p hp RG hRpair hRp hrnorm
  have hRmotion : Nat.card (conjugacyWithin RG r) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
    have hle := conjugacyWithin_card_le hMR r
    rw [hrMmotion] at hle
    exact Nat.le_antisymm hRbound hle
  have hequal : Nat.card (conjugacyWithin M r) = Nat.card (conjugacyWithin RG r) :=
    hrMmotion.trans hRmotion.symm
  have hrMnorm : r ∈ Subgroup.normalizer (M : Set G) := rN.property
  have hrUnorm := equal_orbit_card_normalizes_intermediate M U RG hMltU.le hUR r
    hrnorm hrMnorm hequal
  have hUmotion : Nat.card (conjugacyWithin U r) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
    have hlo := conjugacyWithin_card_le hMltU.le r
    have hhi := conjugacyWithin_card_le hUR r
    rw [hrMmotion] at hlo
    rw [hRmotion] at hhi
    exact Nat.le_antisymm hhi hlo
  have hUcard := maximalPrimeMotion_larger_fixed_card_le_two hmax hUp hMltU
    hrclass hrUnorm hUmotion
  have haU := pointFixedSet_antitone (show U ≤ QG from inf_le_left) haQ
  have hbU := pointFixedSet_antitone (show U ≤ QG from inf_le_left) hbQ
  have hUpair := pointFixedSet_eq_pair_of_card_le_two H U a b hab haU hbU hUcard
  have hstable : pointRightCosetMul H a r ∈ ({a, b} : Set (pointRightCosetSpace H)) := by
    rw [← hUpair]
    exact normalizer_preserves_pointFixedSet hrUnorm haU
  have hflip := (no_fixed_point_involution_swaps_pair H r
    (order_two_of_mem_pointClass h.distinguished_order hrclass) a b hstable (hrno a ha)).1
  exact hnoPair r hrclass rN.property hflip

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
