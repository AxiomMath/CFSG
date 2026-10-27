module

public import CFSG.FeitThompson.Local.PLengthOneNormalComplementElementSubgroup
public import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
import CFSG.FeitThompson.Local.NormalAbelianSylowInPrimeCore
import CFSG.FeitThompson.Local.PCoreSelfCentralizingNoNormalComplement
import CFSG.FeitThompson.Local.FittingSupportExcludesNormalCore
import CFSG.FeitThompson.Local.PComplCoreCentralizerInAmbient
import CFSG.FeitThompson.Local.SimpleGroupNormalizerProper
import CFSG.FeitThompson.Local.NormalPlaneElementCentralizerIndex
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem tCore_eq_pCore {X : Type*} [Group X] [Finite X] (h : pComplCore p X = ⊥) :
    tCore p X = pCore p X := by
  have hinj : Function.Injective (QuotientGroup.mk' (pComplCore p X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact h
  have hmap : (pCore p X).map (QuotientGroup.mk' (pComplCore p X))
      = pCore p (X ⧸ pComplCore p X) :=
    map_pCore_of_mulEquiv p
      (MulEquiv.ofBijective _ ⟨hinj, QuotientGroup.mk'_surjective _⟩)
  rw [tCore_eq_comap, ← hmap, Subgroup.comap_map_eq_self_of_injective hinj]

omit [Finite G] in
theorem centralizer_subgroupOf_eq_iff {P A : Subgroup G} (hAP : A ≤ P) :
    centralizer ((A.subgroupOf P : Subgroup ↥P) : Set ↥P) = A.subgroupOf P
      ↔ P ⊓ centralizer (A : Set G) = A := by
  rw [centralizer_subgroupOf hAP]
  refine ⟨fun hh => ?_, fun hh => by rw [hh]⟩
  have h2 := congrArg (fun K => Subgroup.map P.subtype K) hh
  simp only [Subgroup.subgroupOf_map_subtype] at h2
  rwa [inf_right_comm, inf_idem, inf_eq_left.2 hAP] at h2

theorem pComplCoreIn_eq_bot_iff (q : ℕ) (X : Subgroup G) :
    pComplCoreIn q X = ⊥ ↔ pComplCore q ↥X = ⊥ := by
  rw [pComplCoreIn_eq, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]

structure IsPrimeFittingSylowSetup (p : ℕ) (M P A : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  isSolvable : Group.IsSolvable ↥M
  odd : Odd (Nat.card ↥M)
  prime : p.Prime
  mixedFitting_ne_bot : mixedFitting M ≠ ⊥
  isPGroup_mixedFitting : IsPGroup p ↥(mixedFitting M)
  sylow_le : P ≤ M
  card_sylow : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p
  le_sylow : A ≤ P
  normal : (A.subgroupOf P).Normal
  isMulCommutative : IsMulCommutative ↥A
  centralizer_inf_eq : P ⊓ centralizer (A : Set G) = A

namespace IsPrimeFittingSylowSetup

variable {M P A : Subgroup G} (h : IsPrimeFittingSylowSetup p M P A)

include h

theorem le_of_le : A ≤ M := h.le_sylow.trans h.sylow_le

theorem ne_top : M ≠ ⊤ := h.isCoatom.1

theorem centralizer_subgroupOf_eq :
    centralizer ((A.subgroupOf P : Subgroup ↥P) : Set ↥P) = A.subgroupOf P :=
  (centralizer_subgroupOf_eq_iff h.le_sylow).2 h.centralizer_inf_eq

theorem isPGroup_fittingRaw : IsPGroup p ↥(fittingRaw ↥M) := by
  have hF := h.isPGroup_mixedFitting
  rw [mixedFitting_eq] at hF
  exact hF.of_injective
    (Subgroup.equivMapOfInjective (fittingRaw ↥M) M.subtype M.subtype_injective).toMonoidHom
    (MulEquiv.injective _)

theorem pComplCore_eq_bot : pComplCore p ↥M = ⊥ :=
  have := h.isSolvable
  pComplCore_eq_bot_of_isPGroup_fittingRaw h.prime ↥M h.isPGroup_fittingRaw

theorem fittingRaw_eq_pCore : fittingRaw ↥M = pCore p ↥M :=
  have := h.isSolvable
  fittingRaw_eq_pCore_of_pComplCore_eq_bot h.prime h.pComplCore_eq_bot

theorem card_subgroupOf : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.sylow_le).toEquiv, h.card_sylow]

theorem mixedFitting_le_sylow : mixedFitting M ≤ P := by
  have := Fact.mk h.prime
  have h1 : fittingRaw ↥M ≤ P.subgroupOf M := by
    rw [h.fittingRaw_eq_pCore]
    have h2 := pCore_le_sylow h.prime (Sylow.ofCard (P.subgroupOf M) h.card_subgroupOf)
    rwa [Sylow.coe_ofCard] at h2
  calc mixedFitting M = (fittingRaw ↥M).map M.subtype := mixedFitting_eq M
    _ ≤ (P.subgroupOf M).map M.subtype := Subgroup.map_mono h1
    _ = P ⊓ M := Subgroup.subgroupOf_map_subtype P M
    _ = P := inf_eq_left.2 h.sylow_le

theorem subgroupOf_le_subgroupOf : A.subgroupOf M ≤ P.subgroupOf M := fun {_} hx =>
  Subgroup.mem_subgroupOf.2 (h.le_sylow (Subgroup.mem_subgroupOf.1 hx))

theorem le_mixedFitting : A ≤ mixedFitting M := by
  have := h.isSolvable
  have := h.isMulCommutative
  have hPnorm : P ≤ normalizer (A : Set G) :=
    le_normalizer_of_normal_subgroupOf h.le_sylow h.normal
  have hnorm : ((A.subgroupOf M).subgroupOf (P.subgroupOf M)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer h.subgroupOf_le_subgroupOf).2 ?_
    refine Subgroup.le_normalizer_iff.2 fun x hx y hy => ?_
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.1 hx
    have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.1 hy
    exact Subgroup.mem_subgroupOf.2
      (by simpa using Subgroup.le_normalizer_iff.1 hPnorm (x : G) hxP (y : G) hyA)
  have hle := le_tCore_of_normal_abelian_of_natCard_eq (G := ↥M) h.prime h.odd h.card_subgroupOf
    h.subgroupOf_le_subgroupOf hnorm inferInstance
  rw [tCore_eq_pCore h.pComplCore_eq_bot, ← h.fittingRaw_eq_pCore] at hle
  have h2 := Subgroup.map_mono (f := M.subtype) hle
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h.le_of_le, ← mixedFitting_eq] at h2

theorem centreIn_mixedFitting_ne_bot : centreIn (mixedFitting M) ≠ ⊥ := by
  have hnt : Nontrivial ↥(mixedFitting M) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 h.mixedFitting_ne_bot
  rw [centreIn_eq_map_center, Ne,
    Subgroup.map_eq_bot_iff_of_injective _ (mixedFitting M).subtype_injective]
  exact Group.IsNilpotent.center_ne_bot ↥(mixedFitting M)

theorem centreIn_mixedFitting_le : centreIn (mixedFitting M) ≤ A := by
  rw [← h.centralizer_inf_eq]
  refine le_inf ((centreIn_le _).trans h.mixedFitting_le_sylow) ?_
  exact (centreIn_le_centralizer _).trans
    (Subgroup.centralizer_le fun _ hx => h.le_mixedFitting hx)

theorem normalizer_centreIn_mixedFitting_eq [IsSimpleGroup G] :
    normalizer ((centreIn (mixedFitting M) : Subgroup G) : Set G) = M := by
  set Z := centreIn (mixedFitting M)
  have hbot : ⊥ < Z := bot_lt_iff_ne_bot.2 h.centreIn_mixedFitting_ne_bot
  have htop : Z < ⊤ :=
    lt_of_le_of_lt ((centreIn_le _).trans (mixedFitting_le M))
      (lt_of_le_of_ne le_top h.ne_top)
  have hlt : normalizer (Z : Set G) < ⊤ := normalizer_lt_top_of_isSimpleGroup hbot htop
  rcases eq_or_lt_of_le (le_normalizer_centreIn_mixedFitting M) with heq | hlt2
  · exact heq.symm
  · exact absurd (h.isCoatom.2 _ hlt2) hlt.ne

theorem centralizer_le [IsSimpleGroup G] : centralizer (A : Set G) ≤ M :=
  calc centralizer (A : Set G)
      ≤ centralizer ((centreIn (mixedFitting M) : Subgroup G) : Set G) :=
        Subgroup.centralizer_le fun _ hx => h.centreIn_mixedFitting_le hx
    _ ≤ normalizer ((centreIn (mixedFitting M) : Subgroup G) : Set G) :=
        Subgroup.centralizer_le_normalizer _
    _ = M := h.normalizer_centreIn_mixedFitting_eq

theorem pComplCore_centralizer_eq_bot [IsSimpleGroup G] :
    pComplCore p ↥(centralizer (A : Set G)) = ⊥ := by
  have := h.isSolvable
  have hCM : centralizer (A : Set G) ≤ M := h.centralizer_le
  have hAp : IsPGroup p ↥A := (IsPGroup.of_card h.card_sylow).to_le h.le_sylow
  have key := pComplCore_centralizer_map_subtype_le_pComplCore (G := ↥M) h.prime
    (R := A.subgroupOf M) hAp.comap_subtype
  rw [h.pComplCore_eq_bot, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at key
  rw [centralizer_subgroupOf h.le_of_le, inf_eq_right.2 hCM] at key
  have hpi := map_piCore_of_mulEquiv {q : ℕ | q.Prime ∧ q ≠ p}
    (Subgroup.subgroupOfEquivOfLe hCM)
  rw [pComplCore_eq_piCore] at key ⊢
  rw [← hpi, key, Subgroup.map_bot]

theorem pComplCoreIn_centralizer_eq_bot [IsSimpleGroup G] :
    pComplCoreIn p (centralizer (A : Set G)) = ⊥ :=
  (pComplCoreIn_eq_bot_iff p _).2 h.pComplCore_centralizer_eq_bot

end IsPrimeFittingSylowSetup

theorem isPrimeFittingSylowSetup_sylow {M A : Subgroup G} (hM : IsCoatom M)
    [Group.IsSolvable ↥M] (hodd : Odd (Nat.card ↥M)) (hp : p.Prime)
    (hFbot : mixedFitting M ≠ ⊥) (hFp : IsPGroup p ↥(mixedFitting M)) (S : Sylow p ↥M)
    (hAS : A ≤ (S : Subgroup ↥M).map M.subtype)
    (hAnormal : (A.subgroupOf ((S : Subgroup ↥M).map M.subtype)).Normal)
    (hAcomm : IsMulCommutative ↥A)
    (hCP : (S : Subgroup ↥M).map M.subtype ⊓ centralizer (A : Set G) = A) :
    IsPrimeFittingSylowSetup p M ((S : Subgroup ↥M).map M.subtype) A := by
  have := Fact.mk hp
  have hcard : Nat.card ↥((S : Subgroup ↥M).map M.subtype)
      = p ^ (Nat.card ↥M).factorization p := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact S.card_eq_multiplicity
  exact
    { isCoatom := hM, isSolvable := inferInstance, odd := hodd, prime := hp,
      mixedFitting_ne_bot := hFbot, isPGroup_mixedFitting := hFp,
      sylow_le := Subgroup.map_subtype_le _, card_sylow := hcard, le_sylow := hAS,
      normal := hAnormal, isMulCommutative := hAcomm, centralizer_inf_eq := hCP }

theorem le_mixedFitting_and_centralizer_le_and_pComplCore_eq_bot [IsSimpleGroup G]
    (hodd : Odd (Nat.card G)) (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    {M P A F : Subgroup G} (hM : IsCoatom M) (hp : p.Prime) (hF : F = mixedFitting M)
    (hFbot : F ≠ ⊥) (hFp : IsPGroup p ↥F) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) (hAP : A ≤ P)
    (hAnormal : (A.subgroupOf P).Normal) (hAcomm : IsMulCommutative ↥A)
    (hCP : P ⊓ centralizer (A : Set G) = A) :
    A ≤ F ∧ centralizer (A : Set G) ≤ M ∧ pComplCore p ↥(centralizer (A : Set G)) = ⊥ := by
  subst hF
  have h : IsPrimeFittingSylowSetup p M P A :=
    { isCoatom := hM, isSolvable := hsolv M hM.1, odd := odd_natCard_subgroup hodd M,
      prime := hp, mixedFitting_ne_bot := hFbot, isPGroup_mixedFitting := hFp,
      sylow_le := hPM, card_sylow := hPcard, le_sylow := hAP, normal := hAnormal,
      isMulCommutative := hAcomm, centralizer_inf_eq := hCP }
  exact ⟨h.le_mixedFitting, h.centralizer_le, h.pComplCore_centralizer_eq_bot⟩

end

end CFSG.FeitThompson
