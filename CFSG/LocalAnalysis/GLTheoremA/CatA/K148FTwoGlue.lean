module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148FTwo

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LieType.SemisimpleCentralizers.Held

variable {G H : Type*} [Group G] [Group H]

theorem openQS_of_mulEquiv (e : G ≃* H) (h : CFSG.Open.IsQuasisimple H) :
    CFSG.Open.IsQuasisimple G := by
  obtain ⟨hc, hs⟩ := h
  let f := QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e (Subgroup.map_center_eq e)
  refine ⟨?_, f.isSimpleGroup⟩
  haveI : Group.IsPerfect H := ⟨hc⟩
  exact (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective).commutator_eq_top

theorem catalogIs_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (Q : TauCeti.CFSGIndex → Prop) (h : catalogIs T Q) : catalogIs S Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.trans f⟩⟩

theorem isSubnormal_inf (N : Subgroup G) {A B : Subgroup G}
    (h : CFSG.Open.IsSubnormal A B) : CFSG.Open.IsSubnormal (A ⊓ N) (B ⊓ N) := by
  induction h with
  | refl A => exact CFSG.Open.IsSubnormal.refl _
  | @step A M K hAM hnorm _ ih =>
    refine CFSG.Open.IsSubnormal.step (inf_le_inf_right N hAM) ?_ ih
    constructor
    intro n hn g
    have hnA : (n : G) ∈ A := hn.1
    have hnN : (n : G) ∈ N := hn.2
    have hgN : (g : G) ∈ N := g.2.2
    have hgM : (g : G) ∈ M := g.2.1
    have hc := hnorm.conj_mem ⟨(n : G), n.2.1⟩ (Subgroup.mem_subgroupOf.2 hnA) ⟨(g : G), hgM⟩
    refine ⟨?_, ?_⟩
    · have := Subgroup.mem_subgroupOf.1 hc
      simpa using this
    · exact N.mul_mem (N.mul_mem hgN hnN) (N.inv_mem hgN)

theorem gLAPPrimeCore_eq_bot_of_simple (K : Type) [Group K] [Finite K] [IsSimpleGroup K]
    (h3 : 3 ∣ Nat.card K) : GLAPPrimeCore 3 K = ⊥ := by
  apply le_bot_iff.1
  show CFSG.pPrimeCore 3 K ≤ ⊥
  unfold CFSG.pPrimeCore
  apply sSup_le
  rintro L ⟨hL, hcop⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with h | h
  · exact h.le
  · exfalso
    rw [h, Subgroup.card_top] at hcop
    unfold Nat.Coprime at hcop
    rw [Nat.gcd_eq_left h3] at hcop
    norm_num at hcop

theorem subnormal_eq_bot_or_top_of_simple {P : Type} [Group P] (R : Subgroup P)
    [IsSimpleGroup R] {A B : Subgroup P} (h : CFSG.Open.IsSubnormal A B) (hB : B = R) :
    A = ⊥ ∨ A = R := by
  induction h with
  | refl A => exact Or.inr hB
  | @step A M K hAM hnorm _ ih =>
    rcases ih hB with hM | hM
    · left
      rw [hM] at hAM
      exact le_bot_iff.1 hAM
    · subst hM
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf M) with h1 | h1
      · left
        have h2 := Subgroup.subgroupOf_eq_bot.1 h1
        rw [disjoint_iff, inf_eq_left.2 hAM] at h2
        exact h2
      · right
        exact le_antisymm hAM (Subgroup.subgroupOf_eq_top.1 h1)

theorem nontrivial_of_quotient {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [Nontrivial (G ⧸ N)] : Nontrivial G := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne (G ⧸ N)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨⟨x, y, fun e => hab (by rw [e])⟩⟩

theorem pComp_facts {P : Type} [Group P] [Finite P] {X M : Subgroup P}
    (hO : GLAPPrimeCore 3 ↥X = ⊥) (h : GLAPComponent 3 X M) :
    M ≤ X ∧ CFSG.Open.IsSubnormal M X ∧ CFSG.Open.IsQuasisimple ↥M := by
  obtain ⟨hMX, hIS, hIC, -⟩ := h
  obtain ⟨-, -, hQA⟩ := hIC
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
  let eA := Subgroup.equivMapOfInjective (M.subgroupOf X)
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) hinj
  have hX : CFSG.Open.IsQuasisimple ↥(M.subgroupOf X) := openQS_of_mulEquiv eA hQA
  exact ⟨hMX, hIS, openQS_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMX).symm hX⟩

theorem eq_of_subnormal_quasisimple {P : Type} [Group P] {R M : Subgroup P} [IsSimpleGroup R]
    (hsub : CFSG.Open.IsSubnormal M R) (hq : CFSG.Open.IsQuasisimple ↥M) : M = R := by
  rcases subnormal_eq_bot_or_top_of_simple R hsub rfl with hM | hM
  · exfalso
    have hnt : Nontrivial ↥M := by
      haveI := hq.2.toNontrivial
      exact nontrivial_of_quotient (Subgroup.center ↥M)
    rw [hM, Subgroup.nontrivial_iff_ne_bot] at hnt
    exact hnt rfl
  · exact hM

theorem openQS_not_solvable {A : Type} [Group A] [Group.IsSolvable A]
    (h : CFSG.Open.IsQuasisimple A) : False := by
  obtain ⟨hc, hs⟩ := h
  haveI := hs.toNontrivial
  haveI : Nontrivial A := nontrivial_of_quotient (Subgroup.center A)
  exact (IsSolvable.commutator_lt_top_of_nontrivial (G := A)).ne hc

theorem not_pComp_of_solvable {P : Type} [Group P] [Finite P] {Z M : Subgroup P}
    [Group.IsSolvable ↥Z] (hM : GLAPComponent 3 Z M) : False := by
  obtain ⟨-, -, hIC, -⟩ := hM
  obtain ⟨-, -, hQA⟩ := hIC
  exact openQS_not_solvable hQA

@[expose] def derivedIn {P : Type} [Group P] (X : Subgroup P) : Subgroup P :=
  (commutator ↥X).map X.subtype

theorem derivedIn_le {P : Type} [Group P] (X : Subgroup P) : derivedIn X ≤ X :=
  Subgroup.map_subtype_le _

theorem le_derivedIn_of_quasisimple {P : Type} [Group P] {X S : Subgroup P} (hSX : S ≤ X)
    (hq : CFSG.Open.IsQuasisimple ↥S) : S ≤ derivedIn X := by
  have hS'top : commutator ↥(S.subgroupOf X) = ⊤ :=
    (openQS_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSX) hq).1
  have hle : S.subgroupOf X ≤ commutator ↥X := by
    let f : ↥(S.subgroupOf X) →* ↥X := (S.subgroupOf X).subtype
    have hm := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥(S.subgroupOf X)))
      (H₂ := (⊤ : Subgroup ↥(S.subgroupOf X))) f
    have h1 : (⊤ : Subgroup ↥(S.subgroupOf X)).map f = S.subgroupOf X := by
      ext x
      simp [Subgroup.mem_map, f]
    rw [← commutator_def, hS'top, h1] at hm
    have h2 := Subgroup.commutator_mono (le_top : S.subgroupOf X ≤ ⊤) (le_top : S.subgroupOf X ≤ ⊤)
    rw [← hm, ← commutator_def] at h2
    exact h2
  intro x hx
  have hxX : x ∈ X := hSX hx
  exact ⟨⟨x, hxX⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem simple_derivedIn {P : Type} [Group P] {X : Subgroup P}
    (hR : IsSimpleGroup ↥(commutator ↥X)) : IsSimpleGroup ↥(derivedIn X) := by
  let e : ↥(commutator ↥X) ≃* ↥(derivedIn X) :=
    Subgroup.equivMapOfInjective _ X.subtype X.subtype_injective
  exact e.symm.isSimpleGroup

theorem pComp_eq_derived {P : Type} [Group P] [Finite P] {X : Subgroup P}
    (hO : GLAPPrimeCore 3 ↥X = ⊥) (hR : IsSimpleGroup ↥(commutator ↥X))
    {S : Subgroup P} (hS : GLAPComponent 3 X S) : S = derivedIn X := by
  obtain ⟨hSX, hIS, hq⟩ := pComp_facts hO hS
  have hle : S ≤ derivedIn X := le_derivedIn_of_quasisimple hSX hq
  haveI := simple_derivedIn (P := P) hR
  have hsub := isSubnormal_inf (derivedIn X) hIS
  rw [inf_eq_left.2 hle, inf_eq_right.2 (derivedIn_le X)] at hsub
  exact eq_of_subnormal_quasisimple hsub hq

theorem psimple_nonempty_mulEquiv {P : Type} [Group P] [Finite P] (G : Subgroup P)
    (hO : GLAPPrimeCore 3 ↥G = ⊥) (hZ : Subgroup.center ↥G = ⊥) :
    Nonempty (PSimple 3 G ≃* ↥G) := by
  let q0 : PQuot 3 G ≃* ↥G := (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hZq : Subgroup.center (PQuot 3 G) = ⊥ := by
    have h := Subgroup.map_center_eq q0
    rw [hZ] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ q0.injective).1 h
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZq).trans QuotientGroup.quotientBot).trans q0⟩

end CFSG.LocalAnalysis.GLTheoremA.K148FTwo

end
