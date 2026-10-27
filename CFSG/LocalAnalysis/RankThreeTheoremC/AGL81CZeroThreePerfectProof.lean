module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCore
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JZeroTwoHolds
import CFSG.RankThree.PartTwo.Sec19.Item194Proof
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.QuasithinUnique
open Subgroup

namespace CZeroThreePerfect

theorem eq_bot_of_perfect_of_isSolvable {X : Type*} [Group X] [Group.IsSolvable X]
    {D : Subgroup X} (hp : ⁅D, D⁆ = D) : D = ⊥ := by
  obtain ⟨n, hn⟩ := (Group.isSolvable_def X).mp inferInstance
  have h : ∀ k, D ≤ derivedSeries X k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih => rw [derivedSeries_succ, ← hp]; exact Subgroup.commutator_mono ih ih
  exact le_bot_iff.mp (hn ▸ h n)

theorem eq_bot_or_eq_top_of_isSubnormal {Q : Type*} [Group Q] [IsSimpleGroup Q] {J : Subgroup Q}
    (hJ : J.IsSubnormal) : J = ⊥ ∨ J = ⊤ := by
  induction hJ with
  | top => exact Or.inr rfl
  | step lower upper hle hup hnorm ih =>
    rcases ih with h | h
    · left
      exact eq_bot_iff.2 (h ▸ hle)
    · rw [h] at hnorm
      have hN : lower.Normal := ⟨fun n hn g => by
        have h1 : (⟨n, trivial⟩ : ↥(⊤ : Subgroup Q)) ∈ lower.subgroupOf ⊤ := hn
        exact hnorm.conj_mem _ h1 ⟨g, trivial⟩⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal lower

theorem three_dvd_card_alternatingGroup {n : ℕ} (hn : 3 ≤ n) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h2 := two_mul_card_alternatingGroup (α := Fin n)
  rw [Fintype.card_perm, Fintype.card_fin] at h2
  have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  rw [← h2, Nat.card_eq_fintype_card] at *
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)

theorem three_dvd_card_of_perm {n : ℕ} {D : Subgroup (Equiv.Perm (Fin n))} (hD : D ≠ ⊥)
    (hp : ⁅D, D⁆ = D) (hs : D.IsSubnormal) : 3 ∣ Nat.card D := by
  by_cases hn : n ≤ 4
  · have : Group.IsSolvable (Equiv.Perm (Fin n)) := Equiv.Perm.isSolvable (by simpa using hn)
    exact absurd (eq_bot_of_perfect_of_isSolvable hp) hD
  push Not at hn
  have hDA : D ≤ alternatingGroup (Fin n) := by
    rw [← hp, Subgroup.commutator_le]
    intro a _ b _
    rw [Equiv.Perm.mem_alternatingGroup, commutatorElement_def, map_mul, map_mul, map_mul,
      map_inv, map_inv, mul_comm (Equiv.Perm.sign a) (Equiv.Perm.sign b)]
    group
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hs' : (D.subgroupOf (alternatingGroup (Fin n))).IsSubnormal := hs.subgroupOf
  rcases eq_bot_or_eq_top_of_isSubnormal hs' with h | h
  · exfalso
    apply hD
    rw [← Subgroup.map_subgroupOf_eq_of_le hDA, h, Subgroup.map_bot]
  · have hDeq : D = alternatingGroup (Fin n) := by
      refine le_antisymm hDA fun a ha => ?_
      have : (⟨a, ha⟩ : ↥(alternatingGroup (Fin n))) ∈ D.subgroupOf (alternatingGroup (Fin n)) := by
        rw [h]; trivial
      exact this
    rw [hDeq]
    exact three_dvd_card_alternatingGroup (by omega)

theorem three_dvd_card_of_mulEquiv_perm {X : Type*} [Group X] {n : ℕ}
    (e : X ≃* Equiv.Perm (Fin n)) {D : Subgroup X} (hD : D ≠ ⊥) (hp : ⁅D, D⁆ = D)
    (hs : D.IsSubnormal) : 3 ∣ Nat.card D := by
  have h := three_dvd_card_of_perm (D := D.map e.toMonoidHom)
    (fun h => hD ((Subgroup.map_eq_bot_iff_of_injective D (f := e.toMonoidHom) e.injective).mp h))
    (by rw [← Subgroup.map_commutator, hp]) (hs.map (f := e.toMonoidHom) e.surjective)
  rwa [Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm] at h

theorem three_dvd_card_of_mulEquiv_perm_prod {X : Type*} [Group X] {r m : ℕ}
    (e : X ≃* Equiv.Perm (Fin r) × Equiv.Perm (Fin m)) {D : Subgroup X} (hD : D ≠ ⊥)
    (hp : ⁅D, D⁆ = D) (hs : D.IsSubnormal) : 3 ∣ Nat.card D := by
  set D' := D.map e.toMonoidHom with hD'
  have hD'p : ⁅D', D'⁆ = D' := by rw [hD', ← Subgroup.map_commutator, hp]
  have hD's : D'.IsSubnormal := hs.map (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card D' = Nat.card D :=
    Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm
  rw [← hcard]
  by_cases h1 : D'.map (MonoidHom.fst _ _) = ⊥
  · have h2 : D'.map (MonoidHom.snd _ _) ≠ ⊥ := by
      intro h2
      apply hD
      rw [← Subgroup.map_eq_bot_iff_of_injective D (f := e.toMonoidHom) e.injective]
      rw [eq_bot_iff]
      intro x hx
      have hx1 : (MonoidHom.fst _ _) x ∈ D'.map (MonoidHom.fst _ _) := ⟨x, hx, rfl⟩
      have hx2 : (MonoidHom.snd _ _) x ∈ D'.map (MonoidHom.snd _ _) := ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot] at hx1
      rw [h2, Subgroup.mem_bot] at hx2
      exact (Subgroup.mem_bot).mpr (Prod.ext hx1 hx2)
    have h3 := three_dvd_card_of_perm h2 (by rw [← Subgroup.map_commutator, hD'p])
      (hD's.map Prod.snd_surjective)
    exact h3.trans (Subgroup.card_map_dvd _ _)
  · have h3 := three_dvd_card_of_perm h1 (by rw [← Subgroup.map_commutator, hD'p])
      (hD's.map Prod.fst_surjective)
    exact h3.trans (Subgroup.card_map_dvd _ _)

theorem eq_bot_of_perfect_of_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {D : Subgroup X} (hD : IsPGroup p D) (hp : ⁅D, D⁆ = D) : D = ⊥ := by
  have : Group.IsSolvable D := by
    have := hD.isNilpotent
    infer_instance
  have hD' : ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ = (⊤ : Subgroup D) := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hp]
  have h0 := eq_bot_of_perfect_of_isSolvable hD'
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : D) ∈ (⊤ : Subgroup D) := trivial
  rw [h0, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

theorem quot_facts {P : Type*} [Group P] [Finite P] {C : Subgroup P} (hC : C ≠ ⊥)
    (hp : ⁅C, C⁆ = C) (hs : C.IsSubnormal) :
    C.map (QuotientGroup.mk' (CFSG.pCore 2 P)) ≠ ⊥ ∧
      ⁅C.map (QuotientGroup.mk' (CFSG.pCore 2 P)), C.map (QuotientGroup.mk' (CFSG.pCore 2 P))⁆ =
        C.map (QuotientGroup.mk' (CFSG.pCore 2 P)) ∧
      (C.map (QuotientGroup.mk' (CFSG.pCore 2 P))).IsSubnormal ∧
      Nat.card (C.map (QuotientGroup.mk' (CFSG.pCore 2 P))) ∣ Nat.card C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 P).Normal := CFSG.pCore_normal
  refine ⟨fun h => hC ?_, by rw [← Subgroup.map_commutator, hp],
    hs.map (QuotientGroup.mk'_surjective _), Subgroup.card_map_dvd _ _⟩
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  have h2 : IsPGroup 2 C := CFSG.pCore_isPGroup.to_le h
  have : Group.IsSolvable C := by
    have := h2.isNilpotent
    infer_instance
  have hC' : ⁅(⊤ : Subgroup C), (⊤ : Subgroup C)⁆ = (⊤ : Subgroup C) := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hp]
  have := eq_bot_of_perfect_of_isSolvable hC'
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : C) ∈ (⊤ : Subgroup C) := trivial
  rw [‹(⊤ : Subgroup C) = ⊥›, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

theorem isSolvable_of_map_center_perm_four {Y : Type*} [Group Y] {K : Subgroup Y}
    (e : ↥(K.map (QuotientGroup.mk' (Subgroup.center Y))) ≃* Equiv.Perm (Fin 4)) :
    Group.IsSolvable K := by
  set ψ := (QuotientGroup.mk' (Subgroup.center Y)).subgroupMap K with hψ
  have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
  have : Group.IsSolvable ↥(K.map (QuotientGroup.mk' (Subgroup.center Y))) :=
    solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  have : Group.IsSolvable ψ.ker := by
    refine isSolvable_of_comm fun a b => ?_
    have ha : ((a : K) : Y) ∈ Subgroup.center Y := by
      have h' : QuotientGroup.mk' (Subgroup.center Y) ((a : K) : Y) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
      simpa [QuotientGroup.eq_one_iff] using h'
    apply Subtype.ext; apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp ha _).symm
  exact solvable_of_ker_le_range ψ.ker.subtype ψ (fun x hx => ⟨⟨x, hx⟩, rfl⟩)

theorem quotPCore_congr {M : Type*} [Group M] {X X' : Subgroup M} (h : X = X') {T : Type*} [Group T]
    (e : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* T)) : Nonempty (↥X' ⧸ CFSG.pCore 2 ↥X' ≃* T) := by
  obtain ⟨e⟩ := e
  exact ⟨(QuotientGroup.congr _ _ (MulEquiv.subgroupCongr h).symm
    (CFSG.pCore_map_iso 2 (MulEquiv.subgroupCongr h).symm)).trans e⟩

theorem three_dvd_of_quot_perm {P : Type*} [Group P] [Finite P] {C : Subgroup P} (hC : C ≠ ⊥)
    (hp : ⁅C, C⁆ = C) (hs : C.IsSubnormal) {n : ℕ}
    (e : Nonempty (P ⧸ CFSG.pCore 2 P ≃* Equiv.Perm (Fin n))) : 3 ∣ Nat.card C := by
  obtain ⟨h1, h2, h3, h4⟩ := quot_facts hC hp hs
  exact (three_dvd_card_of_mulEquiv_perm e.some h1 h2 h3).trans h4

theorem three_dvd_of_quot_perm_prod {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : C ≠ ⊥) (hp : ⁅C, C⁆ = C) (hs : C.IsSubnormal) {r m : ℕ}
    (e : Nonempty (P ⧸ CFSG.pCore 2 P ≃* Equiv.Perm (Fin r) × Equiv.Perm (Fin m))) :
    3 ∣ Nat.card C := by
  obtain ⟨h1, h2, h3, h4⟩ := quot_facts hC hp hs
  exact (three_dvd_card_of_mulEquiv_perm_prod e.some h1 h2 h3).trans h4

end CZeroThreePerfect

@[expose] def KFactParabolicPerfectThree : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A), Open.IsQuasisimple ↥Y →
    pCoreOf 2 Y = ⊥ → IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) → IsParabolicTwo Y P →
    ∀ C : Subgroup A, C ≤ P → C ≠ ⊥ → ⁅C, C⁆ = C → (C.subgroupOf P).IsSubnormal →
      3 ∣ Nat.card C

@[expose] def KFactSpTwoPerfectThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (k : ℕ) (d : TauCeti.ValidLieTypeIndex),
    (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) →
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ D : Subgroup X, D ≠ ⊥ → ⁅D, D⁆ = D → D.IsSubnormal → 3 ∣ Nat.card D

namespace CZeroThreePerfect

variable {G : Type} [Group G] [Finite G]

theorem barM_facts {M H L I : Subgroup G} (hLM : L ≤ M) (hIle : I ≤ H ⊓ L)
    (hIsn : CFSG.Open.IsSubnormal I (H ⊓ L)) (hIp : ⁅I, I⁆ = I) (hI1 : I ≠ ⊥) :
    barM M I ≤ barM M (H ⊓ L) ∧ barM M I ≠ ⊥ ∧ ⁅barM M I, barM M I⁆ = barM M I ∧
      ((barM M I).subgroupOf (barM M (H ⊓ L))).IsSubnormal ∧
      Nat.card (barM M I) ∣ Nat.card I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIM : I ≤ M := hIle.trans (inf_le_right.trans hLM)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hsub : ⁅I.subgroupOf M, I.subgroupOf M⁆ = I.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hIM, hIp]
  refine ⟨Subgroup.map_mono (fun x hx => hIle hx), fun h => hI1 ?_, ?_, ?_, ?_⟩
  · rw [barM, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have h2 : IsPGroup 2 (I.subgroupOf M) := CFSG.pCore_isPGroup.to_le h
    have : Group.IsSolvable (I.subgroupOf M) := by
      have := h2.isNilpotent
      infer_instance
    have htop : ⁅(⊤ : Subgroup (I.subgroupOf M)), (⊤ : Subgroup (I.subgroupOf M))⁆ =
        (⊤ : Subgroup (I.subgroupOf M)) := by
      apply Subgroup.map_injective (I.subgroupOf M).subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hsub]
    have h0 := eq_bot_of_perfect_of_isSolvable htop
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨⟨x, hIM hx⟩, hx⟩ : I.subgroupOf M) ∈ (⊤ : Subgroup (I.subgroupOf M)) := trivial
    rw [h0, Subgroup.mem_bot] at hx'
    have := congrArg (fun (y : I.subgroupOf M) => ((y : M) : G)) hx'
    simpa using this
  · rw [barM, ← Subgroup.map_commutator, hsub]
  · have h1 : CFSG.Open.IsSubnormal (I.subgroupOf M) ((H ⊓ L).subgroupOf M) :=
      CFSG.Quasithin.A3.subnormal_comap M.subtype hIsn
    exact CFSG.RankThree.PartTwo.Sec19.Item194Proof.isSubnormal_subgroupOf_of_open
      (CFSG.Quasithin.A3.subnormal_map π h1)
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIM).toEquiv]
    exact Subgroup.card_map_dvd _ _

theorem three_dvd_card_oUpperTwo {I : Subgroup G} (h : 3 ∣ Nat.card I) :
    3 ∣ Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h
  obtain ⟨a, ha⟩ := exists_two_pow_mem_oUpperTwo y.2
  have hy' : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe, hy]
  have hcop : Nat.Coprime (orderOf (y : G)) (2 ^ a) := by
    rw [hy']
    exact Nat.Coprime.pow_right a (by norm_num)
  have hord : orderOf ((y : G) ^ (2 ^ a)) = 3 := by
    rw [Nat.Coprime.orderOf_pow hcop, hy']
  have h4 := orderOf_dvd_natCard
    (⟨(y : G) ^ (2 ^ a), ha⟩ : ↥(CFSG.ComponentClassification.AS76b.oUpperTwo I))
  rwa [Subgroup.orderOf_mk, hord] at h4

end CZeroThreePerfect

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card_of_perfect_member (hS : Setting G) {M H : Subgroup G}
    (hT : TwoLocalPhaseThree M H) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hPL : CitedBlockTransvectionPLType)
    (hPar : KFactParabolicPerfectThree) (hSp : KFactSpTwoPerfectThree)
    (h5 : ∀ M S L : Subgroup G, Open.IsKGroup ↥M → Asc81bHyp M S → IsWeakSBlock M S L →
      ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L → NineThreeFive M L →
      Group.IsSolvable ↥(barM M (normalizer (S : Set G) ⊓ L)) ∨
        Nat.card ↥(barM M (normalizer (S : Set G) ⊓ L)) ∣ 72)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {I : Subgroup G}
    (hI : I ∈ cZero (H ⊓ L)) (hIc : IsTwoPrimeComponent I I) :
    3 ∣ Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I) := by
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  have hLM : L ≤ M := hL.le
  refine CZeroThreePerfect.three_dvd_card_oUpperTwo ?_
  have hI1 : I ≠ ⊥ := by
    have h1 : Nontrivial ↥(barM I I) := by
      have := hIc.component.2.2.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM I I))).nontrivial
    have h2 : Nontrivial (↥I ⧸ CFSG.pCore 2 ↥I) :=
      Function.Injective.nontrivial (f := (barM I I).subtype) (barM I I).subtype_injective
    have h3 : Nontrivial ↥I := (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot I).mp h3
  obtain ⟨hCP, hCne, hCp, hCsn, hCdvd⟩ := CZeroThreePerfect.barM_facts hLM hI.le hI.subnormal
    hIc.perfect hI1
  refine Dvd.dvd.trans ?_ hCdvd
  set Pb := barM M (H ⊓ L) with hPb
  set C' := (barM M I).subgroupOf Pb with hC'
  have hC'card : Nat.card C' = Nat.card (barM M I) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv
  have hC'ne : C' ≠ ⊥ := by
    intro h
    apply hCne
    rw [← Subgroup.map_subgroupOf_eq_of_le hCP, ← hC', h, Subgroup.map_bot]
  have hC'p : ⁅C', C'⁆ = C' := by
    apply Subgroup.map_injective Pb.subtype_injective
    rw [Subgroup.map_commutator, hC', Subgroup.map_subgroupOf_eq_of_le hCP]
    exact hCp
  rw [← hC'card]
  have hsolv : Group.IsSolvable Pb → False := fun hs => by
    have := CZeroThreePerfect.eq_bot_of_perfect_of_isSolvable hC'p
    exact hC'ne this
  rcases hT.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5' | h6 | h7 | h8
  · exact absurd h1 (hT.nineThree_not_one hK h85 hNX hL).1
  ·
    obtain ⟨hcl, hpar, -⟩ := h2
    rw [hNS] at hpar
    rw [hC'card]
    exact hPar _ _ _ hL.component.2.2
      (TenThreeThree.pCoreOf_barM_eq_bot hL.toIsTwoPrimeComponent) hcl hpar _ hCP hCne hCp hCsn
  ·
    have hX := (hT.nineThree_not_one hK h85 hNX hL).1
    have hSy2 := hT.not_isSylowTwoOf_inf hK h85 hNX hL
    obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ := hPL G M (pCoreOf 2 H) L hK hA hL hX hSy2 h3
    have hPP : Pb = blockPL M (pCoreOf 2 H) L := by rw [hPb, ← hNS]
    have tr : ∀ {n : ℕ}, Nonempty (↥(blockPL M (pCoreOf 2 H) L) ≃* Equiv.Perm (Fin n)) →
        3 ∣ Nat.card C' := fun ⟨e⟩ =>
      CZeroThreePerfect.three_dvd_card_of_mulEquiv_perm
        ((MulEquiv.subgroupCongr hPP).trans e) hC'ne hC'p hCsn
    rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd'⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rcases hd' with hd' | hd' | ⟨rfl, hd'⟩
      · obtain ⟨d'', hd'', ⟨eP⟩⟩ := hOrth m d ⟨q, hq, Or.inl hd'⟩ ⟨e⟩
        obtain ⟨g1, g2, g3, g4⟩ := CZeroThreePerfect.quot_facts hC'ne hC'p hCsn
        have eQ : Pb ⧸ CFSG.pCore 2 ↥Pb ≃* (TauCeti.CFSGIndex.lie d'').Group :=
          (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hPP)
            (CFSG.pCore_map_iso 2 (MulEquiv.subgroupCongr hPP))).trans eP
        exact (hSp _ (m - 1) d'' hd'' ⟨eQ⟩ _ g1 g2 g3).trans g4
      · obtain ⟨d'', hd'', ⟨eP⟩⟩ := hOrth m d ⟨q, hq, Or.inr hd'⟩ ⟨e⟩
        obtain ⟨g1, g2, g3, g4⟩ := CZeroThreePerfect.quot_facts hC'ne hC'p hCsn
        have eQ : Pb ⧸ CFSG.pCore 2 ↥Pb ≃* (TauCeti.CFSGIndex.lie d'').Group :=
          (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hPP)
            (CFSG.pCore_map_iso 2 (MulEquiv.subgroupCongr hPP))).trans eP
        exact (hSp _ (m - 1) d'' hd'' ⟨eQ⟩ _ g1 g2 g3).trans g4
      · exact tr (hU4 d ⟨q, hq, hd'⟩ ⟨e⟩)
    · rcases hn with rfl | rfl | rfl
      · exact tr (hA5 ⟨e⟩)
      · exact tr (hA6 ⟨e⟩)
      · exact tr (hA8 ⟨e⟩)
  ·
    obtain ⟨-, -, -, -, ⟨eS4⟩⟩ := h4
    rw [hNS] at eS4
    have hs := CZeroThreePerfect.isSolvable_of_map_center_perm_four eS4
    have hPL' : Pb ≤ barM M L := Subgroup.map_mono fun y hy => by
      rw [mem_subgroupOf] at hy ⊢
      exact hy.2
    set eP := (Subgroup.subgroupOfEquivOfLe hPL').symm
    exact (hsolv (solvable_of_solvable_injective (f := eP.toMonoidHom) eP.injective)).elim
  ·
    have hX := (hT.nineThree_not_one hK h85 hNX hL).1
    have hSy2 := hT.not_isSylowTwoOf_inf hK h85 hNX hL
    rcases h5 M (pCoreOf 2 H) L hK hA hL hX hSy2 h5' with hs | hc
    · rw [hNS] at hs
      exact (hsolv hs).elim
    · rw [hNS] at hc
      have hC72 : Nat.card C' ∣ 72 := (Subgroup.card_subgroup_dvd_card C').trans hc
      by_contra h3
      have h8 : Nat.card C' ∣ 2 ^ 3 := by
        have hcop : Nat.Coprime (Nat.card C') 9 :=
          Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
        exact hcop.dvd_of_dvd_mul_right (by simpa using hC72)
      obtain ⟨k, -, hk8⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h8
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact hC'ne (CZeroThreePerfect.eq_bot_of_perfect_of_isPGroup (IsPGroup.of_card hk8) hC'p)
  ·
    obtain ⟨-, n, -, hPn⟩ := h6
    replace hPn := CZeroThreePerfect.quotPCore_congr (congrArg (barM M) hNS) hPn
    exact CZeroThreePerfect.three_dvd_of_quot_perm hC'ne hC'p hCsn hPn
  ·
    obtain ⟨-, n, -, hPn⟩ := h7
    replace hPn := CZeroThreePerfect.quotPCore_congr (congrArg (barM M) hNS) hPn
    exact CZeroThreePerfect.three_dvd_of_quot_perm hC'ne hC'p hCsn hPn
  ·
    obtain ⟨-, N, r, -, -, -, -, -, -, φ, -, -⟩ := h8
    have hφ : Nonempty (↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
        CFSG.pCore 2 ↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L)) ≃*
          Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))) := ⟨φ⟩
    replace hφ := CZeroThreePerfect.quotPCore_congr (congrArg (barM M) hNS) hφ
    exact CZeroThreePerfect.three_dvd_of_quot_perm_prod hC'ne hC'p hCsn hφ

end CFSG.LocalAnalysis.RankThreeTheoremC
