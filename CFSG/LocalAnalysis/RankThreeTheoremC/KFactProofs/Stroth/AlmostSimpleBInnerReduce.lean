module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBOuter
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo IsChevIndexTwo)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped commutatorElement

section PClosureOdd

@[expose] def PClosureOdd (p : ℕ) (L : Type*) [Group L] : Prop :=
  ∀ d : L, d ≠ 1 → d ^ p = 1 → OddPCoreInClosure p ↥(Subgroup.centralizer ({d} : Set L))

theorem commutator_eq_bot_of_pClosureOdd {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {L : Subgroup X} (h : PClosureOdd p ↥L) {D S : Subgroup X} (hDel : IsElemAbelian p D)
    (hDL : D ≤ L) {d : X} (hd : d ∈ D) (hd1 : d ≠ 1)
    (hSR : S ≤ relPPrimeCore p (L ⊓ Subgroup.centralizer ({d} : Set X))) (hS2 : IsPGroup 2 S)
    (hDS : D ≤ Subgroup.normalizer (S : Set X)) : ⁅S, D⁆ = ⊥ := by
  have hDcomm : ∀ x ∈ D, d * x = x * d := fun x hx =>
    congrArg Subtype.val (hDel.1.is_comm.comm (⟨d, hd⟩ : D) ⟨x, hx⟩)
  set d' : ↥L := ⟨d, hDL hd⟩ with hd'
  have hd'1 : d' ≠ 1 := fun h1 => hd1 (congrArg Subtype.val h1)
  have hd'p : d' ^ p = 1 := Subtype.ext (hDel.2 d hd)
  have hOC := h d' hd'1 hd'p
  set C : Subgroup X := L ⊓ Subgroup.centralizer ({d} : Set X) with hC
  have hCL : C ≤ L := inf_le_left
  have hCeq : C.subgroupOf L = Subgroup.centralizer ({d'} : Set ↥L) := by
    ext g
    simp only [Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hg⟩
      exact Subtype.ext hg
    · intro hg
      exact ⟨g.2, congrArg Subtype.val hg⟩
  let e : ↥(Subgroup.centralizer ({d'} : Set ↥L)) ≃* ↥C :=
    (MulEquiv.subgroupCongr hCeq.symm).trans (Subgroup.subgroupOfEquivOfLe hCL)
  have hOC' : OddPCoreInClosure p ↥C := OddPCoreInClosure.of_mulEquiv e hOC
  have hDC : D ≤ C := fun x hx =>
    ⟨hDL hx, Subgroup.mem_centralizer_singleton_iff.2 (hDcomm x hx).symm⟩
  exact commutator_eq_bot_of_oddPCore hp hOC' hDC (fun x hx => ⟨1, by simpa using hDel.2 x hx⟩)
    hSR hS2 hDS

end PClosureOdd

section Transport

def centralizerSingletonEquiv {L M : Type*} [Group L] [Group M] (e : L ≃* M) (d : L) :
    ↥(Subgroup.centralizer ({d} : Set L)) ≃* ↥(Subgroup.centralizer ({e d} : Set M)) :=
  (MulEquiv.subgroupMap e (Subgroup.centralizer ({d} : Set L))).trans
    (MulEquiv.subgroupCongr (by
      ext y
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hg' : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.1 hg
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        change e g * e d = e d * e g
        rw [← map_mul, ← map_mul, hg']
      · intro hy
        have hy' : y * e d = e d * y := Subgroup.mem_centralizer_singleton_iff.1 hy
        refine ⟨e.symm y, Subgroup.mem_centralizer_singleton_iff.2 ?_, e.apply_symm_apply y⟩
        apply e.injective
        rw [map_mul, map_mul, e.apply_symm_apply]
        exact hy'))

theorem PClosureOdd.of_mulEquiv {p : ℕ} {L M : Type*} [Group L] [Group M] (e : L ≃* M)
    (h : PClosureOdd p L) : PClosureOdd p M := by
  intro d hd1 hdp
  have hd'1 : e.symm d ≠ 1 := fun h1 => hd1 (by simpa using congrArg e h1)
  have hd'p : e.symm d ^ p = 1 := by
    rw [← map_pow, hdp, map_one]
  have h' := h (e.symm d) hd'1 hd'p
  have e1 := centralizerSingletonEquiv e (e.symm d)
  have hed : e (e.symm d) = d := e.apply_symm_apply d
  have e3 : ↥(Subgroup.centralizer ({e (e.symm d)} : Set M)) ≃*
      ↥(Subgroup.centralizer ({d} : Set M)) := MulEquiv.subgroupCongr (by rw [hed])
  exact OddPCoreInClosure.of_mulEquiv (e1.trans e3) h'

end Transport

section Rank

theorem exists_isElemAbelian_card_sq_of_pRank_eq_two {L : Type*} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (h : CFSG.Open.pRank p (⊤ : Subgroup L) = 2) :
    ∃ E : Subgroup L, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  unfold CFSG.Open.pRank at h
  set s : Set ℕ := {k | ∃ E : Subgroup L, E ≤ ⊤ ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} with hs
  have hne : s.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at h
    simp at h
  have hbdd : BddAbove s := by
    refine ⟨Nat.card L, ?_⟩
    rintro k ⟨E, -, -, hk⟩
    have h1 : Nat.card E ≤ Nat.card L :=
      Nat.card_le_card_of_injective E.subtype E.subtype_injective
    have h2 : k < p ^ k := Nat.lt_pow_self hp.one_lt
    rw [hk] at h1
    omega
  have hmem : sSup s ∈ s := Nat.sSup_mem hne hbdd
  rw [h] at hmem
  obtain ⟨E, -, hE, hcard⟩ := hmem
  exact ⟨E, hE, hcard⟩

end Rank

section Assembly

@[expose] def ChevTwoPClosureOdd : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    (∃ a b : L, a * b ≠ b * a) → (¬ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))) →
    IsChevTwo L → CFSG.Open.pRank p (⊤ : Subgroup L) = 2 → ¬ IsRankTwoSEGroup p L →
    PClosureOdd p L

theorem chevTwoInnerTwoPartCentralizedRest_of_pClosureOdd (h : ChevTwoPClosureOdd) :
    ChevTwoInnerTwoPartCentralizedRest := by
  intro p hp hp2 X _ _ L _ hs hnab hcat hnalt hCL hE hrk hchev D hDel hDcard hDL hcase d hd hd1 S
    hSR hS2 hDS
  have hSE : ¬ IsRankTwoSEGroup p ↥L := fun hSE => hcase (Or.inl ⟨hSE, hDL⟩)
  exact commutator_eq_bot_of_pClosureOdd hp (h p hp hp2 ↥L hs hnab hnalt hchev hrk hSE) hDel hDL
    hd hd1 hSR hS2 hDS

end Assembly

section Families

@[expose] def ChevTwoPClosureOddFamily (F : TauCeti.LieTypeIndex → ℕ → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    (∃ a b : L, a * b ≠ b * a) → CFSG.Open.pRank p (⊤ : Subgroup L) = 2 →
    ¬ IsRankTwoSEGroup p L → ∀ d : TauCeti.ValidLieTypeIndex, F d.1 p → IsChevIndexTwo d.1 →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → PClosureOdd p L

@[expose] def LieFamilyLinear : TauCeti.LieTypeIndex → ℕ → Prop
  | .A r q, p => ¬ p ∣ Nat.gcd (r + 1) (q.card - 1)
  | _, _ => False

@[expose] def LieFamilyLinearDiagThree : TauCeti.LieTypeIndex → ℕ → Prop
  | .A r _, p => r = 2 ∧ p = 3
  | _, _ => False

@[expose] def LieFamilyLinearDiagBig : TauCeti.LieTypeIndex → ℕ → Prop
  | .A r q, p => p ∣ Nat.gcd (r + 1) (q.card - 1) ∧ ¬ (r = 2 ∧ p = 3)
  | _, _ => False

@[expose] def LieFamilyUnitary : TauCeti.LieTypeIndex → ℕ → Prop
  | .twistedA r q, p => ¬ p ∣ Nat.gcd (r + 1) (q.card + 1)
  | _, _ => False

@[expose] def LieFamilyUnitaryDiagThree : TauCeti.LieTypeIndex → ℕ → Prop
  | .twistedA r _, p => r = 2 ∧ p = 3
  | _, _ => False

@[expose] def LieFamilyUnitaryDiagBig : TauCeti.LieTypeIndex → ℕ → Prop
  | .twistedA r q, p => p ∣ Nat.gcd (r + 1) (q.card + 1) ∧ ¬ (r = 2 ∧ p = 3)
  | _, _ => False

@[expose] def LieFamilySymplectic : TauCeti.LieTypeIndex → ℕ → Prop
  | .B _ _, _ => True
  | _, _ => False

@[expose] def LieFamilyOrthogonal : TauCeti.LieTypeIndex → ℕ → Prop
  | .D _ _, _ => True
  | .twistedD _ _, _ => True
  | _, _ => False

@[expose] def LieFamilyE6 : TauCeti.LieTypeIndex → ℕ → Prop
  | .E6 _, _ => True
  | _, _ => False

@[expose] def LieFamilyE7 : TauCeti.LieTypeIndex → ℕ → Prop
  | .E7 _, _ => True
  | _, _ => False

@[expose] def LieFamilyE8 : TauCeti.LieTypeIndex → ℕ → Prop
  | .E8 _, _ => True
  | _, _ => False

@[expose] def LieFamilyF4 : TauCeti.LieTypeIndex → ℕ → Prop
  | .F4 _, _ => True
  | _, _ => False

@[expose] def LieFamilyG2 : TauCeti.LieTypeIndex → ℕ → Prop
  | .G2 _, _ => True
  | _, _ => False

@[expose] def LieFamilyTwistedE6 : TauCeti.LieTypeIndex → ℕ → Prop
  | .twistedE6 _, _ => True
  | _, _ => False

@[expose] def LieFamilyTrialityD4 : TauCeti.LieTypeIndex → ℕ → Prop
  | .trialityD4 _, _ => True
  | _, _ => False

@[expose] def LieFamilySuzuki : TauCeti.LieTypeIndex → ℕ → Prop
  | .suzuki _, _ => True
  | _, _ => False

@[expose] def LieFamilyReeF4 : TauCeti.LieTypeIndex → ℕ → Prop
  | .reeF4 _, _ => True
  | _, _ => False

@[expose] def LieFamilyTits : TauCeti.LieTypeIndex → ℕ → Prop
  | .tits, _ => True
  | _, _ => False

end Families

section SmallIsomorphisms

open CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_of_A {L : Type} [Group L] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (e : L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    StatedClassicalModel L .PSL (r + 1) q.p q.exponent := by
  rcases (CFSG.Models.lieModel_A r q hv e).2 with h | ⟨h0, -⟩
  · exact h
  · omega

theorem statedClassicalModel_of_twistedA {L : Type} [Group L] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (e : L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    StatedClassicalModel L .PSU (r + 1) q.p q.exponent := by
  rcases (CFSG.Models.lieModel_twistedA r q hv e).2 with h | ⟨h0, -⟩
  · have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA r q
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA r q
    rw [hc, hf] at h
    exact h
  · omega

theorem primePower_eq_three {q : TauCeti.PrimePower} (hq : q.card = 3) :
    q.p = 3 ∧ q.exponent = 1 := by
  have h1 : q.p ^ q.exponent = 3 := (TauCeti.PrimePower.card_def q).symm.trans hq
  have hp3 : q.p ∣ 3 := by
    rw [← h1]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hq3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hp3
  refine ⟨hq3, ?_⟩
  rw [hq3] at h1
  have h2 : (3 : ℕ) ^ q.exponent = 3 ^ 1 := by rw [h1]; norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2

theorem false_of_pRank_two_psl_two_seven {L : Type} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hrk : CFSG.Open.pRank p (⊤ : Subgroup L) = 2) (q : TauCeti.PrimePower)
    (hq : q.card = 7) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (e : L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) : False := by
  have hmod := statedClassicalModel_of_A 1 q hv e
  have hq' : q.p ^ q.exponent = 7 := (TauCeti.PrimePower.card_def q).symm.trans hq
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (k := 1 + 1) (by norm_num) hmod
  rw [hq'] at hcard
  have hL : Nat.card L = 168 := by simpa using hcard
  obtain ⟨E, -, hEcard⟩ := exists_isElemAbelian_card_sq_of_pRank_eq_two hp hrk
  have hdvd : p ^ 2 ∣ Nat.card L := hEcard ▸ Subgroup.card_subgroup_dvd_card E
  rw [hL] at hdvd
  have hle : p ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) hdvd
  have hp12 : p ≤ 12 := by nlinarith
  interval_cases p <;> first | exact hp2 rfl | (revert hdvd hp; decide)

theorem isRankTwoSEGroup_of_pRank_two_psu_three_three {L : Type} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : CFSG.Open.pRank p (⊤ : Subgroup L) = 2)
    (q : TauCeti.PrimePower) (hq : q.card = 3) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (e : L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) : IsRankTwoSEGroup p L := by
  obtain ⟨hqp, hqe⟩ := primePower_eq_three hq
  have hmod := statedClassicalModel_of_twistedA 2 q hv e
  rw [hqp, hqe] at hmod
  have hL : Nat.card L = 6048 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hmod
  obtain ⟨E, -, hEcard⟩ := exists_isElemAbelian_card_sq_of_pRank_eq_two hp hrk
  have hdvd : p ^ 2 ∣ Nat.card L := hEcard ▸ Subgroup.card_subgroup_dvd_card E
  rw [hL] at hdvd
  have hpd : p ∣ 6048 := (dvd_pow_self p two_ne_zero).trans hdvd
  have hp3 : p = 3 := by
    have hle : p ^ 2 ≤ 6048 := Nat.le_of_dvd (by norm_num) hdvd
    have hp77 : p ≤ 77 := by nlinarith
    interval_cases p <;> first | rfl | (exfalso; revert hdvd hp hp2; decide)
  subst hp3
  exact Or.inr (Or.inl ⟨q, hqp, hqe, hv, ⟨e⟩⟩)

end SmallIsomorphisms

section FamilyAssembly

theorem chevTwoPClosureOdd_of_families
    (hLin : ChevTwoPClosureOddFamily LieFamilyLinear)
    (hLinD3 : ChevTwoPClosureOddFamily LieFamilyLinearDiagThree)
    (hLinDB : ChevTwoPClosureOddFamily LieFamilyLinearDiagBig)
    (hUni : ChevTwoPClosureOddFamily LieFamilyUnitary)
    (hUniD3 : ChevTwoPClosureOddFamily LieFamilyUnitaryDiagThree)
    (hUniDB : ChevTwoPClosureOddFamily LieFamilyUnitaryDiagBig)
    (hSp : ChevTwoPClosureOddFamily LieFamilySymplectic)
    (hOrth : ChevTwoPClosureOddFamily LieFamilyOrthogonal)
    (hE6 : ChevTwoPClosureOddFamily LieFamilyE6) (hE7 : ChevTwoPClosureOddFamily LieFamilyE7)
    (hE8 : ChevTwoPClosureOddFamily LieFamilyE8) (hF4 : ChevTwoPClosureOddFamily LieFamilyF4)
    (hG2 : ChevTwoPClosureOddFamily LieFamilyG2)
    (hTwE6 : ChevTwoPClosureOddFamily LieFamilyTwistedE6)
    (hTri : ChevTwoPClosureOddFamily LieFamilyTrialityD4)
    (hSz : ChevTwoPClosureOddFamily LieFamilySuzuki)
    (hRee : ChevTwoPClosureOddFamily LieFamilyReeF4)
    (hTits : ChevTwoPClosureOddFamily LieFamilyTits) : ChevTwoPClosureOdd := by
  intro p hp hp2 L _ _ hs hnab hnalt hchev hrk hSE
  rcases hchev with ⟨⟨dd, hv⟩, hdi, he⟩ | ⟨n, -, he⟩ | ⟨⟨dd, hv⟩, hd, he⟩
  · obtain ⟨e⟩ := he
    cases dd with
    | A r q =>
      by_cases hdiag : p ∣ Nat.gcd (r + 1) (q.card - 1)
      · by_cases h23 : r = 2 ∧ p = 3
        · exact hLinD3 p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ h23 hdi ⟨e⟩
        · exact hLinDB p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ ⟨hdiag, h23⟩ hdi ⟨e⟩
      · exact hLin p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ hdiag hdi ⟨e⟩
    | twistedA r q =>
      by_cases hdiag : p ∣ Nat.gcd (r + 1) (q.card + 1)
      · by_cases h23 : r = 2 ∧ p = 3
        · exact hUniD3 p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ h23 hdi ⟨e⟩
        · exact hUniDB p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ ⟨hdiag, h23⟩ hdi ⟨e⟩
      · exact hUni p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ hdiag hdi ⟨e⟩
    | B r q => exact hSp p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | C r q =>
      exfalso
      have h1 := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).2
      exact h1 hdi
    | D r q => exact hOrth p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | twistedD r q => exact hOrth p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | E6 q => exact hE6 p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | E7 q => exact hE7 p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | E8 q => exact hE8 p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | F4 q => exact hF4 p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | G2 q => exact hG2 p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | twistedE6 q => exact hTwE6 p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | trialityD4 q => exact hTri p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | suzuki m => exact hSz p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | reeG2 m => exact hdi.elim
    | reeF4 m => exact hRee p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
    | tits => exact hTits p hp hp2 L hs hnab hrk hSE ⟨_, hv⟩ trivial hdi ⟨e⟩
  · exact absurd ⟨n, he⟩ hnalt
  · obtain ⟨e⟩ := he
    rcases hd with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact (false_of_pRank_two_psl_two_seven hp hp2 hrk q hq hv e).elim
    · exact (hSE (isRankTwoSEGroup_of_pRank_two_psu_three_three hp hp2 hrk q hq hv e)).elim

end FamilyAssembly

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
