module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.AbelianAmbientNormalizerFixedDisplacement
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.AbelianAmbientNormalizerChain
import CFSG.FeitThompson.Local.SigmaComplementPlaneActionSupport
import CFSG.FeitThompson.Local.RankOnePrimesRegularKappaComplement
import CFSG.FeitThompson.Local.AbelianAmbientRegularFirstFactorCentral
import CFSG.FeitThompson.Local.TauOneHallFixedCentralizer
import CFSG.FeitThompson.Local.TwoBetaFixedCoresHallPosition
import CFSG.FeitThompson.Local.KappaResidualFixedSpaceAndPrimeOrder
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerCommonFactor
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.OddOrder.ExponentComplementCyclicHallAction
import CFSG.FeitThompson.OddOrder.InvariantHallComplement
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Local.CoprimeOddFixedCentralizerTorsion
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.OddPrimeCyclicQuotientLift
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.InvariantComplementFittingSelfCentralizing
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
public import CFSG.FeitThompson.Representations.ZeroFixedSpacePrimeComplementCentralizes
public import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
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
import CFSG.FeitThompson.Local.CoprimeSolvableCommutatorDecomposition

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise

universe u

variable {G : Type u} [Group G]

theorem inf_centralizer_sup_commutator_eq_of_coprime [Finite G] {P X : Subgroup G}
    (hPab : IsMulCommutative ↥P) (hXN : X ≤ normalizer (P : Set G))
    (hcop : (Nat.card ↥X).Coprime (Nat.card ↥P)) :
    (P ⊓ centralizer (X : Set G)) ⊔ (⁅P, X⁆ : Subgroup G) = P ∧
      (P ⊓ centralizer (X : Set G)) ⊓ (⁅P, X⁆ : Subgroup G) = ⊥ := by
  set N : Subgroup G := normalizer (P : Set G) with hNdef
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hCN : P ⊓ centralizer (X : Set G) ≤ N := inf_le_left.trans hPN
  have hPXP : (⁅P, X⁆ : Subgroup G) ≤ P := commutator_le_left_of_le_normalizer hXN
  have hPXN : (⁅P, X⁆ : Subgroup G) ≤ N := hPXP.trans hPN
  have hPnorm : (P.subgroupOf N).Normal :=
    _root_.CFSG.FeitThompson.normal_subgroupOf_of_le_normalizer hPN le_rfl
  have hPab' : IsMulCommutative ↥(P.subgroupOf N) :=
    isMulCommutative_subgroupOf_of_isMulCommutative hPab
  have hcop' : (Nat.card ↥(X.subgroupOf N)).Coprime (Nat.card ↥(P.subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv]
    exact hcop
  have hcw : (P ⊓ centralizer (X : Set G)).subgroupOf N
      = P.subgroupOf N ⊓ centralizer ((X.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    rw [← CFSG.FeitThompson.centralizerWithin_eq P X]
    exact centralizerWithin_subgroupOf_eq hXN
  have hcomm : (⁅P, X⁆ : Subgroup G).subgroupOf N = ⁅P.subgroupOf N, X.subgroupOf N⁆ :=
    (commutator_subgroupOf hPN hXN).symm
  have h1 := sup_inf_centralizer_commutator_eq (P.subgroupOf N) (X.subgroupOf N) hPab' hcop'
  have h2 := inf_centralizer_inf_commutator_eq_bot (P.subgroupOf N) (X.subgroupOf N) hPab' hcop'
  rw [← hcw, ← hcomm] at h1 h2
  constructor
  · have h3 := congrArg (fun S : Subgroup ↥N => S.map N.subtype) h1
    simpa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hCN,
      Subgroup.map_subgroupOf_eq_of_le hPXN, Subgroup.map_subgroupOf_eq_of_le hPN] using h3
  · have h3 := congrArg (fun S : Subgroup ↥N => S.map N.subtype) h2
    simpa [Subgroup.map_inf _ _ _ N.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hCN,
      Subgroup.map_subgroupOf_eq_of_le hPXN] using h3

theorem subgroupOf_lt_subgroupOf {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    (hne : A ≠ B) : A.subgroupOf C < B.subgroupOf C := by
  refine lt_of_le_of_ne (Subgroup.comap_mono hAB) fun h => hne ?_
  have h1 := congrArg (fun S : Subgroup ↥C => S.map C.subtype) h
  simpa [Subgroup.map_subgroupOf_eq_of_le (hAB.trans hBC),
    Subgroup.map_subgroupOf_eq_of_le hBC] using h1

theorem isCyclic_subgroupOf_of_isCyclic {A B : Subgroup G} (hAB : A ≤ B) (h : IsCyclic ↥A) :
    IsCyclic ↥(A.subgroupOf B) :=
  isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAB).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hAB).symm.surjective

theorem inf_centralizer_conj_smul {S X : Subgroup G} {c : G}
    (hc : c ∈ normalizer (S : Set G)) :
    S ⊓ centralizer ((MulAut.conj c • X : Subgroup G) : Set G)
      = MulAut.conj c • (S ⊓ centralizer (X : Set G)) := by
  rw [smul_inf, _root_.CFSG.FeitThompson.conj_smul_eq_self_of_mem_normalizer hc,
    centralizer_conj_smul]

theorem exists_mem_conj_smul_le_of_isHallPiSubgroupOf [Finite G] {π : Set ℕ} {q : ℕ}
    (hq : q.Prime) (hqπ : q ∈ π) {E X₀ E₁ : Subgroup G}
    (hsolv : Group.IsSolvable ↥E) (hX₀E : X₀ ≤ E) (hX₀q : Nat.card ↥X₀ = q)
    (hE₁ : CFSG.FeitThompson.IsHallPiSubgroupOf π E₁ E) :
    ∃ c ∈ E, MulAut.conj c • X₀ ≤ E₁ := by
  have hπ : CFSG.FeitThompson.IsPiSubgroup π X₀ := by
    rw [CFSG.FeitThompson.isPiSubgroup_iff, hX₀q]
    intro r hr
    rw [Nat.mem_primeFactors] at hr
    obtain ⟨hrp, hrq, -⟩ := hr
    rw [(Nat.prime_dvd_prime_iff_eq hrp hq).1 hrq]
    exact hqπ
  obtain ⟨H, hH, hX₀H⟩ := exists_isHallPiSubgroupOf_ge_of_isPiSubgroup hsolv hX₀E hπ
  obtain ⟨c, hcE, hconj⟩ := exists_mem_conj_smul_eq_of_isHallPiSubgroupOf hsolv hH hE₁
  exact ⟨c, hcE, hconj ▸ Set.smul_set_mono hX₀H⟩

theorem dvd_relIndex_of_isPGroup_of_not_le [Finite G] {q : ℕ}
    (hq : q.Prime) {N X Q : Subgroup G} (hNX : N ≤ X) (hXN : X ≤ normalizer (N : Set G))
    (hQX : Q ≤ X) (hQq : IsPGroup q ↥Q) (hQN : ¬ Q ≤ N) : q ∣ N.relIndex X := by
  have hqf := Fact.mk hq
  have hnorm : (N.subgroupOf X).Normal :=
    _root_.CFSG.FeitThompson.normal_subgroupOf_of_le_normalizer hNX hXN
  have hnorm' := hnorm
  set f := QuotientGroup.mk' (N.subgroupOf X) with hf
  have him : (Q.subgroupOf X).map f ≠ ⊥ := by
    intro hb
    refine hQN fun z hz => ?_
    have hzX : z ∈ X := hQX hz
    have h1 : f ⟨z, hzX⟩ ∈ (Q.subgroupOf X).map f := Subgroup.mem_map_of_mem _ hz
    rw [hb, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff (⟨z, hzX⟩ : ↥X)).1 h1
  have hQsub : IsPGroup q ↥(Q.subgroupOf X) :=
    hQq.comap_of_injective X.subtype X.subtype_injective
  have hQ' : IsPGroup q ↥((Q.subgroupOf X).map f) := hQsub.map f
  obtain ⟨k, hk⟩ := hQ'.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact him (Subgroup.eq_bot_of_card_eq _ hk)
  have hdvd : q ∣ Nat.card (↥X ⧸ N.subgroupOf X) :=
    (hk ▸ dvd_pow_self q hk0).trans (Subgroup.card_subgroup_dvd_card _)
  rwa [Subgroup.relIndex, Subgroup.index_eq_card]

theorem eq_of_isPGroup_of_le_of_natCard_eq [Finite G] {q : ℕ} (hq : q.Prime)
    {E S T : Subgroup G} (hS : Nat.card ↥S = q ^ (Nat.card ↥E).factorization q)
    (hST : S ≤ T) (hTE : T ≤ E) (hTq : IsPGroup q ↥T) : T = S := by
  have hqf := Fact.mk hq
  obtain ⟨m, hm⟩ := hTq.exists_card_eq
  have hdvd : q ^ m ∣ Nat.card ↥E := hm ▸ Subgroup.card_dvd_of_le hTE
  have hle : m ≤ (Nat.card ↥E).factorization q :=
    (Nat.Prime.pow_dvd_iff_le_factorization hq Nat.card_pos.ne').1 hdvd
  refine (Subgroup.eq_of_le_of_card_ge hST ?_).symm
  rw [hS, hm]
  exact Nat.pow_le_pow_right hq.pos hle

theorem elementaryAbelianPRank_le_one_of_isCyclic_sylow [Finite G] {q : ℕ}
    (hq : q.Prime) (hqodd : Odd q) {N Q : Subgroup G} (hQN : Q ≤ N)
    (hQcard : Nat.card ↥Q = q ^ (Nat.card ↥N).factorization q) (hQcyc : IsCyclic ↥Q) :
    elementaryAbelianPRank q ↥N ≤ 1 := by
  have hqf := Fact.mk hq
  have hSyl : Nat.card ↥(Q.subgroupOf N) = q ^ (Nat.card ↥N).factorization q := by
    rw [natCard_subgroupOf_of_le hQN, hQcard]
  refine (isCyclic_sylow_iff_elementaryAbelianPRank_le_one hq hqodd
    (Sylow.ofCard (Q.subgroupOf N) hSyl)).1 ?_
  rw [Sylow.coe_ofCard]
  exact isCyclic_subgroupOf_of_isCyclic hQN hQcyc

theorem le_of_isPGroup_of_isHallPiOf_compl [Finite G] {q : ℕ} (hq : q.Prime)
    {M U E D : Subgroup G} (hU : CFSG.FeitThompson.Prep03.IsHallPiOf
      (kappaPrimes M)ᶜ U E) (hUnorm : E ≤ normalizer (U : Set G))
    (hDE : D ≤ E) (hDq : IsPGroup q ↥D) (hqκ : q ∉ kappaPrimes M) : D ≤ U := by
  have hqf := Fact.mk hq
  refine le_of_isHallPiSubgroup_subgroupOf hU.1
    (_root_.CFSG.FeitThompson.normal_subgroupOf_of_le_normalizer hU.1 hUnorm)
    (isHallPiSubgroup_subgroupOf_of_isHallPiOf_compl hU) hDE ?_
  rw [CFSG.FeitThompson.isPiSubgroup_iff]
  intro r hr
  obtain ⟨m, hm⟩ := hDq.exists_card_eq
  rw [hm] at hr
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · rw [pow_zero, Nat.primeFactors_one] at hr; simp at hr
  · rw [Nat.primeFactors_prime_pow hm0.ne' hq, Finset.mem_singleton] at hr
    subst hr
    exact ⟨hq, hqκ⟩

theorem ker_conjAction_eq {P Q : Subgroup G} (hQN : Q ≤ normalizer (P : Set G)) :
    (conjAction hQN).ker = (Q ⊓ centralizer (P : Set G)).subgroupOf Q := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have h1 : ((conjAction hQN x ⟨y, hy⟩ : ↥P) : G) = (y : G) := by rw [h]; rfl
    rw [coe_conjAction_apply] at h1
    calc y * (x : G) = ((x : G) * y * (x : G)⁻¹) * (x : G) := by rw [h1]
      _ = (x : G) * y := by group
  · rintro ⟨-, hc⟩
    ext y
    have hcomm : (y : G) * (x : G) = (x : G) * (y : G) :=
      Subgroup.mem_centralizer_iff.1 hc _ y.2
    have h2 : ((conjAction hQN x y : ↥P) : G) = (y : G) := by
      rw [coe_conjAction_apply, ← hcomm]; group
    simpa using h2

theorem autFixedSubgroup_conjAction_eq_bot {P Q : Subgroup G}
    (hQN : Q ≤ normalizer (P : Set G)) {y : ↥Q}
    (hy : P ⊓ centralizer ({(y : G)} : Set G) = ⊥) :
    autFixedSubgroup (conjAction hQN y) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  rw [autFixedSubgroup_eq_eqLocus] at hz
  have h1 : ((conjAction hQN y z : ↥P) : G) = (z : G) := congrArg (fun w : ↥P => (w : G)) hz
  rw [coe_conjAction_apply] at h1
  have h2 : (z : G) ∈ P ⊓ centralizer ({(y : G)} : Set G) := by
    refine ⟨z.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro g rfl
    calc (y : G) * (z : G) = ((y : G) * (z : G) * (y : G)⁻¹) * (y : G) := by group
      _ = (z : G) * (y : G) := by rw [h1]
  rw [hy, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

theorem isCyclic_of_forall_autFixedSubgroup_eq_bot {q : ℕ} {R : Type*} {W : Type*}
    [Group R] [Finite R] [CommGroup W] [Finite W] [Nontrivial W]
    (hq : q.Prime) (hqodd : Odd q) (hR : IsPGroup q R) (hqW : ¬ q ∣ Nat.card W)
    (ρ : R →* MulAut W) (hfree : ∀ r : R, r ≠ 1 → autFixedSubgroup (ρ r) = ⊥) :
    IsCyclic R := by
  by_contra hnc
  have hnc' : ¬ IsCyclic ↥(⊤ : Subgroup R) := fun h =>
    hnc (isCyclic_of_surjective (⊤ : Subgroup R).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩)
  obtain ⟨B, -, -, ⟨eB⟩⟩ :=
    exists_normal_le_mulEquiv_zmod_prod_of_not_isCyclic_of_isPGroup hq hqodd hR ⊤ hnc'
  have key := iSup_autFixedSubgroup_eq_top_of_mulEquiv eB hq (ρ.comp B.subtype) hqW
  have hle : (⨆ (b : ↥B) (_ : b ≠ 1), autFixedSubgroup ((ρ.comp B.subtype) b)) ≤ ⊥ :=
    iSup₂_le fun b hb => (hfree (b : R) (by simpa using hb)).le
  rw [key] at hle
  obtain ⟨v, hv⟩ := exists_ne (1 : W)
  exact hv (hle (Subgroup.mem_top v))

theorem isCyclic_quotient_ker_conjAction [Finite G] {p q : ℕ} {P Q : Subgroup G}
    (hp : p.Prime) (hq : q.Prime) (hqodd : Odd q) (hqp : q ≠ p)
    (hPab : IsMulCommutative ↥P) (hPnt : P ≠ ⊥) {k : ℕ} (hk : Nat.card ↥P = p ^ k)
    (hQq : IsPGroup q ↥Q) (hQN : Q ≤ normalizer (P : Set G))
    (hno : ∀ X : Subgroup G, X ≤ normalizer (P : Set G) →
      (Nat.card ↥X).Coprime (Nat.card ↥P) →
      P ⊓ centralizer (X : Set G) = ⊥ ∨ P ⊓ centralizer (X : Set G) = P) :
    IsCyclic (↥Q ⧸ (conjAction hQN).ker) := by
  have hqf := Fact.mk hq
  letI : CommGroup ↥P := @IsMulCommutative.instCommGroup ↥P _ hPab
  have hPntv : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hPnt
  have hqW : ¬ q ∣ Nat.card ↥P := by
    rw [hk]
    intro hdvd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hdvd))
  refine isCyclic_of_forall_autFixedSubgroup_eq_bot hq hqodd (hQq.to_quotient _) hqW
    (QuotientGroup.kerLift (conjAction hQN)) ?_
  intro r hr
  induction r using QuotientGroup.induction_on with
  | H y =>
    have hyker : y ∉ (conjAction hQN).ker := fun h => hr ((QuotientGroup.eq_one_iff y).2 h)
    have hXN : (zpowers (y : G)) ≤ normalizer (P : Set G) := zpowers_le.2 (hQN y.2)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hQq) y
    have hXcard : Nat.card ↥(zpowers (y : G)) = q ^ m := by
      rw [Nat.card_zpowers]
      have hord : orderOf ((y : G)) = orderOf y :=
        orderOf_injective Q.subtype Q.subtype_injective y
      rw [hord, hm]
    have hcop : (Nat.card ↥(zpowers (y : G))).Coprime (Nat.card ↥P) := by
      rw [hXcard, hk]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp).2 hqp)
    have hCeq : P ⊓ centralizer ((zpowers (y : G) : Subgroup G) : Set G)
        = P ⊓ centralizer ({(y : G)} : Set G) := by rw [centralizer_coe_zpowers]
    rcases hno _ hXN hcop with hb | ht
    · rw [hCeq] at hb
      simpa using autFixedSubgroup_conjAction_eq_bot hQN hb
    · exfalso
      rw [hCeq] at ht
      refine hyker ?_
      have hPC : P ≤ centralizer ({(y : G)} : Set G) := le_trans ht.ge inf_le_right
      rw [ker_conjAction_eq, Subgroup.mem_subgroupOf]
      refine ⟨y.2, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 (hPC hz) (y : G) rfl).symm

theorem isCyclic_of_isCyclic_quotient_ker_conjAction [Finite G] {q : ℕ}
    {P Q Q₁ : Subgroup G} (hq : q.Prime) (hqodd : Odd q)
    (hQq : IsPGroup q ↥Q) (hQN : Q ≤ normalizer (P : Set G))
    (hDQ₁ : Q ⊓ centralizer (P : Set G) ≤ Q₁) (hQ₁Q : Q₁ ≤ Q)
    (hne : Q ⊓ centralizer (P : Set G) ≠ Q₁) (hQ₁cyc : IsCyclic ↥Q₁)
    (hquot : IsCyclic (↥Q ⧸ (conjAction hQN).ker)) : IsCyclic ↥Q := by
  have hker : (conjAction hQN).ker = (Q ⊓ centralizer (P : Set G)).subgroupOf Q :=
    ker_conjAction_eq hQN
  have hnorm : ((Q ⊓ centralizer (P : Set G)).subgroupOf Q).Normal := by
    rw [← hker]; exact MonoidHom.normal_ker _
  have hnorm' := hnorm
  have hlt : (Q ⊓ centralizer (P : Set G)).subgroupOf Q < Q₁.subgroupOf Q :=
    subgroupOf_lt_subgroupOf hDQ₁ hQ₁Q hne
  have hQ₁' : IsCyclic ↥(Q₁.subgroupOf Q) := isCyclic_subgroupOf_of_isCyclic hQ₁Q hQ₁cyc
  have hquot' : IsCyclic (↥Q ⧸ (Q ⊓ centralizer (P : Set G)).subgroupOf Q) :=
    isCyclic_of_surjective (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hker).surjective
  exact isCyclic_of_isCyclic_quotient_of_lt_isCyclic hq hqodd hQq hlt hQ₁' hquot'

theorem le_centralizer_of_le_centralizer_torsion [Finite G] {p : ℕ} {P A X : Subgroup G}
    (hp : p.Prime) (hodd : Odd p) (hPp : IsPGroup p ↥P)
    (hA : (A : Set G) = {x ∈ (P : Set G) | x ^ p = 1})
    (hXN : X ≤ normalizer (P : Set G)) (hcop : (Nat.card ↥X).Coprime (Nat.card ↥P))
    (hXA : X ≤ centralizer (A : Set G)) : X ≤ centralizer (P : Set G) := by
  have key := apply_eq_self_of_coprime_of_pow_eq_one_mem hp hodd hPp (conjAction hXN) hcop ?_
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : conjAction hXN ⟨g, hg⟩ ⟨y, hy⟩ = ⟨y, hy⟩ := key ⟨g, hg⟩ ⟨y, hy⟩
    have h2 : g * y * g⁻¹ = y := by
      have := congrArg (fun z : ↥P => (z : G)) h1
      simpa [coe_conjAction_apply] using this
    calc y * g = (g * y * g⁻¹) * g := by rw [h2]
      _ = g * y := by group
  · intro x _ hxp
    rw [mem_fixedPoints_range_iff]
    intro b
    have hxA : (x : G) ∈ (A : Set G) := by
      rw [hA]
      exact ⟨x.2, by simpa using congrArg (fun z : ↥P => (z : G)) hxp⟩
    have hcomm : (x : G) * (b : G) = (b : G) * (x : G) :=
      Subgroup.mem_centralizer_iff.1 (hXA b.2) _ hxA
    refine Subtype.ext ?_
    rw [coe_conjAction_apply, ← hcomm]
    group

theorem exists_sylow_not_le_centralizer [Finite G] {p : ℕ} {U P : Subgroup G}
    (hp : p.Prime) (hPU : P ≤ U) (hPab : IsMulCommutative ↥P)
    (hUN : U ≤ normalizer (P : Set G))
    (hPcard : Nat.card ↥P = p ^ (Nat.card G).factorization p)
    (hnc : ¬ P ≤ U ⊓ centralizer (U : Set G)) :
    ∃ (q : ℕ) (Q : Subgroup G), q.Prime ∧ q ≠ p ∧ Q ≤ U ∧
      Nat.card ↥Q = q ^ (Nat.card ↥U).factorization q ∧ ¬ Q ≤ centralizer (P : Set G) := by
  have hUC : ¬ U ≤ centralizer (P : Set G) := by
    intro h
    refine hnc fun x hx => ⟨hPU hx, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (h hy) x hx).symm
  by_contra hcon
  push Not at hcon
  refine hUC (le_centralizer_of_forall_sylow_map_le_centralizer fun q hq S => ?_)
  have hSU : (S : Subgroup ↥U).map U.subtype ≤ U := Subgroup.map_subtype_le _
  have hScard : Nat.card ↥((S : Subgroup ↥U).map U.subtype)
      = q ^ (Nat.card ↥U).factorization q := by
    rw [Subgroup.card_map_of_injective U.subtype_injective]
    have := Fact.mk hq
    exact S.card_eq_multiplicity
  by_cases hqp : q = p
  · subst hqp
    have hSq : IsPGroup q ↥((S : Subgroup ↥U).map U.subtype) := IsPGroup.of_card hScard
    have hle : (S : Subgroup ↥U).map U.subtype ≤ P :=
      le_of_isPGroup_of_le_normalizer_of_natCard_eq hq hPcard hSq (hSU.trans hUN)
    exact hle.trans (by have := hPab; exact Subgroup.le_centralizer P)
  · exact not_not.1 fun h => h (hcon q _ hq hqp hSU hScard)

theorem mem_tau1Primes_of_not_le_centralizer_plane
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    {G : Type u} [Group G] [Fintype G]
    (hGoom : CFSG.FeitThompson.IsOddOrderMinimalSimple G)
    {p : ℕ} {M A E E₁ E₂ E₃ : Subgroup G} (hM : IsCoatom M) (hp : p.Prime)
    (hpσ : p ∉ sigmaPrimes M) (hAM : A ≤ M)
    (hplane : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A)
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) (hAE : A ≤ E)
    (hE₁ : CFSG.FeitThompson.IsHallPiSubgroupOf (tau1Primes M) E₁ E)
    (hE₂ : CFSG.FeitThompson.IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E)
    (hE₃ : CFSG.FeitThompson.IsHallPiSubgroupOf (tau3Primes M) E₃ E)
    (hout : FreeCore.IsInternalSemidirectProduct E E₃ (E₂ ⊔ E₁))
    (hin : FreeCore.IsInternalSemidirectProduct (E₂ ⊔ E₁) E₂ E₁)
    {q : ℕ} (hq : q.Prime) {Q₁ : Subgroup G} (hQ₁E : Q₁ ≤ E) (hQ₁q : IsPGroup q ↥Q₁)
    (hQ₁A : ¬ Q₁ ≤ centralizer (A : Set G)) :
    q ∈ tau1Primes M ∧ q ∣ (E ⊓ centralizer (A : Set G)).relIndex E := by
  obtain ⟨-, hCEAnorm, hτ₁⟩ := sigma_complement_plane_action_support h₃ h₅ h₆ hGoom hM hp hpσ
    hAM hplane hsd hAE hE₁ hE₂ hE₃ hout hin
  have hCE : E ⊓ centralizer (A : Set G) ≤ E := inf_le_left
  have hEnorm : E ≤ normalizer ((E ⊓ centralizer (A : Set G) : Subgroup G) : Set G) :=
    _root_.CFSG.FeitThompson.le_normalizer_of_normal_subgroupOf hCE hCEAnorm
  have hQ₁notle : ¬ Q₁ ≤ E ⊓ centralizer (A : Set G) := fun h => hQ₁A (h.trans inf_le_right)
  have hdvd : q ∣ (E ⊓ centralizer (A : Set G)).relIndex E :=
    dvd_relIndex_of_isPGroup_of_not_le hq hCE hEnorm hQ₁E hQ₁q hQ₁notle
  refine ⟨hτ₁ q ?_, hdvd⟩
  refine Nat.mem_primeFactors.2 ⟨hq, hdvd, ?_⟩
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

theorem dvd_natCard_inf_centralizer_of_regular_line
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    {G : Type u} [Group G] [Fintype G]
    (hGfbg : CFSG.FeitThompson.IsFBGAmbient G)
    {p : ℕ} {M A E P E₁ E₂ E₃ Kt : Subgroup G}
    (haas : CFSG.FeitThompson.IsAbelianAmbientSetup M p A E P)
    (hdec : CFSG.FeitThompson.IsTauHallDecomposition M E E₁ E₂ E₃ Kt)
    (hAE : A ≤ E)
    {q : ℕ} (hq : q.Prime) {X₀ : Subgroup G} (hX₀E : X₀ ≤ E) (hX₀q : Nat.card ↥X₀ = q)
    (hX₀reg : CFSG.FeitThompson.centralizerWithin (sigmaCore M) X₀ = ⊥)
    (hEsolv : Group.IsSolvable ↥E) (hqτ : q ∈ tau1Primes M) :
    q ∣ Nat.card ↥(E ⊓ centralizer (A : Set G)) := by
  obtain ⟨c, hcE, hle⟩ := exists_mem_conj_smul_le_of_isHallPiSubgroupOf hq hqτ hEsolv hX₀E hX₀q
    ⟨hdec.le_E_E₁, hdec.hall_E₁⟩
  set X₁ : Subgroup G := MulAut.conj c • X₀ with hX₁
  have hcN : c ∈ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    le_normalizer_sigmaCore M (haas.le_M_E hcE)
  have hX₁q : Nat.card ↥X₁ = q := by rw [hX₁, natCard_conj_smul, hX₀q]
  have hX₁reg : CFSG.FeitThompson.centralizerWithin (sigmaCore M) X₁
      = ⊥ := by
    rw [CFSG.FeitThompson.centralizerWithin] at hX₀reg ⊢
    rw [hX₁, inf_centralizer_conj_smul hcN, hX₀reg]
    simp
  have hcentral : X₁ ≤ centreIn E := FBG_abelian_ambient_regular_first_factor_central h₁ h₂ h₅ h₆
    h₇ h₈ G hGfbg M p A E P E₁ E₂ E₃ Kt haas hdec q hq X₁ hle hX₁q hX₁reg
  have hZCA : centreIn E ≤ E ⊓ centralizer (A : Set G) := by
    rw [centreIn_eq]
    exact inf_le_inf_left E (Subgroup.centralizer_le (by exact_mod_cast hAE))
  have hdvd : Nat.card ↥X₁ ∣ Nat.card ↥(E ⊓ centralizer (A : Set G)) :=
    Subgroup.card_dvd_of_le (hcentral.trans hZCA)
  rwa [hX₁q] at hdvd

theorem exists_coprime_le_normalizer_inf_centralizer_lt
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_abelian_plane_overlap_normalizer_rank.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    {G : Type u} [Group G] [Fintype G]
    (hG : CFSG.FeitThompson.Prep03.IsAmbient G) {p : ℕ}
    {M A E K U P : Subgroup G}
    (hsetup : CFSG.FeitThompson.Prep03.IsPlaneSetup G p M A E)
    (hK : CFSG.FeitThompson.Prep03.IsHallPiOf (kappaPrimes M) K M)
    (hKE : K ≤ E) (hUE : U ≤ E)
    (hEUK : CFSG.FeitThompson.Prep03.IsSemidirect E U K)
    (hPsyl : CFSG.FeitThompson.Prep03.IsSylowTop p P)
    (hPab : IsMulCommutative ↥P) (hAP : A ≤ P) (hPU : P ≤ U)
    (hnc : ¬ P ≤ CFSG.FeitThompson.Prep03.cent U (U : Set G)) :
    ∃ X : Subgroup G, X ≤ normalizer (P : Set G) ∧ (Nat.card ↥X).Coprime (Nat.card ↥P) ∧
      P ⊓ centralizer (X : Set G) ≠ ⊥ ∧ P ⊓ centralizer (X : Set G) ≠ P := by
  by_contra hcon
  have hno : ∀ X : Subgroup G, X ≤ normalizer (P : Set G) →
      (Nat.card ↥X).Coprime (Nat.card ↥P) →
      P ⊓ centralizer (X : Set G) = ⊥ ∨ P ⊓ centralizer (X : Set G) = P := by
    intro X hXN hcop
    by_cases hb : P ⊓ centralizer (X : Set G) = ⊥
    · exact Or.inl hb
    by_cases ht : P ⊓ centralizer (X : Set G) = P
    · exact Or.inr ht
    exact absurd ⟨X, hXN, hcop, hb, ht⟩ hcon
  clear hcon
  have hp : p.Prime := hsetup.prime
  have hpf := Fact.mk hp
  have hGosm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hGfbg : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hGoom : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    ⟨hsetup.decomp.2.2.2.1, hsetup.decomp.2.2.1, disjoint_iff.2 hsetup.decomp.2.2.2.2⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hsetup.isCoatom, hsd⟩
  have hplane : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A :=
    ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hsetup.isPlane⟩
  have haas : CFSG.FeitThompson.IsAbelianAmbientSetup M p A E P :=
    ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hsetup.isPlane,
      hsetup.decomp.2.1, hsd, hsetup.le_E_A, hPab,
      ⟨Sylow.ofCard P hPsyl, Sylow.coe_ofCard _ _⟩, hAP⟩
  have hAcard : Nat.card ↥A = p ^ 2 := hplane.isElementaryAbelianPlane.natCard'
  have hEM : E ≤ M := hsetup.decomp.2.1
  have hPM : P ≤ M := hPU.trans (hUE.trans hEM)
  have hPp : IsPGroup p ↥P := IsPGroup.of_card hPsyl
  have hpA : p ∣ Nat.card ↥A := by rw [hAcard]; exact dvd_pow_self p two_ne_zero
  have hodd : Odd p := hG.odd_natCard.of_dvd_nat (hpA.trans A.card_subgroup_dvd_card)
  have hMne : M ≠ ⊤ := hsetup.isCoatom.1
  have hEne : E ≠ ⊤ := fun h => hMne (top_le_iff.1 (h ▸ hEM))
  have hEsolv : Group.IsSolvable ↥E := hG.forall_isSolvable E hEne
  have hPnt : P ≠ ⊥ := by
    intro hb
    rw [hb, le_bot_iff] at hAP
    rw [hAP, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1, rfl⟩⟩] at hAcard
    exact absurd hAcard.symm (by simpa using (Nat.one_lt_pow two_ne_zero hp.one_lt).ne')
  obtain ⟨E₁, E₂, E₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hGosm M E hsc
  have hdec : CFSG.FeitThompson.IsTauHallDecomposition
      M E E₁ E₂ E₃ (E₂ ⊔ E₃) :=
    ⟨hsplit.le_E₁, hsplit.le_E₂, hsplit.le_E₃, hsplit.isHall_E₁, hsplit.isHall_E₂,
      hsplit.isHall_E₃, hsplit.outer, hsplit.inner, rfl⟩
  obtain ⟨hNAP, -, -, -, hENA, -, -⟩ := FBG_abelian_ambient_normalizer_chain h₁ h₂ h₅ h₆ h₇ G
    hGfbg M p A E P E₁ E₂ E₃ (E₂ ⊔ E₃) haas hdec
  have hEN : E ≤ normalizer (P : Set G) := hNAP ▸ hENA
  have hUN : U ≤ normalizer (P : Set G) := hUE.trans hEN
  obtain ⟨hrM, hAmax, hsylclause, A₁, hA₁A, hA₁card, hA₁C⟩ := h₆ G hGosm p M A hplane
  have hfacteq : (Nat.card ↥M).factorization p = (Nat.card G).factorization p := by
    refine le_antisymm ((Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1
      ((Nat.ordProj_dvd _ _).trans M.card_subgroup_dvd_card)) ?_
    refine (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1 ?_
    rw [← hPsyl]
    exact Subgroup.card_dvd_of_le hPM
  have hPsylM : _root_.CFSG.FeitThompson.IsSylowIn p M P :=
    (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp hPM).2 (by rw [hPsyl, hfacteq])
  obtain ⟨hAtors, hNS⟩ := (hsylclause P hPsylM).2 hAP
  obtain ⟨q, Q₁, hq, hqp, hQ₁U, hQ₁card, hQ₁C⟩ := exists_sylow_not_le_centralizer hp hPU hPab hUN
    hPsyl hnc
  have hQ₁q : IsPGroup q ↥Q₁ := IsPGroup.of_card hQ₁card
  have hQ₁E : Q₁ ≤ E := hQ₁U.trans hUE
  have hQ₁M : Q₁ ≤ M := hQ₁E.trans hEM
  have hQ₁N : Q₁ ≤ normalizer (P : Set G) := hQ₁E.trans hEN
  have hcopQ₁ : (Nat.card ↥Q₁).Coprime (Nat.card ↥P) := by
    rw [hQ₁card, hPsyl]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp).2 hqp)
  have hqfact := Fact.mk hq
  have hQ₁nt : Q₁ ≠ ⊥ := by
    intro hb
    exact hQ₁C (by rw [hb]; exact bot_le)
  have hqQ₁ : q ∣ Nat.card ↥Q₁ := by
    obtain ⟨m, hm⟩ := hQ₁q.exists_card_eq
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [pow_zero] at hm; exact absurd (Subgroup.eq_bot_of_card_eq _ hm) hQ₁nt
    · exact hm ▸ dvd_pow_self q hm0.ne'
  have hqodd : Odd q := by
    obtain ⟨x, hx, hxord⟩ := exists_mem_orderOf_eq_of_dvd hq hqQ₁
    refine hG.odd_natCard.of_dvd_nat ?_
    rw [← hxord]
    exact orderOf_dvd_natCard x
  have hQ₁A : ¬ Q₁ ≤ centralizer (A : Set G) := fun h =>
    hQ₁C (le_centralizer_of_le_centralizer_torsion hp hodd hPp hAtors hQ₁N hcopQ₁ h)
  obtain ⟨hqτ, hqrel⟩ := mem_tau1Primes_of_not_le_centralizer_plane h₃ h₅ h₆ hGoom
    hsetup.isCoatom hp hsetup.notMem_sigma hsetup.le_M_A
    (CFSG.FeitThompson.isElementaryAbelianPlane_iff.2 hsetup.isPlane)
    hsd hsetup.le_E_A ⟨hsplit.le_E₁, hsplit.isHall_E₁⟩ ⟨hsplit.le_E₂, hsplit.isHall_E₂⟩
    ⟨hsplit.le_E₃, hsplit.isHall_E₃⟩ hsplit.outer hsplit.inner hq hQ₁E hQ₁q hQ₁A
  have hscs : CFSG.FeitThompson.Prep03.IsSigmaComplementSetup G M E K U :=
    ⟨hG, hsetup.isCoatom, hsetup.decomp, hKE, hK, hUE, hEUK⟩
  obtain ⟨hreg, hUhall, hEUnorm⟩ :=
    FNI_kappa_complement_rank_one_prime_regularity h₁ G hG M E K U hscs
  obtain ⟨x, hxQ₁, hxord⟩ := exists_mem_orderOf_eq_of_dvd hq
    (by
      obtain ⟨m, hm⟩ := hQ₁q.exists_card_eq
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [pow_zero] at hm; exact absurd (Subgroup.eq_bot_of_card_eq _ hm) hQ₁nt
      · exact hm ▸ dvd_pow_self q hm0.ne')
  have hxU : x ∈ U := hQ₁U hxQ₁
  have hxreg : CFSG.FeitThompson.Prep03.cent1 (sigmaCore M) x = ⊥ :=
    hreg q (Or.inl hqτ) x hxU hxord
  have hX₀card : Nat.card ↥(zpowers x) = q := by rw [Nat.card_zpowers, hxord]
  have hX₀E : (zpowers x : Subgroup G) ≤ E := (zpowers_le.2 hxQ₁).trans hQ₁E
  have hX₀reg : CFSG.FeitThompson.centralizerWithin (sigmaCore M)
      (zpowers x) = ⊥ := by
    rw [CFSG.FeitThompson.centralizerWithin, centralizer_coe_zpowers]
    exact hxreg
  have hqcard : q ∣ Nat.card ↥(E ⊓ centralizer (A : Set G)) :=
    dvd_natCard_inf_centralizer_of_regular_line h₁ h₂ h₅ h₆ h₇ h₈ hGfbg haas hdec hsetup.le_E_A
      hq hX₀E hX₀card hX₀reg hEsolv hqτ
  have hrank : elementaryAbelianPRank q ↥(normalizer (P : Set G)) = 2 :=
    h₄ G hG p M A E P hsetup hPsyl hPab hAP q hq hqrel hqcard
  obtain ⟨Q, hQ₁Q, hQN, hQcard⟩ :=
    exists_le_natCard_eq_pow_factorization hq hQ₁N hQ₁q
  have hQq : IsPGroup q ↥Q := IsPGroup.of_card hQcard
  have hrQ₁ : elementaryAbelianPRank q ↥M = 1 := (mem_tau1Primes_iff.1 hqτ).2.2.2.1
  have hQ₁cyc : IsCyclic ↥Q₁ :=
    isCyclic_of_elementaryAbelianPRank_le_one hq hqodd hQ₁q
      (le_trans (elementaryAbelianPRank_le_of_le hq.one_lt hQ₁M) hrQ₁.le)
  have hqκ : q ∉ kappaPrimes M := by
    intro hκ
    obtain ⟨-, hUπ, -⟩ := hUhall
    have hqU : q ∣ Nat.card ↥U := hqQ₁.trans (Subgroup.card_dvd_of_le hQ₁U)
    exact hUπ q (Nat.mem_primeFactors.2 ⟨hq, hqU, Nat.card_pos.ne'⟩) hκ
  obtain ⟨-, -, hCAE, -, -⟩ := h₅ G hGosm p M A E hplane hsc hsetup.le_E_A
  have hDE : Q ⊓ centralizer (P : Set G) ≤ E := fun z hz =>
    hCAE (Subgroup.centralizer_le (by exact_mod_cast hAP) hz.2)
  have hDU : Q ⊓ centralizer (P : Set G) ≤ U :=
    le_of_isPGroup_of_isHallPiOf_compl hq hUhall hEUnorm hDE (hQq.to_le inf_le_left) hqκ
  have hQU : Q ⊓ U = Q₁ :=
    eq_of_isPGroup_of_le_of_natCard_eq hq hQ₁card (le_inf hQ₁Q hQ₁U) inf_le_right
      (hQq.to_le inf_le_left)
  have hDQ₁ : Q ⊓ centralizer (P : Set G) ≤ Q₁ := hQU ▸ le_inf inf_le_left hDU
  have hDne : Q ⊓ centralizer (P : Set G) ≠ Q₁ := fun h =>
    hQ₁C (h ▸ inf_le_right : Q₁ ≤ centralizer (P : Set G))
  have hquot : IsCyclic (↥Q ⧸ (conjAction hQN).ker) :=
    isCyclic_quotient_ker_conjAction hp hq hqodd hqp hPab hPnt hPsyl hQq hQN hno
  have hQcyc : IsCyclic ↥Q :=
    isCyclic_of_isCyclic_quotient_ker_conjAction hq hqodd hQq hQN hDQ₁ hQ₁Q hDne hQ₁cyc hquot
  have hr1 : elementaryAbelianPRank q ↥(normalizer (P : Set G)) ≤ 1 :=
    elementaryAbelianPRank_le_one_of_isCyclic_sylow hq hqodd hQN hQcard hQcyc
  rw [hrank] at hr1
  omega

theorem FNI_abelian_normal_hall_noncentral_action_split
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_abelian_plane_overlap_normalizer_rank.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_abelian_normal_hall_noncentral_action_split.{u} := by
  intro G _ _ hG p M A E K U P hsetup hK hKE hUE hEUK hPsyl hPab hAP hPU hnc
  have hp : p.Prime := hsetup.prime
  have hpfact : Fact p.Prime := ⟨hp⟩
  have hGfbg : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    ⟨hsetup.decomp.2.2.2.1, hsetup.decomp.2.2.1, disjoint_iff.2 hsetup.decomp.2.2.2.2⟩
  have haas : CFSG.FeitThompson.IsAbelianAmbientSetup M p A E P :=
    ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hsetup.isPlane,
      hsetup.decomp.2.1, hsd, hsetup.le_E_A, hPab,
      ⟨Sylow.ofCard P hPsyl, Sylow.coe_ofCard _ _⟩, hAP⟩
  obtain ⟨X, hXN, hcop, hP₀ne, hP₀ne'⟩ :=
    exists_coprime_le_normalizer_inf_centralizer_lt h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hG hsetup hK hKE hUE
      hEUK hPsyl hPab hAP hPU hnc
  obtain ⟨hsup, hinf⟩ := inf_centralizer_sup_commutator_eq_of_coprime hPab hXN hcop
  obtain ⟨hn₀, hn₁⟩ :=
    FBG_abelian_ambient_normalizer_fixed_displacement h₁ h₅ h₆ h₇ G hGfbg M p A E P haas X hXN
  have hP₀P : P ⊓ centralizer (X : Set G) ≤ P := inf_le_left
  have hP₁P : (⁅P, X⁆ : Subgroup G) ≤ P := commutator_le_left_of_le_normalizer hXN
  have hP₀N : P ⊓ centralizer (X : Set G) ≤ normalizer (P : Set G) :=
    hP₀P.trans Subgroup.le_normalizer
  have hP₁N : (⁅P, X⁆ : Subgroup G) ≤ normalizer (P : Set G) :=
    hP₁P.trans Subgroup.le_normalizer
  have hP₁ne : (⁅P, X⁆ : Subgroup G) ≠ ⊥ := by
    intro hb
    rw [hb, sup_bot_eq] at hsup
    exact hP₀ne' hsup
  refine ⟨P ⊓ centralizer (X : Set G), ⁅P, X⁆, hP₀ne, hP₁ne, hP₀P, hP₁P, ?_, ?_, hsup, hinf⟩
  · exact _root_.CFSG.FeitThompson.le_normalizer_of_normal_subgroupOf hP₀N
      (by rw [← CFSG.FeitThompson.centralizerWithin_eq P X] at hP₀N ⊢; exact hn₀)
  · exact _root_.CFSG.FeitThompson.le_normalizer_of_normal_subgroupOf hP₁N hn₁

end

end CFSG.FeitThompson.Proofs
