module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
import CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantElemAbelianFixed
import CFSG.LocalAnalysis.RankThreeUC.Section5.CanonicalBFixedHyperplane
import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.SymmetryReduction

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.Section5
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_ne_self {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Subgroup G} (hK : IsPGroup p K)
    {t x : G} (ht2 : t * t = 1) (hcK : x⁻¹ * t * x * t⁻¹ ∈ K) (hxt : x * t ≠ t * x) :
    t * (x⁻¹ * t * x * t⁻¹) * t⁻¹ ≠ x⁻¹ * t * x * t⁻¹ := by
  intro h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hinv : t * (x⁻¹ * t * x * t⁻¹) * t⁻¹ = (x⁻¹ * t * x * t⁻¹)⁻¹ := by
    have e1 : t * (x⁻¹ * t * x * t⁻¹) * t⁻¹ = t * x⁻¹ * t * x * (t⁻¹ * t⁻¹) := by group
    have e2 : (x⁻¹ * t * x * t⁻¹)⁻¹ = t * x⁻¹ * t⁻¹ * x := by group
    rw [e1, e2, htinv, ht2, mul_one]
  have hcc : (x⁻¹ * t * x * t⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    calc (x⁻¹ * t * x * t⁻¹) * (x⁻¹ * t * x * t⁻¹)
        = (x⁻¹ * t * x * t⁻¹) * (t * (x⁻¹ * t * x * t⁻¹) * t⁻¹) := by rw [h]
      _ = 1 := by rw [hinv, mul_inv_cancel]
  have hc1 := CFSG.RankThree.PartTwo.Sec13.CritProof.eq_one_of_isPGroup_zpowers hK hcK hcc
    (Nat.coprime_two_left.2 ((Fact.out : p.Prime).odd_of_ne_two hp2))
  apply hxt
  calc x * t = x * (x⁻¹ * t * x * t⁻¹) * t := by rw [hc1, mul_one]
    _ = t * x := by group

theorem exists_special {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {t : G} (ht : orderOf t = 2)
    (htP : t ∈ Subgroup.centralizer (P : Set G))
    (hOt : ⁅CFSG.Open.pCoreOf p (⊤ : Subgroup G), Subgroup.zpowers t⁆ ≠ ⊥) :
    ∃ Q : Subgroup G, Q.Normal ∧ P ≤ Q ∧ Q ≤ Subgroup.centralizer (P : Set G) ∧
      (∀ x ∈ Q, x ^ p = 1) ∧
      (∀ b ∈ B, b ≠ 1 → IsCyclic ↥(Q ⊓ Subgroup.centralizer ({b} : Set G))) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ P) ∧
      (∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x ∈ P) ∧
      ∃ y₀ ∈ Q, y₀ * t * y₀⁻¹ * t⁻¹ ∉ P := by
  classical
  have hS := hc.oddPrimeClassTwoAction.setting
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hp2 : p ≠ 2 := by
    intro h
    have hodd := hS.odd
    rw [h] at hodd
    exact absurd hodd (by decide)
  have hPn : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  have hel := isElemAbelian_of_binary_rank_counterexample hc
  have hderived : P ≤ commutator G :=
    LargeElementaryDerivedContainment.derived_le hc.oddPrimeClassTwoAction
      hc.faithfulBinaryIrreducibleAction hel
      (by have := (three_lt_pRank_and_prime_not_dvd_card_actor hc).1; omega)
  have hPsQ := AlphaScriptQ.mem_scriptQ hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction
    hderived
  have hpα := AlphaScriptQ.mem_alpha hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction
    hderived
  have hcan := CanonicalBFixedHyperplane.canonical hc
  have hP1 : P ≠ ⊥ := fun h => hcan.2.1.1 (by rw [h, bot_inf_eq])
  have hcommP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  set O : Subgroup G := CFSG.Open.pCoreOf p (⊤ : Subgroup G) with hOdef
  have hOn : O.Normal :=
    (CFSG.LieType.BorelTits.pCore_normal p).map _ (fun g => ⟨⟨g, trivial⟩, rfl⟩)
  have hOp : IsPGroup p O := (CFSG.LieType.BorelTits.pCore_isPGroup p).map (⊤ : Subgroup G).subtype
  have hPO : P ≤ O := fun x hx =>
    ⟨⟨x, trivial⟩, CFSG.LieType.BorelTits.le_pCore p (hPn.subgroupOf _) hS.pGroup.comap_subtype hx, rfl⟩
  set R : Subgroup G := O ⊓ Subgroup.centralizer (P : Set G) ⊓ commutator G with hRdef
  haveI : P.Normal := hPn
  haveI : O.Normal := hOn
  have hRn : R.Normal := inferInstance
  have hRp : IsPGroup p R := hOp.to_le (inf_le_left.trans inf_le_left)
  have hRP : R ≤ Subgroup.centralizer (P : Set G) := inf_le_left.trans inf_le_right
  have hPR : P ≤ R :=
    le_inf (le_inf hPO fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => hcommP y hy x hx) hderived
  obtain ⟨x, hxO, hxt⟩ : ∃ x ∈ O, x * t ≠ t * x := by
    by_contra hno
    push Not at hno
    apply hOt
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_left (hno y hy).symm k).eq
  have hcR : x⁻¹ * t * x * t⁻¹ ∈ R := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h2 := O.mul_mem (O.inv_mem hxO) (hOn.conj_mem x hxO t)
      simpa [mul_assoc] using h2
    · have h1 := (inferInstance : (Subgroup.centralizer (P : Set G)).Normal).conj_mem t htP x⁻¹
      have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ htP)
      simpa using h2
    · have h3 : ⁅x⁻¹, t⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      simpa [commutatorElement_def] using h3
  have hct := conj_ne_self hp2 hOp ht2 hcR.1.1 hxt
  obtain ⟨C, hCcrit, -, -, hΩset, hΩchar, -, hΩcomm, hΩexp, -, hΩdet⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical_omega (P := ↥R) hp2 hRp
  set Ω := CFSG.RankThree.PartTwo.Sec13.CritProof.omegaOneIn p C with hΩdef
  set Q : Subgroup G := Ω.map R.subtype with hQdef
  have hQR : Q ≤ R := Subgroup.map_subtype_le _
  have hQn : Q.Normal := by
    haveI : R.Normal := hRn
    haveI : Ω.Characteristic := hΩchar
    exact ConjAct.normal_of_characteristic_of_normal
  have hQP : Q ≤ Subgroup.centralizer (P : Set G) := hQR.trans hRP
  have hΩQ : ∀ ω ∈ Ω, (ω : G) ∈ Q := fun ω hω => ⟨ω, hω, rfl⟩
  have hQexp : ∀ y ∈ Q, y ^ p = 1 := by
    rintro _ ⟨ω, hω, rfl⟩
    exact congrArg Subtype.val (hΩexp ω hω)
  have hPQ : P ≤ Q := by
    intro u hu
    refine ⟨⟨u, hPR hu⟩, ?_, rfl⟩
    have hcent : (⟨u, hPR hu⟩ : ↥R) ∈ Subgroup.centralizer (C : Set ↥R) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r _
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hRP r.2) u hu).symm
    rw [hCcrit.2.2.2] at hcent
    exact (Set.ext_iff.1 hΩset _).2 ⟨hcent.1, Subtype.ext (hel.2 u hu)⟩
  have hQcz : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Q ∧
      ∀ z ∈ Q, z * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * z := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h := hΩcomm (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b))
    refine ⟨⟨_, h.1, rfl⟩, ?_⟩
    rintro _ ⟨c', hc', rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 h.2 c' hc')
  have hQcyc : ¬ IsCyclic ↥Q := fun h => hPsQ.2.2.1 (haveI := h; Subgroup.isCyclic_of_le hPQ)
  have hQexpo : Monoid.exponent ↥Q = p := by
    have hdvd : Monoid.exponent ↥Q ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (hQexp y.1 y.2)
    rcases (Nat.dvd_prime hS.prime).1 hdvd with h | h
    · exfalso
      rw [Monoid.exp_eq_one_iff] at h
      obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hP1
      have h1 : (⟨u.1, hPQ u.2⟩ : ↥Q) = 1 := @Subsingleton.elim _ h _ _
      exact hu (Subtype.ext (congrArg Subtype.val h1 : (u : G) = 1))
    · exact h
  have hQcomm2 : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hQcz x hx y hy).2 z hz
  have hQsQ : Q ∈ scriptQ G p :=
    ⟨hQn, fun y => ⟨1, by rw [pow_one]; exact Subtype.ext (hQexp y.1 y.2)⟩, hQcyc, hQexpo, hQcomm2,
      hQR.trans inf_le_right⟩
  have hQcb : ∀ b ∈ B, b ≠ 1 → IsCyclic ↥(Q ⊓ Subgroup.centralizer ({b} : Set G)) := fun b hb hb1 =>
    hc.cyclicCentralizersAndFewComponentConjugates.cyclic_centralizer p hpα Q hQsQ b hb hb1
  set Zc : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G) with hZcdef
  haveI : Q.Normal := hQn
  have hZcn : Zc.Normal := inferInstance
  have hZcel : CFSG.Open.IsElemAbelian p Zc := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hQexp x hx.1⟩
    exact Subgroup.mem_centralizer_iff.1 b.2.2 a a.2.1
  have hPZc : P ≤ Zc := fun u hu => ⟨hPQ hu, Subgroup.mem_centralizer_iff.2 fun y hy =>
    (Subgroup.mem_centralizer_iff.1 (hQP hy) u hu).symm⟩
  have hZcyc : ∀ b ∈ B, b ≠ 1 → IsCyclic ↥(Zc ⊓ Subgroup.centralizer ({b} : Set G)) := by
    intro b hb hb1
    haveI := hQcb b hb hb1
    exact Subgroup.isCyclic_of_le (inf_le_inf_right _ inf_le_left)
  have hZcP := InvariantElemAbelianFixed.eq_of_normal_of_le hc hZcn hZcel hPZc hZcyc
  have hcenter : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x ∈ P := by
    intro x hx hxy
    rw [← hZcP]
    exact ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => (hxy y hy).symm⟩
  have hQQP : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ P := by
    intro x hx y hy
    have h := hQcz x hx y hy
    rw [← hZcP]
    exact ⟨h.1, Subgroup.mem_centralizer_iff.2 h.2⟩
  have hnontriv : ∃ y ∈ Q, y * t ≠ t * y := by
    by_contra hno
    push Not at hno
    haveI : R.Normal := hRn
    set φ : MulAut ↥R := MulAut.conjNormal t with hφ
    have hφ2 : φ ^ 2 = 1 := by
      rw [hφ, ← map_pow, pow_two, ht2, map_one]
    have hφcop : Nat.Coprime (orderOf φ) p :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hφ2)
        (Nat.coprime_two_left.2 (hS.prime.odd_of_ne_two hp2))
    have hφΩ : ∀ ω ∈ Ω, φ ω = ω := by
      intro ω hω
      apply Subtype.ext
      rw [hφ, MulAut.conjNormal_apply, ← hno _ (hΩQ ω hω), mul_inv_cancel_right]
    have hφ1 := hΩdet φ hφcop hφΩ
    apply hct
    have h4 := congrArg (fun ψ : MulAut ↥R => ((ψ ⟨_, hcR⟩ : ↥R) : G)) hφ1
    simpa [hφ, MulAut.conjNormal_apply] using h4
  obtain ⟨y, hyQ, hyt⟩ := hnontriv
  refine ⟨Q, hQn, hPQ, hQP, hQexp, hQcb, hQQP, hcenter, y⁻¹, Q.inv_mem hyQ, ?_⟩
  intro hP
  rw [inv_inv] at hP
  have hdQ : y⁻¹ * t * y * t⁻¹ ∈ Q := by
    have h5 := Q.mul_mem (Q.inv_mem hyQ) (hQn.conj_mem y hyQ t)
    simpa [mul_assoc] using h5
  apply conj_ne_self hp2 hQsQ.2.1 ht2 hdQ hyt
  rw [← Subgroup.mem_centralizer_iff.1 htP _ hP]
  group

end CFSG.LocalAnalysis.RankThreeUC.Section5.SymmetryReduction
