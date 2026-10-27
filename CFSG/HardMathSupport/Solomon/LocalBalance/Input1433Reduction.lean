module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Input1433Type
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Interface
import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Main27
import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Core
import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.Yardstones.Md42047359a2a
open scoped commutatorElement

abbrev ZQ {X : Type} [Group X] (Q : Subgroup X) : Subgroup X :=
  (Subgroup.center ↥Q).map Q.subtype

structure I1433Cfg {X : Type} [Group X] [Finite X] (K Q₁ Q J : Subgroup X) (t : X) (q : ℕ) :
    Prop where
  setup : Input14_33Setup K Q₁ Q t
  comp : CFSG.Open.IsComponentOf J
    (GLAPLayer 3 (K ⊓ Subgroup.centralizer ((ZQ Q : Subgroup X) : Set X)))
  zle : ZQ Q ≤ J
  sl3 : IsSL3EpsOver (↥J ⧸ GLAPPrimeCore 3 ↥J) q
  zctr : ((ZQ Q).subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) =
    Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J)
  ord : (Nat.card J).factorization 3 = 3

theorem input14_33TypeSameField_iff :
    Input14_33TypeSameField ↔
      ∀ (X : Type) [Group X] [Finite X] (K Q₁ Q J : Subgroup X) (t : X) (q : ℕ),
        I1433Cfg K Q₁ Q J t q → IsD4Over ↥K q := by
  constructor
  · intro h X _ _ K Q₁ Q J t q c
    exact h X K Q₁ Q J t q c.setup c.comp c.zle c.sl3 c.zctr c.ord
  · intro h X _ _ K Q₁ Q J t q hS hJ hZJ hSL hZc hf3
    exact h X K Q₁ Q J t q ⟨hS, hJ, hZJ, hSL, hZc, hf3⟩

theorem card_center_eq_three {Q : Type*} [Group Q] [Finite Q] (hc : Nat.card Q = 27)
    (hna : ¬ ∀ a c : Q, a * c = c * a) : Nat.card (Subgroup.center Q) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 Q := IsPGroup.of_card (n := 3) (by simpa using hc)
  have hQnt : Nontrivial Q := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hc]; norm_num
  have hnt : Nontrivial (Subgroup.center Q) := hp.center_nontrivial
  have hdvd : Nat.card (Subgroup.center Q) ∣ 3 ^ 3 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center Q)
    rwa [hc] at this
  obtain ⟨i, hi, hZ⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have h1 : 1 < Nat.card (Subgroup.center Q) := Finite.one_lt_card
  interval_cases i
  · rw [pow_zero] at hZ; omega
  · simpa using hZ
  · exfalso
    apply hna
    have hcard : Nat.card (Q ⧸ Subgroup.center Q) = 3 := by
      have h := (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q))
      rw [hc, hZ] at h
      omega
    haveI : IsCyclic (Q ⧸ Subgroup.center Q) := isCyclic_of_prime_card hcard
    exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center Q))
      (by simp)
  · exfalso
    apply hna
    have : Subgroup.center Q = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hZ, hc]; norm_num
    intro a c
    have ha : a ∈ Subgroup.center Q := by rw [this]; trivial
    exact ((Subgroup.mem_center_iff.1 ha) c).symm

section PRank

variable {G : Type*} [Group G] [Finite G]

theorem pRank_set_bddAbove (p : ℕ) (hp : 2 ≤ p) (H : Subgroup G) :
    BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨E, -, -, hk⟩
  have h1 : p ^ k ≤ Nat.card G := hk ▸ Subgroup.card_le_card_group E
  have h2 : k < p ^ k := Nat.lt_pow_self (by omega)
  omega

theorem le_pRank (p : ℕ) (hp : 2 ≤ p) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p H :=
  le_csSup (pRank_set_bddAbove p hp H) ⟨E, hEH, hE, hk⟩

theorem pRank_le_card (p : ℕ) (hp : 2 ≤ p) (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ Nat.card G := by
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hk⟩
  have h1 : p ^ k ≤ Nat.card G := hk ▸ Subgroup.card_le_card_group E
  have h2 : k < p ^ k := Nat.lt_pow_self (by omega)
  omega

theorem pRank_normalizer_le_twoLocal (p : ℕ) (hp : 2 ≤ p) {P : Subgroup G} (hP1 : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) :
    CFSG.Open.pRank p (Subgroup.normalizer (P : Set G)) ≤ GLATwoLocalRank p G := by
  refine le_csSup ?_ ⟨_, ⟨P, hP1, hP2, rfl⟩, rfl⟩
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨H, -, rfl⟩
  exact pRank_le_card p hp H

end PRank

variable {X : Type} [Group X] [Finite X] {K Q₁ Q J : Subgroup X} {t : X} {q : ℕ}

theorem I1433Cfg.card_zq (c : I1433Cfg K Q₁ Q J t q) : Nat.card (ZQ Q) = 3 := by
  have h1 : Nat.card (ZQ Q) = Nat.card (Subgroup.center ↥Q) :=
    Subgroup.card_map_of_injective Q.subtype_injective
  rw [h1]
  refine card_center_eq_three c.setup.orderQ fun h => c.setup.nonabelianQ ?_
  intro a ha b hb
  exact congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩)

theorem I1433Cfg.exists_gen (c : I1433Cfg K Q₁ Q J t q) :
    ∃ z : X, z ∈ K ∧ orderOf z = 3 ∧ ZQ Q = Subgroup.zpowers z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 := c.card_zq
  haveI : IsCyclic (ZQ Q) := isCyclic_of_prime_card hc3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(ZQ Q))
  have hord : orderOf g = 3 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hc3]
  refine ⟨(g : X), c.setup.containedZ g.2, ?_, ?_⟩
  · rw [← hord]; exact (Subgroup.orderOf_coe g)
  · apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
    · exact Subgroup.zpowers_le.2 g.2

theorem centralizer_zpowers_eq (z : X) :
    Subgroup.centralizer ((Subgroup.zpowers z : Subgroup X) : Set X) =
      Subgroup.centralizer ({z} : Set X) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact h z (Subgroup.mem_zpowers z)
  · intro h g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (Commute.zpow_left (show Commute z x from h) n).eq

theorem I1433Cfg.comp3 (c : I1433Cfg K Q₁ Q J t q) {z : X} (hz : ZQ Q = Subgroup.zpowers z) :
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({z} : Set X)) J := by
  have hcomp : CFSG.Open.IsComponentOf J
      (GLAPLayer 3 (K ⊓ Subgroup.centralizer ({z} : Set X))) := by
    have := c.comp
    rw [hz, centralizer_zpowers_eq z] at this
    exact this
  set H := K ⊓ Subgroup.centralizer ({z} : Set X) with hH
  have hJle : J ≤ H := hcomp.1.trans (Lemma514Ns.glaPLayer_le' 3 H)
  have hlayer : CFSG.Open.IsSubnormal (GLAPLayer 3 H) H :=
    CFSG.Open.IsSubnormal.step (Lemma514Ns.glaPLayer_le' 3 H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Lemma514Ns.glaPLayer_le' 3 H)).2
        (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.le_normalizer_glaPLayer 3 H))
      (CFSG.Open.IsSubnormal.refl H)
  have hsn : CFSG.Open.IsSubnormal J H := isSubnormal_trans' hcomp.2.1 hlayer
  have h3 : 3 ∣ Nat.card J := Nat.dvd_of_factorization_pos (by rw [c.ord]; norm_num)
  exact i253_glaPComponent_of_subnormal hJle hsn hcomp.2.2 h3

theorem I1433Cfg.primeCore_K (c : I1433Cfg K Q₁ Q J t q) : GLAPPrimeCore 3 ↥K = ⊥ := by
  haveI := c.setup.normal
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K)
  have hM : ((GLAPPrimeCore 3 ↥K).map K.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨n, hn, rfl⟩ := hx
    have h2 := map_gLAPPrimeCore 3 (MulAut.conjNormal g : ↥K ≃* ↥K)
    have hmem : MulAut.conjNormal g n ∈ GLAPPrimeCore 3 ↥K := h2.le ⟨n, hn, rfl⟩
    exact ⟨MulAut.conjNormal g n, hmem, by simp [MulAut.conjNormal_apply]⟩
  have hle : (GLAPPrimeCore 3 ↥K).map K.subtype ≤ GLAPPrimeCore 3 X := by
    refine le_sSup ⟨hM, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective]; exact hcop
  rw [c.setup.coreFree] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective (GLAPPrimeCore 3 ↥K) K.subtype_injective).1
    (le_bot_iff.1 hle)

theorem I1433Cfg.zq_inf_center (c : I1433Cfg K Q₁ Q J t q) :
    ZQ Q ⊓ (Subgroup.center ↥K).map K.subtype = ⊥ := by
  haveI : Fact (Nat.card ↥(ZQ Q)).Prime := ⟨by rw [c.card_zq]; exact Nat.prime_three⟩
  have h := Subgroup.eq_bot_or_eq_top_of_prime_card
    (((Subgroup.center ↥K).map K.subtype).subgroupOf (ZQ Q))
  rcases h with h | h
  · exact disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h).symm
  · exact absurd (Subgroup.subgroupOf_eq_top.1 h) c.setup.noncentralZ

theorem I1433Cfg.faithful (c : I1433Cfg K Q₁ Q J t q) :
    Q ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := c.setup.normal
  have hQ3 : IsPGroup 3 ↥Q := IsPGroup.of_card (n := 3) (by simpa using c.setup.orderQ)
  haveI : Group.IsNilpotent ↥Q := hQ3.isNilpotent
  haveI hCn : (Subgroup.centralizer (K : Set X)).Normal := inferInstance
  haveI : ((Subgroup.centralizer (K : Set X)).subgroupOf Q).Normal := hCn.subgroupOf Q
  by_contra hne
  have hne' : (Subgroup.centralizer (K : Set X)).subgroupOf Q ≠ ⊥ := by
    intro h
    apply hne
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_iff.1 h.symm
  have hm := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  obtain ⟨⟨x, hxH⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hm
  obtain ⟨hxC, hxZ⟩ := Subgroup.mem_inf.1 hxH
  have hxC' : (x : X) ∈ Subgroup.centralizer (K : Set X) := Subgroup.mem_subgroupOf.1 hxC
  have hxZQ : (x : X) ∈ ZQ Q := ⟨x, hxZ, rfl⟩
  have hxK : (x : X) ∈ K := c.setup.containedZ hxZQ
  have hxKc : (x : X) ∈ (Subgroup.center ↥K).map K.subtype :=
    ⟨⟨(x : X), hxK⟩, Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 hxC') g.1 g.2), rfl⟩
  have hbot := c.zq_inf_center
  have : (x : X) ∈ ZQ Q ⊓ (Subgroup.center ↥K).map K.subtype := ⟨hxZQ, hxKc⟩
  rw [hbot] at this
  have hx' : (x : X) = 1 := Subgroup.mem_bot.1 this
  exact hx1 (Subtype.ext (Subtype.ext hx'))

theorem I1433Cfg.q1_eq_commutator (c : I1433Cfg K Q₁ Q J t q) :
    Q₁ = ⁅Q₁, Subgroup.zpowers t⁆ := by
  classical
  have hzp : Subgroup.zpowers t ≤ Subgroup.normalizer (Q₁ : Set X) :=
    Subgroup.zpowers_le.2 c.setup.normalizes
  have hTle : ⁅Q₁, Subgroup.zpowers t⁆ ≤ Q₁ := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h2 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ Q₁ :=
      (Subgroup.mem_normalizer_iff.1 (hzp hg₂) g₁⁻¹).1 (Q₁.inv_mem hg₁)
    rw [commutatorElement_def]
    have : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by group
    rw [this]
    exact Q₁.mul_mem hg₁ h2
  refine le_antisymm ?_ hTle
  have hQ3 : IsPGroup 3 ↥Q₁ := c.setup.threeGroup
  set T' : Subgroup ↥Q₁ := (⁅Q₁, Subgroup.zpowers t⁆).subgroupOf Q₁ with hT'
  have hsq : ∀ x : ↥Q₁, x ^ 2 ∈ T' ⊔ frattini ↥Q₁ := by
    intro x
    obtain ⟨φ, hφ, hφeq⟩ := c.setup.inverts ((x : X)⁻¹) (Q₁.inv_mem x.2)
    have hw : (⁅(x : X), t⁆ : X) ∈ Q₁ := hTle (Subgroup.commutator_mem_commutator x.2
      (Subgroup.mem_zpowers t))
    have hwT' : (⟨⁅(x : X), t⁆, hw⟩ : ↥Q₁) ∈ T' :=
      Subgroup.mem_subgroupOf.2 (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_zpowers t))
    have hnorm : (x * φ * x⁻¹)⁻¹ ∈ frattini ↥Q₁ :=
      (frattini ↥Q₁).inv_mem ((Subgroup.Normal.conj_mem inferInstance φ hφ x))
    have heq : x ^ 2 = (x * φ * x⁻¹)⁻¹ * ⟨⁅(x : X), t⁆, hw⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, pow_two, commutatorElement_def]
      have h3 : (φ : X) = t * (x : X)⁻¹ * t⁻¹ * (x : X)⁻¹ := by
        simpa using hφeq
      rw [mul_inv_rev, mul_inv_rev, inv_inv, h3]
      group
    rw [heq]
    have hmem := Subgroup.mul_mem_sup hnorm hwT'
    rwa [sup_comm] at hmem
  have hfr : T' ⊔ frattini ↥Q₁ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨k, hk⟩ := hQ3 x
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    obtain ⟨j, hj⟩ := hodd
    have hx : x = (x ^ (j + 1)) ^ 2 := by
      have h1 : x ^ (3 ^ k + 1) = x := by
        rw [pow_succ, hk, one_mul]
      rw [← pow_mul]
      have h2 : (j + 1) * 2 = 3 ^ k + 1 := by omega
      rw [h2, h1]
    rw [hx]
    exact hsq _
  have htop := frattini_nongenerating hfr
  intro y hy
  have : (⟨y, hy⟩ : ↥Q₁) ∈ T' := by rw [htop]; trivial
  exact Subgroup.mem_subgroupOf.1 this

theorem I1433Cfg.map_le_derived [K.Normal] (c : I1433Cfg K Q₁ Q J t q) :
    Q.map (MulAut.conjNormal : X →* MulAut ↥K) ≤ commutator (MulAut ↥K) := by
  have h1 : Q ≤ ⁅Q₁, Subgroup.zpowers t⁆ := c.setup.contained.trans c.q1_eq_commutator.le
  refine (Subgroup.map_mono h1).trans ?_
  rw [Subgroup.map_commutator, _root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top

theorem rank_le_four_of_normalizes (hX : GLATwoLocalRank 3 X ≤ 4) {U B : Subgroup X}
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hB : B ≤ Subgroup.normalizer (U : Set X))
    (hBe : CFSG.Open.IsElemAbelian 3 B) {m : ℕ} (hm : Nat.card B = 3 ^ m) : m ≤ 4 :=
  (le_pRank 3 (by norm_num) hB hBe hm).trans
    ((pRank_normalizer_le_twoLocal 3 (by norm_num) hU1 hU2).trans hX)

theorem exists_order_three_of_centralizerRank
    (h1 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (K : Set X))) :
    ∃ c₀ ∈ Subgroup.centralizer (K : Set X), c₀ ≠ 1 ∧ c₀ ^ 3 = 1 := by
  have hbdd := pRank_set_bddAbove 3 (by norm_num) (Subgroup.centralizer (K : Set X))
  have hne : {k | ∃ E : Subgroup X, E ≤ Subgroup.centralizer (K : Set X) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : CFSG.Open.pRank 3 (Subgroup.centralizer (K : Set X)) = 0 := by
      unfold CFSG.Open.pRank; rw [h]; exact csSup_empty
    omega
  obtain ⟨E₀, hE₀C, hE₀, hE₀card⟩ := Nat.sSup_mem hne hbdd
  have h1' : 1 ≤ sSup {k | ∃ E : Subgroup X, E ≤ Subgroup.centralizer (K : Set X) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := h1
  have hlt : 1 < Nat.card E₀ := by
    rw [hE₀card]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  obtain ⟨⟨c₀, hc₀E⟩, hc₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    ((Subgroup.one_lt_card_iff_ne_bot E₀).1 hlt)
  exact ⟨c₀, hE₀C hc₀E, fun h => hc₀1 (Subtype.ext h), hE₀.2 c₀ hc₀E⟩

theorem I1433Cfg.rank_le (c : I1433Cfg K Q₁ Q J t q) :
    GLATwoLocalRank 3 ↥K ≤ CFSG.Open.pRank 3 ((Subgroup.center ↥K).map K.subtype) + 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c₀, hc₀C, hc₀1, hc₀3⟩ := exists_order_three_of_centralizerRank c.setup.centralizerRank
  have hX4 := c.setup.localRank
  have hc₀ord : orderOf c₀ = 3 := orderOf_eq_prime hc₀3 hc₀1
  have hcyc3 : Nat.card (Subgroup.zpowers c₀) = 3 := by rw [Nat.card_zpowers, hc₀ord]
  have hzp_cent : Subgroup.zpowers c₀ ≤ Subgroup.centralizer (K : Set X) :=
    Subgroup.zpowers_le.2 hc₀C
  have hzp_el : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers c₀) := by
    refine ⟨inferInstance, ?_⟩
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc₀3, one_zpow]
  show CFSG.Open.twoLocalPrimeRank 3 ↥K ≤ _
  refine csSup_le' ?_
  rintro k ⟨H, ⟨P, hP1, hP2, rfl⟩, rfl⟩
  refine csSup_le' ?_
  rintro j ⟨E, hEP, hE, hj⟩
  set E' : Subgroup X := E.map K.subtype with hE'
  set U : Subgroup X := P.map K.subtype with hU
  have hU1 : U ≠ ⊥ := fun h =>
    hP1 ((Subgroup.map_eq_bot_iff_of_injective P K.subtype_injective).1 h)
  have hU2 : IsPGroup 2 ↥U :=
    hP2.of_surjective (P.equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom
      (P.equivMapOfInjective K.subtype K.subtype_injective).surjective
  have hE'N : E' ≤ Subgroup.normalizer (U : Set X) :=
    (Subgroup.map_mono hEP).trans (Subgroup.le_normalizer_map K.subtype)
  have hE'card : Nat.card E' = 3 ^ j :=
    (Subgroup.card_map_of_injective K.subtype_injective).trans hj
  have hE'el : CFSG.Open.IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨εa, hεa, hεa'⟩ := a.2
      obtain ⟨εb, hεb, hεb'⟩ := b.2
      have h := hE.1.is_comm.comm ⟨εa, hεa⟩ ⟨εb, hεb⟩
      apply Subtype.ext
      show (a : X) * b = b * a
      rw [← hεa', ← hεb']
      exact congrArg (fun x : ↥E => ((x : ↥K) : X)) h
    · intro x hx
      obtain ⟨ε, hε, rfl⟩ := hx
      have := hE.2 ε hε
      show ((ε : ↥K) : X) ^ 3 = 1
      rw [← Subgroup.coe_pow, this]; rfl
  by_cases hc₀E : c₀ ∈ E'
  ·
    have hc₀K : c₀ ∈ K := by
      obtain ⟨ε, -, rfl⟩ := hc₀E
      exact ε.2
    have hc₀Z : c₀ ∈ (Subgroup.center ↥K).map K.subtype :=
      ⟨⟨c₀, hc₀K⟩, Subgroup.mem_center_iff.2 fun g =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.1 hc₀C) g.1 g.2), rfl⟩
    have h1 : 1 ≤ CFSG.Open.pRank 3 ((Subgroup.center ↥K).map K.subtype) :=
      le_pRank 3 (by norm_num) (E := Subgroup.zpowers c₀)
        (Subgroup.zpowers_le.2 hc₀Z) hzp_el (k := 1) (by rw [hcyc3]; norm_num)
    have h4 := rank_le_four_of_normalizes hX4 hU1 hU2 hE'N hE'el hE'card
    omega
  ·
    have hcomm : ∀ (e : ↥E') (z : ↥(Subgroup.zpowers c₀)),
        Commute (E'.subtype e) ((Subgroup.zpowers c₀).subtype z) := by
      intro e z
      have hz : (z : X) ∈ Subgroup.centralizer (K : Set X) := hzp_cent z.2
      have heK : (e : X) ∈ K := by
        obtain ⟨ε, -, hε⟩ := e.2
        rw [← hε]; exact ε.2
      exact (Subgroup.mem_centralizer_iff.1 hz) (e : X) heK
    haveI : Fact (Nat.card ↥(Subgroup.zpowers c₀)).Prime := ⟨by rw [hcyc3]; exact Nat.prime_three⟩
    have hdisj : ∀ z ∈ Subgroup.zpowers c₀, z ∈ E' → z = 1 := by
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card
          (E'.subgroupOf (Subgroup.zpowers c₀)) with h | h
      · intro z hz hzE
        have hzmem : (⟨z, hz⟩ : ↥(Subgroup.zpowers c₀)) ∈ E'.subgroupOf (Subgroup.zpowers c₀) :=
          hzE
        rw [h] at hzmem
        exact congrArg Subtype.val (Subgroup.mem_bot.1 hzmem)
      · exact absurd ((Subgroup.subgroupOf_eq_top.1 h) (Subgroup.mem_zpowers c₀)) hc₀E
    let φ : ↥E' × ↥(Subgroup.zpowers c₀) →* X :=
      MonoidHom.noncommCoprod E'.subtype (Subgroup.zpowers c₀).subtype hcomm
    have hφ : ∀ e z, φ (e, z) = (e : X) * (z : X) := fun e z => rfl
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      rintro ⟨e, z⟩ hker
      have h1 : (e : X) * (z : X) = 1 := by rw [← hφ]; exact hker
      have hz : (z : X) = (e : X)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hzE : (z : X) ∈ E' := by rw [hz]; exact E'.inv_mem e.2
      have hz1 : (z : X) = 1 := hdisj z z.2 hzE
      have he1 : (e : X) = 1 := by rw [hz1, mul_one] at h1; exact h1
      exact Prod.ext (Subtype.ext he1) (Subtype.ext hz1)
    have hBel : CFSG.Open.IsElemAbelian 3 φ.range := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨⟨e₁, z₁⟩, h₁⟩ := a.2
        obtain ⟨⟨e₂, z₂⟩, h₂⟩ := b.2
        apply Subtype.ext
        show (a : X) * b = b * a
        rw [← h₁, ← h₂, ← map_mul, ← map_mul]
        congr 1
        exact Prod.ext (hE'el.1.is_comm.comm e₁ e₂) (hzp_el.1.is_comm.comm z₁ z₂)
      · rintro x ⟨⟨e, z⟩, rfl⟩
        rw [← map_pow]
        have : ((e, z) : ↥E' × ↥(Subgroup.zpowers c₀)) ^ 3 = 1 :=
          Prod.ext (Subtype.ext (by simpa using hE'el.2 (e : X) e.2))
            (Subtype.ext (by simpa using hzp_el.2 (z : X) z.2))
        rw [this, map_one]
    have hBcard : Nat.card φ.range = 3 ^ (j + 1) := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hE'card, hcyc3,
        pow_succ]
    have hBN : φ.range ≤ Subgroup.normalizer (U : Set X) := by
      rintro _ ⟨⟨e, z⟩, rfl⟩
      have hzU : (z : X) ∈ Subgroup.centralizer (U : Set X) := by
        refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
        have huK : u ∈ K := by obtain ⟨π, -, rfl⟩ := hu; exact π.2
        exact (Subgroup.mem_centralizer_iff.1 (hzp_cent z.2)) u huK
      exact (Subgroup.normalizer (U : Set X)).mul_mem (hE'N e.2)
        (Subgroup.centralizer_le_normalizer _ hzU)
    have h4 := rank_le_four_of_normalizes hX4 hU1 hU2 hBN hBel hBcard
    omega

theorem i1433_chev (hS : ∀ s, SporL3Down s) (hL : LieL3Down) (c : I1433Cfg K Q₁ Q J t q) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ IsChevOfChar p (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨z, hzK, hz3, hZz⟩ := c.exists_gen
  have hcomp := c.comp3 hZz
  have hJbar : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    isQuasisimple_quotient_of_glaPComponent hcomp
  have hSL3 : IsSL3Eps (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
    refine ⟨?_, c.sl3.2⟩
    rcases c.sl3.1 with ⟨F, hF, hfin, -, ⟨e⟩⟩ | ⟨F, hF, hfin, hcard, ⟨e⟩⟩
    · exact Or.inl ⟨F, hF, hfin, ⟨e⟩⟩
    · exact Or.inr ⟨F, hF, hfin, q, hcard, ⟨e⟩⟩
  obtain ⟨p, hp, hp3, hpc⟩ := i253_exists_char (i253_any_of_isSL3Eps hJbar hSL3)
  refine ⟨p, hp, hp3, ?_⟩
  have hz1 : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
  have hKq : CFSG.Open.IsQuasisimple ↥K := by
    obtain ⟨hperf, hsimple, -⟩ := c.setup.quasisimple
    exact ⟨hperf.commutator_eq_top, hsimple⟩
  have hKK : CFSG.Open.IsKGroup ↥K := fun K' L _ _ hs _ => c.setup.kGroup K' (L.subgroupOf K') hs
  exact chev_of_branches (fun s => l3EpsSporBranch_of_down (hS s))
    (l3EpsLieBranch_of_down hL) X K hKq hKK z
    (Subgroup.le_normalizer hzK) (by rw [hz1]; exact Subgroup.one_mem _) J hcomp p hp hpc

@[expose] def L3CharUnique : Prop :=
  ∀ (p q' : ℕ) (H : Type) [Group H], p.Prime → IsL3Kind p H →
    CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q' (H ⧸ Subgroup.center H) → q' = p

theorem lieL3Down_of_lieComp (h : LieComp.LieComp) (hu : L3CharUnique) : LieL3Down := by
  intro S _ _ hs hna idx he β hβ J hJ p hp hk
  exact hu p _ (barOf 3 J) hp hk (h S hs hna idx he β hβ J hJ).1.chev

@[expose] def IsD4Simple (S : Type) [Group S] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nonempty (S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F)))

@[expose] def D4CentreTrivial : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K Q₁ Q J : Subgroup X) (t : X) (q : ℕ),
    I1433Cfg K Q₁ Q J t q → IsD4Simple (↥K ⧸ Subgroup.center ↥K) → Subgroup.center ↥K = ⊥

@[expose] def D4FieldSharp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K Q₁ Q J : Subgroup X) (t : X) (q : ℕ),
    I1433Cfg K Q₁ Q J t q → ∀ (F : Type) [Field F] [Finite F],
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F))) →
        Nat.card F = q

theorem d4CentreTrivial_of_noThreeCover
    (h : ∀ (F : Type) [Field F] [Finite F],
      LieComp.NoThreeCover (StatedProj (StatedOmega (StatedQuadPlus 4 F)))) :
    D4CentreTrivial := by
  intro X _ _ K Q₁ Q J t q c ⟨F, hF, hfin, ⟨e⟩⟩
  have hKq : CFSG.Open.IsQuasisimple ↥K := by
    obtain ⟨hperf, hsimple, -⟩ := c.setup.quasisimple
    exact ⟨hperf.commutator_eq_top, hsimple⟩
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K) := h F ↥K hKq ⟨e⟩
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hle : Subgroup.center ↥K ≤ GLAPPrimeCore 3 ↥K := le_sSup ⟨inferInstance, hcop⟩
  rw [c.primeCore_K] at hle
  exact le_bot_iff.1 hle

@[expose] def NonD4LieContraOn (F : LieFamily) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K Q₁ Q J : Subgroup X) (t : X) (q p : ℕ),
    I1433Cfg K Q₁ Q J t q → p.Prime → p ≠ 3 →
    ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = F → IsChevIndexOfChar p idx.1 →
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ¬ IsD4Simple (↥K ⧸ Subgroup.center ↥K) → False

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.Yardstones.Md42047359a2a CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

theorem input14_33TypeSameField_of_leaves
    (hSpor : ∀ s, SporL3Down s) (hLie : LieL3Down)
    (hD4Z : D4CentreTrivial) (hD4F : D4FieldSharp)
    (hLU : NonD4LieContraOn .linearUnitary) (hSO : NonD4LieContraOn .symplecticOrthogonal)
    (hExc : NonD4LieContraOn .exceptional) (hSRT : NonD4LieContraOn .suzukiReeTits) :
    Input14_33TypeSameField := by
  rw [input14_33TypeSameField_iff]
  intro X _ _ K Q₁ Q J t q c
  by_cases hD : IsD4Simple (↥K ⧸ Subgroup.center ↥K)
  · obtain ⟨F, hF, hfin, ⟨e⟩⟩ := hD
    have hZ := hD4Z X K Q₁ Q J t q c ⟨F, hF, hfin, ⟨e⟩⟩
    refine ⟨F, hF, hfin, hD4F X K Q₁ Q J t q c F ⟨e⟩, ⟨?_⟩⟩
    exact (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  · exfalso
    obtain ⟨p, hp, hp3, d, hd, he⟩ := i1433_chev hSpor hLie c
    have key : ∀ F, NonD4LieContraOn F → lieFamily d.1 = F → False := fun F hF hdF =>
      hF X K Q₁ Q J t q p c hp hp3 d hdF hd he hD
    cases hf : lieFamily d.1
    · exact key _ hLU hf
    · exact key _ hSO hf
    · exact key _ hExc hf
    · exact key _ hSRT hf

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns
