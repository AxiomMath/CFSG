module

public import CFSG.Goldschmidt.Steps.G55
import CFSG.Walter.Bender1970.S4.ComponentTools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate

public section

namespace CFSG.Goldschmidt.G55

open CFSG.GorensteinWalter CFSG.Walter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_sup_of_commutator_eq {N K : Subgroup G} {a : G} (hao : orderOf a = 2)
    (haN : a ∈ Subgroup.normalizer (N : Set G)) (hKa : ⁅K, Subgroup.zpowers a⁆ = K) :
    ∀ n : ℕ, ∀ D : Subgroup G, Nat.card D ≤ n → IsPGroup 2 D →
      a ∈ Subgroup.normalizer (D : Set G) → D ≤ Subgroup.normalizer (N : Set G) →
      K ≤ N ⊔ D → K ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
  intro n
  induction n with
  | zero =>
    intro D hD _ _ _ _
    have := Nat.card_pos (α := D)
    omega
  | succ n ih =>
    intro D hD hD2 haD hDN hK
    by_cases hD1 : D = ⊥
    · rwa [hD1, sup_bot_eq] at hK
    set D₁ := ⁅D, Subgroup.zpowers a⁆ with hD₁def
    have hlt : D₁ < D := SchurZassenhaus.commutator_lt_of_pGroups D _ hD2 hzp
      (Subgroup.zpowers_le.mpr haD) hD1
    have hD₁card : Nat.card D₁ ≤ n := by
      have := Subgroup.card_lt_of_lt hlt
      omega
    refine ih D₁ hD₁card (hD2.to_le hlt.le)
      (mem_normalizer_commutator haD (Subgroup.le_normalizer (Subgroup.mem_zpowers a)))
      (hlt.le.trans hDN) ?_
    calc K = ⁅K, Subgroup.zpowers a⁆ := hKa.symm
      _ ≤ ⁅N ⊔ D, Subgroup.zpowers a⁆ := Subgroup.commutator_mono hK le_rfl
      _ ≤ N ⊔ D₁ := by
        refine commutator_zpowers_le_of_forall hao fun g hg => ?_
        rw [sup_comm] at hg
        obtain ⟨d, hd, m, hm, rfl⟩ := mem_sup_of_le_normalizer hDN hg
        have hma : ⁅m, a⁆ ∈ N := by
          have h' : ⁅m, a⁆ = m * (a * m⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
          rw [h']
          exact N.mul_mem hm ((Subgroup.mem_normalizer_iff.mp haN m⁻¹).mp (N.inv_mem hm))
        have h1 : d * ⁅m, a⁆ * d⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hDN hd) _).mp hma
        have h2 : ⁅d, a⁆ ∈ D₁ := Subgroup.commutator_mem_commutator hd (Subgroup.mem_zpowers a)
        have heq : ⁅d * m, a⁆ = (d * ⁅m, a⁆ * d⁻¹) * ⁅d, a⁆ := by
          simp only [commutatorElement_def]
          group
        rw [heq]
        exact Subgroup.mul_mem_sup h1 h2

theorem oddCoreOf_fitting_le {X K C : Subgroup G} (hK : IsNormalIn K X)
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → qCoreOf X q ≤ C) :
    CFSG.Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf K) ≤ C := by
  set N := CFSG.Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf K) with hNdef
  have hNF : N ≤ CFSG.fittingSubgroupOf K := Subgroup.map_subtype_le _
  have hNnil : Group.IsNilpotent N := isNilpotent_of_le (CFSG.fittingSubgroupOf_isNilpotent K) hNF
  have hNodd : Odd (Nat.card N) := by
    rw [hNdef, oddCoreOf_eq]
    exact CFSG.Walter.odd_card_oddCoreOf _
  have hNX : N ≤ X := hNF.trans ((fittingSubgroupOf_isNormalIn K).1.trans hK.1)
  have hNsn : (N.subgroupOf X).IsSubnormal := by
    have h1 : (N.subgroupOf (CFSG.fittingSubgroupOf K)).IsSubnormal :=
      isSubnormal_subgroupOf_of_isNormalIn (isNormalIn_map_subtype _ _)
    have h2 : ((CFSG.fittingSubgroupOf K).subgroupOf K).IsSubnormal :=
      isSubnormal_subgroupOf_of_isNormalIn (fittingSubgroupOf_isNormalIn K)
    exact isSubnormal_subgroupOf_trans hNF h1 (isSubnormal_subgroupOf_trans
      (fittingSubgroupOf_isNormalIn K).1 h2 (isSubnormal_subgroupOf_of_isNormalIn hK))
  rw [← fittingSubgroupOf_eq_self_of_isNilpotent hNnil, (show CFSG.fittingSubgroupOf N = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf N)]
  refine iSup_le fun q => ?_
  have hqp : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  have hq2 : q.1.1 ≠ 2 := by
    intro hq
    have hdvd : 2 ∣ Nat.card N := hq ▸ Nat.dvd_of_mem_primeFactors q.1.2
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdvd)
  have hqN := qCoreOf_normal_in N q.1.1
  exact (le_qCoreOf_of_isSubnormal_isPGroup X _ q.1.1 (hqN.1.trans hNX)
    (isSubnormal_subgroupOf_trans hqN.1 (isSubnormal_subgroupOf_of_isNormalIn hqN) hNsn)
    (qCoreOf_isPGroup N q.1.1)).trans (h _ hqp hq2)

omit [Finite G] in
theorem mem_normalizer_sup {B C : Subgroup G} {g : G} (hB : g ∈ Subgroup.normalizer (B : Set G))
    (hC : g ∈ Subgroup.normalizer (C : Set G)) : g ∈ Subgroup.normalizer ((B ⊔ C : Subgroup G) :
      Set G) := by
  rw [← sSup_pair]
  refine mem_normalizer_sSup fun K hK => ?_
  rcases hK with rfl | rfl
  · exact hB
  · exact hC

structure Gold37 (G : Type) [Group G] [Finite G] where
  Syl : Sylow 2 G
  A : Subgroup G
  hS : GoldSetting G Syl A
  h31 : S_G31
  h37 : S_G37
  a : G
  haA : a ∈ A
  ha1 : a ≠ 1
  H : Subgroup G
  hH : IsCoatom H
  hCH : Subgroup.centralizer ({a} : Set G) ≤ H
  ha2 : a ∈ qCoreOf H 2
  p : ℕ
  hp : p.Prime
  hp2 : p ≠ 2
  V : Subgroup G
  hVP : V ≤ qCoreOf H p
  hVcomm : IsMulCommutative V
  hVexp : ∀ x ∈ V, x ^ p = 1
  hV3 : p ^ 3 ≤ Nat.card V
  hCV : Subgroup.centralizer (V : Set G) ≤ H

namespace Gold37

variable (S : Gold37 G)

@[expose] def primes : Set ℕ := primesOfOrder (CFSG.fittingSubgroupOf S.H)

@[expose] def W : Subgroup G :=
  generalizedFittingSubgroupOf S.H ⊓ Subgroup.centralizer (S.V : Set G)

@[expose] def pieces (X : Subgroup G) : Set (Subgroup G) :=
  {P | (∃ q : ℕ, q.Prime ∧ q ∉ S.primes ∧ P = qCoreOf X q) ∨ (IsComponentOf P X ∧ ¬ P ≤ S.H)}

@[expose] def Q (X : Subgroup G) : Subgroup G := sSup (S.pieces X)

@[expose] def U : Set (Subgroup G) :=
  {K | K ≠ ⊤ ∧ S.W ≤ Subgroup.normalizer (K : Set G) ∧ ⁅K, Subgroup.zpowers S.a⁆ = K}

@[expose] def orbit (L : Subgroup G) : Subgroup G :=
  sSup {L' | ∃ w ∈ S.W, L' = L.map (MulAut.conj w).toMonoidHom}

include S in
theorem isSimpleGroup : IsSimpleGroup G := S.hS.isSimpleGroup

theorem a_mul_a : S.a * S.a = 1 := mul_self_eq_one_of_mem S.hS.elem S.haA

theorem orderOf_a : orderOf S.a = 2 := orderOf_eq_prime (S.hS.elem.2 S.a S.haA) S.ha1

theorem a_mem_centralizer : S.a ∈ Subgroup.centralizer ({S.a} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem a_mem_H : S.a ∈ S.H := S.hCH S.a_mem_centralizer

theorem a_mem_fitting : S.a ∈ CFSG.fittingSubgroupOf S.H :=
  qCoreOf_le_fittingSubgroupOf S.H 2 Nat.prime_two S.ha2

theorem a_mem_F : S.a ∈ generalizedFittingSubgroupOf S.H :=
  (le_sup_left : CFSG.fittingSubgroupOf S.H ≤ generalizedFittingSubgroupOf S.H) S.a_mem_fitting

theorem qCoreOf_le_centralizer_a : qCoreOf S.H S.p ≤ Subgroup.centralizer ({S.a} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp
    (qCoreOf_centralizer_of_ne S.H S.hp Nat.prime_two S.hp2 S.ha2)) x hx

theorem V_isPGroup : IsPGroup S.p S.V := (qCoreOf_isPGroup S.H S.p).to_le S.hVP

theorem p_dvd_card_V : S.p ∣ Nat.card S.V := by
  have : Fact S.p.Prime := ⟨S.hp⟩
  obtain ⟨k, hk⟩ := S.V_isPGroup.exists_card_eq
  have h3 := S.hV3
  rw [hk] at h3 ⊢
  have hk1 : 1 ≤ k := by
    by_contra h
    push Not at h
    have : k = 0 := by omega
    rw [this, pow_zero] at h3
    have := Nat.pow_le_pow_right S.hp.pos (show 1 ≤ 3 by norm_num)
    have := S.hp.one_lt
    nlinarith
  exact dvd_pow_self S.p (by omega)

theorem V_ne_bot : S.V ≠ ⊥ := by
  intro h
  have h1 := S.p_dvd_card_V
  rw [h, Subgroup.card_bot] at h1
  exact S.hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem odd_card_V : Odd (Nat.card S.V) := Bender35.odd_card_of_le S.hp S.hp2 S.hVP

theorem V_le_fitting : S.V ≤ CFSG.fittingSubgroupOf S.H :=
  S.hVP.trans (qCoreOf_le_fittingSubgroupOf S.H S.p S.hp)

theorem V_le_F : S.V ≤ generalizedFittingSubgroupOf S.H := S.V_le_fitting.trans le_sup_left

theorem V_le_W : S.V ≤ S.W := by
  refine le_inf S.V_le_F fun x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (S.hVcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

theorem W_le_F : S.W ≤ generalizedFittingSubgroupOf S.H := inf_le_left

theorem W_le_H : S.W ≤ S.H := S.W_le_F.trans (generalizedFittingSubgroupOf_isNormalIn S.H).1

theorem W_le_centralizer_V : S.W ≤ Subgroup.centralizer (S.V : Set G) := inf_le_right

theorem a_mem_W : S.a ∈ S.W := by
  refine ⟨S.a_mem_F, ?_⟩
  show S.a ∈ Subgroup.centralizer (S.V : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_singleton_iff.mp (S.qCoreOf_le_centralizer_a (S.hVP hv))

theorem W_isSubnormal : (S.W.subgroupOf (generalizedFittingSubgroupOf S.H)).IsSubnormal := by
  refine isSubnormal_of_componentLayerOf_le (le_inf le_sup_right ?_) S.W_le_F
  exact (componentLayerOf_le_centralizer_fitting S.H).trans
    (Subgroup.centralizer_le S.V_le_fitting)

theorem inf_centralizer_W_le :
    generalizedFittingSubgroupOf S.H ⊓ Subgroup.centralizer (S.W : Set G) ≤ S.W :=
  fun _ hx => ⟨hx.1, Subgroup.centralizer_le S.V_le_W hx.2⟩

theorem W_isSubnormal_H : (S.W.subgroupOf S.H).IsSubnormal :=
  isSubnormal_subgroupOf_trans S.W_le_F S.W_isSubnormal
    (isSubnormal_subgroupOf_of_isNormalIn (generalizedFittingSubgroupOf_isNormalIn S.H))

theorem two_mem_primes : 2 ∈ S.primes := by
  show 2 ∈ (Nat.card (CFSG.fittingSubgroupOf S.H)).primeFactors
  rw [Nat.mem_primeFactors]
  refine ⟨Nat.prime_two, ?_, Nat.card_pos.ne'⟩
  have h := Subgroup.orderOf_dvd_natCard _ S.a_mem_fitting
  rwa [S.orderOf_a] at h

theorem p_mem_primes : S.p ∈ S.primes := by
  show S.p ∈ (Nat.card (CFSG.fittingSubgroupOf S.H)).primeFactors
  rw [Nat.mem_primeFactors]
  exact ⟨S.hp, S.p_dvd_card_V.trans (Subgroup.card_dvd_of_le S.V_le_fitting), Nat.card_pos.ne'⟩

theorem two_le_card_primes_F :
    2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf S.H)) := by
  have h2 : 2 ∈ primesOfOrder (generalizedFittingSubgroupOf S.H) := by
    show 2 ∈ (Nat.card (generalizedFittingSubgroupOf S.H)).primeFactors
    rw [Nat.mem_primeFactors]
    refine ⟨Nat.prime_two, ?_, Nat.card_pos.ne'⟩
    have h := Subgroup.orderOf_dvd_natCard _ S.a_mem_F
    rwa [S.orderOf_a] at h
  have hp : S.p ∈ primesOfOrder (generalizedFittingSubgroupOf S.H) := by
    show S.p ∈ (Nat.card (generalizedFittingSubgroupOf S.H)).primeFactors
    rw [Nat.mem_primeFactors]
    exact ⟨S.hp, S.p_dvd_card_V.trans (Subgroup.card_dvd_of_le S.V_le_F), Nat.card_pos.ne'⟩
  have hfin : (primesOfOrder (generalizedFittingSubgroupOf S.H)).Finite :=
    (Nat.card (generalizedFittingSubgroupOf S.H)).primeFactors.finite_toSet
  rw [Nat.card_coe_set_eq, ← Set.ncard_pair (Ne.symm S.hp2)]
  exact Set.ncard_le_ncard (Set.insert_subset_iff.mpr ⟨h2, Set.singleton_subset_iff.mpr hp⟩) hfin

theorem V_le_oddCoreOf {X : Subgroup G} (hWX : S.W ≤ X) :
    S.V ≤ GorensteinWalter.oddCoreOf
      (CFSG.fittingSubgroupOf (X ⊓ Subgroup.centralizer ({S.a} : Set G))) := by
  have hVO : S.V ≤ GorensteinWalter.oddCoreOf (CFSG.fittingSubgroupOf S.H) :=
    le_oddCoreOf_of_odd (CFSG.fittingSubgroupOf_isNilpotent S.H) S.V_le_fitting S.odd_card_V
  exact (le_inf hVO (le_inf (S.V_le_W.trans hWX) (S.hVP.trans S.qCoreOf_le_centralizer_a))).trans
    (oddCoreOf_fitting_inf_le (inf_le_right.trans S.hCH))

theorem map_conj_le_H_iff {A : Subgroup G} {h : G} (hh : h ∈ S.H) :
    A.map (MulAut.conj h).toMonoidHom ≤ S.H ↔ A ≤ S.H := by
  conv_lhs => rw [← map_conj_eq_self_of_mem hh]
  exact map_conj_le_map_conj_iff h

variable {X : Subgroup G}

theorem a_mem (hWX : S.W ≤ X) : S.a ∈ X := hWX S.a_mem_W

theorem qCoreOf_inf_H (hWX : S.W ≤ X) {q : ℕ} (hq : q.Prime) (hqπ : q ∉ S.primes) :
    qCoreOf X q ⊓ S.H = ⊥ :=
  bender1970_1_7_i_oddCoreDisjoint S.isSimpleGroup S.H S.hH S.W S.W_le_F S.W_isSubnormal
    S.inf_centralizer_W_le hWX q hq hqπ

theorem qCoreOf_props (hWX : S.W ≤ X) {q : ℕ} (hq : q.Prime) (hqπ : q ∉ S.primes) :
    (∀ x ∈ qCoreOf X q, S.a * x * S.a⁻¹ = x⁻¹) ∧ IsMulCommutative (qCoreOf X q) ∧
      Odd (Nat.card (qCoreOf X q)) ∧
      ⁅qCoreOf X q, Subgroup.zpowers S.a⁆ = qCoreOf X q ∧
      generalizedFittingSubgroupOf X ≤ Subgroup.centralizer (qCoreOf X q : Set G) := by
  refine qCoreOf_props_of_fixedPointFree (S.a_mem hWX) S.orderOf_a hq ?_
  exact le_bot_iff.mp ((inf_le_inf_left _ S.hCH).trans (S.qCoreOf_inf_H hWX hq hqπ).le)

theorem ne_p_of_not_mem_primes {q : ℕ} (hqπ : q ∉ S.primes) : q ≠ S.p :=
  fun h => hqπ (h ▸ S.p_mem_primes)

theorem ne_two_of_not_mem_primes {q : ℕ} (hqπ : q ∉ S.primes) : q ≠ 2 :=
  fun h => hqπ (h ▸ S.two_mem_primes)

theorem qCoreOf_le_centralizer (hWX : S.W ≤ X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqπ : q ∈ S.primes) : qCoreOf X q ≤ Subgroup.centralizer ({S.a} : Set G) := by
  have h17 := bender1970_1_7_ii_commutator_pResidual S.isSimpleGroup S.H S.hH S.W
    S.W_le_F S.W_isSubnormal S.inf_centralizer_W_le hWX q hq hqπ
  have haR : S.a ∈ pResidualOf (generalizedFittingSubgroupOf S.H) q :=
    mem_pResidualOf_of_order_coprime _ q hq S.a_mem_F (by
      rw [S.orderOf_a]; exact (Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h17 hx
  exact ((Subgroup.mem_centralizer_iff.mp h) S.a haR).symm

theorem qCoreOf_sign (hWX : S.W ≤ X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    (∀ n ∈ qCoreOf X q, S.a * n * S.a⁻¹ = n) ∨ (∀ n ∈ qCoreOf X q, S.a * n * S.a⁻¹ = n⁻¹) := by
  by_cases hqπ : q ∈ S.primes
  · left
    intro n hn
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (S.qCoreOf_le_centralizer hWX hq hq2 hqπ hn),
      mul_inv_cancel_right]
  · exact Or.inr (S.qCoreOf_props hWX hq hqπ).1

theorem commutator_component_eq_bot (hWX : S.W ≤ X) {L : Subgroup G} (hL : IsComponentOf L X)
    (hLH : L ≤ S.H) : ⁅L, Subgroup.zpowers S.a⁆ = ⊥ := by
  rcases le_commutator_or_eq_bot hL (S.a_mem hWX) with h | h
  · exact h
  · exfalso
    have h2 : ⁅L, Subgroup.zpowers S.a⁆ ≤ qCoreOf S.H 2 :=
      commutator_zpowers_le_of_forall S.orderOf_a fun l hl => by
        rw [commutatorElement_def]
        exact (qCoreOf S.H 2).mul_mem ((qCoreOf_normal_in S.H 2).2 l (hLH hl) S.a S.ha2)
          ((qCoreOf S.H 2).inv_mem S.ha2)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isPerfect_of_isComponentOf hL
    have hsolv : Group.IsSolvable (qCoreOf S.H 2) := by
      have := (qCoreOf_isPGroup S.H 2).isNilpotent
      infer_instance
    exact Bender37.ne_bot_of_isComponentOf hL (eq_bot_of_isPerfect_of_le_isSolvable (h.trans h2)
      hsolv)

theorem le_commutator_component (hWX : S.W ≤ X) {L : Subgroup G} (hL : IsComponentOf L X)
    (hLH : ¬ L ≤ S.H) : L ≤ ⁅L, Subgroup.zpowers S.a⁆ := by
  rcases le_commutator_or_eq_bot hL (S.a_mem hWX) with h | h
  · exfalso
    apply hLH
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq'] at h
    exact h.trans S.hCH
  · exact h

theorem le_of_mem_pieces {P : Subgroup G} (hP : P ∈ S.pieces X) : P ≤ X := by
  rcases hP with ⟨q, -, -, rfl⟩ | ⟨hL, -⟩
  · exact Subgroup.map_subtype_le _
  · exact hL.1

theorem Q_le : S.Q X ≤ X := sSup_le fun _ hP => S.le_of_mem_pieces hP

theorem le_Q_of_mem_pieces {P : Subgroup G} (hP : P ∈ S.pieces X) : P ≤ S.Q X := le_sSup hP

theorem le_commutator_of_mem_pieces (hWX : S.W ≤ X) {P : Subgroup G}
    (hP : P ∈ S.pieces X) : P ≤ ⁅P, Subgroup.zpowers S.a⁆ := by
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  · exact (S.qCoreOf_props hWX hq hqπ).2.2.2.1.ge
  · exact S.le_commutator_component hWX hL hLH

theorem map_conj_mem_pieces {P : Subgroup G} (hP : P ∈ S.pieces X) {g : G} (hgX : g ∈ X)
    (hgH : g ∈ S.H) : P.map (MulAut.conj g).toMonoidHom ∈ S.pieces X := by
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  · exact Or.inl ⟨q, hq, hqπ, Bender37.map_conj_eq_of_mem_normalizer
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in X q) hgX)⟩
  · exact Or.inr ⟨fstar_isComponentOf_conjugateSubgroup_of_mem hL g hgX,
      fun h => hLH ((S.map_conj_le_H_iff hgH).mp h)⟩

theorem W_le_normalizer_Q (hWX : S.W ≤ X) : S.W ≤ Subgroup.normalizer (S.Q X : Set G) :=
  fun _ hw => mem_normalizer_sSup_of_map_mem
    (fun _ hP => S.map_conj_mem_pieces hP (hWX hw) (S.W_le_H hw))
    (fun _ hP => S.map_conj_mem_pieces hP (X.inv_mem (hWX hw)) (S.H.inv_mem (S.W_le_H hw)))

theorem Q_mem_U (hWX : S.W ≤ X) (hX : X ≠ ⊤) : S.Q X ∈ S.U := by
  refine ⟨fun h => hX (eq_top_iff.mpr (h ▸ S.Q_le)), S.W_le_normalizer_Q hWX, le_antisymm
    (commutator_zpowers_le_of_mem_normalizer (S.W_le_normalizer_Q hWX S.a_mem_W)) ?_⟩
  refine sSup_le fun P hP => (S.le_commutator_of_mem_pieces hWX hP).trans ?_
  exact Subgroup.commutator_mono (le_sSup hP) le_rfl

theorem Q_le_generalizedFitting : S.Q X ≤ generalizedFittingSubgroupOf X := by
  refine sSup_le fun P hP => ?_
  rcases hP with ⟨q, hq, -, rfl⟩ | ⟨hL, -⟩
  · exact (qCoreOf_le_fittingSubgroupOf X q hq).trans le_sup_left
  · exact (le_sSup (s := {E : Subgroup G | IsComponentOf E X}) hL).trans le_sup_right

theorem generalizedFitting_le_normalizer_Q :
    generalizedFittingSubgroupOf X ≤ Subgroup.normalizer (S.Q X : Set G) := by
  intro g hg
  refine mem_normalizer_sSup fun P hP => ?_
  rcases hP with ⟨r, -, -, rfl⟩ | ⟨hL', -⟩
  · exact le_normalizer_of_isNormalIn (qCoreOf_normal_in X r)
      (generalizedFittingSubgroupOf_le X hg)
  · exact Bender37.generalizedFitting_le_normalizer_component hL' hg

theorem le_generalizedFitting_of_mem_U (hWX : S.W ≤ X) (hX : X ≠ ⊤) {K : Subgroup G}
    (hK : K ∈ S.U) (hKX : K ≤ X) : K ≤ generalizedFittingSubgroupOf X := by
  obtain ⟨g, hAg, hSS⟩ := S.hS.sstar X hX
  set A₁ := conjSub g S.A ⊓ X
  have haX := S.a_mem hWX
  have haA₁ : S.a ∈ A₁ := ⟨hAg ⟨S.haA, haX⟩, haX⟩
  set N₁ := normalClosureIn X A₁
  have hN₁ := normalClosureIn_isNormalIn X A₁
  have haN₁ : S.a ∈ N₁ := inf_le_normalClosureIn X A₁ ⟨haA₁, haX⟩
  have hXa : ⁅X, Subgroup.zpowers S.a⁆ ≤ N₁ ⊓ Subgroup.centralizer
      (CFSG.Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf N₁) : Set G) := by
    refine commutator_zpowers_le_of_forall S.orderOf_a fun x hx => ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact N₁.mul_mem (hN₁.2 x hx S.a haN₁) (N₁.inv_mem haN₁)
    · have hle := oddCoreOf_fitting_le (C := Subgroup.centralizer ({⁅x, S.a⁆} : Set G)) hN₁
        fun q hq hq2 => by
          have h := commutatorElement_mem_centralizer_of_conj
            (le_normalizer_of_isNormalIn (qCoreOf_normal_in X q) hx) (S.qCoreOf_sign hWX hq hq2)
          intro n hn
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp h) n hn
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  calc K = ⁅K, Subgroup.zpowers S.a⁆ := hK.2.2.symm
    _ ≤ ⁅X, Subgroup.zpowers S.a⁆ := Subgroup.commutator_mono hKX le_rfl
    _ ≤ _ := hXa.trans (S.h31 G X A₁ hSS).2

theorem commutator_generalizedFitting_le (hWX : S.W ≤ X) :
    ⁅generalizedFittingSubgroupOf X, Subgroup.zpowers S.a⁆ ≤ S.Q X ⊔ qCoreOf X 2 := by
  have haX := S.a_mem hWX
  refine (Subgroup.commutator_mono Bender37.generalizedFitting_le_sSup le_rfl).trans ?_
  refine commutator_sSup_le _ _ _ (fun A hA => ?_) (fun A hA => ?_)
  · rcases hA with ⟨q, hq, rfl⟩ | hL
    · have haN := le_normalizer_of_isNormalIn (qCoreOf_normal_in X q) haX
      by_cases hq2 : q = 2
      · subst hq2
        exact (commutator_zpowers_le_of_mem_normalizer haN).trans le_sup_right
      · by_cases hqπ : q ∈ S.primes
        · have h : ⁅qCoreOf X q, Subgroup.zpowers S.a⁆ = ⊥ := by
            rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq']
            exact S.qCoreOf_le_centralizer hWX hq hq2 hqπ
          rw [h]
          exact bot_le
        · exact (commutator_zpowers_le_of_mem_normalizer haN).trans
            ((S.le_Q_of_mem_pieces (Or.inl ⟨q, hq, hqπ, rfl⟩)).trans le_sup_left)
    · by_cases hLH : A ≤ S.H
      · rw [S.commutator_component_eq_bot hWX hL hLH]
        exact bot_le
      · have hLa : A.map (MulAut.conj S.a).toMonoidHom ∈ S.pieces X :=
          S.map_conj_mem_pieces (Or.inr ⟨hL, hLH⟩) haX S.a_mem_H
        refine (commutator_zpowers_le_of_forall S.orderOf_a fun l hl => ?_).trans le_sup_left
        have h' : ⁅l, S.a⁆ = l * (S.a * l⁻¹ * S.a⁻¹) := by rw [commutatorElement_def]; group
        rw [h']
        exact (S.Q X).mul_mem (S.le_Q_of_mem_pieces (Or.inr ⟨hL, hLH⟩) hl)
          (S.le_Q_of_mem_pieces hLa ⟨l⁻¹, A.inv_mem hl, rfl⟩)
  · have hAX : A ≤ generalizedFittingSubgroupOf X := by
      rcases hA with ⟨q, hq, rfl⟩ | hL
      · exact (qCoreOf_le_fittingSubgroupOf X q hq).trans le_sup_left
      · exact (le_sSup (s := {E : Subgroup G | IsComponentOf E X}) hL).trans le_sup_right
    intro y hy
    exact mem_normalizer_sup (S.generalizedFitting_le_normalizer_Q (hAX hy))
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in X 2) (generalizedFittingSubgroupOf_le X
        (hAX hy)))

theorem le_Q_of_mem_U (hWX : S.W ≤ X) (hX : X ≠ ⊤) {K : Subgroup G} (hK : K ∈ S.U)
    (hKX : K ≤ X) : K ≤ S.Q X := by
  have hKF := S.le_generalizedFitting_of_mem_U hWX hX hK hKX
  have hK2 : K ≤ S.Q X ⊔ qCoreOf X 2 :=
    calc K = ⁅K, Subgroup.zpowers S.a⁆ := hK.2.2.symm
      _ ≤ ⁅generalizedFittingSubgroupOf X, Subgroup.zpowers S.a⁆ :=
          Subgroup.commutator_mono hKF le_rfl
      _ ≤ _ := S.commutator_generalizedFitting_le hWX
  exact le_of_le_sup_of_commutator_eq S.orderOf_a (S.W_le_normalizer_Q hWX S.a_mem_W) hK.2.2 _
    (qCoreOf X 2) le_rfl (qCoreOf_isPGroup X 2)
    (le_normalizer_of_isNormalIn (qCoreOf_normal_in X 2) (S.a_mem hWX))
    (fun y hy => S.generalizedFitting_le_normalizer_Q
      ((le_sup_left : CFSG.fittingSubgroupOf X ≤ generalizedFittingSubgroupOf X)
        (qCoreOf_le_fittingSubgroupOf X 2 Nat.prime_two hy))) hK2

theorem map_conj_mem_pieces_map {P : Subgroup G} (hP : P ∈ S.pieces X) {h : G} (hh : h ∈ S.H) :
    P.map (MulAut.conj h).toMonoidHom ∈ S.pieces (X.map (MulAut.conj h).toMonoidHom) := by
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  · exact Or.inl ⟨q, hq, hqπ, (qCoreOf_conjugateSubgroup X h q).symm⟩
  · exact Or.inr ⟨IsComponentOf.map_conj hL h, fun h' => hLH ((S.map_conj_le_H_iff hh).mp h')⟩

theorem map_conj_Q_le {h : G} (hh : h ∈ S.H) :
    (S.Q X).map (MulAut.conj h).toMonoidHom ≤ S.Q (X.map (MulAut.conj h).toMonoidHom) := by
  rw [Q, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun P hP => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (S.map_conj_mem_pieces_map hP hh)

theorem map_conj_Q {h : G} (hh : h ∈ S.H) :
    (S.Q X).map (MulAut.conj h).toMonoidHom = S.Q (X.map (MulAut.conj h).toMonoidHom) := by
  refine le_antisymm (S.map_conj_Q_le hh) ?_
  have h1 := S.map_conj_Q_le (X := X.map (MulAut.conj h).toMonoidHom) (S.H.inv_mem hh)
  rw [map_conj_map_conj_inv] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) h1
  rwa [map_conj_inv_map_conj] at h2

theorem le_orbit (L : Subgroup G) : L ≤ S.orbit L :=
  le_sSup ⟨1, S.W.one_mem, (Bender37.map_conj_one L).symm⟩

theorem orbit_le {L Y : Subgroup G} (hLY : L ≤ Y)
    (hWY : S.W ≤ Subgroup.normalizer (Y : Set G)) : S.orbit L ≤ Y := by
  refine sSup_le ?_
  rintro _ ⟨w, hw, rfl⟩
  rintro _ ⟨l, hl, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hWY hw) l).mp (hLY hl)

theorem W_le_normalizer_orbit (L : Subgroup G) :
    S.W ≤ Subgroup.normalizer (S.orbit L : Set G) := by
  intro w hw
  refine mem_normalizer_sSup_of_map_mem ?_ ?_
  · rintro _ ⟨w', hw', rfl⟩
    exact ⟨w * w', S.W.mul_mem hw hw', Bender37.map_conj_map_conj w w' L⟩
  · rintro _ ⟨w', hw', rfl⟩
    exact ⟨w⁻¹ * w', S.W.mul_mem (S.W.inv_mem hw) hw', Bender37.map_conj_map_conj w⁻¹ w' L⟩

theorem orbit_mem_U (hWX : S.W ≤ X) (hX : X ≠ ⊤) {L : Subgroup G} (hL : IsComponentOf L X)
    (hLH : ¬ L ≤ S.H) : S.orbit L ∈ S.U := by
  have hOX : S.orbit L ≤ X := S.orbit_le hL.1 (hWX.trans X.le_normalizer)
  refine ⟨fun h => hX (eq_top_iff.mpr (h ▸ hOX)), S.W_le_normalizer_orbit L, le_antisymm
    (commutator_zpowers_le_of_mem_normalizer (S.W_le_normalizer_orbit L S.a_mem_W)) ?_⟩
  refine sSup_le ?_
  rintro _ ⟨w, hw, rfl⟩
  have hLw : IsComponentOf (L.map (MulAut.conj w).toMonoidHom) X :=
    fstar_isComponentOf_conjugateSubgroup_of_mem hL w (hWX hw)
  have hLwH : ¬ L.map (MulAut.conj w).toMonoidHom ≤ S.H :=
    fun h => hLH ((S.map_conj_le_H_iff (S.W_le_H hw)).mp h)
  exact (S.le_commutator_component hWX hLw hLwH).trans
    (Subgroup.commutator_mono (le_sSup ⟨w, hw, rfl⟩) le_rfl)

end Gold37

end CFSG.Goldschmidt.G55
