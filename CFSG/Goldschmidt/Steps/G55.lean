module

public import CFSG.Goldschmidt.Steps.G55Basic
import CFSG.Walter.Bender1970.S5.Normalizer
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Walter.Bender1970.S3.PGroupFStar

public section

namespace CFSG.Goldschmidt.G55

open CFSG.GorensteinWalter CFSG.Walter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_self_eq_one_of_mem {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) {a : G}
    (ha : a ∈ A) :
    a * a = 1 := by
  rw [← pow_two]
  exact hA.2 a ha

omit [Finite G] in
theorem isNormalIn_map_subtype (X : Subgroup G) (N : Subgroup X) [hN : N.Normal] :
    IsNormalIn (N.map X.subtype) X := by
  refine ⟨Subgroup.map_subtype_le N, fun h hh k hk => ?_⟩
  obtain ⟨k', hk', rfl⟩ := hk
  exact ⟨⟨h, hh⟩ * k' * ⟨h, hh⟩⁻¹, hN.conj_mem k' hk' ⟨h, hh⟩, rfl⟩

omit [Finite G] in
theorem inf_le_normalClosureIn (X A : Subgroup G) : A ⊓ X ≤ normalClosureIn X A := by
  rintro a ⟨haA, haX⟩
  exact ⟨⟨a, haX⟩, Subgroup.subset_normalClosure (show (⟨a, haX⟩ : X) ∈ A.subgroupOf X from haA),
    rfl⟩

omit [Finite G] in
theorem normalClosureIn_isNormalIn (X A : Subgroup G) : IsNormalIn (normalClosureIn X A) X :=
  isNormalIn_map_subtype X _

theorem mem_qCoreOf_of_mem_fitting {H : Subgroup G} {p : ℕ} {x : G}
    (hx : x ∈ CFSG.fittingSubgroupOf H) (hxp : IsPGroup p (Subgroup.zpowers x)) :
    x ∈ qCoreOf H p := by
  have hzF : Subgroup.zpowers x ≤ CFSG.fittingSubgroupOf H := Subgroup.zpowers_le.mpr hx
  have hsn : ((Subgroup.zpowers x).subgroupOf H).IsSubnormal :=
    isSubnormal_subgroupOf_trans hzF
      (isSubnormal_of_nilpotent (CFSG.fittingSubgroupOf_isNilpotent H) _ hzF)
      (isSubnormal_subgroupOf_of_isNormalIn (fittingSubgroupOf_isNormalIn H))
  exact le_qCoreOf_of_isSubnormal_isPGroup H _ p
    (hzF.trans (fittingSubgroupOf_isNormalIn H).1) hsn hxp (Subgroup.mem_zpowers x)

omit [Finite G] in
theorem isElemAbelian_conjSub_inf {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) (g : G)
    (M : Subgroup G) : CFSG.Open.IsElemAbelian 2 (conjSub g A ⊓ M) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h : (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨_, mem_conjSub.1 x.2.1⟩ ⟨_, mem_conjSub.1 y.2.1⟩)
    show (x : G) * y = y * x
    calc (x : G) * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h]
      _ = y * x := by group
  · have h := hA.2 _ (mem_conjSub.1 hx.1)
    rw [conj_pow] at h
    exact conj_eq_one_iff.mp h

theorem eq_componentLayerOf_sup_oddCoreOf {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXp : IsPGroup p X) :
    X = componentLayerOf X ⊔ CFSG.Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent X := hXp.isNilpotent
  rw [componentLayerOf_eq_bot_of_isSolvable inferInstance, bot_sup_eq,
    fittingSubgroupOf_eq_self_of_isNilpotent hnil, oddCoreOf_eq]
  have hodd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := hXp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have htop : CFSG.pPrimeCore 2 X = ⊤ := by
    rw [eq_top_iff]
    refine le_sSup ⟨Subgroup.normal_top, ?_⟩
    rw [Subgroup.card_top]
    exact Nat.coprime_two_left.mpr hodd
  rw [CFSG.GorensteinWalter.oddCoreOf, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem eq_of_le_isCyclic {C Z₁ Z₂ : Subgroup G} {p : ℕ} (hp : p.Prime) (hC : IsCyclic C)
    (h₁ : Z₁ ≤ C) (h₂ : Z₂ ≤ C) (hc₁ : Nat.card Z₁ = p) (hc₂ : Nat.card Z₂ = p) : Z₁ = Z₂ := by
  have hCab : IsMulCommutative C := hC.isMulCommutative
  have hel : ∀ Z : Subgroup G, Z ≤ C → Nat.card Z = p → CFSG.Open.IsElemAbelian p Z := by
    intro Z hZ hc
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩,
      fun x hx => orderOf_dvd_iff_pow_eq_one.mp (hc ▸ Subgroup.orderOf_dvd_natCard Z hx)⟩
    have h := congrArg Subtype.val (hCab.is_comm.comm ⟨x, hZ x.2⟩ ⟨y, hZ y.2⟩)
    exact h
  have h12 : Z₁ ≤ Subgroup.centralizer (Z₂ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hCab.is_comm.comm ⟨y, h₂ hy⟩ ⟨x, h₁ hx⟩)
  have hsup := isElemAbelian_sup (hel Z₁ h₁ hc₁) (hel Z₂ h₂ hc₂) h12
  have hcard := Bender35.card_le_of_isCyclic_of_pow_eq_one hp
    (isCyclic_of_le (sup_le h₁ h₂) hC) hsup.2
  have e₁ : Z₁ = Z₁ ⊔ Z₂ := Subgroup.eq_of_le_of_card_ge le_sup_left (hc₁ ▸ hcard)
  have e₂ : Z₂ = Z₁ ⊔ Z₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (hc₂ ▸ hcard)
  rw [e₁, ← e₂]

omit [Finite G] in
theorem mul_pow_eq_one {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : ∀ u ∈ X, ∀ v ∈ X, ⁅u, v⁆ ∈ Subgroup.centralizer (X : Set G)) {y z : G}
    (hy : y ∈ X) (hz : z ∈ X) (hyp : y ^ p = 1) (hzp : z ^ p = 1) : (y * z) ^ p = 1 := by
  have hc := hcen z hz y hy
  have hcy : Commute ⁅z, y⁆ y := ((Subgroup.mem_centralizer_iff.mp hc) y hy).symm
  have hcz : Commute ⁅z, y⁆ z := ((Subgroup.mem_centralizer_iff.mp hc) z hz).symm
  rw [mul_pow_of_commute_commutator hcy hcz p, hyp, hzp, one_mul, one_mul]
  have hcp : ⁅z, y⁆ ^ p = 1 := by
    rw [← commutatorElement_pow_left hcz, hzp, commutatorElement_one_left]
  have hdvd : p ∣ p.choose 2 := by
    rw [Nat.choose_two_right]
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    refine ⟨k, ?_⟩
    rw [hk]
    have : (2 * k + 1) * (2 * k + 1 - 1) = 2 * ((2 * k + 1) * k) := by
      rw [Nat.add_sub_cancel]; ring
    rw [this, Nat.mul_div_cancel_left _ two_pos]
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, pow_mul, hcp, one_pow]

omit [Finite G] in
theorem mem_closure_iff {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : ∀ u ∈ X, ∀ v ∈ X, ⁅u, v⁆ ∈ Subgroup.centralizer (X : Set G)) {y : G} :
    y ∈ Subgroup.closure {z | z ∈ X ∧ z ^ p = 1} ↔ y ∈ X ∧ y ^ p = 1 := by
  refine ⟨fun hy => ?_, fun hy => Subgroup.subset_closure hy⟩
  induction hy using Subgroup.closure_induction with
  | mem z hz => exact hz
  | one => exact ⟨X.one_mem, one_pow p⟩
  | mul u v _ _ hu hv => exact ⟨X.mul_mem hu.1 hv.1, mul_pow_eq_one hp hp2 hcen hu.1 hv.1 hu.2 hv.2⟩
  | inv u _ hu => exact ⟨X.inv_mem hu.1, by rw [inv_pow, hu.2, inv_one]⟩

@[expose] def IsBad (a : G) (H Y : Subgroup G) : Prop :=
  Y ≠ ⊥ ∧ Y ≤ generalizedFittingSubgroupOf H ∧
    (Y.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal ∧
    a ∈ Subgroup.normalizer (Y : Set G) ∧ Y ∉ goldA a H

section Bad

variable {S : Sylow 2 G} {A : Subgroup G} {a : G} {H : Subgroup G}

theorem eq_bot_of_isBad (h52 : S_G52) (h53 : S_G53) (hS : GoldSetting G S A) (haA : a ∈ A)
    (ha1 : a ≠ 1) (hH : H ∈ CFSG.Walter.benderM a) {Y : Subgroup G} (hY : IsBad a H Y)
    {V : Subgroup G} (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hVsn : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVY : V ≤ Subgroup.normalizer (Y : Set G))
    (hVC : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVa : ⁅V, Subgroup.zpowers a⁆ = V) : V = ⊥ := by
  by_contra hV1
  have hVA := h52 G S A hS a haA ha1 H hH V hV1 hVF hVsn hVC
  have haV : a ∈ Subgroup.normalizer (V : Set G) :=
    hVC (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  exact hY.2.2.2.2 (h53 G S A hS a haA ha1 H hH Y V hY.1 hY.2.1 hY.2.2.1 hY.2.2.2.1 hVF hVsn
    haV hVY (Or.inl ⟨hVa, hVA⟩))

theorem not_mem_goldA_of_isBad (h53 : S_G53) (hS : GoldSetting G S A) (haA : a ∈ A)
    (ha1 : a ≠ 1) (hH : H ∈ CFSG.Walter.benderM a) {Y : Subgroup G} (hY : IsBad a H Y)
    {V : Subgroup G} (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hVsn : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (hVY : V ≤ Subgroup.normalizer (Y : Set G))
    (hVa : ⁅V, Subgroup.zpowers a⁆ = V) : V ∉ goldA a H := fun hVA =>
  hY.2.2.2.2 (h53 G S A hS a haA ha1 H hH Y V hY.1 hY.2.1 hY.2.2.1 hY.2.2.2.1 hVF hVsn haV hVY
    (Or.inl ⟨hVa, hVA⟩))

theorem false_of_isBad (h53 : S_G53) (hS : GoldSetting G S A) (haA : a ∈ A) (ha1 : a ≠ 1)
    (hH : H ∈ CFSG.Walter.benderM a) {Y : Subgroup G} (hY : IsBad a H Y) {V : Subgroup G}
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hVsn : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (hVY : V ≤ Subgroup.normalizer (Y : Set G))
    (hVa : ⁅V, Subgroup.zpowers a⁆ = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hVel : CFSG.Open.IsElemAbelian p V) (hVc : Nat.card V = p ^ 2)
    (hVv : ∀ v ∈ V, v ≠ 1 → Subgroup.zpowers v ∈ goldA a H) : False :=
  hY.2.2.2.2 (h53 G S A hS a haA ha1 H hH Y V hY.1 hY.2.1 hY.2.2.1 hY.2.2.2.1 hVF hVsn haV hVY
    (Or.inr ⟨hVa, ⟨p, hp, hp2, hVel, hVc⟩, hVv⟩))

theorem componentLayerOf_le_centralizer (h52 : S_G52) (h53 : S_G53) (hS : GoldSetting G S A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hH : H ∈ CFSG.Walter.benderM a) {Y : Subgroup G}
    (hY : IsBad a H Y) : componentLayerOf H ≤ Subgroup.centralizer ({a} : Set G) := by
  have hCH := centralizer_le_of_mem_benderM hH
  have haH := mem_of_mem_benderM hH
  set 𝒦 := {L : Subgroup G | IsComponentOf L H ∧ ¬ L ≤ Subgroup.centralizer ({a} : Set G)}
    with h𝒦
  set V := sSup 𝒦 with hVdef
  have hVE : V ≤ componentLayerOf H :=
    sSup_le fun L hL => le_sSup (s := {E : Subgroup G | IsComponentOf E H}) hL.1
  have hVF : V ≤ generalizedFittingSubgroupOf H := hVE.trans le_sup_right
  have hFN : generalizedFittingSubgroupOf H ≤ Subgroup.normalizer (V : Set G) :=
    fun x hx => mem_normalizer_sSup fun L hL =>
      Bender37.generalizedFitting_le_normalizer_component hL.1 hx
  have hVsn : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal :=
    isSubnormal_subgroupOf_of_le_normalizer hVF hFN
  have hmap : ∀ g ∈ Subgroup.centralizer ({a} : Set G), ∀ L ∈ 𝒦,
      L.map (MulAut.conj g).toMonoidHom ∈ 𝒦 := by
    intro g hg L hL
    refine ⟨fstar_isComponentOf_conjugateSubgroup_of_mem hL.1 g (hCH hg), fun h => hL.2 ?_⟩
    have h' := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
    rwa [map_conj_map_conj_inv, map_conj_eq_self_of_mem (Subgroup.inv_mem _ hg)] at h'
  have hVC : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    fun c hc => mem_normalizer_sSup_of_map_mem (hmap c hc) (hmap c⁻¹ (Subgroup.inv_mem _ hc))
  have hYH : Y ≤ H := hY.2.1.trans (generalizedFittingSubgroupOf_le H)
  have hYsnH : (Y.subgroupOf H).IsSubnormal :=
    isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting hY.2.1 hY.2.2.1
  have hVY : V ≤ Subgroup.normalizer (Y : Set G) :=
    hVE.trans ((componentLayerOf_le_sup_centralizer hYH hYsnH).trans
      (sup_centralizer_le_normalizer Y))
  have haC : a ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hVa : ⁅V, Subgroup.zpowers a⁆ = V := by
    refine le_antisymm (commutator_zpowers_le_of_mem_normalizer (hVC haC))
      (sSup_le fun L hL => ?_)
    rcases G55.le_commutator_or_eq_bot hL.1 haH with h | h
    · exfalso
      apply hL.2
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq'] at h
      exact h
    · exact h.trans (Subgroup.commutator_mono (le_sSup hL) le_rfl)
  have hV1 := eq_bot_of_isBad h52 h53 hS haA ha1 hH hY hVF hVsn hVY hVC hVa
  refine sSup_le fun L hL => ?_
  by_contra hLa
  exact Bender37.ne_bot_of_isComponentOf hL
    (le_bot_iff.mp (hV1 ▸ le_sSup (s := 𝒦) ⟨hL, hLa⟩))

theorem mem_qCoreOf_two_of_le_centralizer (h31 : S_G31) (hS : GoldSetting G S A) (haA : a ∈ A)
    (ha1 : a ≠ 1) (hH : H ∈ CFSG.Walter.benderM a)
    (hE : componentLayerOf H ≤ Subgroup.centralizer ({a} : Set G))
    (hq : ∀ q : ℕ, q.Prime → q ≠ 2 → qCoreOf H q ≤ Subgroup.centralizer ({a} : Set G)) :
    a ∈ qCoreOf H 2 := by
  have hHco := isCoatom_of_mem_benderM hH
  have haH := mem_of_mem_benderM hH
  obtain ⟨g, hAg, hSS⟩ := hS.sstar H hHco.1
  set A₁ := conjSub g A ⊓ H
  have haA₁ : a ∈ A₁ := ⟨hAg ⟨haA, haH⟩, haH⟩
  set K := normalClosureIn H A₁
  have haK : a ∈ K := inf_le_normalClosureIn H A₁ ⟨haA₁, haH⟩
  have hKH := normalClosureIn_isNormalIn H A₁
  set N := CFSG.Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf K) with hNdef
  have hNF : N ≤ CFSG.fittingSubgroupOf K := Subgroup.map_subtype_le _
  have hNnil : Group.IsNilpotent N := isNilpotent_of_le (CFSG.fittingSubgroupOf_isNilpotent K) hNF
  have hNodd : Odd (Nat.card N) := by
    rw [hNdef, oddCoreOf_eq]
    exact CFSG.Walter.odd_card_oddCoreOf _
  have hNH : N ≤ H := hNF.trans ((fittingSubgroupOf_isNormalIn K).1.trans hKH.1)
  have hNsn : (N.subgroupOf H).IsSubnormal := by
    have h1 : (N.subgroupOf (CFSG.fittingSubgroupOf K)).IsSubnormal :=
      isSubnormal_subgroupOf_of_isNormalIn (isNormalIn_map_subtype _ _)
    have h2 : ((CFSG.fittingSubgroupOf K).subgroupOf K).IsSubnormal :=
      isSubnormal_subgroupOf_of_isNormalIn (fittingSubgroupOf_isNormalIn K)
    exact isSubnormal_subgroupOf_trans hNF h1 (isSubnormal_subgroupOf_trans
      (fittingSubgroupOf_isNormalIn K).1 h2 (isSubnormal_subgroupOf_of_isNormalIn hKH))
  have hNa : N ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [← fittingSubgroupOf_eq_self_of_isNilpotent hNnil, (show CFSG.fittingSubgroupOf N = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf N)]
    refine iSup_le fun q => ?_
    have hqp : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    have hq2 : q.1.1 ≠ 2 := by
      intro h
      have hdvd : 2 ∣ Nat.card N := h ▸ Nat.dvd_of_mem_primeFactors q.1.2
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdvd)
    have hqN := qCoreOf_normal_in N q.1.1
    refine (le_qCoreOf_of_isSubnormal_isPGroup H _ q.1.1 (hqN.1.trans hNH)
      (isSubnormal_subgroupOf_trans hqN.1 (isSubnormal_subgroupOf_of_isNormalIn hqN) hNsn)
      (qCoreOf_isPGroup N q.1.1)).trans (hq _ hqp hq2)
  have haCN : a ∈ Subgroup.centralizer (N : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hNa hn)
  have haF : a ∈ generalizedFittingSubgroupOf H := (h31 G H A₁ hSS).2 ⟨haK, haCN⟩
  have haCE : a ∈ Subgroup.centralizer (componentLayerOf H : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he => Subgroup.mem_centralizer_singleton_iff.mp (hE he)
  have haFit := generalizedFittingSubgroupOf_inf_centralizer_le H ⟨haF, haCE⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine mem_qCoreOf_of_mem_fitting haFit (IsPGroup.of_card (n := 1) ?_)
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_eq_prime (hS.elem.2 a haA) ha1

end Bad

omit [Finite G] in
theorem coprime_orderOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} (ha2 : a * a = 1) :
    Nat.Coprime p (orderOf a) := by
  have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, ha2])
  exact Nat.Coprime.coprime_dvd_right h2 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

section PCore

variable {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} (ha2 : a * a = 1)
  (haH : a ∈ H)
include hp hp2 ha2 haH

theorem commutator_inf_fstarZero_ne_bot (hPa : ⁅qCoreOf H p, Subgroup.zpowers a⁆ ≠ ⊥) :
    ⁅qCoreOf H p ⊓ fstarZero H, Subgroup.zpowers a⁆ ≠ ⊥ := by
  intro h
  apply hPa
  have hPN := le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have h11 := bender1970_1_1_thompson p hp (qCoreOf H p ⊓ fstarZero H) (Subgroup.zpowers a)
    (qCoreOf H p) ((qCoreOf_isPGroup H p).to_le inf_le_left) (qCoreOf_isPGroup H p)
    (Bender35.pResidualOf_zpowers_eq hp (coprime_orderOf hp hp2 ha2))
    (fun x hx => hPN ((qCoreOf_normal_in H p).1 hx.1))
    (Subgroup.zpowers_le.mpr (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) haH)) h
    (le_bot_iff.mp (h ▸ Subgroup.commutator_mono
      (le_inf inf_le_left (inf_centralizer_le_fstarZero H hp)) le_rfl))
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact h11

theorem exists_inverted_mem_normalizer {Y : Subgroup G} (hYF0 : Y ≤ fstarZero H)
    (hYsn : (Y.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (haY : a ∈ Subgroup.normalizer (Y : Set G))
    (hP₀a : ⁅qCoreOf H p ⊓ fstarZero H, Subgroup.zpowers a⁆ ≠ ⊥) :
    ∃ x ∈ qCoreOf H p ⊓ fstarZero H ⊓ Subgroup.normalizer (Y : Set G),
      orderOf x = p ∧ a * x * a⁻¹ = x⁻¹ := by
  set P := qCoreOf H p
  set P₀ := P ⊓ fstarZero H
  set B := P₀ ⊓ Subgroup.normalizer (Y : Set G) with hBdef
  have hYF : Y ≤ generalizedFittingSubgroupOf H := hYF0.trans (fstarZero_le H)
  have hP₀p : IsPGroup p P₀ := (qCoreOf_isPGroup H p).to_le inf_le_left
  have hBp : IsPGroup p B := hP₀p.to_le inf_le_left
  have haP₀ : a ∈ Subgroup.normalizer (P₀ : Set G) :=
    mem_normalizer_inf (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) haH)
      (le_normalizer_fstarZero H haH)
  have haB : a ∈ Subgroup.normalizer (B : Set G) :=
    mem_normalizer_inf haP₀ (Subgroup.le_normalizer haY)
  have hBa : ⁅B, Subgroup.zpowers a⁆ ≠ ⊥ := by
    intro h
    apply hP₀a
    have hCB : P₀ ⊓ Subgroup.centralizer (B : Set G) ≤ B := by
      rintro c ⟨hcP₀, hcB⟩
      refine ⟨hcP₀, ?_⟩
      have hYP : Y ⊓ P = Y ⊓ P₀ :=
        le_antisymm (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hYF0)))
          (inf_le_inf_left Y inf_le_left)
      have hcN : c ∈ Subgroup.normalizer ((Y ⊓ P : Subgroup G) : Set G) := by
        rw [hYP]
        refine Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le ?_ hcB)
        intro y hy
        exact ⟨hy.2, Subgroup.le_normalizer hy.1⟩
      exact mem_normalizer_of_mem_normalizer_inf_qCoreOf hp hYF hYsn hcP₀.1 hcN
    have h11 := bender1970_1_1_thompson p hp B (Subgroup.zpowers a) P₀ hBp hP₀p
      (Bender35.pResidualOf_zpowers_eq hp (coprime_orderOf hp hp2 ha2))
      (fun x hx => Subgroup.le_normalizer hx.1) (Subgroup.zpowers_le.mpr haP₀) h
      (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hCB le_rfl))
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h11
  obtain ⟨c, hcB, hca⟩ : ∃ c ∈ B, c * a ≠ a * c := by
    by_contra hcon
    push Not at hcon
    exact hBa (by rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]; exact hcon)
  set w := ⁅c, a⁆ with hwdef
  have hwB : w ∈ B := by
    have : w = c * (a * c⁻¹ * a⁻¹) := by rw [hwdef, commutatorElement_def]; group
    rw [this]
    exact B.mul_mem hcB ((Subgroup.mem_normalizer_iff.mp haB _).mp (B.inv_mem hcB))
  have hw1 : w ≠ 1 := by
    rw [hwdef, Ne, commutatorElement_eq_one_iff_mul_comm]
    exact fun h => hca h
  obtain ⟨x, hxw, hxo, hax⟩ := G55.exists_orderOf_eq_prime_of_conj_eq_inv hp hBp hwB hw1
    (conj_commutatorElement_eq_inv ha2 c)
  exact ⟨x, (Subgroup.zpowers_le.mpr hwB) hxw, hxo, hax⟩

end PCore

omit [Finite G] in
theorem conj_eq_inv_of_mem_zpowers {t w : G} (h : t * w * t⁻¹ = w⁻¹) {y : G}
    (hy : y ∈ Subgroup.zpowers w) : t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h, inv_zpow']
  rw [zpow_neg]

omit [Finite G] in
theorem commutator_zpowers_eq_of_conj_eq_inv {t w : G} (h : t * w * t⁻¹ = w⁻¹)
    (hw : Odd (orderOf w)) : ⁅Subgroup.zpowers w, Subgroup.zpowers t⁆ = Subgroup.zpowers w :=
  commutator_zpowers_eq_self_of_conj_eq_inv (Bender35.mem_normalizer_zpowers_of_conj_eq_inv h)
    (fun _ hy => conj_eq_inv_of_mem_zpowers h hy) (by rwa [Nat.card_zpowers])

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers {K : Subgroup G} {x : G} (hx : x ∈ K) :
    Subgroup.centralizer (K : Set G) ≤ Subgroup.normalizer
      ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [centralizer_zpowers_eq']
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx)

section Reduced

variable {S : Sylow 2 G} {A : Subgroup G} {a : G} {H : Subgroup G}

theorem isBad_zpowers (h53 : S_G53) (hS : GoldSetting G S A) (haA : a ∈ A) (ha1 : a ≠ 1)
    (hH : H ∈ CFSG.Walter.benderM a) {Y : Subgroup G} (hY : IsBad a H Y) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : G} (hxP : x ∈ qCoreOf H p) (hxY : x ∈ Subgroup.normalizer (Y : Set G))
    (hxo : orderOf x = p) (hax : a * x * a⁻¹ = x⁻¹) : IsBad a H (Subgroup.zpowers x) := by
  have hzP : Subgroup.zpowers x ≤ qCoreOf H p := Subgroup.zpowers_le.mpr hxP
  obtain ⟨hzF, hzsn⟩ := Bender35.le_and_isSubnormal hp hzP
  have haz := Bender35.mem_normalizer_zpowers_of_conj_eq_inv hax
  have hx1 : x ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hxo, h, orderOf_one])
  refine ⟨by rwa [Ne, Subgroup.zpowers_eq_bot], hzF, hzsn, haz, ?_⟩
  exact not_mem_goldA_of_isBad h53 hS haA ha1 hH hY hzF hzsn haz (Subgroup.zpowers_le.mpr hxY)
    (commutator_zpowers_eq_of_conj_eq_inv hax (hxo ▸ hp.odd_of_ne_two hp2))

omit [Finite G] in
theorem mem_commutator_of_conj_eq_inv {P : Subgroup G} {x : G} (hxP : x ∈ P)
    (hxo : Odd (orderOf x)) (hax : a * x * a⁻¹ = x⁻¹) : x ∈ ⁅P, Subgroup.zpowers a⁆ := by
  have : Subgroup.zpowers x ≤ ⁅P, Subgroup.zpowers a⁆ :=
    calc Subgroup.zpowers x = ⁅Subgroup.zpowers x, Subgroup.zpowers a⁆ :=
          (commutator_zpowers_eq_of_conj_eq_inv hax hxo).symm
      _ ≤ ⁅P, Subgroup.zpowers a⁆ := Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hxP) le_rfl
  exact this (Subgroup.mem_zpowers x)

variable (h52 : S_G52) (h53 : S_G53) (hS : GoldSetting G S A) (haA : a ∈ A) (ha1 : a ≠ 1)
  (hH : H ∈ CFSG.Walter.benderM a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G}
  (hxP : x ∈ qCoreOf H p) (hxo : orderOf x = p) (hax : a * x * a⁻¹ = x⁻¹)
  (hYx : IsBad a H (Subgroup.zpowers x))
include h52 h53 hS haA ha1 hH hp hp2 hxP hxo hax hYx

omit hxP in
theorem centralizer_props {K : Subgroup G} (hKP : K ≤ qCoreOf H p)
    (hKC : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (K : Set G)) (hxK : x ∈ K) :
    qCoreOf H p ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.centralizer ({a} : Set G) ∧
      IsCyclic (qCoreOf H p ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
  have _ := hax
  have hCH := centralizer_le_of_mem_benderM hH
  have ha2 : a * a = 1 := mul_self_eq_one_of_mem hS.elem haA
  have hao : orderOf a = 2 := orderOf_eq_prime (hS.elem.2 a haA) ha1
  have haC : a ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set P := qCoreOf H p
  set C := P ⊓ Subgroup.centralizer (K : Set G) with hCdef
  have hPN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    hCH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p))
  have hCC : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (C : Set G) := fun c hc =>
    mem_normalizer_inf (hPN hc) (Bender35.mem_normalizer_centralizer (hKC hc))
  have hzN : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [← centralizer_zpowers_eq']
    exact Subgroup.centralizer_le_normalizer _
  have hCx : Subgroup.centralizer (K : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    centralizer_le_normalizer_zpowers hxK
  have h1 : C ≤ Subgroup.centralizer ({a} : Set G) := by
    set V := ⁅C, Subgroup.zpowers a⁆ with hVdef
    have hVC : V ≤ C := commutator_zpowers_le_of_mem_normalizer (hCC haC)
    obtain ⟨hVF, hVsn⟩ := Bender35.le_and_isSubnormal hp (hVC.trans inf_le_left)
    have hV := eq_bot_of_isBad h52 h53 hS haA ha1 hH hYx hVF hVsn
      ((hVC.trans inf_le_right).trans hCx)
      (fun c hc => mem_normalizer_commutator (hCC hc) (hzN hc))
      (Bender35.commutator_commutator_eq hp hp2 inf_le_left hao (hCC haC))
    rw [hVdef, Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff] at hV
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hV c hc)
  refine ⟨h1, ?_⟩
  have hKa : ⁅K, Subgroup.zpowers a⁆ ∈ goldA a H := by
    have hKaK : ⁅K, Subgroup.zpowers a⁆ ≤ K := commutator_zpowers_le_of_mem_normalizer (hKC haC)
    obtain ⟨hF, hsn⟩ := Bender35.le_and_isSubnormal hp (hKaK.trans hKP)
    refine h52 G S A hS a haA ha1 H hH _ ?_ hF hsn
      (fun c hc => mem_normalizer_commutator (hKC hc) (hzN hc))
    intro h
    apply hYx.1
    rw [← commutator_zpowers_eq_of_conj_eq_inv hax (hxo ▸ hp.odd_of_ne_two hp2), eq_bot_iff, ← h]
    exact Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hxK) le_rfl
  have hz : ∀ z ∈ C, z ≠ 1 → Subgroup.zpowers z ∈ goldA a H := by
    intro z hz hz1
    have hzP : Subgroup.zpowers z ≤ P := Subgroup.zpowers_le.mpr hz.1
    obtain ⟨hzF, hzsn⟩ := Bender35.le_and_isSubnormal hp hzP
    have haz : a ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [centralizer_zpowers_eq', Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (h1 hz)).symm
    have hKaK : ⁅K, Subgroup.zpowers a⁆ ≤ K := commutator_zpowers_le_of_mem_normalizer (hKC haC)
    obtain ⟨hF, hsn⟩ := Bender35.le_and_isSubnormal hp (hKaK.trans hKP)
    have hKz : K ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
      (Subgroup.le_centralizer_iff.mp
        (Subgroup.zpowers_le.mpr hz.2)).trans (Subgroup.centralizer_le_normalizer _)
    exact h53 G S A hS a haA ha1 H hH _ _ (by rwa [Ne, Subgroup.zpowers_eq_bot]) hzF hzsn haz hF
      hsn (mem_normalizer_commutator (hKC haC) (hzN haC)) (hKaK.trans hKz)
      (Or.inl ⟨Bender35.commutator_commutator_eq hp hp2 hKP hao (hKC haC), hKa⟩)
  by_contra hcyc
  obtain ⟨E, hEC, hE, hEc⟩ :=
    exists_isElemAbelian_card_sq hp hp2 ((qCoreOf_isPGroup H p).to_le inf_le_left) hcyc
  obtain ⟨hEF, hEsn⟩ := Bender35.le_and_isSubnormal hp (hEC.trans inf_le_left)
  have hEa : E ≤ Subgroup.centralizer ({a} : Set G) := hEC.trans h1
  refine false_of_isBad h53 hS haA ha1 hH hYx hEF hEsn ?_ ((hEC.trans inf_le_right).trans hCx)
    ?_ hp hp2 hE hEc fun v hv hv1 => hz v (hEC hv) hv1
  · refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEa he)
  · rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEa he)

section Fstar

variable (hxF0 : x ∈ fstarZero H)
include hxF0

theorem centralizer_inf_fstarZero_props :
    qCoreOf H p ⊓ Subgroup.centralizer ((qCoreOf H p ⊓ fstarZero H : Subgroup G) : Set G) ≤
        Subgroup.centralizer ({a} : Set G) ∧
      IsCyclic (qCoreOf H p ⊓
        Subgroup.centralizer ((qCoreOf H p ⊓ fstarZero H : Subgroup G) : Set G) : Subgroup G) := by
  have hCH := centralizer_le_of_mem_benderM hH
  refine centralizer_props h52 h53 hS haA ha1 hH hp hp2 hxo hax hYx inf_le_left
    (fun c hc => mem_normalizer_inf
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) (hCH hc))
      (le_normalizer_fstarZero H (hCH hc))) ⟨hxP, hxF0⟩

theorem commutator_le_centralizer :
    ⁅qCoreOf H p, qCoreOf H p⁆ ≤ Subgroup.centralizer ({a} : Set G) ∧
      IsCyclic (⁅qCoreOf H p, qCoreOf H p⁆ : Subgroup G) := by
  obtain ⟨h1, h2⟩ := centralizer_inf_fstarZero_props h52 h53 hS haA ha1 hH hp hp2 hxP hxo hax
    hYx hxF0
  set P := qCoreOf H p
  set P' := ⁅P, P⁆
  have hP'P : P' ≤ P := Bender35.commutator_self_le P
  have hZ : P' ⊓ Subgroup.centralizer (P' : Set G) ≤
      P ⊓ Subgroup.centralizer ((P ⊓ fstarZero H : Subgroup G) : Set G) :=
    le_inf (inf_le_left.trans hP'P) ((center_commutator_le_centralizer_fstarZero H hp).trans
      (Subgroup.centralizer_le (fun _ hy => hy.2)))
  have hcyc : IsCyclic P' := by
    by_contra h
    exact not_isCyclic_center_commutator hp hp2 (qCoreOf_isPGroup H p) h
      (isCyclic_of_le hZ h2)
  have hab : P' ≤ Subgroup.centralizer (P' : Set G) := by
    have hcomm : IsMulCommutative P' := hcyc.isMulCommutative
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨z, hz⟩ ⟨y, hy⟩)
  exact ⟨(le_inf le_rfl hab).trans (hZ.trans h1), hcyc⟩

theorem commutator_commutator_centralizer_eq_bot :
    ⁅⁅qCoreOf H p, Subgroup.zpowers a⁆, qCoreOf H p ⊓ Subgroup.centralizer ({a} : Set G)⁆ = ⊥ := by
  have hP' := (commutator_le_centralizer h52 h53 hS haA ha1 hH hp hp2 hxP hxo hax hYx hxF0).1
  refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
  · have h : ⁅Subgroup.zpowers a, qCoreOf H p ⊓ Subgroup.centralizer ({a} : Set G)⁆ = ⊥ := by
      rw [commutator_zpowers_eq_bot_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [h, Subgroup.commutator_bot_left]
  · rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hP' (Subgroup.commutator_mono inf_le_left le_rfl hy))

theorem centralizer_eq_center :
    qCoreOf H p ⊓ Subgroup.centralizer ({a} : Set G) =
        qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G) ∧
      IsCyclic (qCoreOf H p ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) := by
  have hCH := centralizer_le_of_mem_benderM hH
  have haH := mem_of_mem_benderM hH
  have ha2 : a * a = 1 := mul_self_eq_one_of_mem hS.elem haA
  set P := qCoreOf H p
  set P₁ := ⁅P, Subgroup.zpowers a⁆ with hP₁def
  have haP : a ∈ Subgroup.normalizer (P : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) haH
  have hzN : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [← centralizer_zpowers_eq']
    exact Subgroup.centralizer_le_normalizer _
  have hP₁ := centralizer_props h52 h53 hS haA ha1 hH hp hp2 hxo hax hYx (K := P₁)
    (commutator_zpowers_le_of_mem_normalizer haP)
    (fun c hc => mem_normalizer_commutator
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) (hCH hc)) (hzN hc))
    (mem_commutator_of_conj_eq_inv hxP (hxo ▸ hp.odd_of_ne_two hp2) hax)
  have h3 := commutator_commutator_centralizer_eq_bot h52 h53 hS haA ha1 hH hp hp2 hxP hxo hax
    hYx hxF0
  have hCP₁ : P ⊓ Subgroup.centralizer ({a} : Set G) ≤
      P ⊓ Subgroup.centralizer (P₁ : Set G) := by
    refine le_inf inf_le_left ?_
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    exact h3
  have hcyc : IsCyclic (P ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
    isCyclic_of_le hCP₁ hP₁.2
  refine ⟨le_antisymm ?_ ?_, hcyc⟩
  ·
    have hab : IsMulCommutative (P ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
      hcyc.isMulCommutative
    refine le_inf inf_le_left fun c hc => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨c', hc', m, hm, rfl⟩ := exists_mem_centralizer_mul_mem_commutator ha2 haP
      (Bender35.odd_card_of_le hp hp2 le_rfl) hy
    have h1 : c' * c = c * c' := congrArg Subtype.val (hab.is_comm.comm ⟨c', hc'⟩ ⟨c, hc⟩)
    have h2 : m * c = c * m := (Subgroup.mem_centralizer_iff.mp (hCP₁ hc).2) m hm
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  · have hZ := (centralizer_inf_fstarZero_props h52 h53 hS haA ha1 hH hp hp2 hxP hxo hax hYx
      hxF0).1
    exact le_inf inf_le_left ((inf_le_inf_left P (Subgroup.centralizer_le
      (show ((P ⊓ fstarZero H : Subgroup G) : Set G) ⊆ P from inf_le_left))).trans hZ)

theorem false_of_isBad_zpowers (h37 : S_G37) (h54 : S_G54) : False := by
  have hCH := centralizer_le_of_mem_benderM hH
  have haH := mem_of_mem_benderM hH
  have hHco := isCoatom_of_mem_benderM hH
  have := hS.isSimpleGroup
  have ha2 : a * a = 1 := mul_self_eq_one_of_mem hS.elem haA
  have hao : orderOf a = 2 := orderOf_eq_prime (hS.elem.2 a haA) ha1
  have haC : a ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have : Fact p.Prime := ⟨hp⟩
  have hxodd : Odd (orderOf x) := hxo ▸ hp.odd_of_ne_two hp2
  have hx1 : x ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hxo, h, orderOf_one])
  set P := qCoreOf H p with hPdef
  have hPp : IsPGroup p P := qCoreOf_isPGroup H p
  have hPH : IsNormalIn P H := qCoreOf_normal_in H p
  have hPN : H ≤ Subgroup.normalizer (P : Set G) := le_normalizer_of_isNormalIn hPH
  have haP : a ∈ Subgroup.normalizer (P : Set G) := hPN haH
  have hzN : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [← centralizer_zpowers_eq']
    exact Subgroup.centralizer_le_normalizer _
  obtain ⟨hCZ, hZcyc⟩ := centralizer_eq_center h52 h53 hS haA ha1 hH hp hp2 hxP hxo hax hYx hxF0
  have hP' := (commutator_le_centralizer h52 h53 hS haA ha1 hH hp hp2 hxP hxo hax hYx hxF0).1
  have hxa : x ∉ Subgroup.centralizer ({a} : Set G) := by
    intro h
    have h1 : a * x * a⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp h, mul_inv_cancel_right]
    rw [h1] at hax
    have hxx : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hax]
      exact mul_inv_cancel x
    have h2 := orderOf_dvd_of_pow_eq_one hxx
    rw [hxo] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hxP₁ : x ∈ ⁅P, Subgroup.zpowers a⁆ := mem_commutator_of_conj_eq_inv hxP hxodd hax
  have hPa : ⁅P, Subgroup.zpowers a⁆ ≠ ⊥ := by
    intro h
    rw [h] at hxP₁
    exact hx1 (Subgroup.mem_bot.mp hxP₁)
  have hFp : IsPGroup p (generalizedFittingSubgroupOf H) :=
    h54 G S A hS a haA ha1 H hH p hp hp2 hPa hCZ.le (hCZ ▸ hZcyc)
  set P₁ := ⁅P, Subgroup.zpowers a⁆ with hP₁def
  have hP₁P : P₁ ≤ P := commutator_zpowers_le_of_mem_normalizer haP
  have hP₁C : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (P₁ : Set G) :=
    fun c hc => mem_normalizer_commutator (hPN (hCH hc)) (hzN hc)
  have hcen : ∀ u ∈ P₁, ∀ v ∈ P₁, ⁅u, v⁆ ∈ Subgroup.centralizer (P : Set G) := by
    intro u hu v hv
    have hc := Subgroup.commutator_mem_commutator (hP₁P hu) (hP₁P hv)
    have h1 : ⁅u, v⁆ ∈ P ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨Bender35.commutator_self_le P hc, hP' hc⟩
    rw [hCZ] at h1
    exact h1.2
  have hcen₁ : ∀ u ∈ P₁, ∀ v ∈ P₁, ⁅u, v⁆ ∈ Subgroup.centralizer (P₁ : Set G) :=
    fun u hu v hv => Subgroup.centralizer_le hP₁P (hcen u hu v hv)
  set P₂ := Subgroup.closure {y | y ∈ P₁ ∧ y ^ p = 1} with hP₂def
  have hmem₂ : ∀ y, y ∈ P₂ ↔ y ∈ P₁ ∧ y ^ p = 1 := fun y => mem_closure_iff hp hp2 hcen₁
  have hP₂P₁ : P₂ ≤ P₁ := fun y hy => ((hmem₂ y).mp hy).1
  have hP₂P : P₂ ≤ P := hP₂P₁.trans hP₁P
  have hP₂p : IsPGroup p P₂ := hPp.to_le hP₂P
  have hexp : ∀ y ∈ P₂, y ^ p = 1 := fun y hy => ((hmem₂ y).mp hy).2
  have hxP₂ : x ∈ P₂ := (hmem₂ x).mpr ⟨hxP₁, hxo ▸ pow_orderOf_eq_one x⟩
  have hP₂C : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (P₂ : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem₂, hmem₂]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hP₁C hc) y).mp h1,
        by rw [conj_pow, h2, mul_one, mul_inv_cancel]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hP₁C hc) y).mpr h1, ?_⟩
      rw [conj_pow] at h2
      exact conj_eq_one_iff.mp h2
  obtain ⟨hC₂a, hC₂cyc⟩ :=
    centralizer_props h52 h53 hS haA ha1 hH hp hp2 hxo hax hYx hP₂P hP₂C hxP₂
  set C₂ := P ⊓ Subgroup.centralizer (P₂ : Set G) with hC₂def
  set Z₂ := P₂ ⊓ Subgroup.centralizer (P₂ : Set G) with hZ₂def
  have hZ₂C₂ : Z₂ ≤ C₂ := inf_le_inf_right _ hP₂P
  have hP₂1 : P₂ ≠ ⊥ := by
    intro h
    rw [h] at hxP₂
    exact hx1 (Subgroup.mem_bot.mp hxP₂)
  have hZ₂1 : Z₂ ≠ ⊥ :=
    inf_centralizer_ne_bot_of_isPGroup hp hP₂p hP₂p (Subgroup.le_normalizer) hP₂1
  have hZ₂cyc : IsCyclic Z₂ := isCyclic_of_le hZ₂C₂ hC₂cyc
  have hZ₂card : Nat.card Z₂ = p := by
    have hle := Bender35.card_le_of_isCyclic_of_pow_eq_one hp hZ₂cyc (fun y hy => hexp y hy.1)
    obtain ⟨k, hk⟩ := (hP₂p.to_le (inf_le_left : Z₂ ≤ P₂)).exists_card_eq
    have hk1 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hk
      exact hZ₂1 hk
    rw [hk] at hle ⊢
    have : p ^ k ≤ p ^ 1 := by rw [pow_one]; exact hle
    rw [le_antisymm ((Nat.pow_le_pow_iff_right hp.one_lt).mp this)
      (Nat.one_le_iff_ne_zero.mpr hk1), pow_one]
  have hcommle : ⁅P₂, P₂⁆ ≤ Z₂ := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    exact ⟨Bender35.commutator_self_le P₂ (Subgroup.commutator_mem_commutator hu hv),
      Subgroup.centralizer_le hP₂P (hcen u (hP₂P₁ hu) v (hP₂P₁ hv))⟩
  have hP₂na : ⁅P₂, P₂⁆ ≠ ⊥ := by
    intro h
    apply hxa
    have hab : P₂ ≤ Subgroup.centralizer (P₂ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact hC₂a ⟨hP₂P hxP₂, hab hxP₂⟩
  have hprime : ∀ W : Subgroup G, W ≤ Z₂ → W ≠ ⊥ → W = Z₂ := by
    intro W hW hW1
    refine Subgroup.eq_of_le_of_card_ge hW ?_
    rw [hZ₂card]
    rcases (Nat.dvd_prime hp).mp (hZ₂card ▸ Subgroup.card_dvd_of_le hW) with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hW1
    · exact h.ge
  have hcomm : ⁅P₂, P₂⁆ = Z₂ := hprime _ hcommle hP₂na
  have hZ₂Z : Z₂ ≤ P ⊓ Subgroup.centralizer (P : Set G) := by
    rw [← hCZ]
    exact le_inf (inf_le_left.trans hP₂P) (hZ₂C₂.trans hC₂a)
  set Y₁ := P₂ ⊓ Subgroup.centralizer ({x} : Set G) with hY₁def
  set Y₂ := ⁅Y₁, Subgroup.zpowers a⁆ with hY₂def
  have haxN : a ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    Bender35.mem_normalizer_zpowers_of_conj_eq_inv hax
  have haY₁ : a ∈ Subgroup.normalizer (Y₁ : Set G) := by
    refine mem_normalizer_inf (hP₂C haC) ?_
    rw [← centralizer_zpowers_eq']
    exact Bender35.mem_normalizer_centralizer haxN
  have hY₁P : Y₁ ≤ P := inf_le_left.trans hP₂P
  have hxY₁ : x ∈ Y₁ := ⟨hxP₂, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hxY₂ : x ∈ Y₂ := mem_commutator_of_conj_eq_inv hxY₁ hxodd hax
  have hY₂Y₁ : Y₂ ≤ Y₁ := commutator_zpowers_le_of_mem_normalizer haY₁
  have hY₂P : Y₂ ≤ P := hY₂Y₁.trans hY₁P
  obtain ⟨hY₂F, hY₂sn⟩ := Bender35.le_and_isSubnormal hp hY₂P
  have haY₂ : a ∈ Subgroup.normalizer (Y₂ : Set G) :=
    mem_normalizer_commutator haY₁ (Subgroup.le_normalizer (Subgroup.mem_zpowers a))
  have hY₂x : Y₂ ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    refine (hY₂Y₁.trans inf_le_right).trans ?_
    rw [← centralizer_zpowers_eq']
    exact Subgroup.centralizer_le_normalizer _
  have hY₂a : ⁅Y₂, Subgroup.zpowers a⁆ = Y₂ :=
    Bender35.commutator_commutator_eq hp hp2 hY₁P hao haY₁
  have hY₂A : Y₂ ∉ goldA a H :=
    not_mem_goldA_of_isBad h53 hS haA ha1 hH hYx hY₂F hY₂sn haY₂ hY₂x hY₂a
  have hY₂1 : Y₂ ≠ ⊥ := by
    intro h
    rw [h] at hxY₂
    exact hx1 (Subgroup.mem_bot.mp hxY₂)
  have hNZ : Subgroup.normalizer (Z₂ : Set G) = H := by
    have hHZ : H ≤ Subgroup.normalizer (Z₂ : Set G) := by
      intro h hh
      have hhZ : h ∈ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :
          Set G) := mem_normalizer_inf (hPN hh) (Bender35.mem_normalizer_centralizer (hPN hh))
      apply Bender35.mem_normalizer_of_map_conj_eq
      refine eq_of_le_isCyclic hp (hCZ ▸ hZcyc) ?_ hZ₂Z ?_ hZ₂card
      · rw [← Bender37.map_conj_eq_of_mem_normalizer hhZ]
        exact Subgroup.map_mono hZ₂Z
      · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hZ₂card]
    have hNZtop : Subgroup.normalizer (Z₂ : Set G) ≠ ⊤ := by
      intro h
      have hn : Z₂.Normal := Subgroup.normalizer_eq_top_iff.mp h
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Z₂ with h' | h'
      · exact hZ₂1 h'
      · exact hHco.1 (eq_top_iff.mpr (h' ▸ (inf_le_left.trans (hP₂P.trans hPH.1))))
    exact (hHco.le_iff.mp hHZ).resolve_left hNZtop
  have hY₂ab : ⁅Y₂, Y₂⁆ = ⊥ := by
    by_contra hna
    apply hY₂A
    have hY₂Z : ⁅Y₂, Y₂⁆ = Z₂ := hprime _ ((Subgroup.commutator_mono
      (hY₂Y₁.trans inf_le_left) (hY₂Y₁.trans inf_le_left)).trans hcommle) hna
    have hNY₂ : Subgroup.normalizer (Y₂ : Set G) ≤ H := fun g hg => by
      rw [← hNZ, ← hY₂Z]
      exact mem_normalizer_commutator hg hg
    refine ⟨hY₂1, hY₂F, hY₂sn, haY₂, fun M hM hNM => Or.inr ⟨p, hp, ?_, hFp⟩⟩
    have haM : a ∈ M := hNM haY₂
    obtain ⟨g, hAg, hSS⟩ := hS.sstar M hM.1
    have haA₂ : a ∈ conjSub g A ⊓ M := ⟨hAg ⟨haA, haM⟩, haM⟩
    set X := P ⊓ M with hXdef
    have hXC : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) :=
      fun c hc => mem_normalizer_inf (hPN (hCH hc.2)) (M.le_normalizer hc.1)
    have hXeq := eq_componentLayerOf_sup_oddCoreOf hp hp2 (hPp.to_le (inf_le_left : X ≤ P))
    obtain ⟨⟨hXaF, hXasn⟩, -⟩ := h37 G M (conjSub g A ⊓ M) hSS
      (isElemAbelian_conjSub_inf hS.elem g M) a haA₂ ha1 X inf_le_right hXC hXeq
    have haX : a ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_inf haP (M.le_normalizer haM)
    have hXaO : ⁅X, Subgroup.zpowers a⁆ ≤ qCoreOf M p :=
      le_qCoreOf_of_isSubnormal_isPGroup M _ p (hXaF.trans (generalizedFittingSubgroupOf_le M))
        (isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting hXaF hXasn)
        (hPp.to_le ((commutator_zpowers_le_of_mem_normalizer haX).trans inf_le_left))
    have hY₂X : Y₂ ≤ X := le_inf hY₂P (Subgroup.le_normalizer.trans hNM)
    have hY₂O : Y₂ ≤ qCoreOf M p :=
      calc Y₂ = ⁅Y₂, Subgroup.zpowers a⁆ := hY₂a.symm
        _ ≤ ⁅X, Subgroup.zpowers a⁆ := Subgroup.commutator_mono hY₂X le_rfl
        _ ≤ qCoreOf M p := hXaO
    have hCY₂M : Subgroup.centralizer (Y₂ : Set G) ≤ M :=
      (Subgroup.centralizer_le_normalizer _).trans hNM
    have hCY₂H : Subgroup.centralizer (Y₂ : Set G) ≤ H :=
      (Subgroup.centralizer_le_normalizer _).trans hNY₂
    have hFC := isPGroup_generalizedFitting_inf_centralizer hp hFp (hY₂P.trans hPH.1)
      (hPp.to_le hY₂P)
    rw [inf_of_le_right hCY₂H] at hFC
    exact isPGroup_generalizedFitting_of_le_qCoreOf hp hY₂O hCY₂M hFC
  have hY₁ab : Y₁ ≤ Subgroup.centralizer (Y₁ : Set G) := by
    have hZab : IsMulCommutative (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :=
      (hCZ ▸ hZcyc).isMulCommutative
    have hY₂c : IsMulCommutative Y₂ := by
      refine ⟨⟨fun u v => Subtype.ext ?_⟩⟩
      have h := Subgroup.commutator_mem_commutator u.2 v.2
      rw [hY₂ab, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
      exact h
    have hsup := Bender35.isMulCommutative_sup hZab hY₂c
      (inf_le_right.trans (Subgroup.centralizer_le hY₂P))
    have hY₁le : Y₁ ≤ (P ⊓ Subgroup.centralizer (P : Set G)) ⊔ Y₂ := by
      intro y hy
      obtain ⟨c, hc, m, hm, rfl⟩ := exists_mem_centralizer_mul_mem_commutator ha2 haY₁
        (Bender35.odd_card_of_le hp hp2 hY₁P) hy
      have hcZ : c ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
        rw [← hCZ]
        exact ⟨hY₁P hc.1, hc.2⟩
      exact Subgroup.mul_mem_sup hcZ hm
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (hsup.is_comm.comm ⟨v, hY₁le hv⟩ ⟨u, hY₁le hu⟩)
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : G, Z₂ = Subgroup.zpowers z₀ := by
    obtain ⟨⟨z, hz⟩, hgen⟩ := hZ₂cyc.exists_zpow_surjective
    refine ⟨z, le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr hz)⟩
    obtain ⟨k, hk⟩ := hgen ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hz₀C : z₀ ∈ Subgroup.centralizer (P₂ : Set G) :=
    ((hz₀ ▸ Subgroup.mem_zpowers z₀ : z₀ ∈ Z₂)).2
  have hz₀card : Nat.card (Subgroup.zpowers z₀) = p := hz₀ ▸ hZ₂card
  have hcm : ∀ y ∈ P₂, ∀ g ∈ P₂, ⁅y, g⁆ ∈ Subgroup.zpowers z₀ := fun y hy g hg => by
    rw [← hz₀, ← hcomm]
    exact Subgroup.commutator_mem_commutator hy hg
  have hcardP₂ : Nat.card P₂ ≤ p * Nat.card Y₁ := by
    have h := (card_le_and_commutator_le_of_commutator_mem hz₀C (hcm x hxP₂) le_rfl).1
    rwa [hz₀card] at h
  obtain ⟨y, hyP₂, hyY₁⟩ : ∃ y ∈ P₂, y ∉ Y₁ := by
    by_contra hcon
    push Not at hcon
    apply hxa
    have hxZ : x ∈ Z₂ := ⟨hxP₂, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hcon w hw).2)⟩
    exact hC₂a (hZ₂C₂ hxZ)
  have hY₁card : Nat.card Y₁ ≤ p * Nat.card (Y₁ ⊓ Subgroup.centralizer ({y} : Set G) :
      Subgroup G) := by
    have h := (card_le_and_commutator_le_of_commutator_mem hz₀C (hcm y hyP₂)
      (inf_le_left : Y₁ ≤ P₂)).1
    rwa [hz₀card] at h
  have hsupY : Y₁ ⊔ Subgroup.zpowers y = P₂ := by
    have hle : Y₁ ⊔ Subgroup.zpowers y ≤ P₂ := sup_le inf_le_left (Subgroup.zpowers_le.mpr hyP₂)
    have hlt : Y₁ < Y₁ ⊔ Subgroup.zpowers y := lt_of_le_of_ne le_sup_left fun h =>
      hyY₁ (h ▸ (le_sup_right : Subgroup.zpowers y ≤ Y₁ ⊔ Subgroup.zpowers y)
        (Subgroup.mem_zpowers y))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    calc Nat.card P₂ ≤ p * Nat.card Y₁ := hcardP₂
      _ ≤ Nat.card (Y₁ ⊔ Subgroup.zpowers y : Subgroup G) := card_ge_of_lt' hp (hP₂p.to_le hle) hlt
  have hYZ : Y₁ ⊓ Subgroup.centralizer ({y} : Set G) ≤ Z₂ := by
    intro w hw
    refine ⟨hw.1.1, ?_⟩
    rw [← hsupY]
    refine fstar_centralizer_of_centralizes_join ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact ((Subgroup.mem_centralizer_iff.mp (hY₁ab hv)) w hw.1).symm
    · rw [centralizer_zpowers_eq', Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_singleton_iff.mp hw.2
  have hP₂3 : Nat.card P₂ ≤ p ^ 3 :=
    calc Nat.card P₂ ≤ p * Nat.card Y₁ := hcardP₂
      _ ≤ p * (p * Nat.card (Y₁ ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)) :=
          Nat.mul_le_mul_left _ hY₁card
      _ ≤ p * (p * p) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hZ₂card ▸ Subgroup.card_le_of_le hYZ))
      _ = p ^ 3 := by ring
  obtain ⟨B, hAB, hBel, hB8⟩ := hS.rank
  have haB : a ∈ B := hAB haA
  have hBa : B ≤ Subgroup.centralizer ({a} : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hBel.1.is_comm.comm ⟨b, hb⟩ ⟨a, haB⟩)
  have hBN : B ≤ Subgroup.normalizer (P₂ : Set G) := hBa.trans hP₂C
  have hB2 : ∀ e ∈ B, e * e = 1 := fun e he => mul_self_eq_one_of_mem hBel he
  have hFH := generalizedFittingSubgroupOf_isNormalIn H
  have hFP : generalizedFittingSubgroupOf H ≤ P :=
    le_qCoreOf_of_normal_isPGroup H _ p hFH.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hFH.1).mpr (le_normalizer_of_isNormalIn hFH))
      hFp
  have hfaith : ∀ e ∈ B, P₂ ≤ Subgroup.centralizer ({e} : Set G) → e = 1 := by
    intro e he heP₂
    have heH : e ∈ H := hCH (hBa he)
    have heC₂N : e ∈ Subgroup.normalizer (C₂ : Set G) :=
      mem_normalizer_inf (hPN heH) (Bender35.mem_normalizer_centralizer (hBN he))
    have heC₂ : C₂ ≤ Subgroup.centralizer ({e} : Set G) :=
      le_centralizer_of_isCyclic hp hp2 (hPp.to_le inf_le_left) hC₂cyc hZ₂C₂ hZ₂card (hB2 e he)
        heC₂N (inf_le_left.trans heP₂)
    have h11 := bender1970_1_1_thompson p hp P₂ (Subgroup.zpowers e) P hP₂p hPp
      (Bender35.pResidualOf_zpowers_eq hp (coprime_orderOf hp hp2 (hB2 e he)))
      (fun w hw => P.le_normalizer (hP₂P hw)) (Subgroup.zpowers_le.mpr (hPN heH))
      (by
        rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
        intro w hw
        exact Subgroup.mem_centralizer_singleton_iff.mp (heP₂ hw))
      (by
        rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
        intro w hw
        exact Subgroup.mem_centralizer_singleton_iff.mp (heC₂ hw))
    have heCP : e ∈ Subgroup.centralizer (P : Set G) := h11 (Subgroup.mem_zpowers e)
    have heF : e ∈ generalizedFittingSubgroupOf H :=
      Bender35.inf_centralizer_le_generalizedFitting H ⟨heH, Subgroup.centralizer_le hFP heCP⟩
    have heo : Odd (orderOf e) := Bender35.odd_orderOf_of_mem hp hp2 (hFP heF)
    obtain ⟨k, hk⟩ := exists_pow_sq_eq heo
    rw [← hk, pow_two, hB2 e he, one_pow]
  have hE4 := card_le_four_of_faithful hp hp2 hP₂p hexp hZ₂card hP₂3 hcomm hBN hBel.1 hB2 hfaith
  omega

end Fstar

end Reduced

end CFSG.Goldschmidt.G55

namespace CFSG.Goldschmidt

open CFSG.GorensteinWalter CFSG.Walter G55

theorem G55_of (h31 : S_G31) (h37 : S_G37) (h52 : S_G52) (h53 : S_G53) (h54 : S_G54) :
    S_G55 := by
  intro G _ _ S A hS a haA ha1 H hH ha2 Y hY1 hYF0 hYsn0 haY
  by_contra hYA
  obtain ⟨hYF, hYsn⟩ := isSubnormal_of_fstarZero hYF0 hYsn0
  have hY : IsBad a H Y := ⟨hY1, hYF, hYsn, haY, hYA⟩
  have haH := mem_of_mem_benderM hH
  have haa : a * a = 1 := mul_self_eq_one_of_mem hS.elem haA
  have hE := componentLayerOf_le_centralizer h52 h53 hS haA ha1 hH hY
  obtain ⟨p, hp, hp2, hPa⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ⁅qCoreOf H p, Subgroup.zpowers a⁆ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    refine ha2 (mem_qCoreOf_two_of_le_centralizer h31 hS haA ha1 hH hE fun q hq hq2 => ?_)
    have h := hcon q hq hq2
    rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff] at h
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h y hy)
  have hP₀a := commutator_inf_fstarZero_ne_bot hp hp2 haa haH hPa
  obtain ⟨x, ⟨⟨hxP, hxF0⟩, hxN⟩, hxo, hax⟩ :=
    exists_inverted_mem_normalizer hp hp2 haa haH hYF0 hYsn haY hP₀a
  have hYx := isBad_zpowers h53 hS haA ha1 hH hY hp hp2 hxP hxN hxo hax
  exact false_of_isBad_zpowers h52 h53 hS haA ha1 hH hp hp2 hxP hxo hax hYx hxF0 h37 h54

end CFSG.Goldschmidt
