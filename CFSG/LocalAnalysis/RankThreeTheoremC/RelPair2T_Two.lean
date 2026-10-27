module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Burnside
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantQuotientFixedPoints
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem thc_le_pCore {p : ℕ} [Fact p.Prime] {S : Subgroup X} (hS : S.IsSubnormal)
    (hp : IsPGroup p S) : S ≤ CFSG.pCore p X := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val = p} hS
  rw [← CFSG.pCore_eq_piCore ↥S p, ← CFSG.pCore_eq_piCore X p] at h
  have htop : CFSG.pCore p ↥S = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩)
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.le.trans inf_le_right

theorem thc_le_pPrimeCore {p : ℕ} [Fact p.Prime] {S : Subgroup X} (hS : S.IsSubnormal)
    (hcop : p.Coprime (Nat.card S)) : S ≤ CFSG.pPrimeCore p X := by
  have htop : CFSG.pPrimeCore p S = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, by rwa [card_top]⟩)
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val ≠ p} hS
  rw [← CFSG.pPrimeCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore, htop, ← MonoidHom.range_eq_map,
    range_subtype] at h
  exact inf_eq_left.mp h.symm

theorem thc_center_eq_bot {p : ℕ} (hp : p.Prime) (h1 : CFSG.pCore p X = ⊥)
    (h2 : CFSG.pPrimeCore p X = ⊥) {L : Subgroup X} (hL : CFSG.IsComponent L) :
    center L = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hcard : Nat.card (center L) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center L) q hqd
  set Z : Subgroup L := zpowers (z : L) with hZ
  have hZn : Z.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have hc : Commute g ((z : L) ^ k) :=
      Commute.zpow_right (mem_center_iff.mp z.2 g) k
    rw [hc.eq, mul_inv_cancel_right]
    exact zpow_mem_zpowers _ _
  set W : Subgroup X := Z.map L.subtype with hW
  have hWs : W.IsSubnormal := by
    refine Subgroup.IsSubnormal.step W L (map_subtype_le _) hL.2 ?_
    rw [hW, show (Z.map L.subtype).subgroupOf L = Z from
      comap_map_eq_self_of_injective L.subtype_injective Z]
    exact hZn
  have hWcard : Nat.card W = q := by
    rw [hW, card_map_of_injective L.subtype_injective, hZ, Nat.card_zpowers,
      Subgroup.orderOf_coe, hz]
  have hW1 : W = ⊥ := by
    by_cases hqp : q = p
    · subst hqp
      exact le_bot_iff.mp (h1 ▸ thc_le_pCore hWs (IsPGroup.of_card (n := 1) (by rw [hWcard]; simp)))
    · refine le_bot_iff.mp (h2 ▸ thc_le_pPrimeCore hWs ?_)
      rw [hWcard]
      exact (Nat.coprime_primes hp hq).mpr (Ne.symm hqp)
  rw [hW1, card_bot] at hWcard
  exact hq.one_lt.ne hWcard

theorem thc_dvd_card {p : ℕ} (hp : p.Prime) (h2 : CFSG.pPrimeCore p X = ⊥) {L : Subgroup X}
    (hL : CFSG.IsComponent L) : p ∣ Nat.card L := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra h
  have hle := thc_le_pPrimeCore hL.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
  rw [h2, le_bot_iff] at hle
  subst hle
  have := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl

omit [Finite X] in
theorem thc_eq_one {L : Subgroup X} (hZ : center L = ⊥) {y : X} (hyL : y ∈ L)
    (hyC : y ∈ centralizer (L : Set X)) : y = 1 := by
  have hz : (⟨y, hyL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp hyC g g.2)
  rw [hZ, mem_bot] at hz
  exact congrArg Subtype.val hz

theorem thc_le_centralizer {L₁ L₂ : Subgroup X} (h₁ : CFSG.IsComponent L₁)
    (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂) : L₁ ≤ centralizer (L₂ : Set X) :=
  commutator_eq_bot_iff_le_centralizer.mp
    ((CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left hne)

theorem thc_closure {p : ℕ} (hp : p.Prime) {E : Subgroup X} (hE : IsElemAbelian p E) {y : X}
    (hy : y ^ p = 1) (hyE : y ∈ centralizer (E : Set X)) (hyn : y ∉ E) :
    IsElemAbelian p (closure ((E : Set X) ∪ {y})) ∧
      p * Nat.card E ≤ Nat.card (closure ((E : Set X) ∪ {y})) := by
  have : Fact p.Prime := ⟨hp⟩
  set F : Subgroup X := closure ((E : Set X) ∪ {y})
  have hpair : ((E : Set X) ∪ {y}).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rw [Set.mem_singleton_iff.mp hb]
      exact mem_centralizer_iff.mp hyE a ha
    · rw [Set.mem_singleton_iff.mp ha]
      exact (mem_centralizer_iff.mp hyE b hb).symm
    · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  have hFc : IsMulCommutative F := isMulCommutative_closure hpair
  have hFp : ∀ x ∈ F, x ^ p = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hE.2 x hx
      · rw [Set.mem_singleton_iff.mp hx]
        exact hy
    | one => exact one_pow p
    | mul a b ha hb hap hbp =>
      have hc : Commute a b := congrArg Subtype.val (hFc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      rw [hc.mul_pow, hap, hbp, one_mul]
    | inv a _ hap => rw [inv_pow, hap, inv_one]
  refine ⟨⟨hFc, hFp⟩, ?_⟩
  have hEF : E ≤ F := fun x hx => subset_closure (Or.inl hx)
  have hyF : y ∈ F := subset_closure (Or.inr rfl)
  have hFpg : IsPGroup p F := fun x => ⟨1, Subtype.ext (by simpa using hFp x x.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hFpg
  obtain ⟨k, hk⟩ := card_dvd_of_le hEF
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp (show k ∣ p ^ m from ⟨Nat.card E, by
    rw [← hm, hk, mul_comm]⟩)
  rcases j with _ | j
  · exact absurd ((eq_of_le_of_card_ge hEF (by rw [hk, pow_zero, mul_one])) ▸ hyF) hyn
  · rw [hk, mul_comm]
    exact Nat.mul_le_mul_left _ (le_self_pow₀ hp.one_lt.le (Nat.succ_ne_zero j))

theorem thc_card_closure {p : ℕ} (hp : p.Prime) {L E : Subgroup X} (hZ : center L = ⊥)
    (hE : IsElemAbelian p E) (hEL : E ≤ centralizer (L : Set X)) {y : X} (hyL : y ∈ L)
    (hy : orderOf y = p) :
    IsElemAbelian p (closure ((E : Set X) ∪ {y})) ∧
      p * Nat.card E ≤ Nat.card (closure ((E : Set X) ∪ {y})) := by
  refine thc_closure hp hE (hy ▸ pow_orderOf_eq_one y) (le_centralizer_iff.mp hEL hyL)
    fun hyE => ?_
  have h1 := thc_eq_one hZ hyL (hEL hyE)
  rw [h1, orderOf_one] at hy
  exact hp.one_lt.ne hy

omit [Finite X] in
theorem thc_isElemAbelian_bot (p : ℕ) : IsElemAbelian p (⊥ : Subgroup X) :=
  ⟨inferInstance, fun x hx => by rw [mem_bot.mp hx, one_pow]⟩

theorem thc_false_of_le {p : ℕ} (hp : p.Prime) {a : ℕ} (h1 : p * p ^ 2 ≤ a) (h2 : a ≤ p ^ 2) :
    False :=
  absurd (Nat.le_of_mul_le_mul_right (by rw [one_mul]; exact h1.trans h2) (pow_pos hp.pos 2))
    (not_le.mpr hp.one_lt)

omit [Finite X] in
theorem thc_mem_normalizer_inf {H K : Subgroup X} {g : X} (hH : g ∈ normalizer (H : Set X))
    (hK : g ∈ normalizer (K : Set X)) : g ∈ normalizer ((H ⊓ K : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [map_inf_eq _ _ _ (MulAut.conj g).injective, hH, hK]

omit [Finite X] in
theorem thc_mem_normalizer_sup {H K : Subgroup X} {g : X} (hH : g ∈ normalizer (H : Set X))
    (hK : g ∈ normalizer (K : Set X)) : g ∈ normalizer ((H ⊔ K : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

omit [Finite X] in
theorem thc_card_sup_dvd {U E : Subgroup X} (hE : E ≤ normalizer (U : Set X)) :
    Nat.card (U ⊔ E : Subgroup X) ∣ Nat.card U * Nat.card E := by
  have : (U.subgroupOf E).Normal := normal_subgroupOf_of_le_normalizer hE
  have : (U.subgroupOf (E ⊔ U)).Normal := normal_subgroupOf_sup_of_le_normalizer hE
  have hq : Nat.card ((E ⊔ U : Subgroup X) ⧸ U.subgroupOf (E ⊔ U)) ∣ Nat.card E := by
    rw [← Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient E U hE).toEquiv]
    exact card_quotient_dvd_card _
  have hU : Nat.card (U.subgroupOf (E ⊔ U)) = Nat.card U :=
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : U ≤ E ⊔ U)).toEquiv
  rw [sup_comm, card_eq_card_quotient_mul_card_subgroup (U.subgroupOf (E ⊔ U)), hU, mul_comm]
  exact mul_dvd_mul_left _ hq

omit [Finite X] in
theorem thc_coprime_card_sup {p : ℕ} {U E : Subgroup X} (hE : E ≤ normalizer (U : Set X))
    (hU : p.Coprime (Nat.card U)) (hE' : p.Coprime (Nat.card E)) :
    p.Coprime (Nat.card (U ⊔ E : Subgroup X)) :=
  Nat.Coprime.coprime_dvd_right (thc_card_sup_dvd hE) (Nat.Coprime.mul_right hU hE')

omit [Finite X] in
theorem thc_map_conj_mul (L : Subgroup X) (g h : X) :
    L.map (MulAut.conj (g * h)).toMonoidHom =
      (L.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem thc_coprime_of_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup X}
    (hA : IsPGroup 2 A) : p.Coprime (Nat.card A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

theorem thc_exists_mul {p : ℕ} (hp : p.Prime) {R K M : Subgroup X} (hR : IsPGroup p R)
    (hMK : M ≤ K) (hMn : (M.subgroupOf K).Normal) (hRK : R ≤ normalizer (K : Set X))
    (hRM : R ≤ normalizer (M : Set X)) (hM : p.Coprime (Nat.card M))
    (htriv : ∀ k ∈ K, ∀ r ∈ R, k⁻¹ * (r * k * r⁻¹) ∈ M) :
    ∀ k ∈ K, ∃ c ∈ K ⊓ centralizer (R : Set X), ∃ m ∈ M, k = c * m := by
  intro k hk
  let φ := CFSG.RankThreeCoreUniqueness.Helpers.ambientSubgroupActionHom R K hRK
  have hφ : ∀ (r : R) (x : K), ((φ r x : K) : X) = r * x * (r : X)⁻¹ := fun r x =>
    CFSG.RankThreeCoreUniqueness.Helpers.ambientSubgroupActionHom_apply_coe R K hRK r x
  have hinv : ∀ r : R, ∀ x ∈ M.subgroupOf K, φ r x ∈ M.subgroupOf K := by
    intro r x hx
    rw [mem_subgroupOf, hφ]
    exact (mem_normalizer_iff.mp (hRM r.2) x).mp hx
  have hcop : p.Coprime (Nat.card (M.subgroupOf K)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hMK).toEquiv]
  obtain ⟨c, hc, hcfix⟩ := CFSG.RankThreeCoreUniqueness.Helpers.coprime_normal_quotient_fixed_lift
    p hp hR φ (M.subgroupOf K) hinv hcop (QuotientGroup.mk' _ ⟨k, hk⟩) (fun r => by
      rw [CFSG.RankThreeCoreUniqueness.Helpers.invariantQuotientActionHom_mk,
        QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
      have h := M.inv_mem (htriv k hk r r.2)
      simp only [coe_mul, InvMemClass.coe_inv, hφ, mul_inv_rev, inv_inv] at h ⊢
      simpa [mul_assoc] using h)
  refine ⟨c, ⟨c.2, ?_⟩, (c : X)⁻¹ * k, ?_, by group⟩
  · show (c : X) ∈ centralizer (R : Set X)
    rw [mem_centralizer_iff]
    intro r hr
    have h := congrArg Subtype.val (hcfix ⟨r, hr⟩)
    rw [hφ] at h
    calc r * (c : X) = r * c * r⁻¹ * r := by group
      _ = c * r := by rw [h]
  · have h := QuotientGroup.eq.mp hc
    rw [mem_subgroupOf] at h
    simpa using h

theorem thc_not_three {p : ℕ} {D : Subgroup X} (hF : ThompsonFrame p D) {L₁ L₂ L₃ : Subgroup X}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂) (h₃ : CFSG.IsComponent L₃)
    (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) : False := by
  have : Fact p.Prime := ⟨hF.prime⟩
  have hZ : ∀ {L : Subgroup X}, CFSG.IsComponent L → center L = ⊥ := fun hL =>
    thc_center_eq_bot hF.prime hF.pCore_eq_bot hF.pPrimeCore_eq_bot hL
  have hy : ∀ {L : Subgroup X}, CFSG.IsComponent L → ∃ y ∈ L, orderOf y = p := fun {L} hL => by
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := L) p
      (thc_dvd_card hF.prime hF.pPrimeCore_eq_bot hL)
    exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  obtain ⟨y₁, hy₁L, hy₁⟩ := hy h₁
  obtain ⟨y₂, hy₂L, hy₂⟩ := hy h₂
  obtain ⟨y₃, hy₃L, hy₃⟩ := hy h₃
  have hC₁₂ := thc_le_centralizer h₁ h₂ h12
  have hC₁₃ := thc_le_centralizer h₁ h₃ h13
  have hC₂₃ := thc_le_centralizer h₂ h₃ h23
  obtain ⟨hE₁, hc₁⟩ := thc_card_closure hF.prime (hZ h₁) (thc_isElemAbelian_bot p) bot_le hy₁L hy₁
  set F₁ : Subgroup X := closure (((⊥ : Subgroup X) : Set X) ∪ {y₁})
  have hF₁L : F₁ ≤ L₁ := closure_le _ |>.mpr (Set.union_subset (fun x hx => by
    rw [SetLike.mem_coe, mem_bot.mp hx]; exact one_mem _) (Set.singleton_subset_iff.mpr hy₁L))
  obtain ⟨hE₂, hc₂⟩ := thc_card_closure hF.prime (hZ h₂) hE₁ (hF₁L.trans hC₁₂) hy₂L hy₂
  set F₂ : Subgroup X := closure ((F₁ : Set X) ∪ {y₂})
  have hF₂C : F₂ ≤ centralizer (L₃ : Set X) := closure_le _ |>.mpr (Set.union_subset
    (hF₁L.trans hC₁₃) (Set.singleton_subset_iff.mpr (hC₂₃ hy₂L)))
  obtain ⟨hE₃, hc₃⟩ := thc_card_closure hF.prime (hZ h₃) hE₂ hF₂C hy₃L hy₃
  rw [card_bot, mul_one] at hc₁
  refine thc_false_of_le hF.prime ?_ (hF.rank_le _ hE₃)
  calc p * p ^ 2 = p * (p * p) := by ring
    _ ≤ p * Nat.card F₂ := Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul_left _ hc₁) hc₂)
    _ ≤ _ := hc₃

theorem thc_eq_or_eq {p : ℕ} {D : Subgroup X} (hF : ThompsonFrame p D) {L₁ L₂ L : Subgroup X}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂)
    (hL : CFSG.IsComponent L) : L = L₁ ∨ L = L₂ := by
  by_contra h
  obtain ⟨ha, hb⟩ := not_or.mp h
  exact thc_not_three hF h₁ h₂ hL hne (Ne.symm ha) (Ne.symm hb)

theorem thc_mem_normalizer_of_pow_eq_one {p : ℕ} {D : Subgroup X} (hF : ThompsonFrame p D)
    {L : Subgroup X} (hL : CFSG.IsComponent L) {g : X} (hg : g ^ p = 1) :
    g ∈ normalizer (L : Set X) := by
  by_contra hgn
  have hL1 := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL
  have hL2 := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (g * g)) hL
  have h01 : L ≠ L.map (MulAut.conj g).toMonoidHom := fun h =>
    hgn (mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have h02 : L ≠ L.map (MulAut.conj (g * g)).toMonoidHom := by
    intro h
    apply hgn
    have hg2 : g * g ∈ normalizer (L : Set X) := mem_normalizer_iff_map_conj_eq.mpr h.symm
    obtain ⟨k, hk⟩ := (hF.prime.eq_two_or_odd'.resolve_left hF.odd)
    have : g = (g * g) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, hg, one_mul]
    rw [this]
    exact pow_mem hg2 _
  have h12 : L.map (MulAut.conj g).toMonoidHom ≠ L.map (MulAut.conj (g * g)).toMonoidHom := by
    intro h
    rw [thc_map_conj_mul] at h
    exact h01 (map_injective (MulAut.conj g).injective h)
  exact thc_not_three hF hL hL1 hL2 h01 h02 h12

theorem thc_mem_normalizer_of_commute {p : ℕ} {D : Subgroup X} (hF : ThompsonFrame p D)
    {L₁ L₂ : Subgroup X} (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂)
    {e : X} (he : e ∈ L₁) (he1 : e ≠ 1) {g : X} (hg : g ∈ centralizer ({e} : Set X)) :
    g ∈ normalizer (L₁ : Set X) := by
  rcases thc_eq_or_eq hF h₁ h₂ hne (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) h₁)
    with h | h
  · exact mem_normalizer_iff_map_conj_eq.mpr h
  · exfalso
    have he₂ : e ∈ L₂ := by
      rw [← h]
      refine ⟨e, he, ?_⟩
      have h' : g * e * g⁻¹ = e := by rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
      simpa [MulAut.conj_apply] using h'
    exact he1 (thc_eq_one (thc_center_eq_bot hF.prime hF.pCore_eq_bot hF.pPrimeCore_eq_bot h₁) he
      (thc_le_centralizer h₂ h₁ (Ne.symm hne) he₂))

theorem thc_normal {p : ℕ} {D : Subgroup X} (hF : ThompsonFrame p D) {L₁ L₂ : Subgroup X}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂) :
    (normalizer (L₁ : Set X) ⊓ normalizer (L₂ : Set X)).Normal := by
  constructor
  intro n hn g
  have key : ∀ L : Subgroup X, CFSG.IsComponent L → g * n * g⁻¹ ∈ normalizer (L : Set X) := by
    intro L hL
    have hfix : (L.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj n).toMonoidHom =
        L.map (MulAut.conj g⁻¹).toMonoidHom := by
      rcases thc_eq_or_eq hF h₁ h₂ hne (CFSG.LocalCores.isComponent_map_mulEquiv
        (MulAut.conj g⁻¹) hL) with h | h <;> rw [h]
      · exact mem_normalizer_iff_map_conj_eq.mp hn.1
      · exact mem_normalizer_iff_map_conj_eq.mp hn.2
    rw [mem_normalizer_iff_map_conj_eq]
    change L.map (MulAut.conj (g * n * g⁻¹)).toMonoidHom = L
    rw [thc_map_conj_mul, thc_map_conj_mul, hfix,
      ← thc_map_conj_mul, mul_inv_cancel]
    convert map_id L
    ext x
    simp
  exact ⟨key L₁ h₁, key L₂ h₂⟩

theorem thc_exists_mem {p : ℕ} {D : Subgroup X} (hF : ThompsonFrame p D) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hDL : D ≤ normalizer (L : Set X)) : ∃ e ∈ D ⊓ L, e ≠ 1 := by
  have : Fact p.Prime := ⟨hF.prime⟩
  have hDp : IsPGroup p D := IsPGroup.of_card hF.card
  let φ := CFSG.RankThreeCoreUniqueness.Helpers.ambientSubgroupActionHom D L hDL
  let _ : MulAction D L := MulAction.compHom L φ
  have hsmul : ∀ (d : D) (l : L), ((d • l : L) : X) = d * l * (d : X)⁻¹ := fun d l =>
    CFSG.RankThreeCoreUniqueness.Helpers.ambientSubgroupActionHom_apply_coe D L hDL d l
  have hfix : Nat.card (MulAction.fixedPoints D L) =
      Nat.card (L ⊓ centralizer (D : Set X) : Subgroup X) := by
    refine Nat.card_congr
      { toFun := fun l => ⟨l.1, l.1.2, mem_centralizer_iff.mpr fun d hd => ?_⟩
        invFun := fun x => ⟨⟨x, x.2.1⟩, fun d => Subtype.ext ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have h := congrArg Subtype.val (l.2 ⟨d, hd⟩)
      rw [hsmul] at h
      calc d * (l : X) = d * l * d⁻¹ * d := by group
        _ = l * d := by rw [h]
    · rw [hsmul]
      have h := mem_centralizer_iff.mp x.2.2 d d.2
      simp only at h ⊢
      rw [h, mul_inv_cancel_right]
  have hdvd : p ∣ Nat.card (L ⊓ centralizer (D : Set X) : Subgroup X) := by
    rw [← hfix]
    exact Nat.modEq_zero_iff_dvd.mp ((hDp.card_modEq_card_fixedPoints L).symm.trans
      (Nat.modEq_zero_iff_dvd.mpr (thc_dvd_card hF.prime hF.pPrimeCore_eq_bot hL)))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hyo : orderOf (y : X) = p := by rw [Subgroup.orderOf_coe]; exact hy
  have hyD : (y : X) ∈ D := by
    by_contra hyD
    obtain ⟨hE, hc⟩ := thc_closure hF.prime hF.elem (hyo ▸ pow_orderOf_eq_one (y : X)) y.2.2 hyD
    rw [hF.card] at hc
    exact thc_false_of_le hF.prime hc (hF.rank_le _ hE)
  refine ⟨y, ⟨hyD, y.2.1⟩, fun h => ?_⟩
  rw [h, orderOf_one] at hyo
  exact hF.prime.one_lt.ne hyo

theorem thc_mem_mul {p : ℕ} (hp : p.Prime) {D L₁ L₂ : Subgroup X} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (hZ₁ : center L₁ = ⊥) (hZ₂ : center L₂ = ⊥)
    (hL₁₂ : L₁ ≤ centralizer (L₂ : Set X)) {e₁ e₂ : X} (he₁ : e₁ ∈ D ⊓ L₁) (he₂ : e₂ ∈ D ⊓ L₂)
    (he₁1 : e₁ ≠ 1) (he₂1 : e₂ ≠ 1) : ∀ d ∈ D, ∃ x ∈ D ⊓ L₁, ∃ y ∈ D ⊓ L₂, x * y = d := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hE₁, hc₁⟩ := thc_card_closure hp hZ₁ (thc_isElemAbelian_bot p) bot_le he₁.2
    (orderOf_eq_prime (hD.2 e₁ he₁.1) he₁1)
  set F₁ : Subgroup X := closure (((⊥ : Subgroup X) : Set X) ∪ {e₁})
  have hF₁le : F₁ ≤ D ⊓ L₁ := closure_le _ |>.mpr (Set.union_subset (fun x hx => by
    rw [SetLike.mem_coe, mem_bot.mp hx]; exact one_mem _) (Set.singleton_subset_iff.mpr he₁))
  obtain ⟨-, hc₂⟩ := thc_card_closure hp hZ₂ hE₁ ((hF₁le.trans inf_le_right).trans hL₁₂) he₂.2
    (orderOf_eq_prime (hD.2 e₂ he₂.1) he₂1)
  have hF₂le : closure ((F₁ : Set X) ∪ {e₂}) ≤ (D ⊓ L₁) ⊔ (D ⊓ L₂) := closure_le _ |>.mpr
    (Set.union_subset (hF₁le.trans le_sup_left) (Set.singleton_subset_iff.mpr (le_sup_right
      (a := D ⊓ L₁) he₂)))
  have hsup : (D ⊓ L₁) ⊔ (D ⊓ L₂) = D := by
    refine eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
    rw [card_bot, mul_one] at hc₁
    rw [hDcard, sq]
    exact (Nat.mul_le_mul_left _ hc₁).trans (hc₂.trans (card_le_of_le hF₂le))
  have hnorm : D ⊓ L₁ ≤ normalizer ((D ⊓ L₂ : Subgroup X) : Set X) :=
    ((inf_le_right.trans hL₁₂).trans (centralizer_le (fun x hx => hx.2))).trans
      (centralizer_le_normalizer _)
  intro d hd
  rw [← hsup, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hnorm] at hd
  exact Set.mem_mul.mp hd

theorem thc_le_of_normal {p : ℕ} (hp : p.Prime) {D N₀ A : Subgroup X} (hD : IsPGroup p D)
    (hN₀ : N₀.Normal) (hDN : D ≤ N₀) (hCN : centralizer (D : Set X) ≤ N₀)
    (hA : p.Coprime (Nat.card A)) (hDA : D ≤ normalizer (A : Set X)) : A ≤ N₀ := by
  have hNn : ∀ g : X, g ∈ normalizer (N₀ : Set X) := fun g => le_normalizer_of_normal (mem_top g)
  intro a ha
  obtain ⟨c, hc, m, hm, rfl⟩ := thc_exists_mul hp hD (K := A) (M := A ⊓ N₀) inf_le_left
    ((normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun g hg =>
      thc_mem_normalizer_inf (le_normalizer hg) (hNn g))
    hDA (fun d hd => thc_mem_normalizer_inf (hDA hd) (hNn d))
    (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hA)
    (fun k hk r hr => ⟨A.mul_mem (A.inv_mem hk) ((mem_normalizer_iff.mp (hDA hr) k).mp hk), by
      rw [← mul_assoc, ← mul_assoc]
      exact N₀.mul_mem (by simpa using hN₀.conj_mem r (hDN hr) k⁻¹) (N₀.inv_mem (hDN hr))⟩) a ha
  exact N₀.mul_mem (hCN hc.2) hm.2

theorem thc_le_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D L₁ L₂ O₁ O₂ Q A : Subgroup X}
    {e₁ e₂ : X} (hD : IsPGroup p D) (hDL₁ : D ≤ normalizer (L₁ : Set X))
    (hDL₂ : D ≤ normalizer (L₂ : Set X)) (hD₁₂ : ∀ d ∈ D, ∃ x ∈ D ⊓ L₁, ∃ y ∈ D ⊓ L₂, x * y = d)
    (hL₁₂ : L₁ ≤ centralizer (L₂ : Set X)) (he₁ : e₁ ∈ L₁) (he₂ : e₂ ∈ L₂)
    (hO₁ : IsPSignalizer p D e₁ O₁) (hO₂ : IsPSignalizer p D e₂ O₂)
    (hQ : ∀ g ∈ centralizer (D : Set X), p.Coprime (orderOf g) → g ∈ Q)
    (hA : IsPGroup 2 A) (hDA : D ≤ normalizer (A : Set X))
    (hAL₁ : A ≤ normalizer (L₁ : Set X)) (hAL₂ : A ≤ normalizer (L₂ : Set X)) :
    A ≤ ((O₂ ⊓ L₁) ⊔ (O₁ ⊓ L₂)) ⊔ Q := by
  have hL₂₁ : L₂ ≤ centralizer (L₁ : Set X) := le_centralizer_iff.mp hL₁₂
  have hAcop := thc_coprime_of_two hp hp2 hA
  set M : Subgroup X := (A ⊓ L₁) ⊔ (A ⊓ L₂)
  have hMA : M ≤ A := sup_le inf_le_left inf_le_left
  have hNM : ∀ g : X, g ∈ normalizer (A : Set X) → g ∈ normalizer (L₁ : Set X) →
      g ∈ normalizer (L₂ : Set X) → g ∈ normalizer (M : Set X) := fun g hgA hg₁ hg₂ =>
    thc_mem_normalizer_sup (thc_mem_normalizer_inf hgA hg₁) (thc_mem_normalizer_inf hgA hg₂)
  have hDM : D ≤ normalizer (M : Set X) := fun d hd => hNM d (hDA hd) (hDL₁ hd) (hDL₂ hd)
  have hcomm : ∀ {L : Subgroup X}, A ≤ normalizer (L : Set X) → ∀ a ∈ A, ∀ x ∈ D ⊓ L,
      a⁻¹ * x * a * x⁻¹ ∈ A ⊓ L := by
    intro L hAL a ha x hx
    refine ⟨?_, L.mul_mem ?_ (L.inv_mem hx.2)⟩
    · rw [mul_assoc, mul_assoc, ← mul_assoc x]
      exact A.mul_mem (A.inv_mem ha) ((mem_normalizer_iff.mp (hDA hx.1) a).mp ha)
    · simpa using (mem_normalizer_iff.mp (hAL (A.inv_mem ha)) x).mp hx.2
  have htriv : ∀ a ∈ A, ∀ d ∈ D, a⁻¹ * (d * a * d⁻¹) ∈ M := by
    intro a ha d hd
    obtain ⟨x, hx, y, hy, rfl⟩ := hD₁₂ d hd
    have e : a⁻¹ * (x * y * a * (x * y)⁻¹) =
        (a⁻¹ * x * a * x⁻¹) * (x * (a⁻¹ * y * a * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact M.mul_mem (le_sup_left (b := A ⊓ L₂) (hcomm hAL₁ a ha x hx))
      ((mem_normalizer_iff.mp (hDM hx.1) _).mp (le_sup_right (a := A ⊓ L₁) (hcomm hAL₂ a ha y hy)))
  have hW : ∀ {L L' O : Subgroup X} {e : X}, IsPSignalizer p D e O → e ∈ L' →
      L ≤ centralizer (L' : Set X) → D ≤ normalizer (L : Set X) → A ⊓ L ≤ O :=
    fun hO he hLL' hDL => hO.le _
      ((inf_le_right.trans hLL').trans (centralizer_le (Set.singleton_subset_iff.mpr he)))
      (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hAcop)
      (fun d hd => thc_mem_normalizer_inf (hDA hd) (hDL hd))
  have hMB : M ≤ (O₂ ⊓ L₁) ⊔ (O₁ ⊓ L₂) :=
    sup_le_sup (le_inf (hW hO₂ he₂ hL₁₂ hDL₁) inf_le_right) (le_inf (hW hO₁ he₁ hL₂₁ hDL₂)
      inf_le_right)
  intro a ha
  obtain ⟨c, hc, m, hm, rfl⟩ := thc_exists_mul hp hD hMA
    ((normal_subgroupOf_iff_le_normalizer hMA).mpr fun g hg =>
      hNM g (le_normalizer hg) (hAL₁ hg) (hAL₂ hg))
    hDA hDM (Nat.Coprime.coprime_dvd_right (card_dvd_of_le hMA) hAcop) htriv a ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hA ⟨c, hc.1⟩
  have hco : p.Coprime (orderOf c) := Nat.Coprime.coprime_dvd_right
    (orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk))
    (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
  exact mul_mem (le_sup_right (a := (O₂ ⊓ L₁) ⊔ (O₁ ⊓ L₂)) (hQ c hc.2 hco))
    (le_sup_left (b := Q) (hMB hm))

theorem ThompsonFrame.component_unique {p : ℕ} {X : Type} [Group X] [Finite X] {D : Subgroup X}
    (hF : ThompsonFrame p D) {L₁ L₂ : Subgroup X} (h₁ : CFSG.IsComponent L₁)
    (h₂ : CFSG.IsComponent L₂) : L₁ = L₂ := by
  by_contra hne
  have : Fact p.Prime := ⟨hF.prime⟩
  have hDp : IsPGroup p D := IsPGroup.of_card hF.card
  have hZ₁ := thc_center_eq_bot hF.prime hF.pCore_eq_bot hF.pPrimeCore_eq_bot h₁
  have hZ₂ := thc_center_eq_bot hF.prime hF.pCore_eq_bot hF.pPrimeCore_eq_bot h₂
  have hL₁₂ := thc_le_centralizer h₁ h₂ hne
  have hL₂₁ := thc_le_centralizer h₂ h₁ (Ne.symm hne)
  have hDL₁ : D ≤ normalizer (L₁ : Set X) := fun d hd =>
    thc_mem_normalizer_of_pow_eq_one hF h₁ (hF.elem.2 d hd)
  have hDL₂ : D ≤ normalizer (L₂ : Set X) := fun d hd =>
    thc_mem_normalizer_of_pow_eq_one hF h₂ (hF.elem.2 d hd)
  obtain ⟨e₁, he₁, he₁1⟩ := thc_exists_mem hF h₁ hDL₁
  obtain ⟨e₂, he₂, he₂1⟩ := thc_exists_mem hF h₂ hDL₂
  have hC : ∀ {e : X}, e ∈ D → centralizer (D : Set X) ≤ centralizer ({e} : Set X) :=
    fun he => centralizer_le (Set.singleton_subset_iff.mpr he)
  have hCN : centralizer (D : Set X) ≤ normalizer (L₁ : Set X) ⊓ normalizer (L₂ : Set X) :=
    fun g hg => ⟨thc_mem_normalizer_of_commute hF h₁ h₂ hne he₁.2 he₁1 (hC he₁.1 hg),
      thc_mem_normalizer_of_commute hF h₂ h₁ (Ne.symm hne) he₂.2 he₂1 (hC he₂.1 hg)⟩
  obtain ⟨Q, hQC, hQcop, -, hQmem⟩ :=
    exists_normal_pComplement_centralizer hF.prime hF.elem.1 hF.sylow
  obtain ⟨O₁, hO₁⟩ := hF.signalizer e₁ he₁.1 he₁1
  obtain ⟨O₂, hO₂⟩ := hF.signalizer e₂ he₂.1 he₂1
  have hD₁₂ := thc_mem_mul hF.prime hF.elem hF.card hZ₁ hZ₂ hL₁₂ he₁ he₂ he₁1 he₂1
  have hle : invariantTwoJoinIn D ⊤ ≤ ((O₂ ⊓ L₁) ⊔ (O₁ ⊓ L₂)) ⊔ Q :=
    invariantTwoJoinIn_le_of_forall fun A _ hA hDA => by
      have hAN := thc_le_of_normal hF.prime hDp (thc_normal hF h₁ h₂ hne) (le_inf hDL₁ hDL₂) hCN
        (thc_coprime_of_two hF.prime hF.odd hA) hDA
      exact thc_le_sup hF.prime hF.odd hDp hDL₁ hDL₂ hD₁₂ hL₁₂ he₁.2 he₂.2 hO₁ hO₂ hQmem hA hDA
        (hAN.trans inf_le_left) (hAN.trans inf_le_right)
  have hB : p.Coprime (Nat.card ((O₂ ⊓ L₁) ⊔ (O₁ ⊓ L₂) : Subgroup X)) :=
    thc_coprime_card_sup
      ((inf_le_right.trans hL₂₁).trans ((centralizer_le (fun x hx => hx.2)).trans
        (centralizer_le_normalizer _)))
      (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hO₂.coprime)
      (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hO₁.coprime)
  have hQB : Q ≤ normalizer (((O₂ ⊓ L₁) ⊔ (O₁ ⊓ L₂) : Subgroup X) : Set X) := fun g hg =>
    thc_mem_normalizer_sup
      (thc_mem_normalizer_inf (hO₂.normal (hC he₂.1 (hQC hg))) (hCN (hQC hg)).1)
      (thc_mem_normalizer_inf (hO₁.normal (hC he₁.1 (hQC hg))) (hCN (hQC hg)).2)
  exact (Nat.Prime.coprime_iff_not_dvd hF.prime).mp (thc_coprime_card_sup hQB hB hQcop)
    (hF.join.trans (card_dvd_of_le hle))

end CFSG.LocalAnalysis.RankThreeTheoremC
