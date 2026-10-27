module

import CFSG.GroupTheory.CommutingConjugatePair
import CFSG.Quasithin.Background.A4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

open scoped BigOperators Pointwise

open Subgroup CFSG.ABGLocalTools

namespace CFSG

variable {G : Type*} [Group G] [Finite G]

theorem orderOf_finset_prod_of_prime {M : Type*} [CommMonoid M] (s : Finset ℕ)
    (f : ℕ → M) (hprime : ∀ p ∈ s, p.Prime) (horder : ∀ p ∈ s, orderOf (f p) = p) :
    orderOf (∏ p ∈ s, f p) = ∏ p ∈ s, p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hprime_t : ∀ p ∈ t, p.Prime := fun p hp =>
        hprime p (Finset.mem_insert_of_mem hp)
      have horder_t : ∀ p ∈ t, orderOf (f p) = p := fun p hp =>
        horder p (Finset.mem_insert_of_mem hp)
      have hih : orderOf (∏ p ∈ t, f p) = ∏ p ∈ t, p := ih hprime_t horder_t
      have hcop : Nat.Coprime (orderOf (f a)) (orderOf (∏ p ∈ t, f p)) := by
        rw [horder a (Finset.mem_insert_self a t), hih, Nat.coprime_prod_right_iff]
        intro p hp
        refine (Nat.coprime_primes (hprime a (Finset.mem_insert_self a t))
          (hprime_t p hp)).mpr ?_
        rintro rfl
        exact ha hp
      rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (Commute.all _ _) hcop,
        horder a (Finset.mem_insert_self a t), hih]

private theorem exists_prime_order_elem_not_mem_centralizer {A Z : Subgroup G} {p : ℕ}
    (hnc : ∀ p : ℕ, p.Prime → p ∣ Nat.card A →
      ∃ P : Subgroup G, P ≤ A ∧ ¬ IsCyclic P ∧ ∀ x ∈ P, x ^ p = 1)
    (hcyc : IsCyclic ↥(A ⊓ Subgroup.centralizer (Z : Set G)))
    (hp : p.Prime) (hpdvd : p ∣ Nat.card A) :
    ∃ a ∈ A, orderOf a = p ∧ a ∉ Subgroup.centralizer (Z : Set G) := by
  classical
  obtain ⟨P, hPA, hPnc, hPexp⟩ := hnc p hp hpdvd
  haveI : IsCyclic ↥(A ⊓ Subgroup.centralizer (Z : Set G)) := hcyc
  have hPnot : ¬ P ≤ A ⊓ Subgroup.centralizer (Z : Set G) := by
    intro hPC
    exact hPnc (Subgroup.isCyclic_of_le hPC)
  obtain ⟨a, haP, ha_notC⟩ := Set.not_subset.mp hPnot
  have haA : a ∈ A := hPA haP
  have ha_notZ : a ∉ Subgroup.centralizer (Z : Set G) := by
    intro haZ
    exact ha_notC (Subgroup.mem_inf.mpr ⟨haA, haZ⟩)
  have ha_ne : a ≠ 1 := by
    intro h
    exact ha_notZ (by rw [h]; exact Subgroup.one_mem _)
  have ha_ord : orderOf a = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hPexp a haP)) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ha_ne
    · exact h1
  exact ⟨a, haA, ha_ord, ha_notZ⟩

private theorem pow_mem_normalizer_not_mem_centralizer_of_split {A T Z : Subgroup G} {k : ℕ}
    (hab : IsMulCommutative A) (hsq : Squarefree k) {p : ℕ} (hp : p.Prime) (hp_dvd_k : p ∣ k)
    {a y c : G} (ha_ord : orderOf a = p) (ha_notZ : a ∉ Subgroup.centralizer (Z : Set G))
    (hyA : y ∈ A) (hyN : y ∈ Subgroup.normalizer (T : Set G)) (hcA : c ∈ A)
    (hcZ : c ∈ Subgroup.centralizer (Z : Set G)) (hayc : a = y * c) :
    y ^ (k / p) ∈ A ⊓ Subgroup.normalizer (T : Set G) ∧
      y ^ (k / p) ∉ Subgroup.centralizer (Z : Set G) := by
  have hcomm : Commute y c := by
    have h := (IsMulCommutative.is_comm (M := A)).comm ⟨y, hyA⟩ ⟨c, hcA⟩
    exact congrArg Subtype.val h
  have hy_notZ : y ∉ Subgroup.centralizer (Z : Set G) := by
    intro hyZ
    exact ha_notZ (by rw [hayc]; exact Subgroup.mul_mem _ hyZ hcZ)
  have hp_not_dvd_div : ¬ p ∣ k / p := by
    intro hdiv
    have hpp : p * p ∣ k := by
      rw [← Nat.mul_div_cancel' hp_dvd_k]
      exact Nat.mul_dvd_mul_left p hdiv
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hp hpp
  have hcop_ap : Nat.Coprime (k / p) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hp_not_dvd_div).symm
  have hapow_notZ : a ^ (k / p) ∉ Subgroup.centralizer (Z : Set G) := by
    intro hmem
    exact ha_notZ (Subgroup.zpowers_le.mpr hmem ((mem_zpowers_pow_iff).mpr
      (by rw [ha_ord]; exact hcop_ap.gcd_eq_one)))
  have hrel : a ^ (k / p) = (y ^ (k / p)) * (c ^ (k / p)) := by
    rw [hayc, hcomm.mul_pow]
  have hypow_notZ : y ^ (k / p) ∉ Subgroup.centralizer (Z : Set G) := by
    intro hmem
    exact hapow_notZ (by
      rw [hrel]
      exact Subgroup.mul_mem _ hmem (Subgroup.pow_mem _ hcZ _))
  exact ⟨Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ hyA _, Subgroup.pow_mem _ hyN _⟩,
    hypow_notZ⟩

private theorem orderOf_pow_eq_prime_of_split {A Z : Subgroup G} {k p : ℕ}
    (hk : ∀ a ∈ A, a ^ k = 1) (hp : p.Prime) (hp_dvd_k : p ∣ k) {y : G} (hyA : y ∈ A)
    (hypow_notZ : y ^ (k / p) ∉ Subgroup.centralizer (Z : Set G)) :
    orderOf (y ^ (k / p)) = p := by
  have hypow_pow : (y ^ (k / p)) ^ p = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hp_dvd_k, hk y hyA]
  have hypow_ne : y ^ (k / p) ≠ 1 := by
    intro h1
    exact hypow_notZ (by rw [h1]; exact Subgroup.one_mem _)
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hypow_pow) with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hypow_ne
  · exact h1

private theorem exists_prime_order_mem_normalizer_not_mem_centralizer
    {A T Z : Subgroup G} {k : ℕ}
    (hab : IsMulCommutative A) (hk : ∀ a ∈ A, a ^ k = 1) (hsq : Squarefree k)
    (hnc : ∀ p : ℕ, p.Prime → p ∣ Nat.card A →
      ∃ P : Subgroup G, P ≤ A ∧ ¬ IsCyclic P ∧ ∀ x ∈ P, x ^ p = 1)
    (hcyc : IsCyclic ↥(A ⊓ Subgroup.centralizer (Z : Set G)))
    (hsplit : ∀ a ∈ A, ∃ y ∈ A ⊓ Subgroup.normalizer (T : Set G),
      ∃ c ∈ A ⊓ Subgroup.centralizer (Z : Set G), a = y * c)
    {p : ℕ} (hp : p.Prime) (hpdvd : p ∣ Nat.card A) :
    ∃ y ∈ A ⊓ Subgroup.normalizer (T : Set G), orderOf y = p ∧
      y ∉ Subgroup.centralizer (Z : Set G) := by
  classical
  obtain ⟨a, haA, ha_ord, ha_notZ⟩ :=
    exists_prime_order_elem_not_mem_centralizer hnc hcyc hp hpdvd
  obtain ⟨y, hy, c, hc, hayc⟩ := hsplit a haA
  have hp_dvd_k : p ∣ k := by
    have h : orderOf a ∣ k := orderOf_dvd_of_pow_eq_one (hk a haA)
    rwa [ha_ord] at h
  obtain ⟨hy', hy'_notZ⟩ :=
    pow_mem_normalizer_not_mem_centralizer_of_split hab hsq hp hp_dvd_k ha_ord ha_notZ
      hy.1 hy.2 hc.1 hc.2 hayc
  exact ⟨y ^ (k / p), hy',
    orderOf_pow_eq_prime_of_split hk hp hp_dvd_k hy.1 hy'_notZ, hy'_notZ⟩

private theorem card_sup_eq_mul_card_of_mul_comm {A T : Subgroup G}
    (hperm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hdisj : Disjoint A T) : Nat.card ↥(A ⊔ T) = Nat.card A * Nat.card T := by
  have hcoe : ((A ⊔ T : Subgroup G) : Set G) = (A : Set G) * (T : Set G) :=
    CFSG.Quasithin.A4.coe_sup_eq_mul_of_mul_comm hperm.symm
  let f : ↥A × ↥T → ↥(A ⊔ T) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro p q hpq
      have h1 : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := congrArg Subtype.val hpq
      exact Subgroup.mul_injective_of_disjoint (H₁ := A) (H₂ := T) hdisj h1
    · intro x
      have hx : (x : G) ∈ (A : Set G) * (T : Set G) := hcoe ▸ x.2
      obtain ⟨a, ha, t, ht, hat⟩ := hx
      exact ⟨(⟨a, ha⟩, ⟨t, ht⟩), Subtype.ext hat⟩
  calc Nat.card ↥(A ⊔ T) = Nat.card (↥A × ↥T) :=
        (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = Nat.card A * Nat.card T := Nat.card_prod _ _

private theorem isSylowOf_sup_of_odd_mul_isPGroup {A T : Subgroup G}
    (hA : Odd (Nat.card A)) (hT : IsPGroup 2 T)
    (hperm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)) :
    IsSylowOf 2 T (A ⊔ T) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Disjoint A T := by
    rw [disjoint_iff]
    have h := CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd (H := T) (K := A) hT hA
    simpa [inf_comm] using h
  have hcard := card_sup_eq_mul_card_of_mul_comm hperm hdisj
  have hTX : T ≤ A ⊔ T := le_sup_right
  have hrel : T.relIndex (A ⊔ T) = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := T) (K := A ⊔ T)
    rw [inf_eq_left.mpr hTX, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  refine (isSylowOf_iff (p := 2)).mpr ⟨hTX, hT, ?_⟩
  rw [hrel]
  exact hA.not_two_dvd_nat

private theorem mem_normalizer_of_mem_normalizer_subgroupOf {X T : Subgroup G}
    {P : Subgroup ↥X} (hTX : T ≤ X) (hP : (P : Subgroup ↥X) = T.subgroupOf X) {n : ↥X}
    (hn : n ∈ Subgroup.normalizer (P : Set ↥X)) :
    (n : G) ∈ Subgroup.normalizer (T : Set G) := by
  have key : ∀ (m : ↥X), m ∈ Subgroup.normalizer (P : Set ↥X) → ∀ t : G, t ∈ X →
      t ∈ T → (m : G) * t * (m : G)⁻¹ ∈ T := by
    intro m hm t htX htT
    have hsub : (⟨t, htX⟩ : ↥X) ∈ T.subgroupOf X := Subgroup.mem_subgroupOf.mpr htT
    have hmem : (⟨t, htX⟩ : ↥X) ∈ P := hP.symm ▸ hsub
    have h := (Subgroup.mem_normalizer_iff.mp hm (⟨t, htX⟩ : ↥X)).1 hmem
    exact Subgroup.mem_subgroupOf.mp (hP ▸ h)
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact key n hn t (hTX ht) ht
  · intro ht
    have h := key n⁻¹ ((Subgroup.normalizer (P : Set ↥X)).inv_mem hn) (n * t * n⁻¹)
      (hTX ht) ht
    simpa [mul_assoc] using h

private theorem exists_mul_mem_normalizer_of_isSylowOf {X C T : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (C : Set G))
    (hTC : T ≤ C) (hsyl : IsSylowOf 2 T X) :
    ∀ x ∈ X, ∃ n ∈ X ⊓ Subgroup.normalizer (T : Set G), ∃ c ∈ C, x = n * c := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hCnorm : (C.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  obtain ⟨P, hP⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hPle : P ≤ C.subgroupOf X := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    exact hTC (Subgroup.mem_subgroupOf.mp (hP ▸ hy))
  have hfr := Sylow.normalizer_sup_eq_top' (N := C.subgroupOf X) P hPle
  intro x hx
  have hxmem : (⟨x, hx⟩ : ↥X) ∈
      Subgroup.normalizer (P : Set ↥X) ⊔ C.subgroupOf X := by
    rw [hfr]
    exact Subgroup.mem_top _
  have hle : Subgroup.normalizer (P : Set ↥X) ≤
      Subgroup.normalizer (C.subgroupOf X : Set ↥X) := Subgroup.le_normalizer_of_normal
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right
    (H := Subgroup.normalizer (P : Set ↥X)) (N := C.subgroupOf X) hle
  have hxmem' : (⟨x, hx⟩ : ↥X) ∈
      ((Subgroup.normalizer (P : Set ↥X) ⊔ C.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
    hxmem
  rw [hcoe] at hxmem'
  obtain ⟨n, hn, c, hc, hnc⟩ := Set.mem_mul.mp hxmem'
  have hnN : (n : G) ∈ Subgroup.normalizer (T : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf hsyl.le hP hn
  have hcC : (c : G) ∈ C := hc
  exact ⟨(n : G), Subgroup.mem_inf.mpr ⟨n.2, hnN⟩, (c : G), hcC,
    (congrArg Subtype.val hnc).symm⟩

private theorem exists_mul_mem_normalizer_mem_centralizer_of_split {A T Z : Subgroup G}
    (hperm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hTZ : T ≤ centralizer (Z : Set G)) {a n c : G} (ha : a ∈ A)
    (hnX : n ∈ A ⊔ T) (hnN : n ∈ normalizer (T : Set G))
    (hcZ : c ∈ centralizer (Z : Set G)) (hnc : a = n * c) :
    ∃ y ∈ A ⊓ normalizer (T : Set G), ∃ d ∈ A ⊓ centralizer (Z : Set G), a = y * d := by
  have hcoe : ((A ⊔ T : Subgroup G) : Set G) = (A : Set G) * (T : Set G) :=
    CFSG.Quasithin.A4.coe_sup_eq_mul_of_mul_comm hperm.symm
  have hnX' : n ∈ ((A ⊔ T : Subgroup G) : Set G) := hnX
  obtain ⟨a₁, ha₁, t₁, ht₁, hnat⟩ := Set.mem_mul.mp (hcoe ▸ hnX')
  have hyN : a₁ ∈ normalizer (T : Set G) := by
    have h : a₁ = n * t₁⁻¹ := by rw [← hnat]; group
    rw [h]
    exact Subgroup.mul_mem _ hnN ((Subgroup.normalizer (T : Set G)).inv_mem
      (Subgroup.le_normalizer ht₁))
  have hcA : t₁ * c ∈ A := by
    have h : a = a₁ * (t₁ * c) := by rw [hnc, ← hnat]; group
    have h2 : t₁ * c = a₁⁻¹ * a := by rw [h]; group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha₁) ha
  have hcZ' : t₁ * c ∈ centralizer (Z : Set G) :=
    Subgroup.mul_mem _ (hTZ ht₁) hcZ
  exact ⟨a₁, Subgroup.mem_inf.mpr ⟨ha₁, hyN⟩, t₁ * c,
    Subgroup.mem_inf.mpr ⟨hcA, hcZ'⟩, by rw [hnc, ← hnat]; group⟩

theorem exists_mul_mem_normalizer_mem_centralizer {A T Z : Subgroup G} (hA : Odd (Nat.card A))
    (hT : IsPGroup 2 T) (hperm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hAZ : A ≤ normalizer (Z : Set G)) (hTZ : T ≤ centralizer (Z : Set G)) {a : G} (ha : a ∈ A) :
    ∃ y ∈ A ⊓ normalizer (T : Set G), ∃ c ∈ A ⊓ centralizer (Z : Set G), a = y * c := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXZ : A ⊔ T ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le hAZ (hTZ.trans (Subgroup.centralizer_le_normalizer (Z : Set G)))
  have hXN : A ⊔ T ≤
      Subgroup.normalizer (Subgroup.centralizer (Z : Set G) : Set G) :=
    hXZ.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer Z)
  have hXC : A ⊔ T ≤ Subgroup.normalizer
      ((A ⊔ T) ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hx, hXN hx⟩)
  have hTC : T ≤ (A ⊔ T) ⊓ Subgroup.centralizer (Z : Set G) :=
    le_inf le_sup_right hTZ
  have hsyl : IsSylowOf 2 T (A ⊔ T) := isSylowOf_sup_of_odd_mul_isPGroup hA hT hperm
  obtain ⟨n, hn, c, hc, hnc⟩ :=
    exists_mul_mem_normalizer_of_isSylowOf (C := (A ⊔ T) ⊓ Subgroup.centralizer (Z : Set G))
      hXC hTC hsyl a (Subgroup.mem_sup_left ha)
  exact exists_mul_mem_normalizer_mem_centralizer_of_split hperm hTZ ha hn.1 hn.2 hc.2 hnc

private theorem exists_prime_order_mem_zpowers_inf {b x : G} {Z : Subgroup G} {s : Finset ℕ}
    (hprime : ∀ p ∈ s, p.Prime) (hcard : orderOf b = ∏ p ∈ s, p)
    (hxB : x ∈ Subgroup.zpowers b) (hxC : x ∈ Subgroup.centralizer (Z : Set G)) (hx1 : x ≠ 1) :
    ∃ p ∈ s, ∃ z ∈ Subgroup.zpowers b,
      z ∈ Subgroup.centralizer (Z : Set G) ∧ orderOf z = p := by
  classical
  have hxord_ne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hxord_ne
  have hxdvd : orderOf x ∣ orderOf b := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxB
    rw [← hj]
    exact orderOf_dvd_of_pow_eq_one (zpow_pow_orderOf (x := b) (i := j))
  have hp_dvd_b : p ∣ orderOf b := hp_dvd.trans hxdvd
  have hp_mem : p ∈ s := by
    rw [← Nat.primeFactors_prod hprime, ← hcard]
    exact Nat.Prime.mem_primeFactors hp hp_dvd_b (orderOf_pos b).ne'
  let z : G := x ^ (orderOf x / p)
  refine ⟨p, hp_mem, z, Subgroup.pow_mem _ hxB _, Subgroup.pow_mem _ hxC _, ?_⟩
  dsimp [z]
  exact orderOf_pow_orderOf_div (orderOf_pos x).ne' hp_dvd

private theorem mem_centralizer_of_mem_zpowers_of_order_prime {b z : G} {Z : Subgroup G}
    {p e : ℕ} (hzB : z ∈ Subgroup.zpowers b) (hzC : z ∈ Subgroup.centralizer (Z : Set G))
    (hzord : orderOf z = p) (hbeord : orderOf (b ^ e) = p) :
    b ^ e ∈ Subgroup.centralizer (Z : Set G) := by
  classical
  have hbepB : b ^ e ∈ Subgroup.zpowers b := Subgroup.pow_mem _ (Subgroup.mem_zpowers b) _
  let zB : ↥(Subgroup.zpowers b) := ⟨z, hzB⟩
  let wB : ↥(Subgroup.zpowers b) := ⟨b ^ e, hbepB⟩
  have hzBord : orderOf zB = p := by rw [Subgroup.orderOf_mk, hzord]
  have hwBord : orderOf wB = p := by rw [Subgroup.orderOf_mk, hbeord]
  have heq : Subgroup.zpowers zB = Subgroup.zpowers wB := by
    letI : IsCyclic ↥(Subgroup.zpowers b) := Subgroup.isCyclic_zpowers b
    exact (IsCyclic.subgroup_eq_iff_card_eq).mpr (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hzBord, hwBord])
  have hwBmem : wB ∈ Subgroup.zpowers zB := by
    rw [heq]
    exact Subgroup.mem_zpowers wB
  obtain ⟨u, hu⟩ := Subgroup.mem_zpowers_iff.mp hwBmem
  have hmem : b ^ e ∈ Subgroup.zpowers z := by
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨u, congrArg Subtype.val hu⟩
  exact Subgroup.zpowers_le.mpr hzC hmem

private theorem inf_zpowers_eq_bot_of_orderOf_eq_prod {b : G} {Z : Subgroup G} {s : Finset ℕ}
    {e : ℕ → ℕ} (hprime : ∀ p ∈ s, p.Prime) (hcard : orderOf b = ∏ p ∈ s, p)
    (hbeord : ∀ p ∈ s, orderOf (b ^ e p) = p)
    (hbe : ∀ p ∈ s, b ^ e p ∉ Subgroup.centralizer (Z : Set G)) :
    Subgroup.zpowers b ⊓ Subgroup.centralizer (Z : Set G) = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨p, hp, z, hzB, hzC, hzord⟩ :=
    exists_prime_order_mem_zpowers_inf hprime hcard hx.1 hx.2 hx1
  exact hbe p hp
    (mem_centralizer_of_mem_zpowers_of_order_prime hzB hzC hzord (hbeord p hp))

private theorem exists_y_of_prime_factors {A T Z : Subgroup G} {k : ℕ}
    (hab : IsMulCommutative A) (hk : ∀ a ∈ A, a ^ k = 1) (hsq : Squarefree k)
    (hnc : ∀ p : ℕ, p.Prime → p ∣ Nat.card A →
      ∃ P : Subgroup G, P ≤ A ∧ ¬ IsCyclic P ∧ ∀ x ∈ P, x ^ p = 1)
    (hcyc : IsCyclic ↥(A ⊓ Subgroup.centralizer (Z : Set G)))
    (hsplit : ∀ a ∈ A, ∃ y ∈ A ⊓ Subgroup.normalizer (T : Set G),
      ∃ c ∈ A ⊓ Subgroup.centralizer (Z : Set G), a = y * c) :
    ∃ y : ℕ → G, ∀ p ∈ (Nat.card A).primeFactors,
      y p ∈ A ⊓ Subgroup.normalizer (T : Set G) ∧ orderOf (y p) = p ∧
        y p ∉ Subgroup.centralizer (Z : Set G) := by
  classical
  let s : Finset ℕ := (Nat.card A).primeFactors
  have hprime : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (by simpa [s] using hp)
  have hdvd : ∀ p ∈ s, p ∣ Nat.card A := fun p hp =>
    Nat.dvd_of_mem_primeFactors (by simpa [s] using hp)
  have hex : ∀ p ∈ s, ∃ y ∈ A ⊓ Subgroup.normalizer (T : Set G), orderOf y = p ∧
      y ∉ Subgroup.centralizer (Z : Set G) := fun p hp =>
    exists_prime_order_mem_normalizer_not_mem_centralizer hab hk hsq hnc hcyc hsplit
      (hprime p hp) (hdvd p hp)
  let y : ℕ → G := fun p => if hp : p ∈ s then Classical.choose (hex p hp) else 1
  have hy : ∀ p ∈ s, y p ∈ A ⊓ Subgroup.normalizer (T : Set G) ∧ orderOf (y p) = p ∧
      y p ∉ Subgroup.centralizer (Z : Set G) := by
    intro p hp
    dsimp [y]
    rw [dif_pos hp]
    exact Classical.choose_spec (hex p hp)
  exact ⟨y, fun p hp => hy p (by simpa [s] using hp)⟩

private def prodSub (A : Subgroup G) (hA : IsMulCommutative A) (s : Finset ℕ)
    (y : ℕ → ↥A) : ↥A :=
  letI : IsMulCommutative ↥A := hA
  letI : CommGroup ↥A := IsMulCommutative.instCommGroup
  ∏ p ∈ s, y p

private theorem exists_b_of_y {A T Z : Subgroup G} {y : ℕ → G} (hA : IsMulCommutative A)
    (hprime : ∀ p ∈ (Nat.card A).primeFactors, p.Prime)
    (hyA : ∀ p ∈ (Nat.card A).primeFactors, y p ∈ A)
    (hyN : ∀ p ∈ (Nat.card A).primeFactors, y p ∈ Subgroup.normalizer (T : Set G))
    (hyord : ∀ p ∈ (Nat.card A).primeFactors, orderOf (y p) = p) :
    ∃ (yA : ℕ → ↥A) (bA : ↥A) (b : G),
      (∀ p ∈ (Nat.card A).primeFactors, (yA p : G) = y p) ∧
      (∀ p ∈ (Nat.card A).primeFactors, orderOf (yA p) = p) ∧
      b = (bA : G) ∧ bA = prodSub A hA (Nat.card A).primeFactors yA ∧
      b ∈ A ∧ b ∈ Subgroup.normalizer (T : Set G) ∧
      orderOf b = ∏ p ∈ (Nat.card A).primeFactors, p := by
  classical
  letI : IsMulCommutative ↥A := hA
  letI : CommGroup ↥A := IsMulCommutative.instCommGroup
  let s : Finset ℕ := (Nat.card A).primeFactors
  let yA : ℕ → ↥A := fun p => if hp : p ∈ s then ⟨y p, hyA p (by simpa [s] using hp)⟩ else 1
  have hyA' : ∀ p ∈ s, (yA p : G) = y p := by
    intro p hp
    simp [yA, dif_pos hp]
  have hordA : ∀ p ∈ s, orderOf (yA p) = p := by
    intro p hp
    rw [← Subgroup.orderOf_coe (yA p), hyA' p hp, hyord p (by simpa [s] using hp)]
  let bA : ↥A := prodSub A hA s yA
  have hbAprod : bA = ∏ p ∈ s, yA p := rfl
  let b : G := bA
  have hbA_mem : b ∈ A := bA.2
  have hbN_mem : b ∈ Subgroup.normalizer (T : Set G) := by
    have hprod : b = (s.toList.map (Subtype.val ∘ yA)).prod := by
      change (bA : G) = _
      rw [show bA = (s.toList.map yA).prod from hbAprod.trans (Finset.prod_map_toList s yA).symm]
      simpa using A.val_list_prod (s.toList.map yA)
    rw [hprod]
    refine Subgroup.list_prod_mem (K := Subgroup.normalizer (T : Set G)) ?_
    intro z hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    have hps : p ∈ s := Finset.mem_toList.mp hp
    rw [show (Subtype.val ∘ yA) p = y p from hyA' p hps]
    exact hyN p (by simpa [s] using hps)
  have hbAord : orderOf bA = ∏ p ∈ s, p := orderOf_finset_prod_of_prime s yA hprime hordA
  exact ⟨yA, bA, b, fun p hp => hyA' p (by simpa [s] using hp),
    fun p hp => hordA p (by simpa [s] using hp), rfl, rfl, hbA_mem, hbN_mem,
    (Subgroup.orderOf_coe bA).trans hbAord⟩

private theorem exists_e_pow_eq_of_prod {A T : Subgroup G} {s : Finset ℕ} {y : ℕ → G}
    {yA : ℕ → ↥A} {bA : ↥A} {b : G} (hA : IsMulCommutative A)
    (hprime : ∀ p ∈ s, p.Prime) (hordA : ∀ p ∈ s, orderOf (yA p) = p)
    (hyA' : ∀ p ∈ s, (yA p : G) = y p) (hb : b = (bA : G))
    (hbAprod : bA = prodSub A hA s yA) :
    ∃ e : ℕ → ℕ, (∀ p ∈ s, Nat.Coprime (e p) p) ∧ (∀ p ∈ s, b ^ e p = (y p) ^ (e p)) := by
  classical
  letI : IsMulCommutative ↥A := hA
  letI : CommGroup ↥A := IsMulCommutative.instCommGroup
  have hbAprod' : bA = ∏ p ∈ s, yA p := hbAprod
  let e : ℕ → ℕ := fun p => ∏ q ∈ s.erase p, q
  have hp_not_dvd_e : ∀ p ∈ s, ¬ p ∣ e p := by
    intro p hp
    dsimp [e]
    have hp' : Prime (p : ℕ) := Nat.prime_iff.mp (hprime p hp)
    refine Prime.not_dvd_finsetProd (p := (p : ℕ)) hp' ?_
    intro q hq hpq
    have hq' : q ∈ s := Finset.mem_of_mem_erase hq
    have hqp : q ≠ p := Finset.ne_of_mem_erase hq
    exact hqp.symm ((Nat.prime_dvd_prime_iff_eq (hprime p hp) (hprime q hq')).mp hpq)
  have hcop_e : ∀ p ∈ s, Nat.Coprime (e p) p := fun p hp =>
    ((Nat.Prime.coprime_iff_not_dvd (hprime p hp)).mpr (hp_not_dvd_e p hp)).symm
  have hbApow : ∀ p ∈ s, bA ^ e p = (yA p) ^ e p := by
    intro p hp
    rw [hbAprod', ← Finset.prod_pow]
    refine Finset.prod_eq_single_of_mem p hp ?_
    intro q hq hqp
    have hqe : q ∈ s.erase p := Finset.mem_erase.mpr ⟨hqp, hq⟩
    have hqdvd : q ∣ e p := by
      dsimp [e]
      exact Finset.dvd_prod_of_mem (fun x => x) hqe
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hordA q hq]; exact hqdvd)
  have hbpow : ∀ p ∈ s, b ^ e p = (y p) ^ (e p) := by
    intro p hp
    have h := congrArg (fun z : ↥A => (z : G)) (hbApow p hp)
    simpa [hb, hyA' p hp, Subgroup.coe_pow] using h
  exact ⟨e, hcop_e, hbpow⟩

private theorem orderOf_pow_and_not_mem_of_pow_eq {Z : Subgroup G} {s : Finset ℕ} {y : ℕ → G}
    {b : G} {e : ℕ → ℕ} (hord : ∀ p ∈ s, orderOf (y p) = p)
    (hnotC : ∀ p ∈ s, y p ∉ Subgroup.centralizer (Z : Set G))
    (hcop_e : ∀ p ∈ s, Nat.Coprime (e p) p)
    (hbpow : ∀ p ∈ s, b ^ e p = (y p) ^ (e p)) :
    (∀ p ∈ s, orderOf (b ^ e p) = p) ∧
      (∀ p ∈ s, b ^ e p ∉ Subgroup.centralizer (Z : Set G)) := by
  constructor
  · intro p hp
    have hcop := hcop_e p hp
    have hyep : orderOf ((y p) ^ e p) = p := by
      rw [orderOf_pow, hord p hp, hcop.symm.gcd_eq_one, Nat.div_one]
    rw [hbpow p hp, hyep]
  · intro p hp
    have hmemz : y p ∈ Subgroup.zpowers ((y p) ^ e p) := by
      rw [mem_zpowers_pow_iff, hord p hp]
      exact (hcop_e p hp).gcd_eq_one
    rw [hbpow p hp]
    intro hmem
    exact hnotC p hp (Subgroup.zpowers_le.mpr hmem hmemz)

private theorem squarefree_card_and_primeFactors {A : Subgroup G} {B : Subgroup G}
    (hprime : ∀ p ∈ (Nat.card A).primeFactors, p.Prime)
    (hBcard : Nat.card B = ∏ p ∈ (Nat.card A).primeFactors, p) :
    Squarefree (Nat.card B) ∧
      (∀ p : ℕ, p.Prime → (p ∣ Nat.card B ↔ p ∣ Nat.card A)) := by
  constructor
  · rw [hBcard]
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
    · intro p hp
      exact (hprime p hp).squarefree
  · intro p hp
    have hpf : (Nat.card B).primeFactors = (Nat.card A).primeFactors := by
      rw [hBcard]
      exact Nat.primeFactors_prod hprime
    have hmemB : p ∈ (Nat.card B).primeFactors ↔ p ∣ Nat.card B := by
      rw [Nat.mem_primeFactors_of_ne_zero Nat.card_pos.ne']
      exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
    have hmemA : p ∈ (Nat.card A).primeFactors ↔ p ∣ Nat.card A := by
      rw [Nat.mem_primeFactors_of_ne_zero Nat.card_pos.ne']
      exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
    rw [← hmemB, hpf]
    exact hmemA

theorem exists_cyclic_le_normalizer_inf_centralizer_eq_bot {A T Z : Subgroup G} {k : ℕ}
    (hab : IsMulCommutative A) (hk : ∀ a ∈ A, a ^ k = 1) (hsq : Squarefree k)
    (hnc : ∀ p : ℕ, p.Prime → p ∣ Nat.card A →
      ∃ P : Subgroup G, P ≤ A ∧ ¬ IsCyclic P ∧ ∀ x ∈ P, x ^ p = 1)
    (hcyc : IsCyclic ↥(A ⊓ centralizer (Z : Set G)))
    (hsplit : ∀ a ∈ A, ∃ y ∈ A ⊓ normalizer (T : Set G),
      ∃ c ∈ A ⊓ centralizer (Z : Set G), a = y * c) :
    ∃ B : Subgroup G, B ≤ A ∧ B ≤ normalizer (T : Set G) ∧ IsCyclic B ∧ Squarefree (Nat.card B) ∧
      (∀ p : ℕ, p.Prime → (p ∣ Nat.card B ↔ p ∣ Nat.card A)) ∧ B ⊓ centralizer (Z : Set G) = ⊥ := by
  classical
  obtain ⟨y, hy⟩ := exists_y_of_prime_factors hab hk hsq hnc hcyc hsplit
  have hprime : ∀ p ∈ (Nat.card A).primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have hyA : ∀ p ∈ (Nat.card A).primeFactors, y p ∈ A := fun p hp => (hy p hp).1.1
  have hyN : ∀ p ∈ (Nat.card A).primeFactors, y p ∈ normalizer (T : Set G) :=
    fun p hp => (hy p hp).1.2
  have hyord : ∀ p ∈ (Nat.card A).primeFactors, orderOf (y p) = p :=
    fun p hp => (hy p hp).2.1
  have hnotC : ∀ p ∈ (Nat.card A).primeFactors, y p ∉ centralizer (Z : Set G) :=
    fun p hp => (hy p hp).2.2
  obtain ⟨yA, bA, b, hyA', hordA, hb, hbAprod, hbA_mem, hbN_mem, hbord⟩ :=
    exists_b_of_y (A := A) (T := T) (Z := Z) hab hprime hyA hyN hyord
  obtain ⟨e, hcop_e, hbpow⟩ :=
    exists_e_pow_eq_of_prod (A := A) (T := T) hab hprime hordA hyA' hb hbAprod
  obtain ⟨hbeord, hbe⟩ := orderOf_pow_and_not_mem_of_pow_eq hyord hnotC hcop_e hbpow
  let B : Subgroup G := Subgroup.zpowers b
  have hBcard : Nat.card B = ∏ p ∈ (Nat.card A).primeFactors, p := by
    rw [show B = Subgroup.zpowers b from rfl, Nat.card_zpowers, hbord]
  obtain ⟨hBsq, hBdvd⟩ := squarefree_card_and_primeFactors (A := A) hprime hBcard
  have hBbot : B ⊓ centralizer (Z : Set G) = ⊥ := by
    have h := inf_zpowers_eq_bot_of_orderOf_eq_prod hprime hbord hbeord hbe
    simpa [B] using h
  exact ⟨B, Subgroup.zpowers_le.mpr hbA_mem, Subgroup.zpowers_le.mpr hbN_mem,
    Subgroup.isCyclic_zpowers b, hBsq, hBdvd, hBbot⟩

end CFSG
