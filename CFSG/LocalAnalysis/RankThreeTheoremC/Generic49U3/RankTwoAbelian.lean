module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open
open Multiplicative

private theorem rankTwo_val_eq_zero {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] {g : G}
    (hg : orderOf g = p) {i : ZMod p} (h : g ^ i.val = 1) : i = 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hdvd : orderOf g ∣ i.val := orderOf_dvd_of_pow_eq_one h
  rw [hg] at hdvd
  have h0 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt i)
  exact (ZMod.val_eq_zero i).1 h0

private theorem rankTwo_commute_of_pow_val {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G]
    {g u : G} (hg : g ^ p = 1) {j : ZMod p} (hj : j ≠ 0) (h : Commute (g ^ j.val) u) :
    Commute g u := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  have hmul : (j.val * (j⁻¹).val) % p = 1 := by
    rw [← ZMod.val_mul, mul_inv_cancel₀ hj, ZMod.val_one]
  have hg' : g ^ (j.val * (j⁻¹).val) = g := by
    rw [pow_eq_pow_mod (j.val * (j⁻¹).val) hg, hmul, pow_one]
  have hc : Commute ((g ^ j.val) ^ (j⁻¹).val) u := h.pow_left _
  rw [← pow_mul, hg'] at hc
  exact hc

private theorem rankTwo_pow_val_add {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] {g : G}
    (hg : g ^ p = 1) (i i' : ZMod p) :
    g ^ (i + i').val = g ^ i.val * g ^ i'.val := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [ZMod.val_add, ← pow_eq_pow_mod (i.val + i'.val) hg, pow_add]

private theorem rankTwo_reorder {M : Type*} [Monoid M] {a b c a' b' c' : M}
    (hca : c * a' = a' * c) (hba : b * a' = a' * b) (hcb : c * b' = b' * c) :
    a * b * c * (a' * b' * c') = a * a' * (b * b') * (c * c') := by
  calc a * b * c * (a' * b' * c') = a * b * (c * a') * b' * c' := by simp only [mul_assoc]
    _ = a * b * (a' * c) * b' * c' := by rw [hca]
    _ = a * (b * a') * c * b' * c' := by simp only [mul_assoc]
    _ = a * (a' * b) * c * b' * c' := by rw [hba]
    _ = a * a' * b * (c * b') * c' := by simp only [mul_assoc]
    _ = a * a' * b * (b' * c) * c' := by rw [hcb]
    _ = a * a' * (b * b') * (c * c') := by simp only [mul_assoc]

private theorem rankTwo_decomp {G : Type*} [Group G] {T C : Subgroup G}
    (hTC : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t) {g : G} (hg : g ∈ T ⊔ C) :
    ∃ t ∈ T, ∃ c ∈ C, t * c = g := by
  let S : Subgroup G :=
    { carrier := {g | ∃ t ∈ T, ∃ c ∈ C, t * c = g}
      mul_mem' := by
        rintro _ _ ⟨t₁, ht₁, c₁, hc₁, rfl⟩ ⟨t₂, ht₂, c₂, hc₂, rfl⟩
        refine ⟨t₁ * t₂, T.mul_mem ht₁ ht₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
        calc t₁ * t₂ * (c₁ * c₂) = t₁ * (t₂ * c₁) * c₂ := by simp only [mul_assoc]
          _ = t₁ * (c₁ * t₂) * c₂ := by rw [hTC t₂ ht₂ c₁ hc₁]
          _ = t₁ * c₁ * (t₂ * c₂) := by simp only [mul_assoc]
      one_mem' := ⟨1, T.one_mem, 1, C.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨t, ht, c, hc, rfl⟩
        refine ⟨t⁻¹, T.inv_mem ht, c⁻¹, C.inv_mem hc, ?_⟩
        rw [mul_inv_rev]
        exact hTC t⁻¹ (T.inv_mem ht) c⁻¹ (C.inv_mem hc) }
  have hle : T ⊔ C ≤ S :=
    sup_le (fun t ht => ⟨t, ht, 1, C.one_mem, mul_one t⟩)
      (fun c hc => ⟨1, T.one_mem, c, hc, one_mul c⟩)
  obtain ⟨t, ht, c, hc, h⟩ := hle hg
  exact ⟨t, ht, c, hc, h⟩

private theorem rankTwo_quot_comm {p : ℕ} [hp : Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    {j : ℕ} (hQ : Nat.card Q = p ^ j) (hj : j ≤ 2) (a b : Q) : a * b = b * a := by
  interval_cases j
  · rw [pow_zero] at hQ
    haveI : Subsingleton Q := (Nat.card_eq_one_iff_unique.1 hQ).1
    exact Subsingleton.elim _ _
  · rw [pow_one] at hQ
    haveI : IsCyclic Q := isCyclic_of_prime_card hQ
    haveI : IsMulCommutative Q := inferInstance
    exact mul_comm' a b
  · haveI : IsMulCommutative Q := IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
    exact mul_comm' a b

private theorem rankTwo_center_comm {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = p ^ 3) (a b u : K) :
    u * ((a * b)⁻¹ * (b * a)) = ((a * b)⁻¹ * (b * a)) * u := by
  obtain ⟨m, hm0, hm⟩ := IsPGroup.card_center_eq_prime_pow hK (by norm_num)
  have hcard : Nat.card (Subgroup.center K) * Nat.card (K ⧸ Subgroup.center K) = p ^ 3 := by
    have h := Subgroup.card_mul_index (Subgroup.center K)
    rw [hK] at h
    exact h
  rw [hm] at hcard
  have hq : Nat.card (K ⧸ Subgroup.center K) ∣ p ^ 3 :=
    ⟨p ^ m, by rw [← hcard, mul_comm]⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 hq
  have hmj : m + j = 3 := by
    have h3 : p ^ (m + j) = p ^ 3 := by
      rw [pow_add, ← hj]
      exact hcard
    exact Nat.pow_right_injective hp.out.two_le h3
  have hjle : j ≤ 2 := by omega
  have hmem : ∀ x y : K, (x * y)⁻¹ * (y * x) ∈ Subgroup.center K := by
    intro x y
    have hq' := rankTwo_quot_comm hj hjle (QuotientGroup.mk x : K ⧸ Subgroup.center K)
      (QuotientGroup.mk y)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hq'
    exact QuotientGroup.eq.1 hq'
  exact Subgroup.mem_center_iff.1 (hmem a b) u

private theorem rankTwo_central_T {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : Nat.card T = p ^ 3) {t₁ t₂ u : G} (h₁ : t₁ ∈ T) (h₂ : t₂ ∈ T)
    (hu : u ∈ T) :
    u * ((t₁ * t₂)⁻¹ * (t₂ * t₁)) = ((t₁ * t₂)⁻¹ * (t₂ * t₁)) * u := by
  have h := congrArg Subtype.val
    (rankTwo_center_comm (K := ↥T) hT ⟨t₁, h₁⟩ ⟨t₂, h₂⟩ ⟨u, hu⟩)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h

private theorem rankTwo_pow_card_le {H : Type*} [Group H] [Finite H] [IsCyclic H] {q : ℕ}
    (hq : 0 < q) : Nat.card {y : H // y ^ q = 1} ≤ q := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le hq

private theorem rankTwo_zpowers_of_pow {H : Type*} [Group H] [Finite H] [IsCyclic H] {g h : H}
    (hg : g ^ orderOf h = 1) : g ∈ Subgroup.zpowers h := by
  have hq : 0 < orderOf h := orderOf_pos h
  have hsub : (Subgroup.zpowers h : Set H) ⊆ {y : H | y ^ orderOf h = 1} := by
    intro y hy
    have hy' : y ∈ Subgroup.zpowers h := hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
    show (h ^ k) ^ orderOf h = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
      one_zpow]
  have h1 : (Subgroup.zpowers h : Set H).ncard = orderOf h := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_zpowers h
  have h2 : ({y : H | y ^ orderOf h = 1} : Set H).ncard ≤ orderOf h := by
    rw [← Nat.card_coe_set_eq]
    exact rankTwo_pow_card_le hq
  have heq : (Subgroup.zpowers h : Set H) = {y : H | y ^ orderOf h = 1} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [h1]; exact h2)
  have hg' : g ∈ ({y : H | y ^ orderOf h = 1} : Set H) := hg
  rw [← heq] at hg'
  exact hg'

private theorem rankTwo_zpowers_total {p : ℕ} [hp : Fact p.Prime] {H : Type*} [Group H]
    [Finite H] [IsCyclic H] {n : ℕ} (hH : Nat.card H = p ^ n) (a b : H) :
    a ∈ Subgroup.zpowers b ∨ b ∈ Subgroup.zpowers a := by
  have ha : orderOf a ∣ p ^ n := by rw [← hH]; exact orderOf_dvd_natCard a
  have hb : orderOf b ∣ p ^ n := by rw [← hH]; exact orderOf_dvd_natCard b
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).1 ha
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 hb
  rcases le_total i j with hij | hij
  · left
    apply rankTwo_zpowers_of_pow
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hi, hj]; exact pow_dvd_pow p hij)
  · right
    apply rankTwo_zpowers_of_pow
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hi, hj]; exact pow_dvd_pow p hij)

private theorem rankTwo_comparable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {C : Subgroup G} (hCcyc : IsCyclic C) (hCp : IsPGroup p C) {c d : G} (hc : c ∈ C)
    (hd : d ∈ C) : (∃ k : ℤ, c = d ^ k) ∨ (∃ k : ℤ, d = c ^ k) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hCp
  rcases rankTwo_zpowers_total (H := ↥C) hn ⟨c, hc⟩ ⟨d, hd⟩ with h | h
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Or.inl ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Or.inr ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩

private theorem rankTwo_prod {G : Type*} [Group G] {T C : Subgroup G}
    (hTC : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t) {t c t' c' : G} (ht' : t' ∈ T) (hc : c ∈ C) :
    t * c * (t' * c') = t * t' * (c * c') := by
  calc t * c * (t' * c') = t * (c * t') * c' := by simp only [mul_assoc]
    _ = t * (t' * c) * c' := by rw [← hTC t' ht' c hc]
    _ = t * t' * (c * c') := by simp only [mul_assoc]

private theorem rankTwo_C_comm {G : Type*} [Group G] {C : Subgroup G} (hCcyc : IsCyclic C)
    {c d : G} (hc : c ∈ C) (hd : d ∈ C) : c * d = d * c :=
  congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : C) ⟨d, hd⟩)

private theorem rankTwo_F_mul {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] {x s z : G}
    (hxp : x ^ p = 1) (hsp : s ^ p = 1) (hzp : z ^ p = 1)
    (hsx : s * x = x * s) (hzx : z * x = x * z) (hzs : s * z = z * s)
    (i j k i' j' k' : ZMod p) :
    x ^ (i + i').val * s ^ (j + j').val * z ^ (k + k').val =
      x ^ i.val * s ^ j.val * z ^ k.val * (x ^ i'.val * s ^ j'.val * z ^ k'.val) := by
  rw [rankTwo_pow_val_add hxp, rankTwo_pow_val_add hsp, rankTwo_pow_val_add hzp]
  exact (rankTwo_reorder ((show Commute z x from hzx).pow_pow k.val i'.val)
    ((show Commute s x from hsx).pow_pow j.val i'.val)
    ((show Commute z s from hzs.symm).pow_pow k.val j'.val)).symm

private theorem rankTwo_indep {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G]
    {T C : Subgroup G} (hTexp : ∀ t ∈ T, t ^ p = 1) (hTC : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t)
    (hTCbot : T ⊓ C = ⊥) {x : G} (hxC : x ∈ C) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    {s : G} (hsT : s ∈ T) (hsnc : ∃ t ∈ T, s * t ≠ t * s)
    {z : G} (hzT : z ∈ T) (hzc : ∀ t ∈ T, t * z = z * t) (hz1 : z ≠ 1)
    (i j k : ZMod p) (h : x ^ i.val * s ^ j.val * z ^ k.val = 1) : i = 0 ∧ j = 0 ∧ k = 0 := by
  have hxi_eq : x ^ i.val = (s ^ j.val * z ^ k.val)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← mul_assoc]
    exact h
  have hxi_T : x ^ i.val ∈ T := by
    rw [hxi_eq]
    exact T.inv_mem (T.mul_mem (T.pow_mem hsT _) (T.pow_mem hzT _))
  have hxi1 : x ^ i.val = 1 := by
    have hmem : x ^ i.val ∈ T ⊓ C := ⟨hxi_T, C.pow_mem hxC _⟩
    rw [hTCbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hi0 : i = 0 := rankTwo_val_eq_zero (orderOf_eq_prime hxp hx1) hxi1
  have h2 : s ^ j.val * z ^ k.val = 1 := by
    rw [hi0, ZMod.val_zero, pow_zero, one_mul] at h
    exact h
  have hsj_eq : s ^ j.val = (z ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left h2
  have hj0 : j = 0 := by
    by_contra hj
    obtain ⟨t, ht, hne⟩ := hsnc
    have hcomm_pow : Commute (s ^ j.val) t := by
      rw [hsj_eq]
      exact ((show Commute t z from hzc t ht).symm.pow_left k.val).inv_left
    exact hne (rankTwo_commute_of_pow_val (hTexp s hsT) hj hcomm_pow)
  have hk0 : k = 0 := by
    rw [hj0, ZMod.val_zero, pow_zero, one_mul] at h2
    exact rankTwo_val_eq_zero (orderOf_eq_prime (hTexp z hzT) hz1) h2
  exact ⟨hi0, hj0, hk0⟩

private theorem rankTwo_key {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T C R : Subgroup G} (hTexp : ∀ t ∈ T, t ^ p = 1) (hTC : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t)
    (hTCbot : T ⊓ C = ⊥) {x : G} (hxC : x ∈ C) (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxR : x ∈ R)
    {s : G} (hsT : s ∈ T) (hsR : s ∈ R) (hsnc : ∃ t ∈ T, s * t ≠ t * s)
    {z : G} (hzT : z ∈ T) (hzR : z ∈ R) (hzc : ∀ t ∈ T, t * z = z * t) (hz1 : z ≠ 1)
    (hrk : CFSG.Open.pRank p R ≤ 2) : False := by
  have hp1 : 1 < p := hp.out.one_lt
  have hsp : s ^ p = 1 := hTexp s hsT
  have hzp : z ^ p = 1 := hTexp z hzT
  have hsx : s * x = x * s := hTC s hsT x hxC
  have hzx : z * x = x * z := hTC z hzT x hxC
  have hzs : s * z = z * s := hzc s hsT
  let F : Multiplicative (ZMod p × ZMod p × ZMod p) → G := fun u =>
    x ^ (toAdd u).1.val * s ^ (toAdd u).2.1.val * z ^ (toAdd u).2.2.val
  have hF : ∀ u v, F (u * v) = F u * F v := by
    intro u v
    have htm : toAdd (u * v) = toAdd u + toAdd v := rfl
    simp only [F, htm, Prod.fst_add, Prod.snd_add]
    exact rankTwo_F_mul hxp hsp hzp hsx hzx hzs _ _ _ _ _ _
  let f : Multiplicative (ZMod p × ZMod p × ZMod p) →* G := MonoidHom.mk' F hF
  have hfF : ∀ u, f u = F u := fun u => rfl
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, hfF] at hu
    obtain ⟨hi, hj, hk⟩ := rankTwo_indep hTexp hTC hTCbot hxC hx1 hxp hsT hsnc hzT hzc hz1
      (toAdd u).1 (toAdd u).2.1 (toAdd u).2.2 hu
    rw [Subgroup.mem_bot, ← toAdd_eq_zero]
    exact Prod.ext hi (Prod.ext hj hk)
  have hA : Nat.card (Multiplicative (ZMod p × ZMod p × ZMod p)) = p ^ 3 := by
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
    ring
  have hpow : ∀ a : Multiplicative (ZMod p × ZMod p × ZMod p), a ^ p = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
  have hH : f.range ≤ R := by
    intro y hy
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [hfF]
    exact R.mul_mem (R.mul_mem (R.pow_mem hxR _) (R.pow_mem hsR _)) (R.pow_mem hzR _)
  have h3 := CFSG.SectionRank.le_pRank_of_injective hp1 (fun a b => mul_comm a b) hpow hA f hfinj hH
  omega

private theorem rankTwo_case {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T C R : Subgroup G} (hTexp : ∀ t ∈ T, t ^ p = 1) (hTC : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t)
    (hTCbot : T ⊓ C = ⊥) {x : G} (hxC : x ∈ C) (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxR : x ∈ R)
    {a b t₁ t₂ c₁ c₂ : G} (k : ℤ) (ha : a ∈ R) (hb : b ∈ R)
    (ha' : a = t₁ * c₁) (hb' : b = t₂ * c₂) (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T) (hc₂ : c₂ ∈ C)
    (hc : c₁ = c₂ ^ k) (hnc : t₁ * t₂ ≠ t₂ * t₁)
    {z : G} (hzT : z ∈ T) (hzR : z ∈ R) (hzc : ∀ t ∈ T, t * z = z * t) (hz1 : z ≠ 1)
    (hrk : CFSG.Open.pRank p R ≤ 2) : False := by
  have hcomm : Commute t₂ c₂ := hTC t₂ ht₂ c₂ hc₂
  have hsT_eq : a * b ^ (-k) = t₁ * t₂ ^ (-k) := by
    have hcz : c₂ ^ k * t₂ ^ (-k) = t₂ ^ (-k) * c₂ ^ k := (hcomm.zpow_zpow (-k) k).symm.eq
    have hcc : c₂ ^ k * c₂ ^ (-k) = 1 := by rw [← zpow_add]; simp
    rw [ha', hb', hc, hcomm.mul_zpow]
    calc t₁ * c₂ ^ k * (t₂ ^ (-k) * c₂ ^ (-k))
        = t₁ * (c₂ ^ k * t₂ ^ (-k)) * c₂ ^ (-k) := by simp only [mul_assoc]
      _ = t₁ * (t₂ ^ (-k) * c₂ ^ k) * c₂ ^ (-k) := by rw [hcz]
      _ = t₁ * t₂ ^ (-k) * (c₂ ^ k * c₂ ^ (-k)) := by simp only [mul_assoc]
      _ = t₁ * t₂ ^ (-k) := by rw [hcc, mul_one]
  have hsT : t₁ * t₂ ^ (-k) ∈ T := T.mul_mem ht₁ (T.zpow_mem ht₂ _)
  have hsR : t₁ * t₂ ^ (-k) ∈ R := by
    rw [← hsT_eq]
    exact R.mul_mem ha (R.zpow_mem hb _)
  have hsnc : ∃ t ∈ T, t₁ * t₂ ^ (-k) * t ≠ t * (t₁ * t₂ ^ (-k)) := by
    refine ⟨t₂, ht₂, fun h => hnc ?_⟩
    have hpt : t₂ * t₂ ^ (-k) = t₂ ^ (-k) * t₂ := (Commute.self_zpow t₂ (-k)).eq
    have h2 : t₁ * t₂ * t₂ ^ (-k) = t₂ * t₁ * t₂ ^ (-k) := by
      calc t₁ * t₂ * t₂ ^ (-k) = t₁ * (t₂ * t₂ ^ (-k)) := by rw [mul_assoc]
        _ = t₁ * (t₂ ^ (-k) * t₂) := by rw [hpt]
        _ = t₁ * t₂ ^ (-k) * t₂ := by rw [mul_assoc]
        _ = t₂ * (t₁ * t₂ ^ (-k)) := h
        _ = t₂ * t₁ * t₂ ^ (-k) := by rw [mul_assoc]
    exact mul_right_cancel h2
  exact rankTwo_key hTexp hTC hTCbot hxC hx1 hxp hxR hsT hsR hsnc hzT hzR hzc hz1 hrk

theorem rank_two_abelian {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type*} [Group G] [Finite G]
    {T C R : Subgroup G} (hT : Nat.card T = p ^ 3) (hTexp : ∀ t ∈ T, t ^ p = 1)
    (hTnc : ¬ IsMulCommutative T) (hCcyc : IsCyclic C) (hCp : IsPGroup p C)
    (hTC : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t) (hTCbot : T ⊓ C = ⊥)
    {x : G} (hxC : x ∈ C) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hRS : R ≤ T ⊔ C) (hxR : x ∈ R) (hrk : CFSG.Open.pRank p R ≤ 2) : IsMulCommutative R := by
  by_contra hnot
  have hex : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a := by
    by_contra hne
    push Not at hne
    exact hnot ⟨⟨fun a b => Subtype.ext (hne a.1 a.2 b.1 b.2)⟩⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hex
  obtain ⟨t₁, ht₁, c₁, hc₁, h₁⟩ := rankTwo_decomp hTC (hRS ha)
  obtain ⟨t₂, ht₂, c₂, hc₂, h₂⟩ := rankTwo_decomp hTC (hRS hb)
  subst h₁ h₂
  have hnc : t₁ * t₂ ≠ t₂ * t₁ := by
    intro h
    apply hab
    rw [rankTwo_prod hTC ht₂ hc₁, rankTwo_prod hTC ht₁ hc₂, rankTwo_C_comm hCcyc hc₂ hc₁, h]
  have hw : c₁ * c₂ ∈ C := C.mul_mem hc₁ hc₂
  have hzT : (t₁ * t₂)⁻¹ * (t₂ * t₁) ∈ T :=
    T.mul_mem (T.inv_mem (T.mul_mem ht₁ ht₂)) (T.mul_mem ht₂ ht₁)
  have hzc : ∀ t ∈ T, t * ((t₁ * t₂)⁻¹ * (t₂ * t₁)) = ((t₁ * t₂)⁻¹ * (t₂ * t₁)) * t :=
    fun t ht => rankTwo_central_T hT ht₁ ht₂ ht
  have hz1 : (t₁ * t₂)⁻¹ * (t₂ * t₁) ≠ 1 := fun h => hnc (inv_mul_eq_one.1 h)
  have hid : (t₁ * c₁ * (t₂ * c₂))⁻¹ * (t₂ * c₂ * (t₁ * c₁)) = (t₁ * t₂)⁻¹ * (t₂ * t₁) := by
    have e1 : t₁ * c₁ * (t₂ * c₂) = t₁ * t₂ * (c₁ * c₂) := rankTwo_prod hTC ht₂ hc₁
    have e2 : t₂ * c₂ * (t₁ * c₁) = t₂ * t₁ * (c₁ * c₂) := by
      rw [rankTwo_prod hTC ht₁ hc₂, rankTwo_C_comm hCcyc hc₂ hc₁]
    have hzw : (t₁ * t₂)⁻¹ * (t₂ * t₁) * (c₁ * c₂) = (c₁ * c₂) * ((t₁ * t₂)⁻¹ * (t₂ * t₁)) :=
      hTC _ hzT _ hw
    rw [e1, e2, mul_inv_rev (t₁ * t₂) (c₁ * c₂)]
    calc (c₁ * c₂)⁻¹ * (t₁ * t₂)⁻¹ * (t₂ * t₁ * (c₁ * c₂))
        = (c₁ * c₂)⁻¹ * (((t₁ * t₂)⁻¹ * (t₂ * t₁)) * (c₁ * c₂)) := by simp only [mul_assoc]
      _ = (c₁ * c₂)⁻¹ * ((c₁ * c₂) * ((t₁ * t₂)⁻¹ * (t₂ * t₁))) := by rw [hzw]
      _ = (t₁ * t₂)⁻¹ * (t₂ * t₁) := by rw [inv_mul_cancel_left]
  have hzR : (t₁ * t₂)⁻¹ * (t₂ * t₁) ∈ R := by
    rw [← hid]
    exact R.mul_mem (R.inv_mem (R.mul_mem ha hb)) (R.mul_mem hb ha)
  rcases rankTwo_comparable hCcyc hCp hc₁ hc₂ with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact rankTwo_case hTexp hTC hTCbot hxC hx1 hxp hxR k ha hb rfl rfl ht₁ ht₂ hc₂ hk hnc
      hzT hzR hzc hz1 hrk
  · exact rankTwo_case hTexp hTC hTCbot hxC hx1 hxp hxR k hb ha rfl rfl ht₂ ht₁ hc₁ hk hnc.symm
      hzT hzR hzc hz1 hrk

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
