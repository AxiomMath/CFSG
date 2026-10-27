module

public import CFSG.GH74.GLS.Stage4.Q9.ThetaModel
public import CFSG.GH74.GLS.Stage4.Q9.FrobCount
public meta import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public meta import CFSG.GH74.GLS.Stage4.Q9.ChatOrders
public meta import CFSG.GH74.GLS.Stage4.Q9.Tables
public meta import Mathlib
public import CFSG.GH74.GLS.Stage4.Q9.ThetaPropsInputs
public meta import CFSG.GH74.GLS.Stage4.Q9.ThetaPropsInputs
public import Certificates.Certificate5100
public import Certificates.Certificate5101
public import Certificates.Certificate5102
public import Certificates.Certificate5103

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open CFSG Subgroup

namespace ThetaProps

@[expose] def typSet : Finset LTyp := typList.toFinset

@[expose] def cnt (t : LTyp) : ℕ := ((typTab.filter fun p => decide (p.1 = t)).map Prod.snd).sum

theorem typ_memList : ∀ l : Lg, typ l ∈ typList :=
  Certificates.certificate5103.1

theorem typ_mem
    (l : Lg) : typ l ∈ typSet := List.mem_toFinset.mpr (typ_memList l)

theorem typCountsOK_eq : typCountsOK = true :=
  Certificates.certificate5103.2

theorem cnt_typTab : ∀ p ∈ typTab, cnt p.1 = p.2 := by decide +kernel

theorem card_typ (t : LTyp) (ht : t ∈ typList) :
    (Finset.univ.filter fun l : Lg => typ l = t).card = cnt t := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
  have h := typCountsOK_eq
  simp only [typCountsOK, List.all_eq_true, decide_eq_true_eq] at h
  rw [cnt_typTab p hp, ← h p hp, Multiset.count_map]
  simp only [Finset.card, Finset.filter_val, eq_comm]

theorem sum_typ {M : Type*} [AddCommMonoid M] (H : LTyp → M) :
    ∑ l : Lg, H (typ l) = ∑ t ∈ typSet, cnt t • H t := by
  rw [← Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := typSet) (g := typ)
    (fun l _ => typ_mem l) H]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.sum_const, card_typ t (List.mem_toFinset.mp ht)]

theorem parityL_eq_iff_inner (l₁ l₂ : Lg) :
    parityL l₁ = parityL l₂ ↔ (typ l₁).inner = (typ l₂).inner := by
  have h : ∀ a b : Multiplicative (ZMod 2), a = b ↔ decide (a = 1) = decide (b = 1) := by decide
  exact h _ _

theorem sum_Chat_typ
    {M : Type*} [AddCommMonoid M] (F : LTyp → LTyp → M) :
    ∑ c : ↥Chat, F (typ c.1.1) (typ c.1.2) =
      ∑ t₁ ∈ typSet, ∑ t₂ ∈ typSet,
        if t₁.inner = t₂.inner then cnt t₁ • cnt t₂ • F t₁ t₂ else 0 := by
  classical
  have h1 : ∑ c : ↥Chat, F (typ c.1.1) (typ c.1.2) =
      ∑ l₁ : Lg, ∑ l₂ : Lg, if (typ l₁).inner = (typ l₂).inner then F (typ l₁) (typ l₂) else 0 := by
    have e : ∑ c : ↥Chat, F (typ c.1.1) (typ c.1.2) =
        ∑ p : Lg × Lg, if p ∈ Chat then F (typ p.1) (typ p.2) else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter (· ∈ Chat)) (by simp)
        (fun p : Lg × Lg => F (typ p.1) (typ p.2))).symm
    rw [e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l₁ _ => Finset.sum_congr rfl fun l₂ _ => ?_
    simp only [mem_Chat_iff, parityL_eq_iff_inner]
  rw [h1]
  have h2 : ∀ l₁ : Lg, ∑ l₂ : Lg,
      (if (typ l₁).inner = (typ l₂).inner then F (typ l₁) (typ l₂) else 0) =
      ∑ t₂ ∈ typSet, cnt t₂ • (if (typ l₁).inner = t₂.inner then F (typ l₁) t₂ else 0) :=
    fun l₁ => sum_typ (fun t₂ => if (typ l₁).inner = t₂.inner then F (typ l₁) t₂ else 0)
  simp only [h2]
  rw [Finset.sum_comm]
  have h3 : ∀ t₂ : LTyp,
      ∑ l₁ : Lg, cnt t₂ • (if (typ l₁).inner = t₂.inner then F (typ l₁) t₂ else 0) =
      ∑ t₁ ∈ typSet, cnt t₁ • cnt t₂ • (if t₁.inner = t₂.inner then F t₁ t₂ else 0) :=
    fun t₂ => sum_typ (fun t₁ => cnt t₂ • (if t₁.inner = t₂.inner then F t₁ t₂ else 0))
  simp only [h3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ => ?_
  split_ifs <;> simp

theorem typ_inner (l : Lg) : (typ l).inner = decide (parityL l = 1) := rfl

theorem typ_ord (l : Lg) : (typ l).ord = ordL l := rfl

theorem typ_mu (l : Lg) : (typ l).mu = decide (muFlag l) := rfl

theorem typ_ridx (l : Lg) : (typ l).ridx = if parityL l = 1 then repIdx l.left else 0 := rfl

theorem typ_inner_eq (c : ↥Chat) : (typ c.1.1).inner = (typ c.1.2).inner :=
  (parityL_eq_iff_inner _ _).mp (mem_Chat_iff.mp c.2)

theorem ordL_eq_one_iff (l : Lg) : ordL l = 1 ↔ l = 1 := by
  rw [← orderOf_Lg, orderOf_eq_one_iff]

theorem eq_one_iff_typ
    (l : Lg) : l = 1 ↔ (typ l).ord = 1 := (ordL_eq_one_iff l).symm

theorem eq_one_or_minusOne_iff_typ (l : Lg) :
    (l = 1 ∨ l = innerL minusOne) ↔ ((typ l).inner = true ∧ (typ l).ridx = 0) := by
  by_cases h : parityL l = 1
  · obtain ⟨M, rfl⟩ := exists_innerL_of_parityL_eq_one h
    have e1 : innerL M = 1 ↔ M = 1 := by
      rw [← map_one innerL]; exact innerL_injective.eq_iff
    have e2 : innerL M = innerL minusOne ↔ M = minusOne := innerL_injective.eq_iff
    rw [e1, e2, typ_inner, typ_ridx]
    simp only [h, decide_true, ite_true, true_and]
    exact (repIdx_eq_zero_iff M).symm
  · have h1 : l ≠ 1 := fun e => h (e ▸ map_one parityL)
    have h2 : l ≠ innerL minusOne := fun e => h (e ▸ parityL_innerL minusOne)
    simp [h1, h2, typ_inner, h]

theorem eq_innerL_minusOne_iff_typ (l : Lg) :
    l = innerL minusOne ↔ ((typ l).mu = true ∧ (typ l).ord = 2) := by
  have h := pow_eq_innerL_minusOne_iff_muFlag l 1
  rw [pow_one] at h
  rw [h, typ_mu, typ_ord, decide_eq_true_eq]
  constructor
  · rintro ⟨hf, h1⟩
    refine ⟨hf, ?_⟩
    obtain ⟨⟨k, hk⟩, -⟩ := hf
    have hpos := ordL_pos l
    have h2 : 1 < ordL l := by omega
    rw [Nat.mod_eq_of_lt h2] at h1
    omega
  · rintro ⟨hf, h2⟩
    refine ⟨hf, ?_⟩
    rw [h2]

@[expose] def ordC (t₁ t₂ : LTyp) : ℕ :=
  let o := Nat.lcm t₁.ord t₂.ord
  if Even o ∧ (t₁.mu = true ∧ o / 2 % t₁.ord = t₁.ord / 2) ∧
      (t₂.mu = true ∧ o / 2 % t₂.ord = t₂.ord / 2) then o / 2 else o

theorem orderOf_mkC_typ
    (c : ↥Chat) : orderOf (mkC c) = ordC (typ c.1.1) (typ c.1.2) := by
  rw [orderOf_mkC_flags]
  simp only [ordC, typ_ord, typ_mu, decide_eq_true_eq]

abbrev sProp (t₁ t₂ : LTyp) : Prop :=
  ((t₁.mu = true ∧ Nat.gcd t₁.ord t₂.ord ∣ t₁.ord / 2) ∨
      (t₂.mu = true ∧ Nat.gcd t₁.ord t₂.ord ∣ t₂.ord / 2)) ∨
    (3 ∣ t₁.ord ∨ 3 ∣ t₂.ord) ∨
    (ordC t₁ t₂ = 5 ∧ ((t₁.inner = true ∧ t₂.inner = true ∧ t₂.ridx = 0) ∨
      (t₂.inner = true ∧ t₁.inner = true ∧ t₁.ridx = 0)))

theorem mkC_mem_Sset_iff_typ
    (c : ↥Chat) :
    mkC c ∈ Sset zq K1q K2q ↔ sProp (typ c.1.1) (typ c.1.2) := by
  rw [mkC_mem_Sset_iff, orderOf_mkC_typ, eq_one_or_minusOne_iff_typ c.1.2,
    eq_one_or_minusOne_iff_typ c.1.1]
  simp only [sProp, typ_inner, typ_ord, typ_mu, decide_eq_true_eq]

abbrev jProp (t₁ t₂ : LTyp) : Prop :=
  ordC t₁ t₂ = 2 ∧
    ¬(((t₁.mu = true ∧ t₁.ord = 2) ∧ t₂.ord = 1) ∨ (t₁.ord = 1 ∧ (t₂.mu = true ∧ t₂.ord = 2)))

theorem mkC_J_iff_typ (c : ↥Chat) :
    (orderOf (mkC c) = 2 ∧ mkC c ≠ zq) ↔ jProp (typ c.1.1) (typ c.1.2) := by
  rw [orderOf_mkC_typ, Ne, mkC_eq_zq_iff, eq_inl1_minusOne_iff, eq_inr1_minusOne_iff,
    eq_one_iff_typ c.1.2, eq_innerL_minusOne_iff_typ c.1.1, eq_one_iff_typ c.1.1,
    eq_innerL_minusOne_iff_typ c.1.2]

abbrev pProp (p : ℕ) (t₁ t₂ : LTyp) : Prop :=
  sProp t₁ t₂ ∧ ordC t₁ t₂ ≠ 1 ∧ ∃ k < 8, ordC t₁ t₂ = p ^ k

theorem ordC_lt : ∀ t₁ ∈ typList, ∀ t₂ ∈ typList, ordC t₁ t₂ < 256 := by decide +kernel

theorem exists_pow_iff_lt {p n : ℕ} (hp : 2 ≤ p) (hn : n < 256) :
    (∃ k : ℕ, n = p ^ k) ↔ ∃ k < 8, n = p ^ k := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_, rfl⟩
    by_contra hk
    have h8 : 256 ≤ p ^ k :=
      calc 256 = 2 ^ 8 := by norm_num
        _ ≤ p ^ 8 := Nat.pow_le_pow_left hp 8
        _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) (not_lt.mp hk)
    exact absurd hn (not_lt.mpr h8)
  · rintro ⟨k, -, h⟩
    exact ⟨k, h⟩

theorem mkC_mem_pSet_iff_typ
    (p : ℕ) (hp : 2 ≤ p) (c : ↥Chat) :
    mkC c ∈ pSet p zq K1q K2q ↔ pProp p (typ c.1.1) (typ c.1.2) := by
  have hlt : ordC (typ c.1.1) (typ c.1.2) < 256 :=
    ordC_lt _ (typ_memList _) _ (typ_memList _)
  show (mkC c ∈ Sset zq K1q K2q ∧ mkC c ≠ 1 ∧ ∃ k : ℕ, orderOf (mkC c) = p ^ k) ↔ _
  rw [mkC_mem_Sset_iff_typ, Ne, ← orderOf_eq_one_iff, orderOf_mkC_typ]
  simp only [exists_pow_iff_lt hp hlt]

@[expose] noncomputable def evZ : ℤ × ℤ →+ ℂ where
  toFun x := (x.1 : ℂ) + (x.2 : ℂ) * r
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring

theorem evZ_apply (x : ℤ × ℤ) : evZ x = (x.1 : ℂ) + (x.2 : ℂ) * r := rfl

@[expose] def zmul (a b : ℤ × ℤ) : ℤ × ℤ :=
  (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1 + a.2 * b.2)

theorem evZ_zmul (a b : ℤ × ℤ) : evZ (zmul a b) = evZ a * evZ b := by
  simp only [evZ_apply, zmul]
  push_cast
  linear_combination (-(a.2 : ℂ) * b.2) * rho_r_sq

theorem evZ_smul' (k : ℤ) (x : ℤ × ℤ) : evZ (k * x.1, k * x.2) = (k : ℂ) * evZ x := by
  simp only [evZ_apply]
  push_cast
  ring

@[expose] def rhoZ : Fin 7 → ℤ × ℤ :=
  ![(8, 0), (-1, 0), (-1, 0), (0, 0), (0, 0), (0, 1), (1, -1)]

theorem evZ_rhoZ (j : Fin 7) : evZ (rhoZ j) = rhoTab j := by
  fin_cases j <;> simp [evZ_apply, rhoZ, rhoTab, sub_eq_add_neg]

@[expose] def aV (t : LTyp) : ℤ := aByOrder t.inner t.ord

@[expose] def bZ (t₁ t₂ : LTyp) : ℤ × ℤ :=
  if t₁.inner then (muTab t₂.ridx * (rhoZ t₁.ridx).1, muTab t₂.ridx * (rhoZ t₁.ridx).2) else (0, 0)

@[expose] def thZ (t₁ t₂ : LTyp) : ℤ × ℤ := (1 - aV t₁ * aV t₂, 0) + bZ t₁ t₂

theorem aTab_eq_aV
    (l : Lg) : aTab l = aV (typ l) := by
  rw [aTab_eq_aByOrder, orderOf_Lg]
  rfl

theorem alphaHat_eq_typ (c : ↥Chat) :
    alphaHat c = ((aV (typ c.1.1) * aV (typ c.1.2) : ℤ) : ℂ) := by
  rw [alphaHat_apply, aTab_eq_aV, aTab_eq_aV]

theorem betaHat_eq_typ
    (c : ↥Chat) : betaHat c = evZ (bZ (typ c.1.1) (typ c.1.2)) := by
  obtain ⟨⟨l₁, l₂⟩, hc⟩ := c
  have hp : parityL l₁ = parityL l₂ := mem_Chat_iff.mp hc
  rw [betaHat_apply l₁ l₂ hp]
  by_cases h₁ : parityL l₁ = 1
  · have h₂ : parityL l₂ = 1 := hp.symm.trans h₁
    have e : (typ l₂).ridx = repIdx l₂.left := by rw [typ_ridx, ite_eq_left h₂]
    have e1 : (typ l₁).ridx = repIdx l₁.left := by rw [typ_ridx, ite_eq_left h₁]
    have hi : (typ l₁).inner = true := by rw [typ_inner, decide_eq_true_eq]; exact h₁
    show _ = evZ (bZ (typ l₁) (typ l₂))
    rw [bZ, ite_eq_left hi, evZ_smul', e, e1, evZ_rhoZ, ite_eq_left h₁]
    ring
  · have hi : (typ l₁).inner = false := by rw [typ_inner, decide_eq_false_iff_not]; exact h₁
    show _ = evZ (bZ (typ l₁) (typ l₂))
    rw [bZ, hi, ite_eq_right h₁]
    simp [evZ_apply]

theorem thetaHat_eq_typ
    (c : ↥Chat) : thetaHat c = evZ (thZ (typ c.1.1) (typ c.1.2)) := by
  rw [thetaHat_apply_eq, alphaHat_eq_typ, betaHat_eq_typ, thZ, map_add]
  simp [evZ_apply]

theorem theta_check :
    ∀ t₁ ∈ typList, ∀ t₂ ∈ typList, t₁.inner = t₂.inner → ¬ sProp t₁ t₂ → thZ t₁ t₂ = 0 := by
  decide +kernel

theorem J_check : ∀ t₁ ∈ typList, ∀ t₂ ∈ typList, t₁.inner = t₂.inner → jProp t₁ t₂ →
    aV t₁ * aV t₂ = 1 ∧ bZ t₁ t₂ = 0 := by
  decide +kernel

theorem sum_alpha_sq_typ :
    (∑ t₁ ∈ typSet, ∑ t₂ ∈ typSet,
        if t₁.inner = t₂.inner then cnt t₁ • cnt t₂ • ((aV t₁ * aV t₂) ^ 2 : ℤ) else 0) =
      1036800 := by
  decide +kernel

theorem sum_beta_sq_typ :
    (∑ t₁ ∈ typSet, ∑ t₂ ∈ typSet,
        if t₁.inner = t₂.inner then cnt t₁ • cnt t₂ • zmul (bZ t₁ t₂) (bZ t₁ t₂) else 0) =
      (1036800, 0) := by
  decide +kernel

theorem card_jProp_typ :
    (∑ t₁ ∈ typSet, ∑ t₂ ∈ typSet,
        if t₁.inner = t₂.inner then cnt t₁ • cnt t₂ • (if jProp t₁ t₂ then 1 else 0) else 0) =
      13284 := by
  decide +kernel

theorem card_pSet_mul_two
    (p : ℕ) (hp : 2 ≤ p) :
    Nat.card ↥(pSet p zq K1q K2q) * 2 =
      ∑ t₁ ∈ typSet, ∑ t₂ ∈ typSet,
        if t₁.inner = t₂.inner then cnt t₁ • cnt t₂ • (if pProp p t₁ t₂ then 1 else 0) else 0 := by
  have h := natCard_set_mkC (pSet p zq K1q K2q) (fun c => pProp p (typ c.1.1) (typ c.1.2))
    (fun c => mkC_mem_pSet_iff_typ p hp c)
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    sum_Chat_typ (fun t₁ t₂ => if pProp p t₁ t₂ then 1 else 0)]

theorem card_pSet_two_typ :
    (∑ t₁ ∈ typSet, ∑ t₂ ∈ typSet,
        if t₁.inner = t₂.inner then cnt t₁ • cnt t₂ • (if pProp 2 t₁ t₂ then 1 else 0) else 0) =
      85322 := by
  decide +kernel

theorem card_pSet_three_typ :
    (∑ t₁ ∈ typSet, ∑ t₂ ∈ typSet,
        if t₁.inner = t₂.inner then cnt t₁ • cnt t₂ • (if pProp 3 t₁ t₂ then 1 else 0) else 0) =
      13120 := by
  decide +kernel

theorem card_pSet_five_typ :
    (∑ t₁ ∈ typSet, ∑ t₂ ∈ typSet,
        if t₁.inner = t₂.inner then cnt t₁ • cnt t₂ • (if pProp 5 t₁ t₂ then 1 else 0) else 0) =
      576 := by
  decide +kernel

end ThetaProps

open ThetaProps

theorem alphaHat_norm :
    BlocksInnerProduct alphaHat alphaHat = 1 := by
  have e : ∀ x : ↥Chat, alphaHat x * starRingEnd ℂ (alphaHat x) =
      (((aV (typ x.1.1) * aV (typ x.1.2)) ^ 2 : ℤ) : ℂ) := by
    intro x
    rw [alphaHat_conj, alphaHat_eq_typ]
    push_cast
    ring
  unfold BlocksInnerProduct
  simp only [e]
  rw [← Int.cast_sum, sum_Chat_typ (fun t₁ t₂ => (((aV t₁ * aV t₂) ^ 2 : ℤ))), sum_alpha_sq_typ,
    card_Chat]
  norm_num

theorem betaHat_norm :
    BlocksInnerProduct betaHat betaHat = 1 := by
  have e : ∀ x : ↥Chat, betaHat x * starRingEnd ℂ (betaHat x) =
      evZ (zmul (bZ (typ x.1.1) (typ x.1.2)) (bZ (typ x.1.1) (typ x.1.2))) := by
    intro x
    rw [betaHat_conj, betaHat_eq_typ, evZ_zmul]
  unfold BlocksInnerProduct
  simp only [e]
  rw [← map_sum evZ, sum_Chat_typ (fun t₁ t₂ => zmul (bZ t₁ t₂) (bZ t₁ t₂)), sum_beta_sq_typ,
    card_Chat]
  simp [evZ_apply]

theorem thetaHat_support :
    ∀ c : ↥Chat, mkC c ∉ Sset zq K1q K2q → thetaHat c = 0 := by
  intro c hc
  rw [mkC_mem_Sset_iff_typ] at hc
  rw [thetaHat_eq_typ, theta_check _ (typ_memList _) _ (typ_memList _) (typ_inner_eq c) hc,
    map_zero]

theorem alphaHat_J :
    ∀ c : ↥Chat, orderOf (mkC c) = 2 → mkC c ≠ zq → alphaHat c = 1 := by
  intro c h2 hz
  have hj := (mkC_J_iff_typ c).mp ⟨h2, hz⟩
  have h := (J_check _ (typ_memList _) _ (typ_memList _) (typ_inner_eq c) hj).1
  rw [alphaHat_eq_typ, h]
  norm_num

theorem betaHat_J :
    ∀ c : ↥Chat, orderOf (mkC c) = 2 → mkC c ≠ zq → betaHat c = 0 := by
  intro c h2 hz
  have hj := (mkC_J_iff_typ c).mp ⟨h2, hz⟩
  have h := (J_check _ (typ_memList _) _ (typ_memList _) (typ_inner_eq c) hj).2
  rw [betaHat_eq_typ, h, map_zero]

theorem card_J :
    Nat.card {x : Cq // orderOf x = 2 ∧ x ≠ zq} = 6642 := by
  have h := natCard_subtype_mkC (fun x : Cq => orderOf x = 2 ∧ x ≠ zq)
  have e : Nat.card {c : ↥Chat // orderOf (mkC c) = 2 ∧ mkC c ≠ zq} =
      Nat.card {c : ↥Chat // jProp (typ c.1.1) (typ c.1.2)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c => mkC_J_iff_typ c)
  have e2 : Nat.card {c : ↥Chat // jProp (typ c.1.1) (typ c.1.2)} = 13284 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
      sum_Chat_typ (fun t₁ t₂ => if jProp t₁ t₂ then 1 else 0), card_jProp_typ]
  rw [e, e2] at h
  omega

theorem card_pSet_two :
    Nat.card ↥(pSet 2 zq K1q K2q) = 42661 := by
  have h := card_pSet_mul_two 2 (by norm_num)
  rw [card_pSet_two_typ] at h
  omega

theorem card_pSet_three :
    Nat.card ↥(pSet 3 zq K1q K2q) = 6560 := by
  have h := card_pSet_mul_two 3 (by norm_num)
  rw [card_pSet_three_typ] at h
  omega

theorem card_pSet_five :
    Nat.card ↥(pSet 5 zq K1q K2q) = 288 := by
  have h := card_pSet_mul_two 5 (by norm_num)
  rw [card_pSet_five_typ] at h
  omega

end CFSG.GH74.GLS.Stage4.Q9
