module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Model
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup
open scoped commutatorElement

namespace Wr

@[expose] def mk0 (u : ZMod 5 → ZMod 5) : Wr := ⟨u, 0⟩

theorem mk0_mul (u v : ZMod 5 → ZMod 5) : mk0 u * mk0 v = mk0 (u + v) := by
  ext i
  · simp [mk0]
  · simp [mk0]

theorem mk0_pow (u : ZMod 5 → ZMod 5) (n : ℕ) : mk0 u ^ n = mk0 (n • u) := by
  induction n with
  | zero =>
    ext i
    · simp [mk0]
    · simp [mk0]
  | succ n ih =>
    rw [pow_succ, ih, mk0_mul, succ_nsmul]

theorem pow_c (w : Wr) (n : ℕ) : (w ^ n).c = n • w.c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_c, ih, succ_nsmul]

@[expose] def cHom : Wr →* Multiplicative (ZMod 5) where
  toFun w := Multiplicative.ofAdd w.c
  map_one' := rfl
  map_mul' x y := rfl

theorem comm_mk0 (u : ZMod 5 → ZMod 5) (w : Wr) :
    ⁅mk0 u, w⁆ = mk0 (fun i => u i - u (i - w.c)) := by
  rw [commutatorElement_def]
  ext i
  · simp [mk0]
    ring_nf
  · simp [mk0]

end Wr

theorem eq_zero_of_shift {δ : ZMod 5 → ZMod 5} {c : ZMod 5} (hc : c ≠ 0)
    (h : ∀ i, δ i = δ (i - c)) (h0 : δ 0 = 0) : ∀ i, δ i = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hk : ∀ k : ℕ, δ ((k : ZMod 5) * c) = 0 := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      rw [h, Nat.cast_succ, add_mul, one_mul, add_sub_cancel_right, ih]
  intro i
  have : i = (((i * c⁻¹).val : ℕ) : ZMod 5) * c := by
    rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rw [this]
  exact hk _

theorem weight_ge_three {u : ZMod 5 → ZMod 5} (h1 : ∑ i, u i = 0) (h2 : ∑ i, i * u i = 0)
    (hu : u ≠ 0) : (Finset.univ.filter fun i => u i = 0).card ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have key : ∀ u : ZMod 5 → ZMod 5, (∑ i, u i = 0) → (∑ i, i * u i = 0) →
      (Finset.univ.filter fun i => u i = 0).card ≥ 3 → u = 0 := by
    decide +kernel
  exact hu (key u h1 h2 hcon)

theorem exists_sub_shift {v : ZMod 5 → ZMod 5} (hv : ∑ i, v i = 0) :
    ∃ u : ZMod 5 → ZMod 5, ∀ i, u i - u (i - 1) = v i := by
  have key : ∀ v : ZMod 5 → ZMod 5, (∑ i, v i = 0) →
      ∀ i, (fun i : ZMod 5 => ∑ k : ZMod 5 with k.val ≤ i.val, v k) i -
        (fun i : ZMod 5 => ∑ k : ZMod 5 with k.val ≤ i.val, v k) (i - 1) = v i := by
    decide +kernel
  exact ⟨fun i : ZMod 5 => ∑ k : ZMod 5 with k.val ≤ i.val, v k, key v hv⟩


@[expose] def Cw : Subgroup Wr where
  carrier := {w | w.c = 0 ∧ ∑ i, w.a i = 0 ∧ ∑ i, i * w.a i = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hx0, hx1, hx2⟩ ⟨hy0, hy1, hy2⟩
    refine ⟨by simp [hx0, hy0], ?_, ?_⟩
    · simp only [Wr.mul_a, hx0, sub_zero, Finset.sum_add_distrib, hx1, hy1, add_zero]
    · simp only [Wr.mul_a, hx0, sub_zero, mul_add, Finset.sum_add_distrib, hx2, hy2, add_zero]
  inv_mem' := by
    rintro x ⟨hx0, hx1, hx2⟩
    refine ⟨by simp [hx0], ?_, ?_⟩
    · simp only [Wr.inv_a, hx0, add_zero, Finset.sum_neg_distrib, hx1, neg_zero]
    · simp only [Wr.inv_a, hx0, add_zero, mul_neg, Finset.sum_neg_distrib, hx2, neg_zero]

theorem rank_bounds_model (M J : Subgroup Wr) (hJM : J ≤ M)
    (hJc : ∀ j ∈ J, ∀ k ∈ J, j * k = k * j) (hJcard : Nat.card J = 5 ^ 4)
    (hMcard : Nat.card M ≤ 5 ^ 5) (hMc : ∃ w ∈ M, w.c ≠ 0) :
    (∀ w ∈ M, w ∉ J → w.c ≠ 0) ∧ (∀ w ∈ M, ∀ j ∈ J, w * j * w⁻¹ ∈ J) ∧
    (∀ w ∈ ⁅J, M⁆, w ≠ 1 →
      w.c = 0 ∧ (Finset.univ.filter fun i => w.a i = 0).card ≤ 2) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨w₀, hw₀M, hw₀c⟩ := hMc
  have hJB : ∀ j ∈ J, j.c = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j₀, hj₀J, hj₀c⟩ := hcon
    let ev : J → ZMod 5 × ZMod 5 := fun k => ((k : Wr).a 0, (k : Wr).c)
    have hev : Function.Injective ev := by
      intro k k' hkk
      have hc : (k : Wr).c = (k' : Wr).c := congrArg Prod.snd hkk
      have ha0 : (k : Wr).a 0 = (k' : Wr).a 0 := congrArg Prod.fst hkk
      have e1 := congrArg (fun w : Wr => w.a) (hJc k k.2 j₀ hj₀J)
      have e2 := congrArg (fun w : Wr => w.a) (hJc k' k'.2 j₀ hj₀J)
      have hδ : ∀ i, ((k : Wr).a - (k' : Wr).a) i = ((k : Wr).a - (k' : Wr).a) (i - j₀.c) := by
        intro i
        have h1 := congrFun e1 i
        have h2 := congrFun e2 i
        simp only [Wr.mul_a] at h1 h2
        rw [hc] at h1
        simp only [Pi.sub_apply]
        linear_combination h1 - h2
      have hz := eq_zero_of_shift hj₀c hδ (by simp [ha0])
      refine Subtype.ext (Wr.ext (funext fun i => ?_) hc)
      have := hz i
      simp only [Pi.sub_apply] at this
      exact sub_eq_zero.mp this
    have := Nat.card_le_card_of_injective ev hev
    rw [hJcard, Nat.card_prod] at this
    simp [Nat.card_zmod] at this
  let φ : M →* Multiplicative (ZMod 5) := Wr.cHom.comp M.subtype
  have hφsurj : Function.Surjective φ := by
    intro a
    refine ⟨⟨w₀ ^ ((Multiplicative.toAdd a * (w₀.c)⁻¹).val), pow_mem hw₀M _⟩, ?_⟩
    change Multiplicative.ofAdd ((w₀ ^ ((Multiplicative.toAdd a * (w₀.c)⁻¹).val)).c) = a
    rw [Wr.pow_c, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hw₀c, mul_one]
    rfl
  have hindex : φ.ker.index = 5 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hker_card : Nat.card φ.ker * 5 = Nat.card M := by
    have h := Subgroup.card_mul_index φ.ker
    rw [hindex] at h
    exact h
  have hJ'le : J.subgroupOf M ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have := hJB _ (Subgroup.mem_subgroupOf.mp hx)
    change Multiplicative.ofAdd (x : Wr).c = 1
    rw [this]
    rfl
  have hJ'card : Nat.card (J.subgroupOf M) = 5 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJM).toEquiv, hJcard]
  have hJ'eq : J.subgroupOf M = φ.ker := by
    refine Subgroup.eq_of_le_of_card_ge hJ'le ?_
    have h1 := hMcard
    have e5 : (5 : ℕ) ^ 5 = 3125 := by norm_num
    have e4 : (5 : ℕ) ^ 4 = 625 := by norm_num
    rw [e5] at h1
    rw [hJ'card, e4]
    omega
  have hkercard : Nat.card φ.ker = 5 ^ 4 := by rw [← hJ'eq]; exact hJ'card
  have hMJ : ∀ w ∈ M, w.c = 0 → w ∈ J := by
    intro w hw hc0
    have : (⟨w, hw⟩ : M) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd w.c = 1
      rw [hc0]
      rfl
    rw [← hJ'eq] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hi : ∀ w ∈ M, w ∉ J → w.c ≠ 0 := fun w hw hwJ hc0 => hwJ (hMJ w hw hc0)
  have hMcardEq : Nat.card M = 5 ^ 5 := by
    rw [← hker_card, hkercard]
    norm_num
  have hMindex : M.index = 5 := by
    have h := Subgroup.card_mul_index M
    rw [hMcardEq, card_Wr] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5 ^ 5) (by rw [h]; norm_num)
  have hMn : M.Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    rw [hMindex, card_Wr, Nat.Prime.pow_minFac Nat.prime_five (by norm_num)]
  obtain ⟨g₁, hg₁M, hg₁c⟩ : ∃ g₁ ∈ M, g₁.c = 1 := by
    refine ⟨w₀ ^ ((w₀.c)⁻¹).val, pow_mem hw₀M _, ?_⟩
    rw [Wr.pow_c, nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hw₀c]
  have hdiff : ∀ u : ZMod 5 → ZMod 5, Wr.mk0 (fun i => u i - u (i - 1)) ∈ J := by
    intro u
    have h1 : Wr.mk0 u * g₁ * (Wr.mk0 u)⁻¹ ∈ M := hMn.conj_mem g₁ hg₁M (Wr.mk0 u)
    have h2 : ⁅Wr.mk0 u, g₁⁆ ∈ M := by
      rw [commutatorElement_def]
      exact M.mul_mem h1 (M.inv_mem hg₁M)
    rw [Wr.comm_mk0, hg₁c] at h2
    exact hMJ _ h2 rfl
  have hsumJ : ∀ v : ZMod 5 → ZMod 5, ∑ i, v i = 0 → Wr.mk0 v ∈ J := by
    intro v hv
    obtain ⟨u, hu⟩ := exists_sub_shift hv
    have : v = fun i => u i - u (i - 1) := funext fun i => (hu i).symm
    rw [this]
    exact hdiff u
  have hJsum : ∀ j ∈ J, ∑ i, j.a i = 0 := by
    intro j hj
    by_contra hσ
    have hjc : j.c = 0 := hJB j hj
    have hj' : j = Wr.mk0 j.a := Wr.ext rfl hjc
    have hBJ : ∀ w : ZMod 5 → ZMod 5, Wr.mk0 w ∈ J := by
      intro w
      set σ : ZMod 5 := ∑ i, j.a i with hσdef
      set t : ZMod 5 := (∑ i, w i) * σ⁻¹ with htdef
      have h1 : Wr.mk0 (w - t.val • j.a) ∈ J := by
        refine hsumJ _ ?_
        have e : ∑ i, (w - t.val • j.a) i = (∑ i, w i) - (t.val : ZMod 5) * σ := by
          rw [hσdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul]
        rw [e, ZMod.natCast_zmod_val, htdef, mul_assoc, inv_mul_cancel₀ hσ, mul_one, sub_self]
      have h2 : j ^ t.val ∈ J := pow_mem hj _
      have h3 : Wr.mk0 w = Wr.mk0 (w - t.val • j.a) * j ^ t.val := by
        have hjp : j ^ t.val = Wr.mk0 (t.val • j.a) := by
          conv_lhs => rw [hj']
          exact Wr.mk0_pow _ _
        rw [hjp, Wr.mk0_mul, sub_add_cancel]
      rw [h3]
      exact J.mul_mem h1 h2
    have := Nat.card_le_card_of_injective
      (fun w : ZMod 5 → ZMod 5 => (⟨Wr.mk0 w, hBJ w⟩ : J))
      (fun w w' h => by
        have := congrArg (fun x : J => (x : Wr).a) h
        exact this)
    rw [hJcard] at this
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card] at this
  have hnorm : ∀ w ∈ M, ∀ j ∈ J, w * j * w⁻¹ ∈ J := by
    intro w hw j hj
    refine hMJ _ (M.mul_mem (M.mul_mem hw (hJM hj)) (M.inv_mem hw)) ?_
    have := hJB j hj
    simp [Wr.mul_c, Wr.inv_c, this]
  refine ⟨hi, hnorm, ?_⟩
  have hle : ⁅J, M⁆ ≤ Cw := by
    rw [Subgroup.commutator_le]
    intro j hj m hm
    have hjc : j.c = 0 := hJB j hj
    have hj' : j = Wr.mk0 j.a := Wr.ext rfl hjc
    have hcomm : ⁅j, m⁆ = Wr.mk0 (fun i => j.a i - j.a (i - m.c)) := by
      conv_lhs => rw [hj']
      exact Wr.comm_mk0 _ _
    rw [hcomm]
    refine ⟨rfl, ?_, ?_⟩
    · change ∑ i, (j.a i - j.a (i - m.c)) = 0
      rw [Finset.sum_sub_distrib, sub_eq_zero]
      exact (Fintype.sum_equiv (Equiv.subRight m.c) _ _ (fun i => rfl)).symm
    · change ∑ i, i * (j.a i - j.a (i - m.c)) = 0
      have h1 : ∑ i : ZMod 5, i * j.a (i - m.c) = ∑ i : ZMod 5, (i + m.c) * j.a i :=
        Fintype.sum_equiv (Equiv.subRight m.c) _ _ (fun i => by simp)
      simp only [mul_sub, Finset.sum_sub_distrib, h1, add_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hJsum j hj]
      ring
  intro w hw hw1
  obtain ⟨hc0, hs1, hs2⟩ := hle hw
  refine ⟨hc0, weight_ge_three hs1 hs2 ?_⟩
  intro h0
  apply hw1
  exact Wr.ext (funext fun i => by rw [Wr.one_a]; exact congrFun h0 i) (by rw [hc0]; rfl)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
