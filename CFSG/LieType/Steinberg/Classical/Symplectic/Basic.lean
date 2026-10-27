module

public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.LieType.Universal.SymplecticExtras.Commutator
public import CFSG.LieType.Steinberg.OfCartan
public import CFSG.LieType.Steinberg.Statement

public noncomputable section

namespace CFSG.LieType.Steinberg.Sp

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank

variable (n : ℕ) (F : Type) [Field F]

open _root_.Classical in
@[expose] def x (γ : Fin n → ℤ) (c : F) : StatedSp n F :=
  if h : ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ then elt h.choose c else 1

abbrev Φ : RootSystem (Fin n) :=
  RootSystem.ofCartan (rootDatum n F).isFiniteType (rootDatum n F).divisible

variable {n F}

theorem Φ_roots : (Φ n F).roots = roots (isFiniteType_cartanC n) ∅ := rfl

theorem x_eq {γ : Fin n → ℤ} {r : RootSubgroupIndex n} (hr : stdVec r = toStd n γ) (c : F) :
    x n F γ c = elt r c := by
  have h : ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ := ⟨r, hr⟩
  rw [x, dite_eq_left h, stdVec_injective (h.choose_spec.trans hr.symm)]

theorem x_of_not {γ : Fin n → ℤ} (h : ¬∃ r : RootSubgroupIndex n, stdVec r = toStd n γ)
    (c : F) : x n F γ c = 1 := by
  rw [x, dite_eq_right h]

theorem isParametrization :
    IsParametrization (Φ := Φ n F) (rootDatum n F).rootGroup (x n F) := by
  intro γ hγ
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  refine ⟨fun g => ?_, fun c d => ?_, fun c d hcd => ?_⟩
  · change g ∈ rootGroup n F γ ↔ _
    rw [mem_rootGroup_iff hr]
    simp only [x_eq hr]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  · rw [x_eq hr, x_eq hr, x_eq hr, elt_add]
  · rw [x_eq hr, x_eq hr] at hcd
    exact elt_injective r hcd

theorem wt_injective : Function.Injective (wt (n := n)) := by
  intro a b h
  rcases a with i | i <;> rcases b with j | j <;>
    · have h1 := congrFun h i
      have h2 := congrFun h j
      simp only [wt, Pi.neg_apply, Pi.single_apply] at h1 h2
      split_ifs at h1 h2 <;> first | (subst_vars; rfl) | omega

theorem dot_wt_self (a : Fin n ⊕ Fin n) : wt a ⬝ᵥ wt a = 1 := by
  rcases a with i | i <;> simp [wt]

theorem wt_swap (a : Fin n ⊕ Fin n) : wt (Sum.swap a) = -wt a := by
  rcases a with i | i <;> simp [wt]

theorem exists_wt_of_dot_eq_one {w : Fin n → ℤ} (h : w ⬝ᵥ w = 1) : ∃ a, wt a = w := by
  have hsq : ∀ k, 0 ≤ w k * w k := fun k => mul_self_nonneg _
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra hne
    push Not at hne
    have : w ⬝ᵥ w = 0 := by simp [dotProduct, hne]
    omega
  have hk0 := mul_self_pos.2 hk
  have hrest : ∀ j, j ≠ k → w j = 0 := by
    intro j hj
    have hle : ∑ x ∈ {j, k}, w x * w x ≤ w ⬝ᵥ w :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => hsq x
    rw [Finset.sum_pair hj] at hle
    exact mul_self_eq_zero.mp (le_antisymm (by omega) (hsq j))
  have hk1 : w k * w k = 1 := by
    have hle : w k * w k ≤ w ⬝ᵥ w := Finset.single_le_sum (fun j _ => hsq j) (Finset.mem_univ k)
    omega
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hk1 with h1 | h1
  · refine ⟨.inl k, funext fun j => ?_⟩
    by_cases hj : j = k
    · subst hj
      simp [wt, h1]
    · simp [wt, hj, hrest j hj]
  · refine ⟨.inr k, funext fun j => ?_⟩
    by_cases hj : j = k
    · subst hj
      simp [wt, h1]
    · simp [wt, hj, hrest j hj]

theorem dot_sub_self (u v : Fin n → ℤ) :
    (u - v) ⬝ᵥ (u - v) = u ⬝ᵥ u - 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm v u]
  ring

theorem dot_add_self (u v : Fin n → ℤ) :
    (u + v) ⬝ᵥ (u + v) = u ⬝ᵥ u + 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
  simp only [add_dotProduct, dotProduct_add, dotProduct_comm v u]
  ring

theorem dot_self_nonneg (v : Fin n → ℤ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun k _ => mul_self_nonneg (v k)

theorem dot_le_four_of_isPosWt {v : Fin n → ℤ} (hv : IsPosWt v) : v ⬝ᵥ v ≤ 4 := by
  obtain ⟨a, b, rfl⟩ := hv
  have h1 := dot_sub_self (wt a) (wt b)
  have h2 := dot_add_self (wt a) (wt b)
  have h3 := dot_self_nonneg (wt a + wt b)
  rw [dot_wt_self, dot_wt_self] at h1 h2
  omega

theorem stdVec_dot_even {r : RootSubgroupIndex n} (h : stdVec r ⬝ᵥ stdVec r = 4)
    (v : Fin n → ℤ) : v ⬝ᵥ stdVec r % 2 = 0 := by
  cases r with
  | positiveLong i =>
    rw [show stdVec (.positiveLong i) = 2 • Pi.single i 1 from rfl, dotProduct_smul,
      nsmul_eq_mul]
    push_cast
    omega
  | negativeLong i =>
    rw [show stdVec (.negativeLong i) = -(2 • Pi.single i 1) from rfl, dotProduct_neg,
      dotProduct_smul, nsmul_eq_mul]
    push_cast
    omega
  | difference i j hij => simp [stdVec, dotProduct_sub, hij, Ne.symm hij] at h
  | positiveSum i j hij => simp [stdVec, dotProduct_add, hij.ne, hij.ne'] at h
  | negativeSum i j hij => simp [stdVec, dotProduct_add, hij.ne, hij.ne'] at h

@[expose] def Ez : RootSubgroupIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ
  | .positiveLong i => single (.inl i) (.inr i) 1
  | .negativeLong i => single (.inr i) (.inl i) 1
  | .difference i j _ => single (.inl i) (.inl j) 1 - single (.inr j) (.inr i) 1
  | .positiveSum i j _ => single (.inl i) (.inr j) 1 + single (.inl j) (.inr i) 1
  | .negativeSum i j _ => single (.inr i) (.inl j) 1 + single (.inr j) (.inl i) 1

variable (F) in
theorem E_eq_map (r : RootSubgroupIndex n) : E F r = (Ez r).map (Int.castRingHom F) := by
  ext a b
  cases r <;> simp [E, Ez, single_apply]

theorem cast_Ez (r : RootSubgroupIndex n) (a b : Fin n ⊕ Fin n) :
    ((Ez r a b : ℤ) : F) = E F r a b := by
  rw [E_eq_map]
  simp

theorem Ez_ne_zero_iff {r : RootSubgroupIndex n} {a b : Fin n ⊕ Fin n} :
    Ez r a b ≠ 0 ↔ wt a - wt b = stdVec r := by
  rw [← (Int.cast_injective (α := ℚ)).ne_iff, Int.cast_zero, cast_Ez]
  constructor
  · exact hasDeg_E r a b
  · intro h
    rcases eq_pos_of_wt_sub r a b h with h' | h'
    · rw [Prod.ext_iff] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [E_pos1]
      exact one_ne_zero
    · rw [Prod.ext_iff] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [E_pos2]
      cases r <;> simp [sgn2]

theorem natAbs_Ez {r : RootSubgroupIndex n} {a b : Fin n ⊕ Fin n} (h : Ez r a b ≠ 0) :
    (Ez r a b).natAbs = 1 := by
  cases r <;> simp only [Ez, Matrix.sub_apply, Matrix.add_apply, single_apply] at h ⊢ <;>
    split_ifs at h ⊢ <;> (try simp_all) <;> grind

@[expose] def κ (a b : Fin n ⊕ Fin n) : ℤ := if a.isLeft = b.isLeft then -1 else 1

theorem Ez_symm (r : RootSubgroupIndex n) (a b : Fin n ⊕ Fin n) :
    Ez r a b = κ a b * Ez r (Sum.swap b) (Sum.swap a) := by
  rcases a with p | p <;> rcases b with q | q <;> cases r <;>
    simp [Ez, κ, single_apply] <;> grind

theorem κ_swap_mul (a b : Fin n ⊕ Fin n) :
    κ a (Sum.swap b) * κ (Sum.swap b) (Sum.swap a) = -1 := by
  rcases a with p | p <;> rcases b with q | q <;> simp [κ]

theorem Ez_mul_apply_eq {r : RootSubgroupIndex n} {x y z : Fin n ⊕ Fin n}
    (hz : wt z = wt x - stdVec r) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) :
    (Ez r * M) x y = Ez r x z * M z y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single z]
  · intro w _ hw
    apply mul_eq_zero_of_left
    by_contra hne
    apply hw
    apply wt_injective
    rw [hz, ← Ez_ne_zero_iff.1 hne, sub_sub_cancel]
  · intro h
    exact absurd (Finset.mem_univ z) h

theorem Ez_mul_apply_eq_zero {r : RootSubgroupIndex n} {x y : Fin n ⊕ Fin n}
    (h : ∀ z, wt z ≠ wt x - stdVec r) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) :
    (Ez r * M) x y = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  apply mul_eq_zero_of_left
  by_contra hne
  exact h w (by rw [← Ez_ne_zero_iff.1 hne, sub_sub_cancel])

theorem Ez_mul_Ez_apply (r s : RootSubgroupIndex n) {x y : Fin n ⊕ Fin n}
    (hxy : wt x - wt y = stdVec r + stdVec s) :
    ((wt x - stdVec r) ⬝ᵥ (wt x - stdVec r) = 1 → ((Ez r * Ez s) x y).natAbs = 1) ∧
      ((wt x - stdVec r) ⬝ᵥ (wt x - stdVec r) ≠ 1 → (Ez r * Ez s) x y = 0) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨z, hz⟩ := exists_wt_of_dot_eq_one h
    rw [Ez_mul_apply_eq hz, Int.natAbs_mul, natAbs_Ez, natAbs_Ez]
    · rw [Ez_ne_zero_iff, hz]
      calc wt x - stdVec r - wt y = (wt x - wt y) - stdVec r := by abel
        _ = stdVec s := by rw [hxy]; abel
    · rw [Ez_ne_zero_iff, hz, sub_sub_cancel]
  · refine Ez_mul_apply_eq_zero (fun z hz => h ?_) _
    rw [← hz]
    exact dot_wt_self z

theorem coeff11_spec {r s t : RootSubgroupIndex n} (ht : stdVec t = stdVec r + stdVec s) :
    ((Ez r * Ez s - Ez s * Ez r) (pos1 t).1 (pos1 t).2).natAbs = 1 ∨
      (((Ez r * Ez s - Ez s * Ez r) (pos1 t).1 (pos1 t).2).natAbs = 2 ∧
        stdVec t ⬝ᵥ stdVec t = 4) := by
  have ha := dot_stdVec r
  have hb := dot_stdVec s
  have htt := dot_stdVec t
  rw [ht] at htt
  have hxy : wt (pos1 t).1 - wt (pos1 t).2 = stdVec r + stdVec s := (wt_pos1 t).trans ht
  set x := (pos1 t).1
  set y := (pos1 t).2
  set e := stdVec r with he
  set f := stdVec s with hf
  have hx := dot_wt_self x
  have hy := dot_wt_self y
  have hpe : e ⬝ᵥ e = 2 ∨ (e ⬝ᵥ e = 4 ∧ wt x ⬝ᵥ e % 2 = 0) :=
    ha.imp_right fun h => ⟨h, stdVec_dot_even h (wt x)⟩
  have hpf : f ⬝ᵥ f = 2 ∨ (f ⬝ᵥ f = 4 ∧ wt x ⬝ᵥ f % 2 = 0) :=
    hb.imp_right fun h => ⟨h, stdVec_dot_even h (wt x)⟩
  have hD1 := dot_sub_self (wt x) e
  have hD2 := dot_sub_self (wt x) f
  have hn1 := dot_self_nonneg (wt x - e)
  have hn2 := dot_self_nonneg (wt x - f)
  have hsum : wt x ⬝ᵥ e + wt x ⬝ᵥ f = 1 - wt x ⬝ᵥ wt y := by
    rw [← dotProduct_add, ← hxy, dotProduct_sub, hx]
  have hnorm : (e + f) ⬝ᵥ (e + f) = 2 - 2 * (wt x ⬝ᵥ wt y) := by
    rw [← hxy, dot_sub_self, hx, hy]
    ring
  rw [hx] at hD1 hD2
  have key1 := Ez_mul_Ez_apply r s hxy
  have key2 := Ez_mul_Ez_apply s r (hxy.trans (add_comm _ _))
  rw [Matrix.sub_apply]
  by_cases h1 : (wt x - e) ⬝ᵥ (wt x - e) = 1 <;> by_cases h2 : (wt x - f) ⬝ᵥ (wt x - f) = 1
  ·
    right
    have hm : wt x ⬝ᵥ wt y = -1 := by
      rcases hpe with hpe | hpe <;> rcases hpf with hpf | hpf <;> rcases htt with htt | htt <;>
        omega
    refine ⟨?_, by rw [ht, hnorm, hm]; norm_num⟩
    have hyx : y = Sum.swap x := by
      have h0 : (wt x + wt y) ⬝ᵥ (wt x + wt y) = 0 := by
        rw [dot_add_self, hx, hy, hm]
        norm_num
      apply wt_injective
      rw [wt_swap, eq_neg_iff_add_eq_zero, add_comm]
      exact dotProduct_self_eq_zero.1 h0
    obtain ⟨z, hz⟩ := exists_wt_of_dot_eq_one h1
    have hz' : wt (Sum.swap z) = wt x - f := by
      have hwy : wt y = -wt x := by rw [hyx, wt_swap]
      rw [wt_swap, hz]
      have : f = wt x - wt y - e := by rw [hxy]; abel
      rw [this, hwy]
      abel
    rw [Ez_mul_apply_eq hz, Ez_mul_apply_eq hz', hyx, Ez_symm s x (Sum.swap z),
      Ez_symm r (Sum.swap z) (Sum.swap x), Sum.swap_swap, Sum.swap_swap]
    have hk := κ_swap_mul x z
    have hval : (Ez r x z * Ez s z (Sum.swap x)).natAbs = 1 := by
      have := key1.1 h1
      rwa [Ez_mul_apply_eq hz, hyx] at this
    have hrw : Ez r x z * Ez s z (Sum.swap x) -
        κ x (Sum.swap z) * Ez s z (Sum.swap x) * (κ (Sum.swap z) (Sum.swap x) * Ez r x z) =
        2 * (Ez r x z * Ez s z (Sum.swap x)) := by
      linear_combination (-(Ez r x z * Ez s z (Sum.swap x))) * hk
    rw [hrw, Int.natAbs_mul, hval]
    rfl
  · left
    rw [key2.2 h2, sub_zero]
    exact key1.1 h1
  · left
    rw [key1.2 h1, zero_sub, Int.natAbs_neg]
    exact key2.1 h2
  · exfalso
    rcases hpe with hpe | hpe <;> rcases hpf with hpf | hpf <;> rcases htt with htt | htt <;>
      omega

theorem coeff21_spec {r s t : RootSubgroupIndex n} (ht : stdVec t = 2 • stdVec r + stdVec s)
    (hrs : stdVec r + stdVec s ≠ 0) :
    ((Ez r * Ez s * Ez r) (pos1 t).1 (pos1 t).2).natAbs = 1 := by
  have ha := dot_stdVec r
  have hb := dot_stdVec s
  have htt := dot_stdVec t
  have h2ef := dot_comb (stdVec r) (stdVec s) 2 1
  rw [one_smul] at h2ef
  rw [ht, h2ef] at htt
  push_cast at htt
  have hxy : wt (pos1 t).1 - wt (pos1 t).2 = 2 • stdVec r + stdVec s := (wt_pos1 t).trans ht
  set x := (pos1 t).1
  set y := (pos1 t).2
  set e := stdVec r with he
  set f := stdVec s with hf
  have hx := dot_wt_self x
  have hy := dot_wt_self y
  have hef : 0 < (e + f) ⬝ᵥ (e + f) :=
    lt_of_le_of_ne (dot_self_nonneg _) fun h => hrs (dotProduct_self_eq_zero.1 h.symm)
  have hef' := dot_add_self e f
  have hD1 := dot_sub_self (wt x) e
  have hD3 := dot_sub_self (wt x) (e + f)
  rw [dotProduct_add] at hD3
  have hn1 := dot_self_nonneg (wt x - e)
  have hn3 := dot_self_nonneg (wt x - (e + f))
  have hsum : 2 * (wt x ⬝ᵥ e) + wt x ⬝ᵥ f = 1 - wt x ⬝ᵥ wt y := by
    have h := congrArg (wt x ⬝ᵥ ·) hxy
    rw [dotProduct_sub, dotProduct_add, dotProduct_smul, hx, nsmul_eq_mul] at h
    push_cast at h
    linarith
  have hnorm : (2 • e + f) ⬝ᵥ (2 • e + f) = 2 - 2 * (wt x ⬝ᵥ wt y) := by
    rw [← hxy, dot_sub_self, hx, hy]
    ring
  rw [h2ef] at hnorm
  push_cast at hnorm
  rw [hx] at hD1 hD3
  have hD1' : (wt x - e) ⬝ᵥ (wt x - e) = 1 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases htt with htt | htt <;> omega
  have hD3' : (wt x - (e + f)) ⬝ᵥ (wt x - (e + f)) = 1 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases htt with htt | htt <;> omega
  obtain ⟨z₁, hz₁⟩ := exists_wt_of_dot_eq_one hD1'
  obtain ⟨z₂, hz₂⟩ := exists_wt_of_dot_eq_one hD3'
  have hz₂' : wt z₂ = wt z₁ - f := by rw [hz₁, hz₂]; abel
  rw [Matrix.mul_assoc, Ez_mul_apply_eq hz₁, Ez_mul_apply_eq hz₂', Int.natAbs_mul,
    Int.natAbs_mul, natAbs_Ez, natAbs_Ez, natAbs_Ez]
  · rw [Ez_ne_zero_iff, hz₂]
    calc wt x - (e + f) - wt y = (wt x - wt y) - (e + f) := by abel
      _ = e := by rw [hxy, two_nsmul]; abel
  · rw [Ez_ne_zero_iff, hz₂', sub_sub_cancel]
  · rw [Ez_ne_zero_iff, hz₁, sub_sub_cancel]

end CFSG.LieType.Steinberg.Sp
