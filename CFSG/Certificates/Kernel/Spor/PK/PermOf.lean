module

public import CFSG.Certificates.Kernel.Spor.PK.Ord
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.KS.PK

open Classical in
@[expose] noncomputable def permOf (n : Nat) (f : Nat → Nat) : Equiv.Perm (Fin n) :=
  if h : IsPermN n f then
    { toFun := fun i => ⟨f i, h.1 i i.isLt⟩
      invFun := fun i => ⟨finv n f i, finv_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt) f i⟩
      left_inv := fun i => Fin.ext (finv_apply h i.isLt)
      right_inv := fun i => Fin.ext (finv_spec h i.isLt).2 }
  else 1

variable {n : Nat} {f g : Nat → Nat}

theorem permOf_apply (hf : IsPermN n f) (i : Fin n) : (permOf n f i : Nat) = f i := by
  unfold permOf
  rw [dif_pos hf]
  rfl

theorem permOf_inv_apply (hf : IsPermN n f) (i : Fin n) :
    ((permOf n f)⁻¹ i : Nat) = finv n f i := by
  unfold permOf
  rw [dif_pos hf]
  rfl

theorem permOf_mul (hf : IsPermN n f) (hg : IsPermN n g) :
    permOf n f * permOf n g = permOf n fun x => f (g x) := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, permOf_apply hf, permOf_apply hg, permOf_apply (hf.comp hg)]

theorem permOf_inv (hf : IsPermN n f) : (permOf n f)⁻¹ = permOf n (finv n f) := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [permOf_inv_apply hf, permOf_apply hf.finv]

private theorem isPermN_congr (h : ∀ x < n, f x = g x) (hf : IsPermN n f) : IsPermN n g := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · rw [← h x hx]
    exact hf.1 x hx
  · rw [← h x hx, ← h y hy] at hxy
    exact hf.2 x hx y hy hxy

theorem permOf_congr (h : ∀ x < n, f x = g x) : permOf n f = permOf n g := by
  by_cases hf : IsPermN n f
  · have hg : IsPermN n g := isPermN_congr h hf
    refine Equiv.ext fun i => Fin.ext ?_
    rw [permOf_apply hf, permOf_apply hg]
    exact h i i.isLt
  · have hg : ¬ IsPermN n g := fun hg => hf (isPermN_congr (fun x hx => (h x hx).symm) hg)
    unfold permOf
    rw [dif_neg hf, dif_neg hg]

theorem permOf_eq_iff (hf : IsPermN n f) (hg : IsPermN n g) :
    permOf n f = permOf n g ↔ ∀ x < n, f x = g x := by
  refine ⟨fun h x hx => ?_, permOf_congr⟩
  have h1 := congrArg (fun σ : Equiv.Perm (Fin n) => (σ ⟨x, hx⟩ : Nat)) h
  rw [permOf_apply hf, permOf_apply hg] at h1
  exact h1

private theorem permOf_id : permOf n (fun x => x) = 1 := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [permOf_apply (isPermN_id n)]
  rfl

theorem permOf_eq_one_iff (hf : IsPermN n f) : permOf n f = 1 ↔ ∀ x < n, f x = x := by
  rw [← permOf_id (n := n), permOf_eq_iff hf (isPermN_id n)]

private theorem isPermN_itr (hf : IsPermN n f) : ∀ k, IsPermN n (itr f k)
  | 0 => isPermN_id n
  | k + 1 => hf.comp (isPermN_itr hf k)

theorem permOf_pow (hf : IsPermN n f) (k : Nat) : permOf n f ^ k = permOf n (itr f k) := by
  induction k with
  | zero => rw [pow_zero]; exact permOf_id.symm
  | succ k ih => rw [pow_succ', ih, permOf_mul hf (isPermN_itr hf k)]; rfl

theorem isPermN_val (σ : Equiv.Perm (Fin n)) :
    IsPermN n fun x => if h : x < n then (σ ⟨x, h⟩ : Nat) else x := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · simp only [dif_pos hx]
    exact (σ ⟨x, hx⟩).isLt
  · simp only [dif_pos hx, dif_pos hy] at hxy
    exact congrArg Fin.val (σ.injective (Fin.ext hxy))

theorem permOf_val (σ : Equiv.Perm (Fin n)) :
    permOf n (fun x => if h : x < n then (σ ⟨x, h⟩ : Nat) else x) = σ := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [permOf_apply (isPermN_val σ) i]
  simp [i.isLt]

private theorem itr_eq_iterate (f : Nat → Nat) (k x : Nat) : itr f k x = f^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ← ih]; rfl

private theorem exists_period (hf : IsPermN n f) {i : Nat} (hi : i < n) :
    ∃ p, 0 < p ∧ p ≤ n ∧ itr f p i = i := by
  let x : Fin n := ⟨i, hi⟩
  have hpos : 0 < Function.minimalPeriod (permOf n f) x :=
    Function.minimalPeriod_pos_of_mem_periodicPts ((permOf n f).injective.mem_periodicPts x)
  have hle : Function.minimalPeriod (permOf n f) x ≤ n := by
    simpa using Function.minimalPeriod_le_card (f := permOf n f) (x := x)
  refine ⟨Function.minimalPeriod (permOf n f) x, hpos, hle, ?_⟩
  have hper : ((permOf n f)^[Function.minimalPeriod (permOf n f) x]) x = x :=
    Function.isPeriodicPt_minimalPeriod (permOf n f) x
  have h1 := congrArg Fin.val hper
  rw [← Equiv.Perm.coe_pow] at h1
  rw [permOf_pow hf, permOf_apply (isPermN_itr hf _)] at h1
  exact h1

private theorem cycW_minimalPeriod (f : Nat → Nat) (i : Nat) :
    ∀ K k, k < Function.minimalPeriod f i → Function.minimalPeriod f i ≤ k + K →
      cycW f i K (f^[k] i) (k + 1) = Function.minimalPeriod f i := by
  intro K
  induction K with
  | zero => intro k hk hK; omega
  | succ K ih =>
    intro k hk hK
    rw [cycW]
    have hs : f (f^[k] i) = f^[k + 1] i := (Function.iterate_succ_apply' f k i).symm
    rw [hs]
    by_cases hP : k + 1 = Function.minimalPeriod f i
    · rw [if_pos (by rw [hP]; exact Function.isPeriodicPt_minimalPeriod f i), hP]
    · rw [if_neg]
      · exact ih (k + 1) (by omega) (by omega)
      · intro h
        exact Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (n := k + 1) (by omega)
          (by omega) h

private theorem cycF_eq (hf : IsPermN n f) {i : Nat} (hi : i < n) :
    cycF n f i = Function.minimalPeriod f i := by
  obtain ⟨p, hp0, hpn, hp⟩ := exists_period hf hi
  have hper : Function.IsPeriodicPt f p i := by
    show f^[p] i = i
    rw [← itr_eq_iterate]
    exact hp
  have hpos : 0 < Function.minimalPeriod f i := hper.minimalPeriod_pos hp0
  have hle : Function.minimalPeriod f i ≤ n := (hper.minimalPeriod_le hp0).trans hpn
  have := cycW_minimalPeriod f i n 0 hpos (by omega)
  simpa [cycF] using this

private theorem itr_fix_iff (hf : IsPermN n f) {i : Nat} (hi : i < n) (m : Nat) :
    itr f m i = i ↔ cycF n f i ∣ m := by
  rw [cycF_eq hf hi, itr_eq_iterate]
  exact Function.isPeriodicPt_iff_minimalPeriod_dvd

private theorem foldr_lcm_dvd_iff' (a : Nat → Nat) (m : Nat) : ∀ l : List Nat,
    l.foldr (fun i s => Nat.lcm s (a i)) 1 ∣ m ↔ ∀ i ∈ l, a i ∣ m
  | [] => by simp
  | i :: l => by
    rw [List.foldr_cons, Nat.lcm_dvd_iff, foldr_lcm_dvd_iff' a m l]
    simp only [List.mem_cons, forall_eq_or_imp]
    exact and_comm

private theorem ordF_dvd_iff' (n : Nat) (f : Nat → Nat) (m : Nat) :
    ordF n f ∣ m ↔ ∀ i < n, cycF n f i ∣ m := by
  unfold ordF
  rw [foldr_lcm_dvd_iff']
  simp only [List.mem_range]

private theorem pow_eq_one_iff (hf : IsPermN n f) (m : Nat) :
    permOf n f ^ m = 1 ↔ ordF n f ∣ m := by
  rw [permOf_pow hf, permOf_eq_one_iff (isPermN_itr hf m), ordF_dvd_iff']
  exact ⟨fun h i hi => (itr_fix_iff hf hi m).1 (h i hi),
    fun h i hi => (itr_fix_iff hf hi m).2 (h i hi)⟩

theorem orderOf_permOf (hf : IsPermN n f) : orderOf (permOf n f) = ordF n f :=
  Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.2 ((pow_eq_one_iff hf _).2 (Nat.dvd_refl _)))
    ((pow_eq_one_iff hf _).1 (pow_orderOf_eq_one _))

end CFSG.KS.PK

end
