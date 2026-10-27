module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Act

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {A : Type} [Group A] {B : Subgroup A} {t : A} {K : Subgroup (MulAut A)}
  {φ : (Fin 5 → ZMod 2) → A}

@[expose] def sec1011_phi6 (t : A) (φ : (Fin 5 → ZMod 2) → A) (v : Fin 6 → ZMod 2) : A :=
  t ^ (∑ i, v i).val * φ (∑ i : Fin 5, v i.succ • sec1011_wfour i)

private theorem sec1011a_u_even (v : Fin 6 → ZMod 2) :
    IsEvenVec (∑ i : Fin 5, v i.succ • sec1011_wfour i) := by
  revert v
  unfold IsEvenVec sec1011_wfour
  decide +kernel

private theorem sec1011a_u_add (v w : Fin 6 → ZMod 2) :
    (∑ i : Fin 5, (v + w) i.succ • sec1011_wfour i) =
      (∑ i : Fin 5, v i.succ • sec1011_wfour i)
        + (∑ i : Fin 5, w i.succ • sec1011_wfour i) := by
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

private theorem sec1011a_sum_add (v w : Fin 6 → ZMod 2) :
    (∑ i, (v + w) i) = (∑ i, v i) + (∑ i, w i) := by
  simp only [Pi.add_apply, Finset.sum_add_distrib]

private theorem sec1011a_ker_f3 (v : Fin 6 → ZMod 2) :
    ((∑ i, v i) = 0 ∧ (∑ i : Fin 5, v i.succ • sec1011_wfour i) = 0) ↔
      (v = 0 ∨ v = sec1011_one6) := by
  revert v
  unfold sec1011_one6 sec1011_wfour
  decide +kernel

private theorem sec1011a_f4 (s : ZMod 2) (x : Fin 5 → ZMod 2) (hx : IsEvenVec x) :
    ∃ v : Fin 6 → ZMod 2,
      (∑ i, v i) = s ∧ (∑ i : Fin 5, v i.succ • sec1011_wfour i) = x := by
  revert s x
  unfold IsEvenVec sec1011_wfour
  decide +kernel

private theorem sec1011a_sum_single (i : Fin 6) :
    (∑ j : Fin 6, (Pi.single i 1 : Fin 6 → ZMod 2) j) = 1 := by
  revert i
  decide +kernel

private theorem sec1011a_u_single_zero :
    (∑ j : Fin 5, (Pi.single 0 1 : Fin 6 → ZMod 2) j.succ • sec1011_wfour j) = 0 := by
  unfold sec1011_wfour
  decide +kernel

private theorem sec1011a_u_single_succ (k : Fin 5) :
    (∑ j : Fin 5, (Pi.single k.succ 1 : Fin 6 → ZMod 2) j.succ • sec1011_wfour j)
      = sec1011_wfour k := by
  revert k
  unfold sec1011_wfour
  decide +kernel

private theorem sec1011a_sum_zero :
    (∑ i : Fin 6, (0 : Fin 6 → ZMod 2) i) = 0 := by
  decide +kernel

private theorem sec1011a_u_zero :
    (∑ i : Fin 5, (0 : Fin 6 → ZMod 2) i.succ • sec1011_wfour i) = 0 := by
  unfold sec1011_wfour
  decide +kernel

private theorem sec1011a_sum_one6 : (∑ i : Fin 6, sec1011_one6 i) = 0 := by
  unfold sec1011_one6
  decide +kernel

private theorem sec1011a_u_one6 :
    (∑ i : Fin 5, sec1011_one6 i.succ • sec1011_wfour i) = 0 := by
  unfold sec1011_one6 sec1011_wfour
  decide +kernel

private theorem sec1011a_val_one : ((1 : ZMod 2)).val = 1 := by
  decide +kernel

private theorem sec1011a_zmod_two_cases (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s
  decide +kernel

private theorem sec1011a_zmod_two_eq (s : ZMod 2) (h : s ≠ 0) : s = 1 := by
  rcases sec1011a_zmod_two_cases s with h0 | h1
  · exact absurd h0 h
  · exact h1

private theorem sec1011a_zero_even : IsEvenVec (0 : Fin 5 → ZMod 2) := by
  simp [IsEvenVec]

private theorem sec1011a_pow_mod_two {t : A} (ht : t * t = 1) (n : ℕ) :
    t ^ (n % 2) = t ^ n := by
  have h2 : t ^ 2 = 1 := by rw [pow_two, ht]
  conv_rhs => rw [← Nat.mod_add_div n 2]
  rw [pow_add, pow_mul, h2, one_pow, mul_one]

private theorem sec1011a_pow_val_add {t : A} (ht : t * t = 1) (a b : ZMod 2) :
    t ^ (a + b).val = t ^ a.val * t ^ b.val := by
  rw [ZMod.val_add, sec1011a_pow_mod_two ht (a.val + b.val), pow_add]

theorem sec1011_phi6_hom (h : Sec1011Core B t K φ) (v w : Fin 6 → ZMod 2) :
    sec1011_phi6 t φ (v + w) = sec1011_phi6 t φ v * sec1011_phi6 t φ w := by
  letI : CommGroup A := { ‹Group A› with mul_comm := h.comm }
  have hhom : φ (∑ i : Fin 5, (v + w) i.succ • sec1011_wfour i) =
      φ (∑ i : Fin 5, v i.succ • sec1011_wfour i)
        * φ (∑ i : Fin 5, w i.succ • sec1011_wfour i) := by
    rw [sec1011a_u_add, h.hom _ _ (sec1011a_u_even v) (sec1011a_u_even w)]
  unfold sec1011_phi6
  rw [sec1011a_sum_add, hhom, sec1011a_pow_val_add h.t_sq]
  ac_rfl

theorem sec1011_phi6_single (h : Sec1011Core B t K φ) (i : Fin 6) :
    sec1011_phi6 t φ (Pi.single i 1) = sec1011_delta t φ i := by
  cases i using Fin.cases with
  | zero =>
      unfold sec1011_phi6 sec1011_delta
      rw [sec1011a_sum_single 0, sec1011a_u_single_zero, h.map_zero, sec1011a_val_one, pow_one,
        mul_one]
      rfl
  | succ k =>
      unfold sec1011_phi6 sec1011_delta
      rw [sec1011a_sum_single k.succ, sec1011a_u_single_succ k, sec1011a_val_one, pow_one]
      rfl

theorem sec1011_phi6_ker (h : Sec1011Core B t K φ) (v : Fin 6 → ZMod 2) :
    sec1011_phi6 t φ v = 1 ↔ v = 0 ∨ v = sec1011_one6 := by
  constructor
  · intro hphi
    by_cases hs : (∑ i, v i) = 0
    · have h1 : φ (∑ i : Fin 5, v i.succ • sec1011_wfour i) = 1 := by
        have hphi' := hphi
        unfold sec1011_phi6 at hphi'
        rw [hs, ZMod.val_zero, pow_zero, one_mul] at hphi'
        exact hphi'
      have huv : (∑ i : Fin 5, v i.succ • sec1011_wfour i) = 0 :=
        h.inj _ _ (sec1011a_u_even v) sec1011a_zero_even (by rw [h1, h.map_zero])
      exact (sec1011a_ker_f3 v).1 ⟨hs, huv⟩
    · have hs1 : (∑ i, v i) = 1 := sec1011a_zmod_two_eq _ hs
      have h1 : t * φ (∑ i : Fin 5, v i.succ • sec1011_wfour i) = 1 := by
        have hphi' := hphi
        unfold sec1011_phi6 at hphi'
        rw [hs1, sec1011a_val_one, pow_one] at hphi'
        exact hphi'
      have htinv : t = (φ (∑ i : Fin 5, v i.succ • sec1011_wfour i))⁻¹ :=
        eq_inv_of_mul_eq_one_left h1
      have hmem : (φ (∑ i : Fin 5, v i.succ • sec1011_wfour i))⁻¹ ∈ B :=
        B.inv_mem (h.mem (sec1011a_u_even v))
      exact absurd (htinv.symm ▸ hmem) h.t_not_mem
  · rintro (rfl | rfl)
    · unfold sec1011_phi6
      rw [sec1011a_sum_zero, sec1011a_u_zero, h.map_zero, ZMod.val_zero, pow_zero, one_mul]
    · unfold sec1011_phi6
      rw [sec1011a_sum_one6, sec1011a_u_one6, h.map_zero, ZMod.val_zero, pow_zero, one_mul]

theorem sec1011_phi6_surj (h : Sec1011Core B t K φ) (a : A) : ∃ v, sec1011_phi6 t φ v = a := by
  rcases h.split a with ha | ha
  · obtain ⟨x, hx, hxφ⟩ := (h.mem_B a).1 ha
    obtain ⟨v, hvsum, hvu⟩ := sec1011a_f4 0 x hx
    refine ⟨v, ?_⟩
    have hphi : sec1011_phi6 t φ v = t ^ ((0 : ZMod 2)).val * φ x := by
      unfold sec1011_phi6
      rw [hvsum, hvu]
    rw [hphi, ZMod.val_zero, pow_zero, one_mul, hxφ]
  · obtain ⟨x, hx, hxφ⟩ := (h.mem_B (t * a)).1 ha
    obtain ⟨v, hvsum, hvu⟩ := sec1011a_f4 1 x hx
    refine ⟨v, ?_⟩
    have hphi : sec1011_phi6 t φ v = t ^ ((1 : ZMod 2)).val * φ x := by
      unfold sec1011_phi6
      rw [hvsum, hvu]
    rw [hphi, sec1011a_val_one, pow_one, hxφ, ← mul_assoc, h.t_sq, one_mul]

theorem sec1011_phi6_ext (hcomm : ∀ a b : A, a * b = b * a) (f g : (Fin 6 → ZMod 2) → A)
    (hf : ∀ v w, f (v + w) = f v * f w) (hg : ∀ v w, g (v + w) = g v * g w)
    (hfg : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  letI : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  have hzero_f : f 0 = 1 := by
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_left_cancel (by rw [mul_one]; exact h.symm)
  have hzero_g : g 0 = 1 := by
    have h := hg 0 0
    rw [add_zero] at h
    exact mul_left_cancel (by rw [mul_one]; exact h.symm)
  let F : (Fin 6 → ZMod 2) →+ Additive A :=
    { toFun := fun v => Additive.ofMul (f v)
      map_zero' := by rw [hzero_f]; rfl
      map_add' := fun v w => by rw [hf v w]; rfl }
  let G : (Fin 6 → ZMod 2) →+ Additive A :=
    { toFun := fun v => Additive.ofMul (g v)
      map_zero' := by rw [hzero_g]; rfl
      map_add' := fun v w => by rw [hg v w]; rfl }
  have hsingle : ∀ (i : Fin 6) (x : ZMod 2), F (Pi.single i x) = G (Pi.single i x) := by
    intro i x
    rcases sec1011a_zmod_two_cases x with rfl | rfl
    · rw [Pi.single_zero, map_zero F, map_zero G]
    · exact congrArg Additive.ofMul (hfg i)
  have hFG : F = G := AddMonoidHom.functions_ext (Additive A) F G hsingle
  funext v
  exact Additive.ofMul.injective (DFunLike.congr_fun hFG v)

theorem sec1011_phi6_act (h : Sec1011Core B t K φ) {α : MulAut A} (σ : Equiv.Perm (Fin 6))
    (hα : ∀ i, α (sec1011_delta t φ i) = sec1011_delta t φ (σ i))
    (v : Fin 6 → ZMod 2) : α (sec1011_phi6 t φ v) = sec1011_phi6 t φ (permVec σ v) := by
  have hf : ∀ v w, α (sec1011_phi6 t φ (v + w)) =
      α (sec1011_phi6 t φ v) * α (sec1011_phi6 t φ w) := by
    intro v w
    rw [sec1011_phi6_hom h v w, map_mul]
  have hg : ∀ v w, sec1011_phi6 t φ (permVec σ (v + w)) =
      sec1011_phi6 t φ (permVec σ v) * sec1011_phi6 t φ (permVec σ w) := by
    intro v w
    rw [sec1011_permVec_add, sec1011_phi6_hom h]
  have hfg : ∀ i, α (sec1011_phi6 t φ (Pi.single i 1)) =
      sec1011_phi6 t φ (permVec σ (Pi.single i 1)) := by
    intro i
    rw [sec1011_phi6_single h i, hα i, sec1011_permVec_single, sec1011_phi6_single h]
  exact congrFun (sec1011_phi6_ext h.comm (fun v => α (sec1011_phi6 t φ v))
    (fun v => sec1011_phi6 t φ (permVec σ v)) hf hg hfg) v

end CFSG.OddStandard.SmallF3.Omega