module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUCent

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section D130
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap

section PosEquiv

@[expose] def posEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (n + n) :=
  (Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv

theorem posEquiv_inl {n : ℕ} (a : Fin n) : (posEquiv n (Sum.inl a)).val = a.val := by
  simp [posEquiv]

theorem posEquiv_inr {n : ℕ} (a : Fin n) : (posEquiv n (Sum.inr a)).val = n + (n - 1 - a.val) := by
  simp [posEquiv, Fin.revPerm_apply]
  omega

theorem posEquiv_swap {n : ℕ} (z : Fin n ⊕ Fin n) :
    posEquiv n z.swap = Fin.rev (posEquiv n z) := by
  rcases z with a | a
  · apply Fin.ext
    simp only [Sum.swap_inl, Fin.val_rev, posEquiv_inr, posEquiv_inl]
    have := a.isLt
    omega
  · apply Fin.ext
    simp only [Sum.swap_inr, Fin.val_rev, posEquiv_inr, posEquiv_inl]
    have := a.isLt
    omega

end PosEquiv


section MatD

variable (n : ℕ) (F : Type) [Field F]

@[expose] noncomputable def matD : spinGroup (quadPlus n F) →* Matrix (Fin (n + n)) (Fin (n + n)) F :=
  (Matrix.reindexAlgEquiv F F (posEquiv n)).toAlgHom.toMonoidHom.comp
    ((Units.coeHom _).comp (spinMatrix (quadPlus n F)))

variable {n F}

@[expose] noncomputable def Smat (x : spinGroup (quadPlus n F)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  ((spinMatrix (quadPlus n F) x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)

theorem matD_apply (x : spinGroup (quadPlus n F)) (u v : Fin (n + n)) :
    matD n F x u v = Smat x ((posEquiv n).symm u) ((posEquiv n).symm v) := by
  simp [matD, Matrix.reindexAlgEquiv_apply, Smat]

theorem Smat_polar (x : spinGroup (quadPlus n F)) (v w : Fin n ⊕ Fin n → F) :
    polar (quadPlus n F) (Smat x *ᵥ v) (Smat x *ᵥ w) = polar (quadPlus n F) v w := by
  have h : ∀ v, quadPlus n F (Smat x *ᵥ v) = quadPlus n F v := spinMatrix_mem (quadPlus n F) x
  unfold QuadraticMap.polar
  rw [← Matrix.mulVec_add, h, h, h]

theorem polar_quadPlus_eq (v w : Fin n ⊕ Fin n → F) :
    polar (quadPlus n F) v w = ∑ z, v z * w z.swap := by
  rw [polar_quadPlus, Fintype.sum_sum_type]
  simp only [Sum.swap_inl, Sum.swap_inr]
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem matD_unit (x : spinGroup (quadPlus n F)) (a b : Fin (n + n)) :
    ∑ t, matD n F x t a * matD n F x (Fin.rev t) b = if b = Fin.rev a then 1 else 0 := by
  have key := Smat_polar x (Pi.single ((posEquiv n).symm a) 1) (Pi.single ((posEquiv n).symm b) 1)
  rw [polar_quadPlus_eq, polar_quadPlus_eq] at key
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at key
  set a' := (posEquiv n).symm a with ha'
  set b' := (posEquiv n).symm b with hb'
  have hR : (∑ x : Fin n ⊕ Fin n, if x.swap = b' then (if x = a' then (1 : F) else 0) else 0) =
      if b = Fin.rev a then 1 else 0 := by
    rw [Finset.sum_eq_single a']
    · have hiff : (a'.swap = b') ↔ (b = Fin.rev a) := by
        constructor
        · intro h
          have : b = posEquiv n b' := by rw [hb']; simp
          rw [this, ← h, posEquiv_swap, ha']
          simp
        · intro h
          rw [hb', h, ha']
          have : (posEquiv n).symm (Fin.rev a) = ((posEquiv n).symm a).swap := by
            apply (posEquiv n).injective
            rw [Equiv.apply_symm_apply, posEquiv_swap, Equiv.apply_symm_apply]
          rw [this]
      by_cases h : a'.swap = b'
      · rw [if_pos h, if_pos rfl, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
    · intro x _ hx
      simp [hx]
    · simp
  rw [hR] at key
  rw [← key, ← (posEquiv n).sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [matD_apply, matD_apply, ← posEquiv_swap]
  simp only [Equiv.symm_apply_apply]
  rfl



theorem matD_quad (x : spinGroup (quadPlus n F)) (c : Fin (n + n)) :
    ∑ i : Fin n, matD n F x (posEquiv n (Sum.inl i)) c * matD n F x (posEquiv n (Sum.inr i)) c = 0 := by
  have h : ∀ v, quadPlus n F (Smat x *ᵥ v) = quadPlus n F v := spinMatrix_mem (quadPlus n F) x
  have key := h (Pi.single ((posEquiv n).symm c) 1)
  rw [quadPlus_apply, quadPlus_apply] at key
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at key
  have hz : (∑ i : Fin n, (Pi.single ((posEquiv n).symm c) (1 : F) : Fin n ⊕ Fin n → F) (Sum.inl i) *
      (Pi.single ((posEquiv n).symm c) (1 : F) : Fin n ⊕ Fin n → F) (Sum.inr i)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : (Sum.inl i : Fin n ⊕ Fin n) = (posEquiv n).symm c
    · have h2 : (Sum.inr i : Fin n ⊕ Fin n) ≠ (posEquiv n).symm c := by
        rw [← h1]; simp
      simp [Pi.single_apply, h1, h2]
    · simp [Pi.single_apply, h1]
  rw [hz] at key
  rw [← key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [matD_apply, matD_apply]
  simp

theorem matD_injective (hF : (2 : F) = 0) : Function.Injective (matD n F) := by
  intro x y hxy
  have h1 : Smat x = Smat y := by
    ext a b
    have := congrFun (congrFun hxy (posEquiv n a)) (posEquiv n b)
    simpa [matD_apply] using this
  have h2 : spinMatrix (quadPlus n F) x = spinMatrix (quadPlus n F) y := Units.ext h1
  have hk := ker_spinMatrix_quadPlus_eq_bot (n := n) (K := F) hF
  have : x⁻¹ * y ∈ (spinMatrix (quadPlus n F)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  rw [hk, Subgroup.mem_bot] at this
  exact inv_mul_eq_one.mp this

end MatD


section Gamma

open CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin.PlusCT
  CFSG.LieType.Steinberg.SpinFrame

variable {n : ℕ}

@[expose] def mvec (z : Fin n ⊕ Fin n) : Fin n → ℤ := fun k =>
  let s : ℤ := Sum.elim (fun _ => 1) (fun _ => -1) z
  let c : ℕ := (Sum.elim (fun a => a.val) (fun a => a.val) z)
  if k.val + 3 ≤ n then 2 * s * (if c ≤ k.val then 1 else 0)
  else if k.val + 2 = n then s * (if c + 1 = n then -1 else 1)
  else s

theorem toStdD_mvec (hn : 3 ≤ n) (z : Fin n ⊕ Fin n) : toStdD n (mvec z) = (2 : ℤ) • plusWt z := by
  funext a
  have ha := a.isLt
  rcases z with c | c <;>
  · by_cases h0 : 0 < a.val <;> by_cases h2 : a.val + 2 = n <;>
    · simp [toStdD, mvec, plusWt, Pi.single_apply, Fin.ext_iff, h0, h2]
      simp only [Fin.le_def]
      split_ifs <;> omega

theorem mvec_sub_even (x y : Fin n ⊕ Fin n) (k : Fin n) : (2 : ℤ) ∣ mvec x k - mvec y k := by
  rcases x with a | a <;> rcases y with b | b <;>
  · simp only [mvec, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> omega

@[expose] def Dgamma (x y : Fin n ⊕ Fin n) : Fin n → ℤ := fun k => (mvec x k - mvec y k) / 2

theorem two_mul_Dgamma (x y : Fin n ⊕ Fin n) (k : Fin n) :
    2 * Dgamma x y k = mvec x k - mvec y k := by
  have := mvec_sub_even x y k
  unfold Dgamma
  omega

theorem toStdD_Dgamma (hn : 3 ≤ n) (x y : Fin n ⊕ Fin n) : toStdD n (Dgamma x y) = plusWt x - plusWt y := by
  have h2 : (2 : ℤ) • Dgamma x y = mvec x - mvec y := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    exact two_mul_Dgamma x y k
  have h3 : (2 : ℤ) • toStdD n (Dgamma x y) = (2 : ℤ) • (plusWt x - plusWt y) := by
    rw [← toStdD_smul, h2, toStdD_sub, toStdD_mvec hn, toStdD_mvec hn, smul_sub]
  funext k
  have := congrFun h3 k
  simp only [Pi.smul_apply, smul_eq_mul] at this
  simp only [Pi.sub_apply] at this ⊢
  omega


@[expose] def zi (z : Fin n ⊕ Fin n) : Fin n := Sum.elim id id z

@[expose] def zs (z : Fin n ⊕ Fin n) : Bool := Sum.elim (fun _ => true) (fun _ => false) z

theorem plusIdx_zi_zs (z : Fin n ⊕ Fin n) : plusIdx (zi z) (zs z) = z := by
  rcases z with a | a <;> rfl

theorem swap_plusIdx (m : Fin n) (r : Bool) : (plusIdx m r).swap = plusIdx m (!r) := by
  cases r <;> rfl

theorem plusWt_eq (z : Fin n ⊕ Fin n) : plusWt z = Pi.single (zi z) (boolSign (zs z)) := by
  rw [← plusIdx_zi_zs z, plusWt_plusIdx]
  simp [plusIdx_zi_zs]

variable {F : Type} [Field F]

theorem exists_rootElt [CharP F 2] (hn : 3 ≤ n) {x y : Fin n ⊕ Fin n} (hxy : x ≠ y)
    (hyx : y ≠ x.swap) (c : F) :
    ∃ u : spinGroup (quadPlus n F), Dgamma x y ∈ (plusDatum n F hn).roots ∧
      u ∈ (plusDatum n F hn).rootGroup (Dgamma x y) ∧
      Smat u = 1 + c • (Matrix.single x y 1 + Matrix.single y.swap x.swap 1) := by
  set i := zi x with hi
  set s := zs x with hs
  set j := zi y with hj
  set t := !(zs y) with ht
  have hx : plusIdx i s = x := plusIdx_zi_zs x
  have hy : plusIdx j (!t) = y := by
    rw [ht, Bool.not_not]; exact plusIdx_zi_zs y
  have hij : i ≠ j := by
    intro h
    have h1 : y = plusIdx i (!t) := by rw [← hy, ← h]
    by_cases hst : (!t) = s
    · exact hxy (by rw [h1, hst, hx])
    · have hb : ∀ a b : Bool, (!a) ≠ b → (!a) = !b := by decide
      have : (!t) = !s := hb t s hst
      exact hyx (by rw [h1, this, ← swap_plusIdx, hx])
  have he : plusWt x - plusWt y = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
    rw [plusWt_eq, plusWt_eq]
    have e1 : zi y = j := hj.symm
    have e2 : zs y = !t := by rw [ht, Bool.not_not]
    rw [← hi, ← hs, e1, e2, boolSign_not, Pi.single_neg, sub_neg_eq_add]
  have hγ : toStdD n (Dgamma x y) = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
    rw [toStdD_Dgamma hn, he]
  have hroots : Dgamma x y ∈ (plusDatum n F hn).roots := mem_rootsD_of_toStdD_eq hij s t hγ
  have hgrp : (plusDatum n F hn).rootGroup (Dgamma x y) =
      ((plusFrame n F hn).longRoot hij s t).range := plusRootGroup_eq hn hij s t hγ
  refine ⟨(plusFrame n F hn).longRoot hij s t (Multiplicative.ofAdd c), hroots, ?_, ?_⟩
  · rw [hgrp]; exact ⟨_, rfl⟩
  · have := coe_spinMatrix_longRoot (isCoordFrame_plusFrame (n := n) (K := F) (hn := hn)) hij s t c
    unfold Smat
    rw [this]
    unfold longMat
    have hys : y.swap = plusIdx j t := by rw [← hy, swap_plusIdx, Bool.not_not]
    have hxs : x.swap = plusIdx i (!s) := by rw [← hx, swap_plusIdx]
    rw [hys, hxs, hx, hy, sub_eq_add_neg, Matrix.single_neg, CharTwo.neg_eq]

end Gamma


end D130

section D132
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary

section MatDe

variable {n : ℕ} {F : Type} [Field F]

@[expose] noncomputable def matDe (e : Equiv.Perm (Fin (n + n))) :
    spinGroup (quadPlus n F) →* Matrix (Fin (n + n)) (Fin (n + n)) F :=
  (Matrix.reindexAlgEquiv F F e.symm).toAlgHom.toMonoidHom.comp (matD n F)

theorem matDe_apply (e : Equiv.Perm (Fin (n + n))) (g : spinGroup (quadPlus n F)) (a b : Fin (n + n)) :
    matDe e g a b = matD n F g (e a) (e b) := by
  simp [matDe, Matrix.reindexAlgEquiv_apply]

theorem matDe_injective [CharP F 2] (e : Equiv.Perm (Fin (n + n))) : Function.Injective (matDe (F := F) e) := by
  intro x y h
  apply matD_injective (CharTwo.two_eq_zero)
  ext a b
  have := congrFun (congrFun h (e.symm a)) (e.symm b)
  simpa [matDe_apply] using this

theorem matDe_unit (e : Equiv.Perm (Fin (n + n))) (he : ∀ t, e (Fin.rev t) = Fin.rev (e t))
    (g : spinGroup (quadPlus n F)) (a b : Fin (n + n)) :
    ∑ t, matDe e g t a * matDe e g (Fin.rev t) b = if b = Fin.rev a then 1 else 0 := by
  simp only [matDe_apply, he]
  rw [Equiv.sum_comp e (fun s => matD n F g s (e a) * matD n F g (Fin.rev s) (e b))]
  rw [matD_unit]
  have : e b = Fin.rev (e a) ↔ b = Fin.rev a := by
    rw [← he, e.injective.eq_iff]
  simp only [this]

theorem zi_swap (z : Fin n ⊕ Fin n) : zi z.swap = zi z := by
  rcases z with a | a <;> rfl

theorem sum_pairs (f : Fin (n + n) → F) (w0 : Fin (n + n))
    (h : ∀ w, f w ≠ 0 → f (Fin.rev w) ≠ 0 → w = w0 ∨ w = Fin.rev w0) :
    ∑ i : Fin n, f (posEquiv n (Sum.inl i)) * f (posEquiv n (Sum.inr i)) = f w0 * f (Fin.rev w0) := by
  set z0 := (posEquiv n).symm w0 with hz0
  have hw0 : posEquiv n z0 = w0 := by simp [hz0]
  have hinr : ∀ i : Fin n, posEquiv n (Sum.inr i) = Fin.rev (posEquiv n (Sum.inl i)) := fun i =>
    posEquiv_swap (Sum.inl i)
  rw [Finset.sum_eq_single (zi z0)]
  · rw [hinr]
    rcases z0 with a | a
    · have : posEquiv n (Sum.inl (zi (Sum.inl a : Fin n ⊕ Fin n))) = w0 := hw0
      rw [this]
    · have e1 : posEquiv n (Sum.inl (zi (Sum.inr a : Fin n ⊕ Fin n))) = Fin.rev w0 := by
        rw [← hw0, ← posEquiv_swap]; rfl
      rw [e1, Fin.rev_rev, mul_comm]
  · intro i _ hi
    by_contra hne
    have h1 : f (posEquiv n (Sum.inl i)) ≠ 0 := left_ne_zero_of_mul hne
    have h2 : f (Fin.rev (posEquiv n (Sum.inl i))) ≠ 0 := by
      have := right_ne_zero_of_mul hne
      rwa [hinr] at this
    rcases h _ h1 h2 with e | e
    · apply hi
      have : Sum.inl i = z0 := by rw [← (posEquiv n).injective.eq_iff, hw0, ← e]
      rw [← this]; rfl
    · apply hi
      have : Sum.inl i = z0.swap := by
        apply (posEquiv n).injective
        rw [posEquiv_swap, hw0, ← e]
      rw [← zi_swap z0, ← this]; rfl
  · intro h; exact absurd (Finset.mem_univ _) h


theorem matDe_diag_zero [CharP F 2] (e : Equiv.Perm (Fin (n + n)))
    (he : ∀ t, e (Fin.rev t) = Fin.rev (e t)) (g : spinGroup (quadPlus n F))
    (j : Fin ((n + n) / 2)) (hS : ShS0 j 1 (matDe e g)) {a : Fin (n + n)} (ha : InA j a) :
    matDe e g a (Fin.rev a) = 0 := by
  set G := matDe e g with hG
  have hq := matD_quad g (e (Fin.rev a))
  have hsum := sum_pairs (fun w => matD n F g w (e (Fin.rev a))) (e a) (by
    intro w h1 h2
    obtain ⟨u, rfl⟩ := e.surjective w
    have hu : G u (Fin.rev a) ≠ 0 := by rw [hG, matDe_apply]; exact h1
    have hu' : G (Fin.rev u) (Fin.rev a) ≠ 0 := by
      rw [hG, matDe_apply, he]; exact h2
    have key : ∀ v, G v (Fin.rev a) ≠ 0 → InA j v ∨ v = Fin.rev a := by
      intro v hv
      by_contra hcon
      have h1 : ¬ InA j v := fun h => hcon (Or.inl h)
      have h2 : v ≠ Fin.rev a := fun h => hcon (Or.inr h)
      apply hv
      rw [hS v (Fin.rev a) (fun ⟨h, _⟩ => h1 h), if_neg h2]
    have hnA : ¬ InA j (Fin.rev a) := fun h => InA_not_InA' ha h
    have hAA : ∀ v, InA j v → ¬ InA j (Fin.rev v) := fun v hv h => InA_not_InA' hv h
    rcases key u hu with h | h
    · rcases key _ hu' with h' | h'
      · exact absurd h' (hAA u h)
      · left; congr 1
        have : u = a := by rw [← Fin.rev_rev u, h', Fin.rev_rev]
        rw [this]
    · rcases key _ hu' with h' | h'
      · right; rw [h, he]
      · exfalso
        have : a = Fin.rev a := by
          have := h'
          rw [h, Fin.rev_rev] at this
          exact this
        exact InA_ne_rev ha this)
  rw [hsum] at hq
  have e1 : matD n F g (e a) (e (Fin.rev a)) = G a (Fin.rev a) := by rw [hG, matDe_apply]
  have e2 : matD n F g (Fin.rev (e a)) (e (Fin.rev a)) = 1 := by
    rw [← he, ← matDe_apply, ← hG]
    exact sh_diagA' hS.toShS (InA_rev_InA' ha)
  rw [e1, e2, mul_one] at hq
  exact hq

end MatDe


section Frames

variable {n : ℕ}

theorem posEquiv_symm_lt (v : Fin (n + n)) (h : v.val < n) :
    (posEquiv n).symm v = Sum.inl ⟨v.val, h⟩ := by
  apply (posEquiv n).injective
  apply Fin.ext
  rw [Equiv.apply_symm_apply, posEquiv_inl]

theorem posEquiv_symm_ge (v : Fin (n + n)) (h : n ≤ v.val) :
    (posEquiv n).symm v = Sum.inr ⟨n + n - 1 - v.val, by have := v.isLt; omega⟩ := by
  apply (posEquiv n).injective
  apply Fin.ext
  have := v.isLt
  rw [Equiv.apply_symm_apply, posEquiv_inr]
  simp only [Fin.val_mk]
  omega

@[expose] def tauE (n : ℕ) (hn : 3 ≤ n) : Equiv.Perm (Fin (n + n)) :=
  Equiv.swap ⟨n - 1, by omega⟩ ⟨n, by omega⟩

theorem tauE_val (hn : 3 ≤ n) (w : Fin (n + n)) :
    (tauE n hn w).val = if w.val = n - 1 then n else if w.val = n then n - 1 else w.val := by
  unfold tauE
  rw [Equiv.swap_apply_def]
  have e1 : (w = (⟨n - 1, by omega⟩ : Fin (n + n))) ↔ w.val = n - 1 := Fin.ext_iff
  have e2 : (w = (⟨n, by omega⟩ : Fin (n + n))) ↔ w.val = n := Fin.ext_iff
  simp only [e1, e2]
  split_ifs <;> rfl

theorem tauE_rev (hn : 3 ≤ n) (t : Fin (n + n)) :
    tauE n hn (Fin.rev t) = Fin.rev (tauE n hn t) := by
  apply Fin.ext
  have := t.isLt
  have h1 := tauE_val hn t
  have h2 := tauE_val hn (Fin.rev t)
  simp only [Fin.val_rev] at h1 h2 ⊢
  split_ifs at h1 h2 <;> omega

@[expose] def fE (hn : 3 ≤ n) (k : Fin n) : Equiv.Perm (Fin (n + n)) :=
  if k.val + 2 = n then tauE n hn else 1

theorem fE_rev (hn : 3 ≤ n) (k : Fin n) (t : Fin (n + n)) :
    fE hn k (Fin.rev t) = Fin.rev (fE hn k t) := by
  unfold fE
  split_ifs
  · exact tauE_rev hn t
  · rfl

theorem fE_val (hn : 3 ≤ n) (k : Fin n) (w : Fin (n + n)) :
    (fE hn k w).val = if k.val + 2 = n then
      (if w.val = n - 1 then n else if w.val = n then n - 1 else w.val) else w.val := by
  unfold fE
  by_cases h : k.val + 2 = n
  · rw [if_pos h, if_pos h]; exact tauE_val hn w
  · rw [if_neg h, if_neg h]; simp

@[expose] def jD (n : ℕ) (k : Fin n) : Fin ((n + n) / 2) :=
  ⟨if k.val + 2 = n then n - 1 else k.val, by have := k.isLt; split_ifs <;> omega⟩

theorem jD_val (k : Fin n) : (jD n k).val = if k.val + 2 = n then n - 1 else k.val := rfl

theorem mvec_pos_iff (hn : 3 ≤ n) (k : Fin n) (w : Fin (n + n)) :
    0 < mvec ((posEquiv n).symm (fE hn k w)) k ↔ w.val ≤ (jD n k).val := by
  have hk := k.isLt
  have hw := w.isLt
  have hv := fE_val hn k w
  rw [jD_val]
  set v := fE hn k w with hvdef
  have hvlt := v.isLt
  by_cases hk2 : k.val + 2 = n
  · simp only [hk2, if_true] at hv ⊢
    split_ifs at hv with h1 h2
    · rcases lt_or_ge v.val n with h | h
      · rw [posEquiv_symm_lt v h]
        simp only [mvec, Sum.elim_inl, Fin.val_mk]
        split_ifs <;> omega
      · rw [posEquiv_symm_ge v h]
        simp only [mvec, Sum.elim_inr, Fin.val_mk]
        split_ifs <;> omega
    · rcases lt_or_ge v.val n with h | h
      · rw [posEquiv_symm_lt v h]
        simp only [mvec, Sum.elim_inl, Fin.val_mk]
        split_ifs <;> omega
      · rw [posEquiv_symm_ge v h]
        simp only [mvec, Sum.elim_inr, Fin.val_mk]
        split_ifs <;> omega
    · rcases lt_or_ge v.val n with h | h
      · rw [posEquiv_symm_lt v h]
        simp only [mvec, Sum.elim_inl, Fin.val_mk]
        split_ifs <;> omega
      · rw [posEquiv_symm_ge v h]
        simp only [mvec, Sum.elim_inr, Fin.val_mk]
        split_ifs <;> omega
  · simp only [hk2, if_false] at hv ⊢
    rcases lt_or_ge v.val n with h | h
    · rw [posEquiv_symm_lt v h]
      simp only [mvec, Sum.elim_inl, Fin.val_mk]
      split_ifs <;> omega
    · rw [posEquiv_symm_ge v h]
      simp only [mvec, Sum.elim_inr, Fin.val_mk]
      split_ifs <;> omega

end Frames


section RootE

open CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin.PlusCT

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem swap_posEquiv_symm (w : Fin (n + n)) :
    ((posEquiv n).symm w).swap = (posEquiv n).symm (Fin.rev w) := by
  apply (posEquiv n).injective
  rw [posEquiv_swap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem exists_rootElt_e (hn : 3 ≤ n) (e : Equiv.Perm (Fin (n + n)))
    (he : ∀ t, e (Fin.rev t) = Fin.rev (e t)) {a b : Fin (n + n)} (hab : a ≠ b)
    (hba : b ≠ Fin.rev a) (c : F) :
    ∃ u : spinGroup (quadPlus n F),
      Dgamma ((posEquiv n).symm (e a)) ((posEquiv n).symm (e b)) ∈ (plusDatum n F hn).roots ∧
      u ∈ (plusDatum n F hn).rootGroup
        (Dgamma ((posEquiv n).symm (e a)) ((posEquiv n).symm (e b))) ∧
      matDe e u = rootMatrix (RingEquiv.refl F) a b c := by
  set Q : Fin (n + n) → Fin n ⊕ Fin n := fun w => (posEquiv n).symm (e w) with hQ
  have hQinj : Function.Injective Q := (posEquiv n).symm.injective.comp e.injective
  have hQs : ∀ w, (Q w).swap = Q (Fin.rev w) := fun w => by
    simp only [hQ, swap_posEquiv_symm, he]
  have h1 : Q a ≠ Q b := fun h => hab (hQinj h)
  have h2 : Q b ≠ (Q a).swap := by
    rw [hQs]; exact fun h => hba (hQinj h)
  obtain ⟨u, hr, hu, hS⟩ := exists_rootElt hn h1 h2 c
  refine ⟨u, hr, hu, ?_⟩
  ext a' b'
  have : matDe e u a' b' = Smat u (Q a') (Q b') := by
    rw [matDe_apply, matD_apply]
  rw [this, hS, hQs, hQs]
  simp only [rootMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.single_apply, hQinj.eq_iff, RingEquiv.refl_apply, smul_eq_mul]
  have hrb : Fin.rev b ≠ a := fun h => hba (by rw [← h, Fin.rev_rev])
  have hn2 : ∀ x : F, -x = x := fun x => CharTwo.neg_eq x
  split_ifs <;> simp_all [sub_eq_add_neg, hn2] <;> ring

end RootE


section HunitRefl
variable {n : ℕ} {F : Type} [Field F]
theorem hunit_refl (e : Equiv.Perm (Fin (n + n))) (he : ∀ t, e (Fin.rev t) = Fin.rev (e t))
    (g : spinGroup (quadPlus n F)) (a b : Fin (n + n)) :
    ∑ t, (RingEquiv.refl F) (matDe e g t a) * matDe e g (Fin.rev t) b =
      if b = Fin.rev a then 1 else 0 := by
  simpa using matDe_unit e he g a b

end HunitRefl


end D132

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
