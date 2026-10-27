module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4FixMat
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidWeights
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.ModelFacts.D4Rigid
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] noncomputable def rA (F : Type) [Field F] (c : F) : spinGroup (quadPlus 4 F) :=
  (fr F).longRoot ne01 true false (.ofAdd c)

@[expose] noncomputable def rB (F : Type) [Field F] (c : F) : spinGroup (quadPlus 4 F) :=
  (fr F).longRoot ne01 true true (.ofAdd c)

@[expose] def jk : Fin 4 → Fin 4 := ![2, 2, 3, 3]

@[expose] def tk : Fin 4 → Bool := ![true, false, true, false]

theorem jk_ne (k : Fin 4) : (0 : Fin 4) ≠ jk k := by fin_cases k <;> decide

theorem jk_ne1 (k : Fin 4) : (1 : Fin 4) ≠ jk k := by fin_cases k <;> decide

theorem kap_eq (k : Fin 4) : kap k = idx (jk k) (tk k) := by fin_cases k <;> rfl

@[expose] noncomputable def qq (F : Type) [Field F] (k : Fin 4) (a : F) :
    spinGroup (quadPlus 4 F) :=
  (fr F).longRoot (jk_ne k) true (tk k) (.ofAdd a)

theorem spinAction_rA (c : F) (v : Idx → F) : spinAction (quadPlus 4 F) (rA F c) v =
    v + c • X1 v := by
  ext μ
  rw [rA, spinAction_longRoot_apply]
  simp [idx, X1_apply]
  split_ifs <;> ring

theorem spinAction_rB (c : F) (v : Idx → F) : spinAction (quadPlus 4 F) (rB F c) v =
    v + c • X2 v := by
  ext μ
  rw [rB, spinAction_longRoot_apply]
  simp [idx, X2_apply]
  split_ifs <;> ring

theorem quadPlus_ek (k : Fin 4) : quadPlus 4 F (ek F k) = 0 := by
  rw [quadPlus_apply]
  apply Finset.sum_eq_zero
  intro i _
  fin_cases k <;> simp [ek, kap, Pi.single_apply]

theorem polar_ek (v : Idx → F) (k : Fin 4) :
    polar (quadPlus 4 F) v (ek F k) = v (idx (jk k) (!tk k)) := by
  have h := polar_vec (F := F) v (jk k) (tk k)
  rw [vec_eq] at h
  rw [← h]
  rw [ek, kap_eq]

theorem spinAction_qq (k : Fin 4) (a : F) (v : Idx → F) :
    spinAction (quadPlus 4 F) (qq F k a) v = eich (-a • ek F k) v := by
  ext μ
  rw [qq, spinAction_longRoot_apply, eich_apply, QuadraticMap.polar_smul_right, polar_ek,
    QuadraticMap.map_smul, quadPlus_ek]
  have h1 : ek F k μ = if μ = idx (jk k) (tk k) then 1 else 0 := by
    rw [ek_apply, kap_eq]
  simp only [idx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, smul_eq_mul, Pi.smul_apply,
    neg_mul, mul_zero, h1] at *
  simp
  ring

theorem qq_add (k : Fin 4) (a b : F) : qq F k (a + b) = qq F k a * qq F k b := by
  unfold qq
  rw [← map_mul, ← ofAdd_add]

theorem qq_zero (k : Fin 4) : qq F k 0 = 1 := by
  unfold qq
  rw [ofAdd_zero, map_one]

theorem qq_pow_char {p : ℕ} [CharP F p] (k : Fin 4) (a : F) : qq F k a ^ p = 1 := by
  unfold qq
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero, map_one]

theorem commute_qq_rA (k : Fin 4) (a c : F) : Commute (qq F k a) (rA F c) :=
  (fr F).commute_longRoot_longRoot_left (jk_ne k) ne01 true (tk k) false a c

theorem commute_qq_rB (k : Fin 4) (a c : F) : Commute (qq F k a) (rB F c) :=
  (fr F).commute_longRoot_longRoot_left (jk_ne k) ne01 true (tk k) true a c

@[expose] noncomputable def torA (F : Type) [Field F] (s : Fˣ) : spinGroup (quadPlus 4 F) :=
  (fr F).longTorus ne01 true false s

@[expose] noncomputable def nA (F : Type) [Field F] : spinGroup (quadPlus 4 F) :=
  (fr F).longWeyl ne01 true false

@[expose] noncomputable def nB (F : Type) [Field F] : spinGroup (quadPlus 4 F) :=
  (fr F).longWeyl ne01 true true

theorem spinAction_torA (s : Fˣ) (v : Idx → F) :
    spinAction (quadPlus 4 F) (torA F s) v = Dt (s : F) v := by
  ext μ
  rw [torA, spinAction_longTorus_apply]
  rcases μ with i | i <;> fin_cases i <;> simp [lamT, idx, Dt, lamS]

theorem spinAction_nA (v : Idx → F) : spinAction (quadPlus 4 F) (nA F) v = Nw v := by
  ext μ
  rw [nA, HypFrame.longWeyl, HypFrame.spinAction_longSL2_weylSL2]
  simp only [vec_eq, Units.val_one, inv_one, one_mul, Bool.not_true, Bool.not_false, idx]
  rcases μ with i | i <;> fin_cases i <;>
    simp [Nw, polar_quadPlus_single_inl, polar_quadPlus_single_inr]

@[expose] noncomputable def yy (F : Type) [Field F] (k : Fin 4) (b : F) :
    spinGroup (quadPlus 4 F) :=
  (fr F).longRoot (jk_ne1 k) true (tk k) (.ofAdd b)

theorem torA_conj_qq (s : Fˣ) (k : Fin 4) (a : F) :
    torA F s * qq F k a * (torA F s)⁻¹ = qq F k ((s : F) * a) := by
  have h := (fr F).longTorus_conj_longRoot ne01 true false s (jk_ne k) true (tk k) a
  have e : longCoroot (0 : Fin 4) 1 true false 0 true +
      longCoroot (0 : Fin 4) 1 true false (jk k) (tk k) = 1 := by
    fin_cases k <;> simp [longCoroot, jk]
  rw [e, zpow_one] at h
  exact h

theorem nA_conj_qq (k : Fin 4) (a : F) : nA F * qq F k a * (nA F)⁻¹ = yy F k (-a) := by
  have hi : spinAction (quadPlus 4 F) (nA F) ((fr F).vec 0 true) = (-1 : F) • (fr F).vec 1 true := by
    rw [nA, (fr F).spinAction_longWeyl_vec ne01 true false 0 true]
    simp [longWeylSign]
  have hj : spinAction (quadPlus 4 F) (nA F) ((fr F).vec (jk k) (tk k)) =
      (1 : F) • (fr F).vec (jk k) (tk k) := by
    rw [nA, (fr F).spinAction_longWeyl_vec ne01 true false (jk k) (tk k)]
    have h0 : jk k ≠ 0 := (jk_ne k).symm
    have h1 : jk k ≠ 1 := (jk_ne1 k).symm
    simp [longWeylSign, longWeylBool, h0, h1, Equiv.swap_apply_of_ne_of_ne h0 h1]
  have h := (fr F).conj_longRoot (nA F) (jk_ne k) true (tk k) (jk_ne1 k) true (tk k) hi hj a
  rw [qq, yy, h]
  congr 2
  simp

theorem comm_x_y (j : Fin 4) (t : Bool) (h0 : (0 : Fin 4) ≠ j) (h1 : (1 : Fin 4) ≠ j) (a b : F) :
    ⁅(fr F).longRoot h0 true t (.ofAdd a), (fr F).longRoot h1 true (!t) (.ofAdd b)⁆ =
      rB F (-(a * b)) := by
  rw [(fr F).longRoot_swap h1 true (!t) b]
  have h := (fr F).commutator_longRoot_longRoot h0 h1.symm ne01 true t true a (-b)
  rw [h, rB]
  congr 2
  ring

theorem commute_x_y_disjoint (j j' : Fin 4) (hjj : j ≠ j') (h0 : (0 : Fin 4) ≠ j)
    (h1 : (1 : Fin 4) ≠ j') (h0' : (0 : Fin 4) ≠ j') (h1' : (1 : Fin 4) ≠ j) (t t' : Bool)
    (a b : F) :
    Commute ((fr F).longRoot h0 true t (.ofAdd a)) ((fr F).longRoot h1 true t' (.ofAdd b)) :=
  (fr F).commute_longRoot_longRoot_of_disjoint h0 h1 (by decide) h0' h1'.symm hjj true t true t'
    a b

theorem yy_of_partner {k l : Fin 4} (hj : jk l = jk k) (ht : tk l = !tk k) (b : F) :
    yy F l b = (fr F).longRoot (jk_ne1 k) true (!tk k) (.ofAdd b) := by
  unfold yy
  rw [CFSG.LieType.Steinberg.SpinFrame.longRoot_congr (fr F) (jk_ne1 l) (jk_ne1 k) rfl hj rfl ht]

theorem comm_qq_yy_partner {k l : Fin 4} (hj : jk l = jk k) (ht : tk l = !tk k) (a b : F) :
    ⁅qq F k a, yy F l b⁆ = rB F (-(a * b)) := by
  rw [yy_of_partner hj ht]
  exact comm_x_y (jk k) (tk k) (jk_ne k) (jk_ne1 k) a b

theorem commute_qq_yy_of_ne {k l : Fin 4} (hj : jk l ≠ jk k) (a b : F) :
    Commute (qq F k a) (yy F l b) :=
  (fr F).commute_longRoot_longRoot_of_disjoint (jk_ne k) (jk_ne1 l) ne01 (jk_ne l)
    (jk_ne1 k).symm (Ne.symm hj) true (tk k) true (tk l) a b

theorem commute_qq_yy_self (k : Fin 4) (a b : F) : Commute (qq F k a) (yy F k b) :=
  (fr F).commute_longRoot_longRoot_right (jk_ne k) (jk_ne1 k) true (tk k) true a b

theorem eq_of_jk_tk : ∀ k l : Fin 4, jk l = jk k → tk l = tk k → l = k := by decide

theorem commute_qq_yy {k l : Fin 4} (hl : ¬ (jk l = jk k ∧ tk l = !tk k)) (a b : F) :
    Commute (qq F k a) (yy F l b) := by
  by_cases hj : jk l = jk k
  · have ht : tk l = tk k := by
      by_contra h
      apply hl
      refine ⟨hj, ?_⟩
      cases h1 : tk l <;> cases h2 : tk k <;> simp_all
    have := eq_of_jk_tk k l hj ht
    subst this
    exact commute_qq_yy_self l a b
  · exact commute_qq_yy_of_ne hj a b

end CFSG.ClassicalInvolution.G2D4Models.Twin
