module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L5Cnt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.QuasithinUnique.A5.Kc3L5

open Matrix

theorem act_smul (g : Gl) (c : ZMod 2) (x : W) : act g (c • x) = c • act g x := by
  simp [act, Matrix.mulVec_smul]

theorem act_inj (g : Gl) {a b : W} (h : act g a = act g b) : a = b := by
  have := congrArg (act g⁻¹) h
  rwa [← act_mul, ← act_mul, inv_mul_cancel, act_one, act_one] at this

theorem mat_ext_mulVec {A B : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : ∀ x : W, A *ᵥ x = B *ᵥ x) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem gl_ext_act {g h : Gl} (hg : ∀ x : W, act g x = act h x) : g = h :=
  Units.ext (mat_ext_mulVec hg)

@[expose] def e4 : W := Pi.single 4 1

@[expose] def M0 : AddSubgroup W where
  carrier := {w | w 4 = 0}
  add_mem' := by
    intro a b ha hb
    have ha' : a 4 = 0 := ha
    have hb' : b 4 = 0 := hb
    show (a + b) 4 = 0
    simp [ha', hb']
  zero_mem' := rfl
  neg_mem' := by
    intro a ha
    have ha' : a 4 = 0 := ha
    have h1 : (-a) 4 = -(a 4) := rfl
    show (-a) 4 = 0
    rw [h1, ha']
    decide

theorem mem_M0 {w : W} : w ∈ M0 ↔ w 4 = 0 := Iff.rfl

theorem card_M0_le : Nat.card M0 ≤ 16 := by
  have hinj : Function.Injective (fun w : M0 => fun i : Fin 4 => (w : W) i.castSucc) := by
    intro a b h
    apply Subtype.ext
    funext i
    have h4a : (a : W) 4 = 0 := a.2
    have h4b : (b : W) 4 = 0 := b.2
    by_cases hi : i = 4
    · subst hi; rw [h4a, h4b]
    · have : ∃ j : Fin 4, j.castSucc = i := ⟨⟨i.val, by omega⟩, Fin.ext (by simp)⟩
      obtain ⟨j, rfl⟩ := this
      exact congrFun h j
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Nat.card_fun] using this

@[expose] def U0 : Subgroup Gl where
  carrier := {g | ∀ z : W, z 4 = 0 → act g z = z}
  mul_mem' := by
    intro a b ha hb z hz
    rw [act_mul, hb z hz, ha z hz]
  one_mem' := fun z _ => act_one z
  inv_mem' := by
    intro a ha z hz
    have h1 : act a z = z := ha z hz
    calc act a⁻¹ z = act a⁻¹ (act a z) := by rw [h1]
      _ = z := by rw [← act_mul, inv_mul_cancel, act_one]

@[expose] def tauMat (v : W) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  1 + Matrix.vecMulVec v (Pi.single 4 1)

theorem tauMat_mulVec (v x : W) : tauMat v *ᵥ x = x + x 4 • v := by
  funext i
  fin_cases i <;>
    simp [tauMat, Matrix.mulVec, Matrix.vecMulVec, dotProduct, Fin.sum_univ_five,
      Matrix.one_apply, Pi.single_apply, mul_comm]
  ring

theorem tauMat_mul_self {v : W} (hv : v 4 = 0) : tauMat v * tauMat v = 1 := by
  refine mat_ext_mulVec fun x => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, tauMat_mulVec, tauMat_mulVec]
  funext i
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv, mul_zero, add_zero]
  have : ∀ a : ZMod 2, a + a = 0 := fun a => by
    rw [← two_mul, h2, zero_mul]
  calc x i + x 4 * v i + x 4 * v i = x i + (x 4 * v i + x 4 * v i) := add_assoc _ _ _
    _ = x i := by rw [this, add_zero]

@[expose] def tau (v : W) (hv : v 4 = 0) : Gl :=
  ⟨tauMat v, tauMat v, tauMat_mul_self hv, tauMat_mul_self hv⟩

theorem act_tau (v : W) (hv : v 4 = 0) (x : W) : act (tau v hv) x = x + x 4 • v :=
  tauMat_mulVec v x

theorem tau_mem_U0 (v : W) (hv : v 4 = 0) : tau v hv ∈ U0 := by
  intro z hz
  rw [act_tau, hz]
  simp

theorem e4_four : (e4 : W) 4 = 1 := by simp [e4]

theorem act_e4_four {g : Gl} (hg : g ∈ U0) : (act g e4) 4 = 1 := by
  by_contra hne
  have h0 : (act g e4) 4 = 0 := by
    generalize (act g e4) 4 = c at hne
    revert c; decide
  have h1 := hg _ h0
  have h2 : act g (act g e4) = act g e4 := h1
  have h3 : act g e4 = e4 := act_inj g h2
  rw [h3, e4_four] at h0
  exact one_ne_zero h0

theorem act_of_mem_U0 {g : Gl} (hg : g ∈ U0) (w : W) :
    act g w = w + w 4 • (act g e4 - e4) := by
  set z : W := w - w 4 • e4 with hz
  have hz4 : z 4 = 0 := by simp [hz, e4]
  have hgz : act g z = z := hg z hz4
  have hw : w = z + w 4 • e4 := by simp [hz]
  have h1 : act g w = z + w 4 • act g e4 := by
    conv_lhs => rw [hw]
    rw [act_add, act_smul, hgz]
  rw [h1]
  funext i
  simp [hz, smul_sub]
  ring

theorem card_U0_le : Nat.card U0 ≤ 16 := by
  have hv : ∀ g : U0, (act (g : Gl) e4 - e4) 4 = 0 := fun g => by
    rw [Pi.sub_apply, act_e4_four g.2, e4_four, sub_self]
  have hinj : Function.Injective (fun g : U0 => (⟨act (g : Gl) e4 - e4, hv g⟩ : M0)) := by
    intro a b h
    have h' : act (a : Gl) e4 - e4 = act (b : Gl) e4 - e4 := congrArg Subtype.val h
    have h'' : act (a : Gl) e4 = act (b : Gl) e4 := sub_left_injective h'
    apply Subtype.ext
    refine gl_ext_act fun w => ?_
    rw [act_of_mem_U0 a.2, act_of_mem_U0 b.2, h'']
  exact (Nat.card_le_card_of_injective _ hinj).trans card_M0_le

theorem mem_U0_of_centralizes (g : Gl) (h : ∀ u ∈ U0, g * u = u * g) : g ∈ U0 := by
  have key : ∀ (v : W), v 4 = 0 → act g v = (act g e4) 4 • v := by
    intro v hv
    have h1 := h _ (tau_mem_U0 v hv)
    have h2 : act g (act (tau v hv) e4) = act (tau v hv) (act g e4) := by
      rw [← act_mul, ← act_mul, h1]
    have hl : act (tau v hv) e4 = e4 + v := by rw [act_tau, e4_four, one_smul]
    rw [hl, act_add, act_tau] at h2
    exact add_left_cancel h2
  have hs : (act g e4) 4 = 1 := by
    by_contra hne
    have h0 : (act g e4) 4 = 0 := by
      generalize (act g e4) 4 = c at hne
      revert c; decide
    have hv0 : (Pi.single 0 1 : W) 4 = 0 := by simp
    have h6 := key _ hv0
    rw [h0, zero_smul] at h6
    have h7 : act g (Pi.single 0 1) = act g 0 := by rw [h6, act_zero]
    have h8 := act_inj g h7
    have := congrFun h8 0
    simp at this
  intro z hz
  rw [key z hz, hs, one_smul]

@[expose] def aMat (p : Fin 4 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of ![![1, 0, p 0, p 1, 0], ![0, 1, p 2, p 3, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1]]

theorem aMat_mul (p q : Fin 4 → ZMod 2) : aMat p * aMat q = aMat (p + q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aMat, Matrix.mul_apply, Fin.sum_univ_five, add_comm]

theorem aMat_zero : aMat 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aMat]

theorem add_self_zmod (a : ZMod 2) : a + a = 0 := by
  revert a; decide

theorem aMat_mul_self (p : Fin 4 → ZMod 2) : aMat p * aMat p = 1 := by
  have : p + p = 0 := by
    funext i
    exact add_self_zmod (p i)
  rw [aMat_mul, this, aMat_zero]

@[expose] def aGl (p : Fin 4 → ZMod 2) : Gl := ⟨aMat p, aMat p, aMat_mul_self p, aMat_mul_self p⟩

theorem aGl_mul (p q : Fin 4 → ZMod 2) : aGl p * aGl q = aGl (p + q) :=
  Units.ext (aMat_mul p q)

theorem aGl_zero : aGl 0 = 1 := Units.ext aMat_zero

@[expose] def aHom : Multiplicative (Fin 4 → ZMod 2) →* Gl where
  toFun p := aGl (Multiplicative.toAdd p)
  map_one' := aGl_zero
  map_mul' p q := by
    rw [toAdd_mul]
    exact (aGl_mul _ _).symm

theorem aHom_injective : Function.Injective aHom := by
  intro p q h
  have h' : aMat (Multiplicative.toAdd p) = aMat (Multiplicative.toAdd q) := congrArg Units.val h
  have h02 := congrFun (congrFun h' 0) 2
  have h03 := congrFun (congrFun h' 0) 3
  have h12 := congrFun (congrFun h' 1) 2
  have h13 := congrFun (congrFun h' 1) 3
  simp [aMat] at h02 h03 h12 h13
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simpa using ‹_›

theorem act_aGl_four (p : Fin 4 → ZMod 2) (w : W) : (act (aGl p) w) 4 = w 4 := by
  simp [act, aGl, aMat, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

theorem mem_normalizer_U0 {a : Gl} (ha : ∀ w : W, (act a w) 4 = w 4) :
    a ∈ Subgroup.normalizer (U0 : Set Gl) := by
  have ha' : ∀ w : W, (act a⁻¹ w) 4 = w 4 := fun w => by
    have := ha (act a⁻¹ w)
    rw [← act_mul, mul_inv_cancel, act_one] at this
    exact this.symm
  have hconj : ∀ b : Gl, (∀ w : W, (act b w) 4 = w 4) → ∀ u ∈ U0, b * u * b⁻¹ ∈ U0 := by
    intro b hb
    have hb' : ∀ w : W, (act b⁻¹ w) 4 = w 4 := fun w => by
      have := hb (act b⁻¹ w)
      rw [← act_mul, mul_inv_cancel, act_one] at this
      exact this.symm
    intro u hu z hz
    rw [act_mul, act_mul, hu _ (by rw [hb' z, hz]), ← act_mul, mul_inv_cancel, act_one]
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact hconj a ha u hu
  · intro hu
    have := hconj a⁻¹ ha' _ hu
    simpa [mul_assoc] using this

theorem exists_A : ∃ A : Subgroup Gl, A ≤ Subgroup.normalizer (U0 : Set Gl) ∧ Nat.card A = 16 ∧
    ∀ a ∈ A, (∀ u ∈ U0, a * u * a⁻¹ = u) → a = 1 := by
  refine ⟨aHom.range, ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact mem_normalizer_U0 fun w => act_aGl_four _ w
  · rw [Nat.card_congr (MonoidHom.ofInjective aHom_injective).toEquiv.symm]
    simp
  · rintro _ ⟨p, rfl⟩ hcomm
    have hc : aHom p ∈ U0 := by
      refine mem_U0_of_centralizes _ fun u hu => ?_
      have := hcomm u hu
      calc aHom p * u = (aHom p * u * (aHom p)⁻¹) * aHom p := by group
        _ = u * aHom p := by rw [this]
    have h2 : act (aHom p) (Pi.single 2 1) = Pi.single 2 1 := hc _ (by simp)
    have h3 : act (aHom p) (Pi.single 3 1) = Pi.single 3 1 := hc _ (by simp)
    have e2 := congrFun h2
    have e3 := congrFun h3
    have p0 := e2 0
    have p2 := e2 1
    have p1 := e3 0
    have p3 := e3 1
    simp [act, aHom, aGl, aMat, Matrix.mulVec, dotProduct, Fin.sum_univ_five] at p0 p1 p2 p3
    have hp : Multiplicative.toAdd p = 0 := by
      funext i
      fin_cases i <;> simpa using ‹_›
    have : p = 1 := Multiplicative.toAdd.injective (by rw [hp]; rfl)
    rw [this, map_one]

theorem W_neg (x : W) : -x = x := by
  funext i
  simp only [Pi.neg_apply]
  generalize x i = c
  revert c; decide

theorem W_zero_add (x : W) : (0 : W) + x = x := by
  funext i
  simp

theorem W_add_sub_cancel (w w' : W) : w + w' - w = w' := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply]
  generalize w i = a
  generalize w' i = b
  revert a b; decide

theorem add_mem_of_not_mem (C : AddSubgroup W) (hC : Nat.card C = 16) {w w' : W} (hw : w ∉ C)
    (hw' : w' ∉ C) : w + w' ∈ C := by
  classical
  have hidx : C.index = 2 := by
    have h := AddSubgroup.card_mul_index C
    rw [hC, card_W] at h
    omega
  have hcard : Nat.card (W ⧸ C) = 2 := by rw [← AddSubgroup.index]; exact hidx
  have hcls : ∀ q q' q'' : W ⧸ C, q ≠ q' → q ≠ q'' → q' = q'' := by
    obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.1 hcard
    have hmem : ∀ q : W ⧸ C, q = x ∨ q = y := fun q => by
      have : q ∈ ({x, y} : Set (W ⧸ C)) := by rw [hset]; trivial
      simpa using this
    intro q q' q'' h1 h2
    rcases hmem q with rfl | rfl <;> rcases hmem q' with rfl | rfl <;>
      rcases hmem q'' with rfl | rfl <;> simp_all
  have h1 : (QuotientAddGroup.mk 0 : W ⧸ C) ≠ QuotientAddGroup.mk w := fun h => hw (by
    have this : -(0 : W) + w ∈ C := (QuotientAddGroup.eq).1 h
    rwa [W_neg, W_zero_add] at this)
  have h2 : (QuotientAddGroup.mk 0 : W ⧸ C) ≠ QuotientAddGroup.mk w' := fun h => hw' (by
    have this : -(0 : W) + w' ∈ C := (QuotientAddGroup.eq).1 h
    rwa [W_neg, W_zero_add] at this)
  have h3 : -w + w' ∈ C := (QuotientAddGroup.eq).1 (hcls _ _ _ h1 h2)
  rwa [W_neg] at h3

theorem exists_form (C : AddSubgroup W) (hC : Nat.card C = 16) :
    ∃ a : W, a ≠ 0 ∧ ∀ w : W, w ∈ C ↔ (∑ i, a i * w i) = 0 := by
  classical
  let l : W → ZMod 2 := fun w => if w ∈ C then 0 else 1
  have hsub : ∀ w w' : W, w + w' ∈ C → w ∈ C → w' ∈ C := fun w w' h hw => by
    have h3 := C.sub_mem h hw
    rwa [W_add_sub_cancel] at h3
  have hl : ∀ w w' : W, l (w + w') = l w + l w' := by
    intro w w'
    by_cases hw : w ∈ C <;> by_cases hw' : w' ∈ C
    · have : w + w' ∈ C := C.add_mem hw hw'
      simp [l, hw, hw', this]
    · have : w + w' ∉ C := fun h => hw' (hsub w w' h hw)
      simp [l, hw, hw', this]
    · have : w + w' ∉ C := fun h => hw (hsub w' w (by rwa [add_comm] at h) hw')
      simp [l, hw, hw', this]
    · have : w + w' ∈ C := add_mem_of_not_mem C hC hw hw'
      simp [l, hw, hw', this]
      decide
  let L : W →+ ZMod 2 := AddMonoidHom.mk' l hl
  let a : W := fun i => L (Pi.single i 1)
  have hform : ∀ w : W, l w = ∑ i, a i * w i := by
    intro w
    have h1 : w = ∑ i, Pi.single i (w i) := (Finset.univ_sum_single w).symm
    have h2 : l w = ∑ i, l (Pi.single i (w i)) := by
      have := map_sum L (fun i => (Pi.single i (w i) : W)) Finset.univ
      rw [← h1] at this
      exact this
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : w i = 0 ∨ w i = 1 := by
      generalize w i = c
      revert c; decide
    rcases hc with h | h
    · rw [h]
      simp [l]
    · rw [h]
      simp [a, L]
  refine ⟨a, ?_, fun w => ?_⟩
  · intro ha
    have hall : ∀ w : W, w ∈ C := by
      intro w
      by_contra hw
      have h1 : l w = 1 := by simp [l, hw]
      rw [hform, ha] at h1
      simp at h1
    have : C = ⊤ := eq_top_iff.2 fun w _ => hall w
    rw [this, AddSubgroup.card_top, card_W] at hC
    omega
  · rw [← hform]
    by_cases hw : w ∈ C
    · simp [l, hw]
    · simp [l, hw]

@[expose] def Tmat (a : W) (k : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => if i = k then a j else if i = j then 1 else 0

@[expose] def Pmat (k : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => if j = Equiv.swap k 4 i then 1 else 0

theorem Tmat_sq : ∀ (a : W) (k : Fin 5), a k = 1 → Tmat a k * Tmat a k = 1 := by
  decide +kernel

theorem Pmat_sq : ∀ k : Fin 5, Pmat k * Pmat k = 1 := by
  decide +kernel

@[expose] def tauA (a : W) (k : Fin 5) (hk : a k = 1) : Gl :=
  ⟨Pmat k * Tmat a k, Tmat a k * Pmat k, by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Tmat a k) (Tmat a k), Tmat_sq a k hk, Matrix.one_mul,
      Pmat_sq],
    by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Pmat k) (Pmat k), Pmat_sq, Matrix.one_mul,
      Tmat_sq a k hk]⟩

theorem act_tauA_four (a : W) (k : Fin 5) (hk : a k = 1) (w : W) :
    (act (tauA a k hk) w) 4 = ∑ i, a i * w i := by
  fin_cases k <;>
    simp [act, tauA, Pmat, Tmat, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      Matrix.mul_apply, Equiv.swap_apply_def]

theorem exists_conj_M0 (C : AddSubgroup W) (hC : Nat.card C = 16) :
    ∃ τ : Gl, ∀ w : W, w ∈ C ↔ act τ w ∈ M0 := by
  obtain ⟨a, ha, hC'⟩ := exists_form C hC
  have : ∃ k : Fin 5, a k = 1 := by
    by_contra hcon
    push Not at hcon
    apply ha
    funext i
    have h1 := hcon i
    have h2 : a i = 0 := by
      generalize a i = c at h1
      revert c; decide
    exact h2
  obtain ⟨k, hk⟩ := this
  refine ⟨tauA a k hk, fun w => ?_⟩
  rw [hC' w, mem_M0, act_tauA_four]

end CFSG.QuasithinUnique.A5.Kc3L5
