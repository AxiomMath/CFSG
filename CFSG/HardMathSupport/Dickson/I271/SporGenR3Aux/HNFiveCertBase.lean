
module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveCertInputs
public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveKer

@[expose] public section

namespace CFSG.HardMathSupport.Dickson.I271.HNFive

open CFSG.Sporadic.He.Native CFSG.Sporadic.F5 CFSG.Sporadic.F5.Native CFSG.Sporadic.HNSchreier
  CFSG.Sporadic.HNSchreier.Native
  CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix
open CFSG.HardMathSupport.Dickson.I271.HNFive.Native

section Semantics

theorem toMat_addM (p d : ℕ) (X Y : Array (Array ℕ)) :
    toMat p d (addM p d X Y) = toMat p d X + toMat p d Y := by
  ext i j
  rw [toMat_apply, Matrix.add_apply, toMat_apply, toMat_apply]
  unfold addM
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt, ZMod.natCast_mod, Nat.cast_add]

theorem toMat_subIdM (d : ℕ) (X : Array (Array ℕ)) :
    toMat 5 d (subIdM 5 d X) = toMat 5 d X - 1 := by
  ext i j
  rw [toMat_apply, Matrix.sub_apply, toMat_apply, Matrix.one_apply]
  unfold subIdM
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt, ZMod.natCast_mod, Nat.cast_add]
  by_cases h : i = j
  · subst h
    have : ((5 - 1 : ℕ) : ZMod 5) = -1 := by decide
    rw [if_pos rfl, if_pos rfl, this]
    exact (sub_eq_add_neg _ _).symm
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    rw [if_neg h, if_neg h', Nat.cast_zero]
    exact (add_zero _).trans (sub_zero _).symm

theorem toMat_zeroM (p d : ℕ) : toMat p d (zeroM d) = 0 := by
  ext i j
  rw [toMat_apply]
  unfold zeroM
  rw [getElem!_pos _ i.val (by simp), Array.getElem_replicate,
    getElem!_pos _ j.val (by simp), Array.getElem_replicate, Nat.cast_zero, Matrix.zero_apply]

theorem toMat_ne_of_neAt {p d : ℕ} {X Y : Array (Array ℕ)} {i j : ℕ} (hi : i < d) (hj : j < d)
    (h : neAt p X Y i j = true) : toMat p d X ≠ toMat p d Y := by
  intro he
  have := congrFun (congrFun he ⟨i, hi⟩) ⟨j, hj⟩
  rw [toMat_apply, toMat_apply, ZMod.natCast_eq_natCast_iff'] at this
  unfold neAt at h
  simp only [bne_iff_ne, ne_eq] at h
  exact h this

end Semantics

section Core

def Hn5Spec (Mg Mc : Matrix (Fin 133) (Fin 133) (ZMod 5)) : Prop :=
  Mg ^ 30 = 1 ∧ Mg ^ 6 ≠ 1 ∧ Mg ^ 10 ≠ 1 ∧
    (Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29) * Mg ^ 6 = Mg ^ 6 * (Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29) ∧
    Mg ^ 10 * (Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29) ≠ (Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29) * Mg ^ 10 ∧
    ∃ A Lam R W Phi : Matrix (Fin 133) (Fin 133) (ZMod 5),
      (Mg ^ 6 - 1) * A = 0 ∧ A * Lam + R * (Mg ^ 6 - 1) = 1 ∧
      (Mg ^ 29 * Mc * Mg * Mc * Mg ^ 29 - 1) * A = (Mg ^ 6 - 1) * (Mg ^ 6 - 1) * W ∧
      Phi * ((Mg ^ 6 - 1) * (Mg ^ 6 - 1)) = 0 ∧ Phi * (Mg ^ 10 - 1) * A ≠ 0

theorem hn5Core_spec {Ng Nc : Array (Array ℕ)} (h : hn5Core Ng Nc = true) :
    Hn5Spec (toMat 5 133 Ng) (toMat 5 133 Nc) := by
  unfold hn5Core at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, toMat 5 133 (rowsOf 5 133 dataA), toMat 5 133 (rowsOf 5 133 dataLam),
    toMat 5 133 (rowsOf 5 133 dataR), toMat 5 133 (rowsOf 5 133 dataW),
    toMat 5 133 (rowsOf 5 133 dataPhi), ?_, ?_, ?_, ?_, ?_⟩
  · have := toMat_eq_of_beq (p := 5) (d := 133) h1
    simp only [toMat_powM, toMat_idM] at this
    exact this
  · have := toMat_ne_of_neAt (d := 133) (by norm_num) (by norm_num) h2
    simp only [toMat_powM, toMat_idM] at this
    exact this
  · have := toMat_ne_of_neAt (d := 133) (by norm_num) (by norm_num) h3
    simp only [toMat_powM, toMat_idM] at this
    exact this
  · have := toMat_eq_of_beq (p := 5) (d := 133) h4
    simp only [toMat_mulM, toMat_powM] at this
    exact this
  · have := toMat_ne_of_neAt (d := 133) (by norm_num) (by norm_num) h5
    simp only [toMat_mulM, toMat_powM] at this
    exact this
  · have := toMat_eq_of_beq (p := 5) (d := 133) h6
    simp only [toMat_mulM, toMat_subIdM, toMat_powM, toMat_zeroM] at this
    exact this
  · have := toMat_eq_of_beq (p := 5) (d := 133) h7
    simp only [toMat_mulM, toMat_addM, toMat_subIdM, toMat_powM, toMat_idM] at this
    exact this
  · have := toMat_eq_of_beq (p := 5) (d := 133) h8
    simp only [toMat_mulM, toMat_subIdM, toMat_powM] at this
    exact this
  · have := toMat_eq_of_beq (p := 5) (d := 133) h9
    simp only [toMat_mulM, toMat_subIdM, toMat_powM, toMat_zeroM] at this
    exact this
  · have := toMat_ne_of_neAt (d := 133) (by norm_num) (by norm_num) h10
    simp only [toMat_mulM, toMat_subIdM, toMat_powM, toMat_zeroM] at this
    exact this

end Core

section Tab

theorem toMat_tabMat' {t : Array ℕ} {g : JH} (ht : PRep hnsData.n t (permJ g)) :
    toMat 5 hnsData.d (tabMat hnsData (hnsData.orbit ())
      (invM 5 hnsData.d (colsMat hnsData.d (QVecs hnsData))) t) = mat hnsData g := by
  have hB := hnsBase
  unfold tabMat
  rw [toMat_mulM]
  have h1 : toMat 5 hnsData.d (colsMat hnsData.d (hnsData.Q.map fun q =>
      bytesToNats (hnsData.orbit ()).keys[t[q]!]!)) = mat hnsData g * basisM hnsData := by
    ext i j
    have hjQ : j.val < hnsData.Q.size := lt_of_lt_of_le j.isLt hB.Q_size
    have hlt := hB.Q_lt j.val hjQ
    have e1 : t[hnsData.Q[j.val]!]! = ((g • (⟨hnsData.Q[j.val]!, hlt⟩ : X)) : X).val :=
      ht ⟨_, hlt⟩
    have e2 := P_smul hB g ⟨hnsData.Q[j.val]!, hlt⟩
    rw [toMat_colsMat, toVec_apply, Matrix.mul_apply]
    rw [getElem!_pos _ j.val (by simpa using hjQ), Array.getElem_map, bytesToNats_get,
      ← getElem!_pos hnsData.Q j.val hjQ, e1]
    show (P hnsData ((g • (⟨hnsData.Q[j.val]!, hlt⟩ : X)) : X).val) i = _
    rw [e2, smul_vec, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [basisM_apply hB]
  rw [h1, mul_assoc, basisM_mul_inv hB, mul_one]

theorem toMat_tabMat {t : Array ℕ} {g : JH} (ht : PRep hnsData.n t (permJ g)) :
    toMat 5 133 (tabMat hnsData (hnsData.orbit ())
      (invM 5 hnsData.d (colsMat hnsData.d (QVecs hnsData))) t) = matJ g :=
  toMat_tabMat' ht

end Tab

section Vectors

theorem vec_fact_q {T Mq A Lam R W : Matrix (Fin 133) (Fin 133) (ZMod 5)}
    (hAL : A * Lam + R * T = 1) (hqA : (Mq - 1) * A = T * T * W) :
    ∀ v : Fin 133 → ZMod 5, T *ᵥ v = 0 → ∃ w, (Mq - 1) *ᵥ v = T *ᵥ (T *ᵥ w) := by
  intro v hv
  obtain ⟨u, hu⟩ : ∃ u, v = A *ᵥ u := by
    refine ⟨Lam *ᵥ v, ?_⟩
    calc v = (1 : Matrix (Fin 133) (Fin 133) (ZMod 5)) *ᵥ v := (Matrix.one_mulVec v).symm
      _ = (A * Lam + R * T) *ᵥ v := by rw [hAL]
      _ = A *ᵥ (Lam *ᵥ v) + R *ᵥ (T *ᵥ v) := by
        rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = A *ᵥ (Lam *ᵥ v) := by rw [hv, Matrix.mulVec_zero, add_zero]
  subst hu
  refine ⟨W *ᵥ u, ?_⟩
  calc (Mq - 1) *ᵥ (A *ᵥ u) = ((Mq - 1) * A) *ᵥ u := by rw [Matrix.mulVec_mulVec]
    _ = (T * T * W) *ᵥ u := by rw [hqA]
    _ = T *ᵥ (T *ᵥ (W *ᵥ u)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem vec_fact_s {T Ms A Phi : Matrix (Fin 133) (Fin 133) (ZMod 5)}
    (hTA : T * A = 0) (hPT : Phi * (T * T) = 0) (hPs : Phi * (Ms - 1) * A ≠ 0) :
    ∃ v : Fin 133 → ZMod 5, T *ᵥ v = 0 ∧ ∀ w, (Ms - 1) *ᵥ v ≠ T *ᵥ (T *ᵥ w) := by
  by_contra hcon
  push Not at hcon
  apply hPs
  ext i j
  have hv : T *ᵥ (A *ᵥ Pi.single j 1) = 0 := by
    rw [Matrix.mulVec_mulVec, hTA, Matrix.zero_mulVec]
  obtain ⟨w, hw⟩ := hcon _ hv
  have h0 : (Phi * (Ms - 1) * A) *ᵥ Pi.single j 1 = 0 := by
    calc (Phi * (Ms - 1) * A) *ᵥ Pi.single j 1
        = Phi *ᵥ ((Ms - 1) *ᵥ (A *ᵥ Pi.single j 1)) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = Phi *ᵥ (T *ᵥ (T *ᵥ w)) := by rw [hw]
      _ = 0 := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, hPT, Matrix.zero_mulVec]
  have h1 := congrFun h0 i
  rw [Matrix.mulVec_single_one] at h1
  exact h1

end Vectors

section Facts

noncomputable def hn5C : JH := seedWordJ cWord

noncomputable def hn5Q : JH := g3J ^ 29 * hn5C * g3J * hn5C * g3J ^ 29

theorem matJ_hn5Q :
    matJ hn5Q = matJ g3J ^ 29 * matJ hn5C * matJ g3J * matJ hn5C * matJ g3J ^ 29 := by
  simp only [hn5Q, matJ_mul, matJ_pow]

theorem cWord_letters : ∀ l ∈ cWord, l = 1 ∨ l = 2 := by decide

end Facts

end CFSG.HardMathSupport.Dickson.I271.HNFive
