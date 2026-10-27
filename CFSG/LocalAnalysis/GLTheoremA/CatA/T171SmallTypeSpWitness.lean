module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open
open CFSG.LieType.SteinbergBR.EvenSp
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (det_eq_one_of_GL_two)

noncomputable section

private abbrev c3 : GL (Fin 2) (ZMod 2) := @tGL (ZMod 2) _ (ZMod.charP 2)

private def sGLMat : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 0, 1]

private theorem sGLMat_mul_self : sGLMat * sGLMat = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private def sGL : GL (Fin 2) (ZMod 2) := ⟨sGLMat, sGLMat, sGLMat_mul_self, sGLMat_mul_self⟩

private theorem sGL_pow_two : sGL ^ 2 = 1 := by
  apply Units.ext
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem sGL_ne_one : sGL ≠ 1 := by
  intro h
  have h10 := congrArg (fun g : GL (Fin 2) (ZMod 2) =>
    (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1) h
  simp [sGL, sGLMat] at h10

private def extendCoords (n m : ℕ) (hm : m ≤ n) :
    (Fin m → GL (Fin 2) (ZMod 2)) →* (Fin n → GL (Fin 2) (ZMod 2)) where
  toFun x j := if h : (j : ℕ) < m then x ⟨j, h⟩ else 1
  map_one' := by
    funext j
    by_cases h : (j : ℕ) < m <;> simp [h]
  map_mul' := by
    intro x y
    funext j
    by_cases h : (j : ℕ) < m <;> simp [h]

private lemma extendCoords_apply_of_lt {n m : ℕ} (hm : m ≤ n) (x : Fin m → GL (Fin 2) (ZMod 2))
    {j : Fin n} (h : (j : ℕ) < m) :
    extendCoords n m hm x j = x ⟨j, h⟩ := by
  show (if h' : (j : ℕ) < m then x ⟨j, h'⟩ else 1) = x ⟨j, h⟩
  rw [dif_pos h]

private lemma extendCoords_apply_of_not_lt {n m : ℕ} (hm : m ≤ n) (x : Fin m → GL (Fin 2) (ZMod 2))
    {j : Fin n} (h : ¬ (j : ℕ) < m) :
    extendCoords n m hm x j = 1 := by
  show (if h' : (j : ℕ) < m then x ⟨j, h'⟩ else 1) = 1
  rw [dif_neg h]

private def lastCoords (n : ℕ) (hn : 1 ≤ n) :
    GL (Fin 2) (ZMod 2) →* (Fin n → GL (Fin 2) (ZMod 2)) where
  toFun g j := if j = ⟨n - 1, by omega⟩ then g else 1
  map_one' := by
    funext j
    by_cases h : j = ⟨n - 1, by omega⟩ <;> simp [h]
  map_mul' := by
    intro g h
    funext j
    by_cases hj : j = ⟨n - 1, by omega⟩ <;> simp [hj]

private noncomputable def coordTorus (n m : ℕ) (hm : m ≤ n) :
    (Fin m → Subgroup.zpowers c3) →* StatedSp n (ZMod 2) :=
  ((planeHom (K := ZMod 2) (n := n)).comp
    ((extendCoords n m hm).comp (MonoidHom.piMap fun _ =>
      (Subgroup.zpowers c3).subtype))).codRestrict
    (StatedSp n (ZMod 2)) (fun x => by
      apply planeHom_mem_statedSp
      intro j
      rw [MonoidHom.comp_apply]
      by_cases h : (j : ℕ) < m
      · rw [extendCoords_apply_of_lt hm _ h]
        exact det_of_mem_zpowers (Subtype.property (x ⟨j, h⟩))
      · rw [extendCoords_apply_of_not_lt hm _ h]
        exact det_eq_one_of_GL_two 1)

private noncomputable def lastGL (n : ℕ) (hn : 1 ≤ n) :
    GL (Fin 2) (ZMod 2) →* StatedSp n (ZMod 2) :=
  ((planeHom (K := ZMod 2) (n := n)).comp
    ((lastCoords n hn))).codRestrict (StatedSp n (ZMod 2)) (fun g => by
      apply planeHom_mem_statedSp
      intro j
      rw [show ((lastCoords n hn) g j) =
        (if j = ⟨n - 1, by omega⟩ then g else 1 : GL (Fin 2) (ZMod 2)) from rfl]
      by_cases h : j = ⟨n - 1, by omega⟩
      · rw [if_pos h]
        exact det_eq_one_of_GL_two g
      · rw [if_neg h]
        exact det_eq_one_of_GL_two 1)

private theorem lastGL_ne_one (n : ℕ) (hn : 1 ≤ n) :
    lastGL n hn sGL ≠ 1 := by
  intro h
  have h' : planeHom (K := ZMod 2) (n := n) (fun j =>
      if j = ⟨n - 1, by omega⟩ then sGL else 1) = 1 := by
    have := congrArg (fun g : StatedSp n (ZMod 2) =>
      (g : GL (Fin n ⊕ Fin n) (ZMod 2))) h
    simpa [lastGL, lastCoords] using this
  rw [← map_one (planeHom (K := ZMod 2) (n := n))] at h'
  have h'' := planeHom_injective h'
  have h3 := congrFun h'' ⟨n - 1, by omega⟩
  simp at h3
  exact sGL_ne_one h3

private theorem lastGL_pow_two (n : ℕ) (hn : 1 ≤ n) :
    (lastGL n hn sGL) ^ 2 = 1 := by
  rw [← map_pow, sGL_pow_two, map_one]

private theorem orderOf_lastGL (n : ℕ) (hn : 1 ≤ n) :
    orderOf (lastGL n hn sGL) = 2 :=
  orderOf_eq_prime (lastGL_pow_two n hn) (lastGL_ne_one n hn)

private noncomputable def lastT2 (n : ℕ) (hn : 1 ≤ n) : Subgroup (StatedSp n (ZMod 2)) :=
  Subgroup.zpowers (lastGL n hn sGL)

private theorem lastT2_isPGroup (n : ℕ) (hn : 1 ≤ n) : IsPGroup 2 (lastT2 n hn) := by
  apply IsPGroup.of_card (n := 1)
  rw [lastT2, Nat.card_zpowers, orderOf_lastGL, pow_one]

private theorem lastT2_ne_bot (n : ℕ) (hn : 1 ≤ n) : lastT2 n hn ≠ ⊥ := by
  intro h
  have hmem : lastGL n hn sGL ∈ lastT2 n hn := Subgroup.mem_zpowers _
  rw [h, Subgroup.mem_bot] at hmem
  exact lastGL_ne_one n hn hmem

private theorem coordTorus_injective (n m : ℕ) (hm : m ≤ n) :
    Function.Injective (coordTorus n m hm) := by
  intro x y hxy
  have h1 : planeHom (K := ZMod 2) (n := n)
      (fun j => if h : (j : ℕ) < m then (x ⟨j, h⟩ : GL (Fin 2) (ZMod 2)) else 1) =
      planeHom (K := ZMod 2) (n := n)
      (fun j => if h : (j : ℕ) < m then (y ⟨j, h⟩ : GL (Fin 2) (ZMod 2)) else 1) := by
    have := congrArg (fun g : StatedSp n (ZMod 2) => (g : GL (Fin n ⊕ Fin n) (ZMod 2))) hxy
    simpa [coordTorus, extendCoords, MonoidHom.piMap_apply, Subgroup.subtype_apply] using this
  have h2 := congrFun (planeHom_injective h1)
  funext j
  have h3 := h2 ⟨j, lt_of_lt_of_le j.isLt hm⟩
  simpa [dif_pos j.isLt] using h3

private theorem card_coordTorus_range (n m : ℕ) (hm : m ≤ n) :
    Nat.card (coordTorus n m hm).range = 3 ^ m := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (coordTorus_injective n m hm)).toEquiv]
  rw [Nat.card_fun, Nat.card_fin, Nat.card_zpowers, orderOf_tGL]

private theorem isElemAbelian_coordTorus_range (n m : ℕ) (hm : m ≤ n) :
    IsElemAbelian 3 (coordTorus n m hm).range := by
  have hcomm : ∀ x y : Fin m → Subgroup.zpowers c3, x * y = y * x := by
    intro x y
    funext j
    exact (Subgroup.zpowers_isMulCommutative c3).is_comm.comm (x j) (y j)
  have hexp : ∀ x : Fin m → Subgroup.zpowers c3, x ^ 3 = 1 := by
    intro x
    funext j
    have h := pow_card_eq_one' (x := x j)
    rw [show Nat.card ↥(Subgroup.zpowers c3) = 3 by
      rw [Nat.card_zpowers, orderOf_tGL]] at h
    exact h
  haveI : IsElementaryAbelian 3 (coordTorus n m hm).range :=
    isElementaryAbelian_range (coordTorus n m hm) hcomm hexp
  exact isElemAbelian_of_isElementaryAbelian

private theorem coordTorus_commute_lastGL (n m : ℕ) (hm : m < n)
    (x : Fin m → Subgroup.zpowers c3) (g : GL (Fin 2) (ZMod 2)) :
    Commute (coordTorus n m (le_of_lt hm) x) (lastGL n (by omega) g) := by
  have hcomm : ∀ j : Fin n,
      (if h : (j : ℕ) < m then (x ⟨j, h⟩ : GL (Fin 2) (ZMod 2)) else 1) *
        (if j = ⟨n - 1, by omega⟩ then g else 1) =
      (if j = ⟨n - 1, by omega⟩ then g else 1) *
        (if h : (j : ℕ) < m then (x ⟨j, h⟩ : GL (Fin 2) (ZMod 2)) else 1) := by
    intro j
    by_cases h : (j : ℕ) < m
    · have hj : j ≠ ⟨n - 1, by omega⟩ := by
        intro hjeq
        have : (j : ℕ) = n - 1 := by rw [hjeq]
        omega
      simp only [dif_pos h, if_neg hj, mul_one, one_mul]
    · by_cases hj : j = ⟨n - 1, by omega⟩
      · have h' : ¬ (⟨n - 1, by omega⟩ : Fin n).val < m := by simpa [hj] using h
        rw [hj]
        simp only [dif_neg h', if_pos rfl, mul_one, one_mul]
      · simp only [dif_neg h, if_neg hj, mul_one, one_mul]
  apply Subtype.ext
  show (planeHom (K := ZMod 2) (n := n) (fun j =>
      if h : (j : ℕ) < m then (x ⟨j, h⟩ : GL (Fin 2) (ZMod 2)) else 1) :
        GL (Fin n ⊕ Fin n) (ZMod 2)) *
      (planeHom (K := ZMod 2) (n := n) (fun j =>
        if j = ⟨n - 1, by omega⟩ then g else 1) :
        GL (Fin n ⊕ Fin n) (ZMod 2)) =
      (planeHom (K := ZMod 2) (n := n) (fun j =>
        if j = ⟨n - 1, by omega⟩ then g else 1) :
        GL (Fin n ⊕ Fin n) (ZMod 2)) *
      (planeHom (K := ZMod 2) (n := n) (fun j =>
        if h : (j : ℕ) < m then (x ⟨j, h⟩ : GL (Fin 2) (ZMod 2)) else 1) :
        GL (Fin n ⊕ Fin n) (ZMod 2))
  rw [← map_mul, ← map_mul]
  congr 1
  funext j
  exact hcomm j

private theorem twoLocal_coordTorus (n m : ℕ) (hm : m < n) :
    TwoLocal (coordTorus n m (le_of_lt hm)).range := by
  let hn : 1 ≤ n := by omega
  refine ⟨lastT2 n hn, lastT2_isPGroup n hn, lastT2_ne_bot n hn, ?_⟩
  rintro b ⟨x, rfl⟩
  exact CFSG.ClassicalInvolution.GlaubermanAut.mem_normalizer_zpowers_of_commute
    (coordTorus_commute_lastGL n m hm x sGL)

theorem exists_twoLocal_elementaryAbelian (n m : ℕ) (hm : m < n) :
    ∃ B : Subgroup (StatedSp n (ZMod 2)), IsElemAbelian 3 B ∧ Nat.card B = 3 ^ m ∧
      TwoLocal B :=
  ⟨(coordTorus n m (le_of_lt hm)).range, isElemAbelian_coordTorus_range n m (le_of_lt hm),
    card_coordTorus_range n m (le_of_lt hm), twoLocal_coordTorus n m hm⟩

end

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
