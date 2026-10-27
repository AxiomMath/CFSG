module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Equiv Subgroup

@[expose] noncomputable def conjPerm5 {K : Type*} [Group K] {A : Subgroup K} [A.Normal]
    (e : ↥A ≃* alternatingGroup (Fin 5)) : K →* Perm (Fin 5) :=
  (MulEquiv.ofBijective (MulAut.conjNormal : Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))).symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)

variable {K : Type*} [Group K] {A : Subgroup K} [A.Normal]

theorem conjNormal_conjPerm5 (e : ↥A ≃* alternatingGroup (Fin 5)) (k : K) :
    (MulAut.conjNormal (conjPerm5 e k) : MulAut (alternatingGroup (Fin 5))) =
      MulAut.congr e (MulAut.conjNormal k) :=
  (MulEquiv.ofBijective
    (MulAut.conjNormal : Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))).apply_symm_apply (MulAut.congr e (MulAut.conjNormal k))

theorem conjPerm5_conj (e : ↥A ≃* alternatingGroup (Fin 5)) (k : K) (a : ↥A) :
    (e (MulAut.conjNormal k a) : Perm (Fin 5)) =
      conjPerm5 e k * (e a : Perm (Fin 5)) * (conjPerm5 e k)⁻¹ := by
  have h := congrArg
    (fun f : MulAut (alternatingGroup (Fin 5)) => ((f (e a) : alternatingGroup (Fin 5)) :
      Perm (Fin 5))) (conjNormal_conjPerm5 e k)
  simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h
  exact h.symm

theorem conjPerm5_of_mem (e : ↥A ≃* alternatingGroup (Fin 5)) (a : ↥A) :
    conjPerm5 e (a : K) = (e a : Perm (Fin 5)) := by
  apply (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
    (by norm_num)).1
  rw [conjNormal_conjPerm5]
  ext b
  rw [MulAut.conjNormal_val]
  simp [MulAut.congr_apply, MulAut.conj_apply, MulAut.conjNormal_apply]

theorem conjPerm5_eq_one_iff (e : ↥A ≃* alternatingGroup (Fin 5)) (k : K) :
    conjPerm5 e k = 1 ↔ k ∈ centralizer (A : Set K) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := conjPerm5_conj e k ⟨a, ha⟩
    rw [h, one_mul, inv_one, mul_one] at h1
    have h2 : MulAut.conjNormal k (⟨a, ha⟩ : ↥A) = ⟨a, ha⟩ :=
      e.injective (Subtype.ext h1)
    have h3 := congrArg Subtype.val h2
    rw [MulAut.conjNormal_apply] at h3
    simp only at h3
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  · intro h
    apply (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num)).1
    rw [conjNormal_conjPerm5, map_one]
    have h1 : MulAut.conjNormal k = (1 : MulAut ↥A) := by
      ext a
      rw [MulAut.conjNormal_apply]
      simp only [MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact (h a a.2).symm
    rw [h1, map_one]

structure Alt5Pair (A : Subgroup K) (w c : K) : Prop where
  sq_w : w * w = 1
  mem : c ∈ A
  sq_c : c * c = 1
  ne_one : c ≠ 1
  conj : ∀ a ∈ A, w * a * w⁻¹ = c * a * c⁻¹

namespace Alt5Pair

variable {w c : K}

theorem h₀_mem (hS : Alt5Pair A w c) : c⁻¹ * w ∈ centralizer (A : Set K) := by
  rw [mem_centralizer_iff]
  intro a ha
  have h : w * a = c * a * c⁻¹ * w := by rw [← hS.conj a ha]; group
  calc a * (c⁻¹ * w) = c⁻¹ * (c * a * c⁻¹ * w) := by group
    _ = c⁻¹ * (w * a) := by rw [← h]
    _ = c⁻¹ * w * a := by group

theorem w_eq (_hS : Alt5Pair A w c) : w = c * (c⁻¹ * w) := by
  group

theorem h₀_comm (hS : Alt5Pair A w c) : (c⁻¹ * w) * c = c * (c⁻¹ * w) :=
  (mem_centralizer_iff.1 hS.h₀_mem c hS.mem).symm

theorem h₀_sq (hS : Alt5Pair A w c) : (c⁻¹ * w) * (c⁻¹ * w) = 1 := by
  have h1 := hS.h₀_comm
  have h2 := hS.sq_w
  have h3 := hS.sq_c
  have hw := hS.w_eq
  set h₀ := c⁻¹ * w with hh
  calc h₀ * h₀ = (c * c) * (h₀ * h₀) := by rw [h3, one_mul]
    _ = c * (c * h₀) * h₀ := by group
    _ = c * (h₀ * c) * h₀ := by rw [h1]
    _ = (c * h₀) * (c * h₀) := by group
    _ = w * w := by rw [← hw]
    _ = 1 := h2

end Alt5Pair

end CFSG.EvenSporadicStandard.M12Std.Rbc
