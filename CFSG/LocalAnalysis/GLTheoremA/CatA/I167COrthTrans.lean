module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open

variable {S T : Type} [Group S] [Group T]

@[expose] def COrthInnerImage (e : S ≃* T) (Bb : Subgroup (MulAut S)) : Subgroup T :=
  (Bb.comap (MulAut.conj : S →* MulAut S)).map e.toMonoidHom

theorem i167COrth_innerImage_mem (e : S ≃* T) {Bb : Subgroup (MulAut S)} {a₀ : S}
    (h : (MulAut.conj a₀ : MulAut S) ∈ Bb) : e a₀ ∈ COrthInnerImage e Bb :=
  ⟨a₀, h, rfl⟩

theorem i167COrth_descent_elem (e : S ≃* T) {p : ℕ} (hZ : Subgroup.center S = ⊥)
    {Bb : Subgroup (MulAut S)} (hBb : IsElemAbelian p Bb) : IsElemAbelian p (COrthInnerImage e Bb) := by
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  haveI : IsMulCommutative Bb := hBb.1
  constructor
  · rw [isMulCommutative_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_comap] at hs ht
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hst : s * t = t * s := by
      apply hinj
      rw [map_mul, map_mul]
      exact congrArg Subtype.val
        (mul_comm' (⟨MulAut.conj s, hs⟩ : Bb) ⟨MulAut.conj t, ht⟩)
    rw [← map_mul, ← map_mul, hst]
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_comap] at hs
    have hs_pow : s ^ p = 1 := by
      apply hinj
      rw [map_pow, map_one]
      exact hBb.2 (MulAut.conj s) hs
    rw [← map_pow, hs_pow, map_one]

theorem i167COrth_descent_max (e : S ≃* T) {p : ℕ} {Bb : Subgroup (MulAut S)}
    (hBinn : ∀ β ∈ Bb, ∃ s : S, (MulAut.conj s : MulAut S) = β)
    (hScp : ∀ s : S, (∀ β ∈ Bb, β s = s) → s ^ p = 1 → (MulAut.conj s : MulAut S) ∈ Bb) :
    ∀ E : Subgroup T, IsElemAbelian p E → COrthInnerImage e Bb ≤ E → E = COrthInnerImage e Bb := by
  intro E hE hAE
  refine le_antisymm ?_ hAE
  intro y hy
  haveI : IsMulCommutative E := hE.1
  let s : S := e.symm y
  have hys : e s = y := e.apply_symm_apply y
  have hs_pow : s ^ p = 1 := by
    apply e.injective
    rw [map_pow, map_one, hys]
    exact hE.2 y hy
  have hcomm : ∀ β ∈ Bb, β s = s := by
    intro β hβ
    obtain ⟨s', hs'⟩ := hBinn β hβ
    have hs'B : (MulAut.conj s' : MulAut S) ∈ Bb := by rw [hs']; exact hβ
    have hs'mem : e s' ∈ COrthInnerImage e Bb := ⟨s', hs'B, rfl⟩
    have hEc : e s' * y = y * e s' :=
      congrArg Subtype.val (mul_comm' (⟨e s', hAE hs'mem⟩ : E) ⟨y, hy⟩)
    have h2 : s' * s = s * s' := by
      have h4 := congrArg (fun z : T => e.symm z) hEc
      simpa only [map_mul, MulEquiv.symm_apply_apply] using h4
    rw [← hs', MulAut.conj_apply, h2, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : (MulAut.conj s : MulAut S) ∈ Bb := hScp s hcomm hs_pow
  exact ⟨s, hconj, hys⟩

theorem i167COrth_descent_cent (e : S ≃* T) (hZ : Subgroup.center S = ⊥) {Bb : Subgroup (MulAut S)}
    {a₀ : S} {J : Subgroup S}
    (hCent : ∀ β ∈ Bb, (∀ j ∈ J, β j = j) → β ∈ Subgroup.zpowers (MulAut.conj a₀ : MulAut S)) :
    ∀ a ∈ COrthInnerImage e Bb, (∀ j ∈ J.map e.toMonoidHom, a * j = j * a) →
      a ∈ Subgroup.zpowers (e a₀) := by
  intro a ha hcomm
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha
  rw [Subgroup.mem_comap] at hs
  have hβ : (MulAut.conj s : MulAut S) ∈ Subgroup.zpowers (MulAut.conj a₀) := by
    refine hCent (MulAut.conj s) hs ?_
    intro j hj
    have hje : e j ∈ J.map e.toMonoidHom := ⟨j, hj, rfl⟩
    have h := hcomm (e j) hje
    change e s * e j = e j * e s at h
    have h' : s * j = j * s := by
      apply e.injective
      simpa only [map_mul] using h
    rw [MulAut.conj_apply, h', mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.mem_zpowers_iff] at hβ ⊢
  obtain ⟨i, hi⟩ := hβ
  refine ⟨i, ?_⟩
  have h_eq : a₀ ^ i = s := by
    apply CFSG.mulAutConj_injective_of_center_eq_bot hZ
    rw [map_zpow]
    exact hi
  rw [← h_eq, map_zpow]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.I167

end
