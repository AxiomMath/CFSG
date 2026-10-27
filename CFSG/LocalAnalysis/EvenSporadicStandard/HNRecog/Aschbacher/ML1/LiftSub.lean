module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreDefs
public import CFSG.RankThree.Literature.FSmithForm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Subgroup CFSG.RankThree.Literature.FSmith

variable {C C' : Type} [Group C] [Group C'] {Q : Subgroup C} {Q' : Subgroup C'}
  {K : Subgroup C} {K' : Subgroup C'}

open Classical in
@[expose] noncomputable def liftSub (hK : Q ≤ K) (hK' : Q' ≤ K') (φ₀ : ↥Q ≃* ↥Q') : ↥K → ↥K' :=
  fun l => if h : (l : C) ∈ Q then ⟨(φ₀ ⟨(l : C), h⟩ : C'), hK' (φ₀ ⟨(l : C), h⟩).2⟩ else 1

theorem coe_liftSub_of_mem (hK : Q ≤ K) (hK' : Q' ≤ K') (φ₀ : ↥Q ≃* ↥Q') {l : ↥K}
    (h : (l : C) ∈ Q) :
    ((liftSub hK hK' φ₀ l : ↥K') : C') = (φ₀ ⟨(l : C), h⟩ : C') := by
  unfold liftSub
  rw [dif_pos h]

theorem isSubIso_liftSub (hK : Q ≤ K) (hK' : Q' ≤ K') (φ₀ : ↥Q ≃* ↥Q') :
    IsSubIso (Q.subgroupOf K) (Q'.subgroupOf K') (liftSub hK hK' φ₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hx' : (x : C) ∈ Q := hx
    have hy' : (y : C) ∈ Q := hy
    have hxy : ((x * y : ↥K) : C) ∈ Q := by simpa using Q.mul_mem hx' hy'
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [coe_liftSub_of_mem hK hK' φ₀ hxy, coe_liftSub_of_mem hK hK' φ₀ hx',
      coe_liftSub_of_mem hK hK' φ₀ hy']
    rw [show (⟨((x * y : ↥K) : C), hxy⟩ : ↥Q) = ⟨(x : C), hx'⟩ * ⟨(y : C), hy'⟩ from
      Subtype.ext rfl, map_mul φ₀]
    rfl
  · intro x hx
    rw [Subgroup.mem_subgroupOf, coe_liftSub_of_mem hK hK' φ₀ hx]
    exact (φ₀ ⟨(x : C), hx⟩).2
  · intro x hx y hy hxy
    apply Subtype.ext
    have hx' : ((liftSub hK hK' φ₀ x : ↥K') : C') = (φ₀ ⟨(x : C), hx⟩ : C') :=
      coe_liftSub_of_mem hK hK' φ₀ hx
    have hy' : ((liftSub hK hK' φ₀ y : ↥K') : C') = (φ₀ ⟨(y : C), hy⟩ : C') :=
      coe_liftSub_of_mem hK hK' φ₀ hy
    have hval : (φ₀ ⟨(x : C), hx⟩ : C') = (φ₀ ⟨(y : C), hy⟩ : C') := by
      have := congrArg (fun z : ↥K' => (z : C')) hxy
      rwa [hx', hy'] at this
    have hxy' : (⟨(x : C), hx⟩ : ↥Q) = ⟨(y : C), hy⟩ := φ₀.injective (Subtype.ext hval)
    exact congrArg (fun z : ↥Q => (z : C)) hxy'
  · intro y hy
    refine ⟨⟨((φ₀.symm ⟨(y : C'), hy⟩ : ↥Q) : C), hK (φ₀.symm ⟨(y : C'), hy⟩).2⟩, ?_, ?_⟩
    · exact (φ₀.symm ⟨(y : C'), hy⟩).2
    · apply Subtype.ext
      rw [coe_liftSub_of_mem hK hK' φ₀ (φ₀.symm ⟨(y : C'), hy⟩).2]
      simp

theorem compat_liftSub_iff [hQn : Q.Normal] [hQn' : Q'.Normal] (hK : Q ≤ K) (hK' : Q' ≤ K')
    (φ₀ : ↥Q ≃* ↥Q') (l : ↥K) (l' : ↥K') :
    Compat (Q.subgroupOf K) (liftSub hK hK' φ₀) l l' ↔
      ∀ x : ↥Q, φ₀ (conjAut hQn (l : C) x) = conjAut hQn' (l' : C') (φ₀ x) := by
  constructor
  · intro h x
    unfold Compat at h
    let xK : ↥K := ⟨(x : C), hK x.2⟩
    have hxK : xK ∈ Q.subgroupOf K := x.2
    have key := h xK hxK
    have hconj : ((l * xK * l⁻¹ : ↥K) : C) = (l : C) * (x : C) * (l : C)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    have hmem : ((l * xK * l⁻¹ : ↥K) : C) ∈ Q := by
      rw [hconj]; exact hQn.conj_mem (x : C) x.2 (l : C)
    have h1 : ((liftSub hK hK' φ₀ (l * xK * l⁻¹) : ↥K') : C')
        = (φ₀ (conjAut hQn (l : C) x) : C') := by
      rw [coe_liftSub_of_mem hK hK' φ₀ (l := l * xK * l⁻¹) hmem]
      have harg : (⟨((l * xK * l⁻¹ : ↥K) : C), hmem⟩ : ↥Q) = conjAut hQn (l : C) x := by
        apply Subtype.ext
        rw [conjAut_apply]
        rfl
      rw [harg]
    have h2 : ((l' * liftSub hK hK' φ₀ xK * l'⁻¹ : ↥K') : C')
        = (conjAut hQn' (l' : C') (φ₀ x) : C') := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [coe_liftSub_of_mem hK hK' φ₀ (l := xK) x.2, conjAut_apply]
    have hkey := congrArg (fun z : ↥K' => (z : C')) key
    rw [h1, h2] at hkey
    exact Subtype.ext hkey
  · intro h
    unfold Compat
    intro x hx
    have hxQ : (x : C) ∈ Q := hx
    have hconj : ((l * x * l⁻¹ : ↥K) : C) = (l : C) * (x : C) * (l : C)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hmem : ((l * x * l⁻¹ : ↥K) : C) ∈ Q := by
      rw [hconj]; exact hQn.conj_mem (x : C) hxQ (l : C)
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [coe_liftSub_of_mem hK hK' φ₀ (l := l * x * l⁻¹) hmem,
      coe_liftSub_of_mem hK hK' φ₀ (l := x) hxQ]
    have harg : (⟨((l * x * l⁻¹ : ↥K) : C), hmem⟩ : ↥Q)
        = conjAut hQn (l : C) ⟨(x : C), hxQ⟩ := by
      apply Subtype.ext
      rw [conjAut_apply, hconj]
    have hh := congrArg (fun z : ↥Q' => (z : C')) (h ⟨(x : C), hxQ⟩)
    rw [harg, hh, conjAut_apply]

end CFSG.EvenSporadicStandard.HNRecog.ML1
