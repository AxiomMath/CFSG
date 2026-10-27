module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyN1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyLink
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyHHBase

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.LyObs

open Subgroup CFSG CFSG.ABGLocalTools

theorem carry {Y J : Type*} [Group Y] [Group J] (e1 : Y ≃* J) {b : MulAut Y} {y g : Y} {x : J}
    (hb : b = MulAut.conj y) (hg : g * y * g⁻¹ = e1.symm x) {E : Subgroup J}
    (hE5 : IsPGroup 5 ↥E) (hEx : ∀ z ∈ E, x * z * x⁻¹ ∈ E) {z : J} (hzE : z ∈ E)
    (hzx : x * z * x⁻¹ ≠ z) :
    ∃ E' : Subgroup Y, IsPGroup 5 ↥E' ∧ (∀ w ∈ E', b w ∈ E') ∧ ∃ w ∈ E', b w ≠ w := by
  let θ : J →* Y :=
    { toFun := fun w => g⁻¹ * e1.symm w * g
      map_one' := by simp
      map_mul' := fun a b => by rw [map_mul]; group }
  have hθw : ∀ w : J, θ w = g⁻¹ * e1.symm w * g := fun w => rfl
  have hθ : Function.Injective θ := fun a b h =>
    e1.symm.injective (mul_left_cancel (mul_right_cancel (by rw [← hθw, ← hθw]; exact h)))
  have hy' : y = g⁻¹ * e1.symm x * g := by rw [← hg]; group
  have hbθ : ∀ w : J, b (θ w) = θ (x * w * x⁻¹) := by
    intro w
    rw [hb, MulAut.conj_apply, hθw, hθw, map_mul, map_mul, map_inv, hy']
    group
  refine ⟨E.map θ, hE5.map θ, ?_, θ z, ⟨z, hzE, rfl⟩, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [hbθ]
    exact ⟨_, hEx w hw, rfl⟩
  · rw [hbθ]
    intro h
    exact hzx (hθ h)

theorem ly_hhobs
    {Y : Type} [Group Y] [Finite Y]
    (hY : Blueprint.NativeSporadic.IsSporadic Y .Ly) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {b : MulAut Y} (hb : orderOf b = p) {R₀ : Subgroup Y} (hR₀ : IsSylowOf 2 R₀ ⊤)
    (hpg : IsPGroup p ↥(closure {c : MulAut Y | ∃ r ∈ R₀,
      c = MulAut.conj r * b * (MulAut.conj r)⁻¹})) :
    p = 3 ∧ ∃ E : Subgroup Y, IsPGroup 5 ↥E ∧ (∀ z ∈ E, b z ∈ E) ∧ ∃ z ∈ E, b z ≠ z := by
  obtain ⟨hp3, τ, y, s, hy, hτ, hy3, hs, hyτ, hsτ, hys⟩ := LyN1.ly_n1 hY hp2 hb hR₀ hpg
  refine ⟨hp3, ?_⟩
  obtain ⟨e⟩ := id hY
  let e1 : Y ≃* CFSG.Sporadic.Ly.J := e.trans CFSG.Sporadic.Ly.lyEquivJ
  obtain ⟨x, s₀, hx3, hs7, hax, has, hxs, E, hE5, hEx, z, hzE, hzx⟩ := LyHH.hh_obstruction
  have hord2 : orderOf (e1.symm CFSG.Sporadic.Ly.a) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact CFSG.Sporadic.Ly.orderOf_a
  have hord3 : orderOf (e1.symm x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx3
  have hord7 : orderOf (e1.symm s₀) = 7 := by rw [MulEquiv.orderOf_eq]; exact hs7
  obtain ⟨g, hg⟩ := LyLink.ly_conj_threeSeven hY hτ hy3 hs hyτ hsτ hys hord2 hord3 hord7
    (by simpa only [map_mul] using congrArg e1.symm hax.symm)
    (by simpa only [map_mul] using congrArg e1.symm has.symm)
    (by simpa only [map_mul] using congrArg e1.symm hxs)
  exact @carry Y CFSG.Sporadic.Ly.J _ inferInstance e1 b y g x hy hg E hE5 hEx z hzE hzx

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.LyObs
