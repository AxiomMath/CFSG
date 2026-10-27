module

public import CFSG.GH74.GLS.Stage4.HexCD4Alg1
public import CFSG.GH74.GLS.Stage4.HexCD4Act

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F K : Type} [Field F] [Field K]

theorem d4Funcs_of_data (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData4 root F K)
    (Gl : GalData F K) (hθ : D.θ = Gl.θ) {β : K → G → F} (hβ : PairData D β) {p3 : K → G}
    (hp3add : ∀ a b, p3 (a + b) = p3 a * p3 b) (hp3inj : Function.Injective p3)
    (hp3β : ∀ a s, β s (p3 a) = Gl.trF (a * s))
    {a2 a4 : K → K → F} {L : K → K → G} (hcd : CommData4 D a2 a4 L) {A2 A4 : F → K → F}
    {g3 : F → K → G} (had : ActData4 D A2 A4 g3) {ℓ : K → K → K} (hℓ : ∀ s t, L s t = p3 (ℓ s t))
    {gh : F → K → K} (hgh : ∀ c s, g3 c s = p3 (gh c s)) :
    D4Funcs Gl a2 a4 ℓ A2 A4 gh where
  c1 s s' t := by
    have h := (comm15_add_s4 R hC D hβ hcd s s' t).1
    rwa [hℓ s' t, hp3β] at h
  c2 s s' t := by
    have h := (comm15_add_s4 R hC D hβ hcd s s' t).2.1
    rw [hℓ (s + s') t, hℓ s' t, hℓ s t, ← hp3add] at h
    exact hp3inj h
  c3 s s' t := (comm15_add_s4 R hC D hβ hcd s s' t).2.2
  c4 s t t' := (comm15_add_t4 R hC D hβ hcd s t t').1
  c5 s t t' := by
    have h := (comm15_add_t4 R hC D hβ hcd s t t').2.1
    rw [hℓ s (t + t'), hℓ s t, hℓ s t', ← hp3add] at h
    exact hp3inj h
  c6 s t t' := by
    have h := (comm15_add_t4 R hC D hβ hcd s t t').2.2
    rwa [hℓ s t', hp3β] at h
  c7 x hx s t := by
    have h := comm15_torus4 R D hcd (Units.mk0 x⁻¹ (inv_ne_zero hx)) s t
    simp only [Units.val_mk0, inv_inv, map_inv₀, hθ] at h ⊢
    refine ⟨h.1, hp3inj (by rw [← hℓ, ← hℓ]; exact h.2.1), h.2.2⟩
  d1 c c' s := (act_add_c4 R hC D hβ had c c' s).1
  d2 c c' s := by
    have h := (act_add_c4 R hC D hβ had c c' s).2.1
    rw [hgh (c + c') s, hgh c' s, hgh c s, ← hp3add] at h
    exact hp3inj h
  d3 c c' s := by
    have h := (act_add_c4 R hC D hβ had c c' s).2.2
    rw [hgh c s, hp3β, hθ] at h
    exact h
  d4 c s s' := by
    have h := (act_add_s4 R hC D hβ hcd had c s s').1
    rw [hgh c s', hp3β, hθ] at h
    exact h
  d5 c s s' := by
    have h := (act_add_s4 R hC D hβ hcd had c s s').2.1
    rw [hgh c (s + s'), hgh c s, hgh c s', hℓ s (D.θ c * s'), ← hp3add, ← hp3add] at h
    have h' := hp3inj h
    rw [hθ] at h'
    exact h'
  d6 c s s' := by
    have h := (act_add_s4 R hC D hβ hcd had c s s').2.2
    rw [hgh c s', hℓ s (D.θ c * s'), ← hp3add, hp3β, hθ] at h
    exact h
  d7 c s t := by
    have h := act_comm4 R hC D hβ hcd had c s t
    rw [hℓ s t, hgh c s, hp3β, hp3β, hθ] at h
    exact h
  d8 x hx c s := by
    have h := act_torus4 R D had (Units.mk0 x⁻¹ (inv_ne_zero hx)) c s
    simp only [Units.val_mk0, inv_pow, inv_inv, map_inv₀, hθ] at h ⊢
    refine ⟨h.1, hp3inj (by rw [← hgh, ← hgh]; exact h.2.1), h.2.2⟩

end CFSG.GH74.GLS.Stage4.Hex
