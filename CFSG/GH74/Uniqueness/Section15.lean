module

public import CFSG.GH74.Uniqueness.Section15Facts
public import CFSG.GH74.Uniqueness.Section156B
public import CFSG.GH74.Uniqueness.Section157
public import CFSG.GH74.Uniqueness.Section155

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.prop151
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M)
    (hH : Hering32Stmt) : Prop151Stmt Z M := by
  intro c n hL
  have F := S.facts15 h12 h131 hL
  obtain ⟨W, hWJ, hW1, hWP, hWn⟩ := F.lemma154
  obtain ⟨U, Y, hU, hY, hUp, hU2, hUsq, hYodd, hYdvd, hYcomm, hJUY, hfpf⟩ :=
    F.J_frob ⟨W, hWJ, hW1, hWP, hWn⟩
  have hWU : W ≤ U := fun w hw => hU2 w (hWJ hw) (hWP.to_le (zpowers_le.mpr hw))
  have hUne : U ≠ ⊥ := fun hb => hW1 (eq_bot_iff.mpr (hb ▸ hWU))
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    F.lemma155 hU hY hUp hU2 hUsq hYodd hYdvd hYcomm hJUY hfpf hUne
  have H : Hyp156 M n c.L c.D (c.D ⊓ c.L) (centralizer (c.L : Set X)) (zHull Z M) (oTwoIn M)
      U Y :=
    { F := F
      U_le := hU
      Y_le := hY
      U_pgroup := hUp
      U_two := hU2
      U_sq := hUsq
      Y_odd := hYodd
      Y_comm := hYcomm
      JUY := hJUY
      fpf := hfpf
      U_ne := hUne
      C0_two := h1
      C0_eq := h2
      inv_U := h3
      VD_eq := h4
      TI := h5
      NU := h6 }
  obtain ⟨u, C⟩ := H.conf156
  exact C.false hH

end CFSG.GH74.Uniqueness
