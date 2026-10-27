module

public import CFSG.GH74.Uniqueness.Section166E

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.cor166
    (S : ZDSetup X Z M) (h163 : Lemma163Stmt Z M) (h164 : Lemma164Stmt Z M)
    (h165 : Prop165Stmt Z M) : Cor166Stmt Z M := by
  intro c
  obtain ⟨n, i, e, hB⟩ := (h163 c).1
  exact ⟨Cor166.cor166a S c h164 h165 hB, Cor166.cor166b S c h163 h164 h165 hB,
    ⟨Cor166.cor166c_conj S c h163 h164 h165 hB,
      fun y hy => Cor166.cor166c_invol S c h163 h164 h165 hB hy⟩,
    fun W hW4 hW2 => Cor166.cor166d S c h163 h164 h165 hB W hW4 hW2,
    fun Y hY => Cor166.cor166e S c h163 h164 h165 hB Y hY⟩

end CFSG.GH74.Uniqueness
