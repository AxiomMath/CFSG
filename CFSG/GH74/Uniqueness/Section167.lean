module

public import CFSG.GH74.Uniqueness.Section167B
public import CFSG.GH74.Uniqueness.Section167A

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma167
    (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) : Lemma167Stmt Z M := by
  intro p hp hp2 Y hY h3
  by_contra hnot
  have hs : ∃ s ∈ Z, s ∈ normalizer (Y : Set X) ∧ ¬ ∀ y ∈ Y, s * y = y * s := by
    by_contra h
    push Not at h
    apply hnot
    rw [zHull, Subgroup.closure_le]
    rintro s ⟨hsZ, hsN⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (h s hsZ hsN y hy).symm
  obtain ⟨s, hsZ, hsN, hsC⟩ := hs
  obtain ⟨-, -, hZCY, -⟩ := S.lemma167_stepA hp hp2 hY h3 hsZ hsN hsC
  obtain ⟨W, hYW, hW⟩ : ∃ W : Subgroup X, Y ≤ W ∧ IsMaxFixingThree M p W := by
    have hfin : {U : Subgroup X | Y ≤ U ∧ IsPGroup p U ∧
        3 ≤ (omegaFix M (U : Set X)).ncard}.Finite := Set.toFinite _
    obtain ⟨W, hWmax⟩ := hfin.exists_maximal ⟨Y, le_rfl, hY, h3⟩
    exact ⟨W, hWmax.1.1, ⟨hWmax.1.2.1, hWmax.1.2.2⟩, fun R hR hle =>
      hWmax.2 ⟨hWmax.1.1.trans hle, hR⟩ hle⟩
  obtain ⟨s', hs'Z, hs'N⟩ := S.lemma167_stepB h166 hp hp2 hW
  have hs'C : ¬ ∀ w ∈ W, s' * w = w * s' := fun hall =>
    hZCY s' hs'Z (fun y hy => hall y (hYW hy))
  obtain ⟨hfixW, -, -, hZstW⟩ := S.lemma167_stepA hp hp2 hW.1.1 hW.1.2 hs'Z hs'N hs'C
  exact S.lemma167_stepC hp hW hs'Z hs'N hfixW hZstW

end CFSG.GH74.Uniqueness
