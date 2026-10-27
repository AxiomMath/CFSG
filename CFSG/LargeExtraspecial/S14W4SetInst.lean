module

public import CFSG.LargeExtraspecial.S14W4SetPi
public import CFSG.LargeExtraspecial.S14W4SetDictC
public import CFSG.LargeExtraspecial.S14W4SetNQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G]

namespace W4Hyp

variable {S : Setting G} {g : G} {t : S.O} {c : Config} (h : W4Hyp S g t c)
include h

theorem dictHyp : W4Dict.Hyp h.S₀ (ι S) (Nbar S g t) (Rbar S g t) t where
  inj := ι_injective S
  z_eq := rfl
  mem_QG := fun _ => h.mem_S₀_QG
  N_le := fun _ hy => MonoidHom.mem_range.mpr (exists_ι_eq (h.Nbar_le_map hy))
  R_lift := fun _ hy => by
    have hr := h.exists_R₀ hy
    cases hr with
    | intro r hr => exact ⟨r, h.R₀_le_M hr.1, hr.2⟩

omit h in
theorem ne_omegaPlus8b_of_minus (hm : c = .omegaMinus6) : c ≠ .omegaPlus8b := fun hc =>
  absurd (hm.symm.trans hc) (fun h' => by cases h')

omit h in
theorem ne_omegaPlus6_of_minus (hm : c = .omegaMinus6) : c ≠ .omegaPlus6 := fun hc =>
  absurd (hm.symm.trans hc) (fun h' => by cases h')

theorem irr [IsSimpleGroup G] (hNQ : NQIrredStmt) (hm : c = .omegaMinus6)
    (W : Submodule (ZMod 2) h.S₀.Qt) (hW : W4Dict.IsInv h.S₀ h.R₀ W) : W = ⊥ ∨ W = ⊤ :=
  W4Dict.irr_of h.dictHyp (hNQ G S g t c h.stage h.occ h.ext (ne_omegaPlus8b_of_minus hm)
    (ne_omegaPlus6_of_minus hm)) W hW

theorem lattice [IsSimpleGroup G] (hNQ6 : NQPlus6Stmt) (hp : c = .omegaPlus6) :
    ∃ W₁ W₂ : Submodule (ZMod 2) h.S₀.Qt, W4Dict.IsInv h.S₀ h.R₀ W₁ ∧
      W4Dict.IsInv h.S₀ h.R₀ W₂ ∧ W₁ ⊓ W₂ = ⊥ ∧ Nat.card W₁ = 2 ^ 4 ∧ Nat.card W₂ = 2 ^ 4 ∧
      ∀ W : Submodule (ZMod 2) h.S₀.Qt, W4Dict.IsInv h.S₀ h.R₀ W →
        W = ⊥ ∨ W = W₁ ∨ W = W₂ ∨ W = ⊤ := by
  have hocc : Config.omegaPlus6.Occurs S g t := hp ▸ h.occ
  have hU := hNQ6 G S g t h.stage hocc h.ext
  cases hU with
  | intro U₁ hU =>
  cases hU with
  | intro U₂ hU =>
  exact W4Dict.lattice_of h.dictHyp hU.1 hU.2.1 hU.2.2.1 hU.2.2.2.1 hU.2.2.2.2.1
    hU.2.2.2.2.2.1 hU.2.2.2.2.2.2.1 hU.2.2.2.2.2.2.2.1 hU.2.2.2.2.2.2.2.2.1
    hU.2.2.2.2.2.2.2.2.2

end W4Hyp

end CFSG.LargeExtraspecial.S14
