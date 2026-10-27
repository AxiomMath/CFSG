module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Filter
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Groups.Alt
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Groups.PSL2
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Groups.U33
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Groups.L34
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Groups.U42

public section

namespace CFSG.GF2Type.Smith1979.OmegaPlus

section FilterBinders


theorem false_of_layerData_catalog {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : CFSG.Blueprint.Catalog X) (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hord : Nat.card X ∣ 348364800) (hle : Nat.card X ≤ 30240) {A : Subgroup (MulAut X)}
    {τ : MulAut X} {B : Subgroup X} (D : LayerData X A τ B) : False := by
  rcases filter_W4Plus hX hnonab hord hle with ⟨n, hn5, hn8, ⟨e⟩⟩ | h7 | h8 | hu | hl | hs
  · interval_cases n
    · exact false_of_alt5 D e
    · exact false_of_alt6 D e
    · exact false_of_alt7 D e
    · exact false_of_alt8 D e
  · exact h7.elim (false_of_psl27 D)
  · exact h8.elim (false_of_psl28 D)
  · exact false_of_u33 D hu
  · exact false_of_l34 D hl
  · exact false_of_u42 D hs

end FilterBinders

end CFSG.GF2Type.Smith1979.OmegaPlus
