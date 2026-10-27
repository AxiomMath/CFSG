module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx65

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem Fused8.nonempty_equiv_imgBar (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    Nonempty (↥S ≃* ↥(imgBar z S)) := by
  have hSC : S ≤ Cz z := hf.S_le_C hII
  let φ : ↥(S.subgroupOf (Cz z)) →* CentralizerBar z := (piC z).comp (S.subgroupOf (Cz z)).subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (x : ↥(Cz z)) ∈ pPrimeCore 2 ↥(Cz z) := by
      have : piC z (x : ↥(Cz z)) = 1 := hx
      exact (QuotientGroup.eq_one_iff _).1 this
    have hxO : ((x : ↥(Cz z)) : G) ∈ Oz z := ⟨(x : ↥(Cz z)), hx1, rfl⟩
    have hxS : ((x : ↥(Cz z)) : G) ∈ S := x.2
    have hbot : S ⊓ Oz z = ⊥ := M.inf_eq_bot_of_pgroup_odd (hf.S_pgroup hII) card_Oz_odd
    have : ((x : ↥(Cz z)) : G) ∈ S ⊓ Oz z := ⟨hxS, hxO⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subtype.ext (Subtype.ext this)
  have hrange : φ.range = imgBar z S := by
    show ((piC z).comp (S.subgroupOf (Cz z)).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  exact ⟨((Subgroup.subgroupOfEquivOfLe hSC).symm.trans (MonoidHom.ofInjective hinj)).trans
    (MulEquiv.subgroupCongr hrange)⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
