module

public import CFSG.Holt.H78.Sec4Prop49End
public import CFSG.Holt.H78.Sec4FinalA
import CFSG.Holt.H78.Sec4Setting
import CFSG.Holt.H78.Sec4Lemma41
import CFSG.Holt.H78.Sec4Lemma48
import CFSG.Holt.H78.Sec4Prop49S6
import CFSG.Holt.H78.Sec4FinalC7

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open

section Final

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.nonempty_finConfig_of (hS : Sec4Setting G Ω)
    (hP43 : ∀ {α β : Ω}, α ≠ β → IsEmpty (AltConfig G Ω α β))
    (hP46 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥)
    (h94 : P49Step94 G Ω) (h95 : P49Step95 G Ω) (h97b : P49Step97b G Ω) :
    ∃ (α β : Ω) (v : G), Nonempty (FinConfig G Ω α β v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, v, hv⟩ := hS.toSec4Hyp.exists_isTypeL
  obtain ⟨Dv⟩ := hS.holtData_typeLSection hv
  have hO := hP46 hv
  have hSE : ∀ k, IsNaturalSE (Dv.M k) := fun k =>
    hS.isNaturalSE_factor_typeLSection_of hP43 hv hO Dv k
  have hOK : jOddCore (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) = ⊥ :=
    le_bot_iff.mp (hO ▸ jOddCore_le_pPrimeCore)
  obtain ⟨i⟩ : Nonempty Dv.ι := by
    by_contra hne
    have := Dv.isEmpty_ι_iff.mp (not_nonempty_iff.mp hne)
    have : Nontrivial (fixSet Ω (Subgroup.zpowers v)) := Finite.one_lt_card_iff_nontrivial.mp
      (by have := three_le_card_fixSet_of_isTypeL hS.star hv; omega)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (fixSet Ω (Subgroup.zpowers v))
    obtain ⟨g, hg⟩ := exists_smul_eq
      (jOddCore (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) a b
    have hg1 : (g : typeLSection G Ω v) = 1 := Subgroup.mem_bot.mp (le_bot_iff.mpr hOK g.2)
    rw [Subgroup.smul_def, hg1, one_smul] at hg
    exact hab hg
  let a : fixSet Ω (Subgroup.zpowers v) := ⟨α, hv.mem_fixSet⟩
  have : Nontrivial (Dv.Ψc i) := Fintype.one_lt_card_iff_nontrivial.mp
    (by have := Dv.five_le_card i; omega)
  obtain ⟨x, hx⟩ := exists_ne (Dv.coord a i)
  obtain ⟨b, hb⟩ := Dv.exists_coord_eq_update a i x
  have hab : Dv.coord a i ≠ Dv.coord b i := by
    rw [hb, Function.update_self]
    exact hx.symm
  have hab' : ∀ j ≠ i, Dv.coord a j = Dv.coord b j := fun j hj => by
    rw [hb, Function.update_of_ne hj]
  have hαb : α ≠ (b : Ω) := fun h => hab (by rw [show a = b from Subtype.ext h])
  obtain ⟨hT, D, hD1, hDSE, hB⟩ := hS.prop_4_9_of h94 h95 (hS.p49Step96_of hP43 hP46) h97b
    hv hO Dv hSE i (a := a) rfl hab hab'
  have hV := isPGroup_zpowers_of_orderOf_eq_two hv.orderOf_eq_two
  have hVαβ : Subgroup.zpowers v ≤ stabilizer G α ⊓ stabilizer G (b : Ω) :=
    le_inf (mem_fixSet_iff_le_stabilizer.mp hv.mem_fixSet) (mem_fixSet_iff_le_stabilizer.mp b.2)
  obtain ⟨γ, hγΔ, hγv⟩ := hS.exists_mem_holtDelta_mem_fixSet hV hVαβ
  obtain ⟨S, hVS, hSyl⟩ :=
    exists_fusionIsSylowIn_ge hV (le_inf hVαβ (mem_fixSet_iff_le_stabilizer.mp hγv))
  obtain ⟨-, w, hw, hwγ, hwS⟩ := hS.sylow_twoPoint hαb hγΔ hSyl
  exact ⟨α, b, v, ⟨{
    isTypeL := hv, Dv := Dv, pPrimeCore_eq_bot := hO, isNaturalSE_Dv := hSE, i := i
    mem_fixSet := b.2, coord_ne := hab, coord_eq := hab', odd_twoPointKernel := hT, D := D
    card_ι := hD1, isNaturalSE_D := hDSE, orbit_iff := hB, γ := ⟨γ, hγΔ⟩, γ_mem := hγv
    S := S, sylow := hSyl, v_mem := hVS (Subgroup.mem_zpowers v), w := w, w_mem := hw
    w_fix := hwγ, w_comm := hwS }⟩⟩

theorem Sec4Setting.false_of (hS : Sec4Setting G Ω)
    (hP43 : ∀ {α β : Ω}, α ≠ β → IsEmpty (AltConfig G Ω α β))
    (hP46 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥)
    (h94 : P49Step94 G Ω) (h95 : P49Step95 G Ω) (h97b : P49Step97b G Ω) : False := by
  obtain ⟨α, β, v, ⟨C⟩⟩ := hS.nonempty_finConfig_of hP43 hP46 h94 h95 h97b
  exact C.false hS

end Final

theorem holtSection4Statement_of_section4Hyps
    (hP43 : ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω]
      [MulAction G Ω] [FaithfulSMul G Ω], Sec4Setting G Ω →
        ∀ {α β : Ω}, α ≠ β → IsEmpty (AltConfig G Ω α β))
    (hP46 : ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω]
      [MulAction G Ω] [FaithfulSMul G Ω], Sec4Setting G Ω →
        ∀ {α : Ω} {v : G}, IsTypeL G Ω α v → CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥)
    (h94 : ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω]
      [MulAction G Ω] [FaithfulSMul G Ω], Sec4Setting G Ω → P49Step94 G Ω)
    (h95 : ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω]
      [MulAction G Ω] [FaithfulSMul G Ω], Sec4Setting G Ω → P49Step95 G Ω)
    (h97b : ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω]
      [MulAction G Ω] [FaithfulSMul G Ω], Sec4Setting G Ω → P49Step97b G Ω) :
    HoltSection4Statement :=
  holtSection4Statement_of_false fun G _ _ Ω _ _ _ _ hS =>
    hS.toSetting.false_of (hP43 G Ω hS.toSetting) (hP46 G Ω hS.toSetting)
      (h94 G Ω hS.toSetting) (h95 G Ω hS.toSetting) (h97b G Ω hS.toSetting)

end CFSG.Holt.H78
