module

public import CFSG.GF2Type.Smith1979.GammaU.ThetaConfig
public import CFSG.GF2Type.Smith1979.GammaU.Dict3
public import CFSG.GF2Type.Smith1979.GammaU.ThetaCanon

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.GammaU.Dict

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S10
  CFSG.GF2Type.Smith1980Orth

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem two_of_dec108 (I : TimInputs) (hw : S.width = 6) (hP : NoPGL25 S g) {t : S.O}
    {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb) {θ : S.O}
    (hθ : θ ∈ ⁅Yb, Yb⁆) (hθ1 : θ ≠ 1) :
    ∃ s₁ ∈ S.Lbar g, ∃ s₂ ∈ S.Lbar g, s₁ ≠ s₂ ∧ s₁ ≠ 1 ∧ s₂ ≠ 1 ∧ s₁ * θ = θ * s₁ ∧
      s₂ * θ = θ * s₂ ∧ 4 ≤ finrank (ZMod 2) (Vt S g s₁) ∧
        4 ≤ finrank (ZMod 2) (Vt S g s₂) := by
  obtain ⟨k₀, hk₀L, hk₀ne⟩ := timmesfeld_10_4_six I.hCE X D hw
  obtain ⟨k, hkN, hkeq⟩ := exists_normalizer_conj X hk₀L
  have htθ : t * θ = θ * t :=
    D.dec.comm t (D.t_mem_Ebar I.hCE).2 θ ((D.dec.mem_commutator_iff).1 hθ).1
  have hfix := (S.timmesfeld_12_4_1 X.H.conj_mem X.H.conj_ne (by omega) k).1 hkN
  have hcan := canon_of_dec108 I hw hP D hθ hθ1 (S.ρ k) ⟨k, rfl⟩ hfix
  set x := S.ρ k
  have hθ' : t * (x⁻¹ * θ * x) = (x⁻¹ * θ * x) * t := by
    rcases hcan with h | h
    · have hc : θ * x = x * θ := by
        calc θ * x = (x * θ * x⁻¹) * x := by rw [h]
          _ = x * θ := by group
      rw [show x⁻¹ * θ * x = θ by
        calc x⁻¹ * θ * x = x⁻¹ * (θ * x) := by group
          _ = x⁻¹ * (x * θ) := by rw [hc]
          _ = θ := by group]
      exact htθ
    · have h' : x * θ⁻¹ * x⁻¹ = θ := by
        rw [show x * θ⁻¹ * x⁻¹ = (x * θ * x⁻¹)⁻¹ by group, h, inv_inv]
      have hc : θ * x = x * θ⁻¹ := by
        calc θ * x = (x * θ⁻¹ * x⁻¹) * x := by rw [h']
          _ = x * θ⁻¹ := by group
      rw [show x⁻¹ * θ * x = θ⁻¹ by
        calc x⁻¹ * θ * x = x⁻¹ * (θ * x) := by group
          _ = x⁻¹ * (x * θ⁻¹) := by rw [hc]
          _ = θ⁻¹ := by group]
      calc t * θ⁻¹ = θ⁻¹ * (θ * t) * θ⁻¹ := by group
        _ = θ⁻¹ * (t * θ) * θ⁻¹ := by rw [htθ]
        _ = θ⁻¹ * t := by group
  refine ⟨t, X.ht, x * t * x⁻¹, hkeq ▸ hk₀L, fun h => hk₀ne (hkeq ▸ h.symm), X.ht1,
    fun h => X.ht1 (by
      calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group), htθ, ?_, ?_, ?_⟩
  · calc x * t * x⁻¹ * θ = x * (t * (x⁻¹ * θ * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * θ * x) * t) * x⁻¹ := by rw [hθ']
      _ = θ * (x * t * x⁻¹) := by group
  · rw [X.h4]
  · rw [Vt_conj X.H.conj_mem k t, LinearEquiv.finrank_map_eq, X.h4]

theorem thetaInputs_of_dec108 (I : TimInputs) (hw : S.width = 6) (hP : NoPGL25 S g) {t : S.O}
    {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb) {θ : S.O}
    (hθ : θ ∈ ⁅Yb, Yb⁆) (hθ1 : θ ≠ 1)
    (hanti : ∀ s ∈ S.Lbar g, s * θ = θ⁻¹ * s → finrank (ZMod 2) (Vt S g s) ≤ 2) :
    ThetaInputs S g θ where
  mem := Rbar_le_Mbar (D.dec.le_Rbar_right ((D.dec.mem_commutator_iff).1 hθ).1)
  pow_three := ((D.dec.mem_commutator_iff).1 hθ).2
  fix := fun v hv => timmesfeld_10_3_alpha I.hCE X D.dec fun y hy => by
    by_cases hy1 : y = 1
    · rw [hy1]
      rfl
    rcases D.dec.eq_or_eq_inv_of_mem_commutator hθ hθ1 hy hy1 with rfl | rfl
    · exact hv
    · conv_lhs => rw [← hv]
      exact inv_apply_apply_O θ v
  canon := canon_of_dec108 I hw hP D hθ hθ1
  anti := hanti
  config := config_of_dec108 I hw hP D hθ hθ1
  two := two_of_dec108 I hw hP D hθ hθ1

end CFSG.GF2Type.Smith1979.GammaU.Dict
