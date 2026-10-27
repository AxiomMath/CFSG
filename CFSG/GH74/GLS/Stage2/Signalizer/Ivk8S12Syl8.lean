module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgThm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem AFrame.sylCfg_syl8 (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hnc : ¬ Vb ≤ centralizer (J : Set A))
    (hY : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J)) :
    ∃ T W : Subgroup (MulAut (↥J ⧸ center ↥J)),
      SylCfg (↥J ⧸ center ↥J) T W ∧ Nat.card ↥T = 2 ^ 8 := by
  obtain ⟨hZ, hu, -⟩ := hfr.reduce hJ hY
  have hcomps : ∀ K₁ K₂ K₃ : Subgroup A, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := fun _ _ _ h₁ h₂ h₃ => hfr.comps_le_two h₁ h₂ h₃
  have : Group.IsPerfect ↥J := hJ.1.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowOf 2 (Sb ⊓ J) J := YCfg.isSylowOf_inf_isSubnormal_top hfr.sylow hJ.2
  have hcfg := YCfg.sylCfg_yAct hfr.sylow.isPGroup hfr.v3 hfr.v_norm
    (hfr.v_normalizes_component hcomps hJ) hnc hsyl
  refine ⟨_, _, hcfg, ?_⟩
  obtain ⟨φ, hφinj, hφ⟩ := hfr.embed_aut hJ hZ hu
  have hJn : J.Normal := Gen.normal_of_unique_comp hJ hu
  have hnorm : Sb ≤ normalizer (J : Set A) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  set g : ↥(Sb.subgroupOf (normalizer (J : Set A))) →* MulAut (↥J ⧸ center ↥J) :=
    (yAct J).comp (Sb.subgroupOf (normalizer (J : Set A))).subtype with hg
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hs1 : yAct J (s : ↥(normalizer (J : Set A))) = 1 := hs
    have hcent : ((s : ↥(normalizer (J : Set A))) : A) ∈ centralizer (J : Set A) :=
      (yAct_eq_one_iff J _).1 hs1
    have hsSb : ((s : ↥(normalizer (J : Set A))) : A) ∈ Sb := s.2
    have hφ1 : φ ⟨(s : A), hsSb⟩ = 1 := by
      ext x
      rw [hφ]
      have := Subgroup.mem_centralizer_iff.1 hcent (x : A) x.2
      show (s : A) * (x : A) * (s : A)⁻¹ = (x : A)
      rw [← this]
      group
    have := hφinj (hφ1.trans (map_one φ).symm)
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val this
  have hrange : g.range = (Sb.subgroupOf (normalizer (J : Set A))).map (yAct J) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hnorm).toEquiv, hfr.card]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
