module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Cons
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011S4a
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Type

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Local.P34
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_S1_iff)

section YStep

variable {G : Type} [Group G] [Finite G]

theorem yStep20_of (hCF : CFTypeAut) (h20b : Coprime20b) (hcore : CentCoreProp) : YStep20 := by
  intro G _ _ z k S hC g hg hJ hSJ
  obtain ⟨q, L₁, L₂, K₁, K₂, hP, -, hK⟩ := exists_data2011 hC
  have hconcl := typeData20 hCF h20b hcore hC hg hJ hP hK
  have hctx : Stage2Ctx G z k S := hC.1.ctx.ctx17.ctx
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  obtain ⟨ε, hε, hmod, hLn⟩ := hconcl.typ
  obtain ⟨T, hT, hzT, hzc⟩ := exists_sylow_bar hctx hJ.z_mem hSJ
  have hzbar2 : orderOf (mkH (J0 z g) ⟨z, hJ.z_mem⟩) = 2 := hJ.central.1
  obtain ⟨y₀, hy₀T, hy₀2, hy₀z, hy₀c, hy₀N₁, hy₀N₂⟩ := l2011S4a (HBar (J0 z g)) ε q hε hP.odd hP.gt3
    hmod hLn T (mkH (J0 z g) ⟨z, hJ.z_mem⟩) hzT hzbar2 hzc (barIn (J0 z g) K₁) (barIn (J0 z g) K₂)
    hconcl.sup hconcl.comm hconcl.inf hconcl.sl₁ hconcl.sl₂
  have hy₀S : y₀ ∈ barIn (J0 z g) S := by rw [← hT]; exact hy₀T
  obtain ⟨s', hs', hsy⟩ := Subgroup.mem_map.1 hy₀S
  have hyS : (s' : G) ∈ S := Subgroup.mem_subgroupOf.1 hs'
  have hyC : (s' : G) ∈ Cen z := hctx.S_le_Cen hyS
  have hy₀sq : y₀ * y₀ = 1 := by
    have h := pow_orderOf_eq_one y₀
    rwa [hy₀2, pow_two] at h
  have hysq : (s' : G) * (s' : G) = 1 :=
    lift_sq_eq_one hctx.sylow.isPGroup hyS (by rw [hsy]; exact hy₀sq)
  have hy1 : (s' : G) ≠ 1 := by
    intro h
    have : s' = 1 := Subtype.ext h
    rw [this, map_one] at hsy
    rw [← hsy, orderOf_one] at hy₀2
    omega
  have hy2 : orderOf (s' : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hysq) hy1
  have hyz : (s' : G) ≠ z := by
    intro h
    apply hy₀z
    rw [← hsy]
    congr 1
    exact Subtype.ext h
  have hPS := PairShape.of_stage1Pair hP
  have hnoswap : ¬ cj (toBar z ⟨(s' : G), hyC⟩) L₁ = L₂ := by
    intro hswap
    obtain ⟨hs₁, -⟩ := hK.swap (s' : G) hyC hswap
    have hle : barIn (J0 z g) K₁ ≤ barIn (J0 z g) K₂ := by
      intro x hx
      have hx' : y₀⁻¹ * x * y₀ ∈ barIn (J0 z g) K₁ := by
        have h1 := (Subgroup.mem_normalizer_iff.1 hy₀N₁ (y₀⁻¹ * x * y₀)).2
        have e : y₀ * (y₀⁻¹ * x * y₀) * y₀⁻¹ = x := by group
        rw [e] at h1
        exact h1 hx
      obtain ⟨a', ha', hae⟩ := Subgroup.mem_map.1 hx'
      refine Subgroup.mem_map.2 ⟨s' * a' * s'⁻¹, Subgroup.mem_subgroupOf.2 (hs₁ _ (Subgroup.mem_subgroupOf.1 ha')), ?_⟩
      rw [map_mul, map_mul, map_inv, hae, hsy]
      group
    have hinf : barIn (J0 z g) K₁ ⊓ barIn (J0 z g) K₂ = barIn (J0 z g) K₁ := inf_eq_left.2 hle
    have hcard : Nat.card ↥(barIn (J0 z g) K₁) = 2 := by
      have h1 : Nat.card ↥(barIn (J0 z g) K₁) = Nat.card ↥(zpowers (mkH (J0 z g) ⟨z, hJ.z_mem⟩)) := by
        rw [← hconcl.inf, hinf]
      rw [h1, Nat.card_zpowers, hzbar2]
    have := two_lt_card_of_sl2 hconcl.sl₁ hP.gt3
    omega
  have hfix₁ : cj (toBar z ⟨(s' : G), hyC⟩) L₁ = L₁ := (hPS.cj_cases _).resolve_right hnoswap
  have hfix₂ : cj (toBar z ⟨(s' : G), hyC⟩) L₂ = L₂ := hPS.cj_fix hfix₁
  have hyS1 : (s' : G) ∈ S1 S z := by
    rw [bar_mem_S1_iff]
    refine ⟨hyS, hyC, fun K hK' _ => ?_⟩
    have hmem : K ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
      rw [← hP.comps]; exact hK'
    rcases hmem with rfl | hmem
    · exact cj_eq_iff.1 hfix₁
    · rw [Set.mem_singleton_iff] at hmem
      subst hmem
      exact cj_eq_iff.1 hfix₂
  obtain ⟨c, hc⟩ := isConj_iff.1 hy₀c
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(J0 z g)) c
  refine ⟨(s' : G), hyS, hy2, hyz, hyS1, ((j⁻¹ : ↥(J0 z g)) : G), (j⁻¹).2, ?_⟩
  have hjmk : mkH (J0 z g) (s' * (j * ⟨z, hJ.z_mem⟩ * j⁻¹)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hsy]
    change y₀ * (mkH (J0 z g) j * mkH (J0 z g) ⟨z, hJ.z_mem⟩ * (mkH (J0 z g) j)⁻¹)⁻¹ = 1
    rw [← hc]
    simp
  have hcore' := (mkH_eq_one_iff (J0 z g)).1 hjmk
  refine ⟨_, hcore', ?_⟩
  simp only [Subgroup.coe_inv, inv_inv]
  rfl

end YStep

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
