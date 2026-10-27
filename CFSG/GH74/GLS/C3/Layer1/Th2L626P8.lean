module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.St1P41L42
public import CFSG.GH74.GLS.C3.Layer1.Th2V2Core

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools

structure Cfg626 {G : Type} [Group G] [Finite G] (t u : G) (J B T : Subgroup G) : Prop where
  hmax : IsEStarUnbalMax t u J
  hB : IsE 4 ⊤ B
  htB : t ∈ B
  huB : u ∈ B
  hT : IsSylowOf 2 T (centralizer ({t} : Set G))
  hBT : B ≤ T
  hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (J : Set G)

section Cfg

variable {G : Type} [Group G] [Finite G] {t u : G} {J B T : Subgroup G}

theorem Cfg626.exists_of_max (hmax : IsEStarUnbalMax t u J)
    (hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (J : Set G)) :
    ∃ B T : Subgroup G, Cfg626 t u J B T := by
  obtain ⟨-, B, hB, htB, huB⟩ := hmax.1
  obtain ⟨hab, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB.2.1
  have hBC : B ≤ centralizer ({t} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr (hab b hb t htB)
  have hB2 : IsPGroup 2 ↥B := by
    have := hB.2.1
    exact CFSG.IsElementaryAbelian.isPGroup 2 ↥B
  obtain ⟨T, hT, hBT⟩ := C3.Layer1.Iv251.exists_isSylowOf_ge hBC hB2
  exact ⟨B, T, hmax, hB, htB, huB, hT, hBT, hN⟩

theorem Cfg626.sylow_Q (cfg : Cfg626 t u J B T) : IsSylowOf 2 (T ⊓ CxK t J) (CxK t J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine cfg.hT.inf_of_le_normalizer inf_le_left fun c hc => ?_
  exact C3.Layer1.PumpL42.mem_normalizer_CxK ⟨hc, cfg.hN c hc⟩

theorem Cfg626.T_le_normalizer_Q (cfg : Cfg626 t u J B T) :
    T ≤ normalizer ((T ⊓ CxK t J : Subgroup G) : Set G) := fun c hc =>
  TwoThin.mem_normalizer_inf (Subgroup.le_normalizer hc)
    (C3.Layer1.PumpL42.mem_normalizer_CxK ⟨cfg.hT.le hc, cfg.hN c (cfg.hT.le hc)⟩)

theorem Cfg626.t_mem_Q (cfg : Cfg626 t u J B T) : t ∈ T ⊓ CxK t J :=
  ⟨cfg.hBT cfg.htB, C3.Layer1.Iv251.self_mem_CxK cfg.hmax.1.1.1.2.1⟩

theorem Cfg626.B_comm (cfg : Cfg626 t u J B T) : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a :=
  (C3.Layer1.Back.forall_of_isElementaryAbelian cfg.hB.2.1).1

end Cfg

end CFSG.GH74.GLS
