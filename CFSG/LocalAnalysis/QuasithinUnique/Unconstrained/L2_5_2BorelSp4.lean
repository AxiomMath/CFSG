module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.QuasithinUnique.Borel252

open CFSG.QuasithinUnique.Fin257 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X7b CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

namespace Sp4

theorem overgroupData_Sp (K : Type) [Field K] [Finite K] [CharP K 2] :
    OvergroupData (StatedProj (StatedSp 2 K)) (projUnipotent 2 K) (projBorel 2 K)
      ((Q2 K 0).map (proj 2 K)) ((Q2 K 1).map (proj 2 K)) :=
  OvergroupData.of_cover (proj_surjective (r := 2) (K := K)) (V := unipotent 2 K)
    (B := borelSubgroup 2 K) (Q := Q2 K)
    (by
      rw [ker_proj, borelSubgroup_eq_flagStabilizer]
      exact spScalars_le_flagStabilizer _)
    covBy_Q2 (fun A hVA hAt => contained_in_Q2 hVA hAt)
    (normalizer_projUnipotent (K := K) 2 (r := 2) (by norm_num)).ge

theorem statedModel_Sp {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) : StatedClassicalModel (antiSp K) .PSp 2 2 n := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨antiProjEquiv K⟩⟩
  intro h
  have := (Prod.mk.inj h).2
  omega

theorem borelData_Sp {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    BorelData (antiSp K) (antiUnipotent K) (radA1 K) (radA2 K) := by
  have hd := Fin257.Sp4.modelData_Sp hn hK
  obtain ⟨K', hF', hFin', hCh', φ, -, hφ, -⟩ :=
    even_rank_two_residual_symplectic (statedModel_Sp hn hK) hd.sylow
  have hU' : (projUnipotent 2 K').map φ.symm.toMonoidHom = antiUnipotent K := by
    rw [← hφ, Subgroup.map_map]
    ext x
    simp
  have hov := (overgroupData_Sp K').map φ.symm
  rw [hU'] at hov
  exact
    { center_trivial := hd.center_trivial
      sylow := hd.sylow
      le₁ := hd.le₁
      le₂ := hd.le₂
      sup := hd.sup
      cent₁ := hd.cent₁
      cent₂ := hd.cent₂
      lt₁ := hd.lt₁
      lt₂ := hd.lt₂
      lt_top₁ := hd.lt_top₁
      lt_top₂ := hd.lt_top₂
      core₁ := hd.core₁
      core₂ := hd.core₂
      only := fun _ h1 h2 =>
        only_of_overgroupData hov hd.lt₁ hd.lt_top₁ hd.lt₂ hd.lt_top₂
          (ne_normalizer_of_sup hd.sup hd.lt₁) h1 h2 }

end Sp4

end CFSG.QuasithinUnique.Borel252
