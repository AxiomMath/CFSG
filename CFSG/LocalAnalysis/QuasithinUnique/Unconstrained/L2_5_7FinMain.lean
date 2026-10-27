module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3Pkg
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.QuasithinUnique.Fin257

open CFSG.Open

@[expose] noncomputable def statedSLEquiv (F : Type) [Field F] :
    StatedProj (StatedSL 3 F) ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
  (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
    (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)

theorem modelsAvailable :
    (∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
        ∃ U R₁ R₂ : Subgroup (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F),
          ModelPkg _ U R₁ R₂) ∧
    (∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
        ∃ U R₁ R₂ : Subgroup (ComponentClassification.UnbalancedCatalog.SpChain.antiSp F),
          ModelPkg _ U R₁ R₂) :=
  ⟨fun _ _ _ _ _ hn hF => ⟨_, _, _, L3.modelPkg_L3 hn hF⟩,
    fun _ _ _ _ _ hn hF => ⟨_, _, _, Sp4.modelPkg_Sp hn hF⟩⟩

theorem exists_model_pkg {G : Type} [Group G] {K : Subgroup G} {n : ℕ}
    (hM : IsRank2Model257 K n) :
    ∃ (M : Type) (_ : Group M) (_ : Finite M) (U R₁ R₂ : Subgroup M),
      ModelPkg M U R₁ R₂ ∧ Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* M) := by
  have hmod := modelsAvailable
  obtain ⟨hn2, hmodel⟩ := hM
  rcases hmodel with hL | hS
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hL.2
    have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hcard
    obtain ⟨U, R₁, R₂, hpkg⟩ := hmod.1 F n hn2 hcard
    exact ⟨_, inferInstance, inferInstance, U, R₁, R₂, hpkg, ⟨e.trans (statedSLEquiv F)⟩⟩
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hS.2
    have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hcard
    obtain ⟨U, R₁, R₂, hpkg⟩ := hmod.2 F n hn2 hcard
    exact ⟨_, inferInstance, inferInstance, U, R₁, R₂, hpkg,
      ⟨e.trans (QuasithinUnique.Setup.X7b.antiProjEquiv F).symm⟩⟩

theorem geom257_of_models : RankTwoGeom257 := by
  intro G _ _ K P K₁ K₂ V V' n hq hM _ hpair hV hV' hZ
  obtain ⟨M, _, _, U, R₁, R₂, hpkg, ⟨e⟩⟩ := exists_model_pkg hM
  obtain ⟨π, R₁', R₂', hswap, hred⟩ := reduce257 hq hpkg.data e hpair hV hV'
  have hpkg' : ModelPkg M U R₁' R₂' := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpkg
    · exact hpkg.symm
  exact geom_of_red hq hred hpkg' hZ

theorem autOdd257_of_models : AutOdd257 := by
  intro G _ _ K P K₁ K₂ V V' n hq hM _ hpair hV hV' _
  obtain ⟨M, _, _, U, R₁, R₂, hpkg, ⟨e⟩⟩ := exists_model_pkg hM
  obtain ⟨π, R₁', R₂', hswap, hred⟩ := reduce257 hq hpkg.data e hpair hV hV'
  have hdata : ModelData M U R₁' R₂' := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpkg.data
    · exact hpkg.data.symm
  exact autOdd_of_red hq hpair hred hdata

theorem torus257_of_models : RankTwoTorus257 := by
  intro G _ _ K P K₁ K₂ V V' n hq hM _ hpair hV hV' _
  obtain ⟨M, _, _, U, R₁, R₂, hpkg, ⟨e⟩⟩ := exists_model_pkg hM
  obtain ⟨π, R₁', R₂', hswap, hred⟩ := reduce257 hq hpkg.data e hpair hV hV'
  have hdata : ModelData M U R₁' R₂' := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpkg.data
    · exact hpkg.data.symm
  exact torus_of_red hred hdata

theorem geom257 : RankTwoGeom257 := geom257_of_models

theorem torus257 : RankTwoTorus257 := torus257_of_models

theorem autOdd257 : AutOdd257 := autOdd257_of_models

end CFSG.QuasithinUnique.Fin257
