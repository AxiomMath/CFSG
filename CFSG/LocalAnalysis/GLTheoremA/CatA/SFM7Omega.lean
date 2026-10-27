module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM7OmegaModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM7OmegaRad
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM7OmegaSeven
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM7Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 SFM7Omega Module

theorem I2017LieNoA7Omega_holds : I2017LieNoA7Omega := by
  intro S _ _ hcat T hT hT1 H hH ⟨eH⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_elementaryGroup_of_catalog hcat
  have hQ : (QuadraticMap.polarBilin Q8).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 4 (ZMod 2)
      (by decide)
  let ι : S →* (V8 ≃ₗ[ZMod 2] V8) :=
    (CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q8).subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιO : ∀ s, ι s ∈ TauCeti.QuadraticMap.orthogonalGroup Q8 := fun s =>
    CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_orthogonalGroup Q8 (e s).2
  have hTΩ : T.map ι ≤ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q8 hQ := by
    rintro _ ⟨t, -, rfl⟩
    exact CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup hQ (e t).2
  have hU0 := radSing_ne_bot Q8 hQ hTΩ (hT.map ι)
    (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective T hι])
  have h8 : finrank (ZMod 2) V8 = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    rfl
  have h4 := two_mul_finrank_radSing_le Q8 hQ (T.map ι)
  let ρ : alternatingGroup (Fin 7) →* (V8 ≃ₗ[ZMod 2] V8) :=
    ι.comp (H.subtype.comp eH.symm.toMonoidHom)
  have hρ : Function.Injective ρ := hι.comp (Subtype.val_injective.comp eH.symm.injective)
  have hρU : ∀ a, ∀ x ∈ radSing Q8 (T.map ι), ρ a x ∈ radSing Q8 (T.map ι) := fun a x hx =>
    apply_mem_radSing (hιO _) (Subgroup.le_normalizer_map ι ⟨_, hH (eH.symm a).2, rfl⟩) hx
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 7)) 7 (by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide)
  obtain ⟨u, hu, hu0, hσu⟩ := exists_ne_zero_fixed_of_alternatingGroup ρ _ hρU
    (Submodule.one_le_finrank_iff.mpr hU0) (by omega) hσ
  have hσ7 : σ ^ 7 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ] at this
  have hρ7 : ρ σ ^ 7 = 1 := by rw [← map_pow ρ, hσ7, map_one]
  have h1 := eq_one_of_pow_seven_eq_one_of_fixed_singular Q8 hQ card_V8 card_zeros_Q8
    (hιO _ : ρ σ ∈ _) hρ7 hu0 (mem_radSing.mp hu).2.2 hσu
  have hσ1 : σ = 1 := hρ (h1.trans (map_one ρ).symm)
  rw [hσ1, orderOf_one] at hσ
  exact absurd hσ (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA
