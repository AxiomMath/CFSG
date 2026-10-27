module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCentPGL
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisBase
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSubfield

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup

theorem congr_self_eq {F : Type} [Field F] (γ c : MulAut (PSL2 F)) :
    MulAut.congr γ c = γ * c * γ⁻¹ := by
  ext z
  simp [MulAut.congr_apply, MulAut.mul_apply]

theorem autPSL2FieldCentralizer :
    ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 →
      Blueprint.LieModel Y .PSL 2 p f → ∀ k : MulAut Y, HarrisLit.IsFieldAutPSL2 k →
        Blueprint.LieModel
            ↥(perfectResidual ↥(MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y)))
            .PSL 2 p (f / 2) ∧
          2 * Nat.card (perfectResidual ↥(MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y))) =
            Nat.card (MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y)) ∧
          (Nat.card (MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y))).factorization 2 =
            (Nat.card Y).factorization 2 ∧
          ∀ φ : MulAut Y,
            (∀ y ∈ (perfectResidual ↥(MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y))).map
                (MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y)).subtype, φ y = y) →
              φ = 1 ∨ φ = k := by
  intro Y _ _ p f hp hp2 hfe h16 hY k hk
  obtain ⟨-, hf1, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hH : HarrisHyp F := harrisHyp_of hp hp2 hF hfe h16
  have hodd := hH.odd
  have hY4 : ∃ y : Y, y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
    obtain ⟨y, hy4, hy2⟩ := exists_psl2_pow_four (F := F) (by have := hH.four_le; omega)
    refine ⟨e.symm y, by rw [← map_pow, hy4, map_one], fun h => hy2 ?_⟩
    rw [← map_pow] at h
    exact e.symm.injective (h.trans (map_one _).symm)
  obtain ⟨b, σ, hσ, hkb⟩ := (isFieldAutPSL2_iff hodd e hY4 k).mp hk
  set E : Y ≃* PSL2 F := e.trans (semilinearAction F b⁻¹) with hEdef
  have hE : autEquiv E k = SemidirectProduct.inr σ := by
    rw [autEquiv_eq_iff, congr_trans_apply, ← semilinearAction_autEquiv e k, hkb, congr_self_eq,
      ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
    have := congrArg (fun τ : F ≃+* F => τ z) h1
    simpa using this
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    norm_num at hσ
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield σ hσ
  obtain ⟨g, hg⟩ := hfe
  have hK₀card : Nat.card K₀ = p ^ (f / 2) := by
    rw [show f / 2 = g by omega]
    apply Nat.pow_left_injective two_ne_zero
    show Nat.card K₀ ^ 2 = (p ^ g) ^ 2
    rw [← hcard, hF, hg, ← pow_mul, mul_two]
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨p', n, -, hpodd, -, hc⟩ := hodd
    rw [hc]
    exact hpodd.pow
  have hK₀odd' : Odd (Nat.card K₀) := by
    rw [hcard] at hFodd
    exact Nat.Odd.of_mul_left (by rwa [← pow_two])
  have hK₀odd : IsOddPrimePower (Nat.card K₀) := isOddPrimePower_of_odd_card _ hK₀odd'
  have hr3 : Nat.card K₀ ≠ 3 := by
    intro h3
    have h9 : p ^ f = 9 := by rw [← hF, hcard, h3]; norm_num
    rw [h9] at h16
    norm_num at h16
  have hr5 : 5 ≤ Nat.card K₀ := by
    obtain ⟨j, hj⟩ := hK₀odd'
    have h1 : 1 < Nat.card K₀ := Finite.one_lt_card
    omega
  have : Group.IsPerfect (PSL2 K₀) := psl2_isPerfect_of_card_gt_three K₀ (by omega)
  set C := MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y) with hCdef
  have hmemC : ∀ y : Y, y ∈ C ↔ E y ∈ fieldCent σ := by
    intro y
    change k y = y ↔ psl2FieldAut F σ (E y) = E y
    rw [← semilinearAction_inr, ← hE, semilinearAction_autEquiv_apply, E.injective.eq_iff]
  have hmap : C.map E.toMonoidHom = fieldCent σ := by
    ext z
    rw [Subgroup.mem_map_equiv, hmemC, MulEquiv.apply_symm_apply]
  have hCcard : Nat.card C = Nat.card (PGL2 K₀) := by
    rw [← card_fieldCent_eq hK₀ h90 hσσ hcard hodd, ← hmap,
      Subgroup.card_map_of_injective E.injective]
  let ψ : PSL2 K₀ →* C := (E.symm.toMonoidHom.comp (psl2Sub K₀)).codRestrict C fun g =>
    (hmemC _).mpr (by
      show E (E.symm (psl2Sub K₀ g)) ∈ fieldCent σ
      rw [MulEquiv.apply_symm_apply]
      exact psl2Sub_mem_fieldCent hK₀ g)
  have hψ : Function.Injective ψ := fun a b h =>
    psl2Sub_injective K₀ (E.symm.injective (congrArg Subtype.val h))
  have hPR : perfectResidual C = ψ.range := by
    refine perfectResidual_eq_of_two_mul (Group.IsPerfect.range ψ) ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hCcard, pgl2_card_eq_two_mul hK₀odd]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hPR]
    refine Or.inl ⟨by simp [Blueprint.classicalTags], ⟨hp, by omega, le_rfl, ?_, ?_⟩, K₀,
      inferInstance, inferInstance, hK₀card,
      ⟨(MonoidHom.ofInjective hψ).symm.trans
        (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K₀)⟩⟩
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      rw [← hK₀card] at h
      omega
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      rw [← hK₀card] at h
      omega
  ·
    rw [hPR, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hCcard,
      pgl2_card_eq_two_mul hK₀odd]
  ·
    rw [hCcard, pgl2_card_formula, Nat.card_congr e.toEquiv, psl2_card_formula F hodd, hcard]
    obtain ⟨j, hj⟩ := hK₀odd'
    rw [hj]
    exact factorization_two_pgl_psl (by omega)
  ·
    intro φ hφ
    have hfix : ∀ g : PSL2 K₀,
        semilinearAction F (autEquiv E φ) (psl2Sub K₀ g) = psl2Sub K₀ g := by
      intro g
      have hmem : E.symm (psl2Sub K₀ g) ∈ (perfectResidual C).map C.subtype := by
        rw [hPR]
        exact ⟨ψ g, ⟨g, rfl⟩, rfl⟩
      have h := hφ _ hmem
      rw [← E.apply_symm_apply (psl2Sub K₀ g), semilinearAction_autEquiv_apply, h]
    rcases eq_of_fixes_psl2Sub hσ1 hK₀ hcard _ hfix with h | h
    · left
      apply (autEquiv E).injective
      rw [h, map_one]
    · right
      apply (autEquiv E).injective
      rw [h, hE]

end CFSG.ComponentClassification.AutL2Facts
