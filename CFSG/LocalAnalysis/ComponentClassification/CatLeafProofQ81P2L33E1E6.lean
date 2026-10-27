module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1E6Graph
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1Field
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1Inner

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_isPGroup_twistedFixedGroup_E6
    {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) (σ : K ≃+* K) :
    ¬ IsPGroup 2 (↥(twistedFixedGroup TwistTag.E6 K σ.toRingHom) ⧸
      pPrimeCore 2 ↥(twistedFixedGroup TwistTag.E6 K σ.toRingHom)) := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set a := TwistTag.E6.orbitIndex (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank)
  have ha : (TwistTag.E6.orbit a).card = 1 := by decide
  exact not_isPGroup_of_sl2 (ExcSelector.ringChar_subfield_ne_two hK _)
    (orbitRankOneHom TwistTag.E6 K σ.toRingHom a)
    (ExcSelector.orbitRankOneHom_E6_singleton_injective' hK σ.toRingHom a ha)
    ((range_orbitRankOneHom_le a).trans (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom))

theorem not_isPGroup_E6
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    (α : MulAut (adjointGroup Tag.E6 K)) (hα : α ^ 2 = 1) :
    ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α)) := by
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  have h1 : ∀ x : ModGL Tag.E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ0 : exactQ Tag.E6 K 0 = 1 := pow_zero _
  have hQ1 : exactQ Tag.E6 K 1 = diagramMap TwistTag.E6 K := pow_one _
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨Θ, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF α
  have hσ2 := hsq α g a σ ε hgaσ hα
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h2 : (ε : ℕ) < 2 := ε.isLt
    omega
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases hε with hε | hε
    ·
      refine not_isPGroup_inner_diagonal (τ := Tag.E6) (Or.inr (Or.inr (Or.inl rfl))) hK
        (g := g) (a := a) (fun h => ?_) hα
      rw [hgaσ h, hε, hQ0, h1, mul_one, inv_one, mul_one]
    ·
      refine not_isPGroup_E6_pure_graph hK (g := g) (a := a) (fun h => ?_) hα
      exact (hgaσ h).trans (by rw [hε, hQ1, h1]; rfl)
  ·
    obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hcard σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hcard]
    rcases hε with hε | hε
    ·
      refine not_isPGroup_quadratic_field hK2 hp he hKe σ hσc (g := g) (a := a)
        (fun h => ?_) hα
      rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]
    ·
      obtain ⟨-, β, hβ, hβα⟩ :=
        exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe σ.toRingHom hσc
      obtain ⟨-, hconj⟩ := hβα g a
      obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α (fun h => (hgaσ h).trans (by rw [hε, hQ1]; rfl))
        ((sq α).symm.trans hα)
      have hβfix : (fixedSubgroup β).map (adjointGroup TwistTag.E6.tag K).subtype =
          twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
        ext y
        simp only [Subgroup.mem_map, twistedFixedGroup, Subgroup.mem_inf]
        constructor
        · rintro ⟨u, hu, rfl⟩
          refine ⟨u.2, ?_⟩
          change twistHom TwistTag.E6 K σ.toRingHom (u : ModGL TwistTag.E6.tag K) = u
          rw [twistHom_apply, ← hβ u]
          exact congrArg Subtype.val hu
        · rintro ⟨hyG, hyσ⟩
          refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
          change (β ⟨y, hyG⟩ : ModGL TwistTag.E6.tag K) = y
          rw [hβ]
          change twistHom TwistTag.E6 K σ.toRingHom y = y at hyσ
          rw [twistHom_apply] at hyσ
          exact hyσ
      let e₂ : ↥(fixedSubgroup β) ≃* ↥(twistedFixedGroup TwistTag.E6 K σ.toRingHom) :=
        (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
          (MulEquiv.subgroupCongr hβfix)
      have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
      exact not_isPGroup_of_mulEquiv (e₁.trans e₂) (not_isPGroup_twistedFixedGroup_E6 hK2 σ)

end CFSG.ComponentClassification.HarrisLit.L33.E1
