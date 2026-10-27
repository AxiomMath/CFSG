module

public import CFSG.LieType.AlgebraicGroups.OddG2F4E8AllInvolutionComponents
public import CFSG.LieType.AlgebraicGroups.E6RationalGraphCosetPure

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.AlgebraicGroups

theorem odd_E6_all_involution_fixed_p_components
    (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (α : MulAut (adjointGroup Tag.E6 K)) (hα : α ^ 2 = 1) (r : ℕ)
    (hr : r.Prime) (L : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup Tag.E6 K))))
    (hL : CFSG.IsPComponent r L) : CFSG.IsQuasisimple L := by
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
      refine exceptional_inner_diagonal_involution_fixed_p_components (τ := Tag.E6)
        (Or.inr (Or.inr (Or.inl rfl))) hK (g := g) (a := a) (fun h => ?_) hα r hr L hL
      rw [hgaσ h, hε, hQ0, h1, mul_one, inv_one, mul_one]
    ·
      refine odd_E6_pure_graph_coset_fixed_p_components K hK g a α (fun h => ?_) hα r hr L hL
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
      refine exceptional_quadratic_field_involution_fixed_p_components hK2 hp he hKe σ hσc
        (g := g) (a := a) (fun h => ?_) hα r hr L hL
      rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]
    ·
      obtain ⟨-, β, hβ, hβα⟩ :=
        exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe σ.toRingHom hσc
      obtain ⟨-, hconj⟩ := hβα g a
      obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α (fun h => (hgaσ h).trans (by rw [hε, hQ1]; rfl))
        ((sq α).symm.trans hα)
      have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag K))).map
          (adjointGroup TwistTag.E6.tag K).subtype =
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
      let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag K))) ≃*
          ↥(twistedFixedGroup TwistTag.E6 K σ.toRingHom) :=
        (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
          (MulEquiv.subgroupCongr hβfix)
      exact OddToralFixed.pComponent_quasisimple_of_mulEquiv (e₁.trans e₂)
        (fun J hJ => ((odd_diagram_field_fixed_p_components TwistTag.E6 K hK2 σ).2.2 r hr J
          hJ).1) L hL

end CFSG.LieType.Chevalley
