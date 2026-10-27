module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4FieldInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three


private theorem ringChar_eq_of_card {F : Type} [Field F] [Finite F] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hF : Nat.card F = ℓ ^ f) : ringChar F = ℓ := by
  have := Fintype.ofFinite F
  obtain ⟨n, hr, hcard⟩ := FiniteField.card F (ringChar F)
  rw [Nat.card_eq_fintype_card, hcard] at hF
  have hdvd : ℓ ∣ ringChar F ^ (n : ℕ) := hF ▸ dvd_pow_self ℓ (by omega)
  exact ((Nat.prime_dvd_prime_iff_eq hℓ hr).mp (hℓ.dvd_of_dvd_pow hdvd)).symm

theorem perfectInLayer_omega_D4_three {G : Type} [Group G] [Finite G] {ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus 4 ℓ f) (hℓ3 : ℓ ≠ 3) (β : MulAut G)
    (hβ : β ^ 3 = 1) : PerfectInLayer β := by
  have hG' := hG
  obtain ⟨⟨hℓ, hf, -⟩, F, _, _, hF, ⟨eG⟩⟩ := hG'
  obtain ⟨eC⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  let e₂ : G ≃* ↥(adjointGroup Tag.D4 F) := eG.trans eC
  have hchar : ringChar F ≠ 3 := by rw [ringChar_eq_of_card hℓ hf hF]; exact hℓ3
  refine perfectInLayer_of_congr e₂ β ?_
  have hα : MulAut.congr e₂ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  obtain ⟨g, a, σ, ε, hε, hσ3, hαeq⟩ := exists_cube_normal_form_sigma _ hα
  rw [hαeq] at hα ⊢
  have hd0 : d4Graph F 0 = 1 := by
    ext h
    simp [coe_d4Graph]
  interval_cases ε
  · rw [hd0, mul_one] at hα ⊢
    by_cases hσ1 : σ = 1
    · subst hσ1
      obtain ⟨h, hh⟩ := d4_inner_of_diag hchar g a hα
      rw [hh] at hα ⊢
      have hh3 : h ^ 3 = 1 := by
        have hc : h ^ 3 ∈ Subgroup.center ↥(adjointGroup Tag.D4 F) := by
          rw [Subgroup.mem_center_iff]
          intro y
          have h1 := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 F) => φ y)
            (show MulAut.conj (h ^ 3) = 1 by rw [map_pow]; exact hα)
          simp only [MulAut.conj_apply, MulAut.one_apply] at h1
          calc y * h ^ 3 = h ^ 3 * y * (h ^ 3)⁻¹ * h ^ 3 := by rw [h1]
            _ = h ^ 3 * y := by group
        rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
      apply perfectInLayer_of_congr e₂.symm
      have hconj : MulAut.congr e₂.symm (MulAut.conj h) = MulAut.conj (e₂.symm h) := by
        ext y
        simp [MulAut.congr_apply, MulAut.conj_apply]
      rw [hconj]
      exact perfectInLayer_conj_omega (Or.inr (Or.inl rfl)) hG Nat.prime_three (by norm_num)
        (Ne.symm hℓ3) (e₂.symm h) (by rw [← map_pow, hh3, map_one])
    · exact perfectInLayer_d4_field hchar g a σ hσ1 hσ3 hα
  · by_cases hσ1 : σ = 1
    · subst hσ1
      exact perfectInLayer_d4_graph hchar g a (Or.inl rfl) hα
    · exact perfectInLayer_d4_graphField hchar g a σ hσ1 hσ3 (Or.inl rfl) hα
  · by_cases hσ1 : σ = 1
    · subst hσ1
      exact perfectInLayer_d4_graph hchar g a (Or.inr rfl) hα
    · exact perfectInLayer_d4_graphField hchar g a σ hσ1 hσ3 (Or.inr rfl) hα

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
