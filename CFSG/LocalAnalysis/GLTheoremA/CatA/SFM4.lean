module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM4E9
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor fieldActor_one)
open CFSG.Blueprint.Chevalley (TwistTag)


theorem I2023FactC1_holds : I2023FactC1 := by
  intro S _ _ q hq hcat φ hφ3 hφi
  obtain ⟨d, hv, hP, ⟨eS⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  cases d with
  | trialityD4 q' =>
    have hP' : q'.card = q.card := hP
    have hcardq : q'.p ^ q'.exponent = 2 ^ q.exponent := by
      rw [← TauCeti.PrimePower.card_def, hP', TauCeti.PrimePower.card_def, hq]
    have hp2 : q'.p = 2 := by
      have hdvd : q'.p ∣ 2 ^ q.exponent := by
        rw [← hcardq]
        exact dvd_pow_self _ (Nat.pos_iff_ne_zero.1 q'.exponent_pos)
      exact (Nat.prime_dvd_prime_iff_eq q'.prime_p Nat.prime_two).1
        (q'.prime_p.dvd_of_dvd_pow hdvd)
    have hn : q'.exponent = q.exponent := by
      have h := hcardq
      rw [hp2] at h
      exact Nat.pow_right_injective (le_refl 2) h
    obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q' hv
    rw [hp2, hn] at hK
    simp only [hp2, hn] at hσ
    have hf : 1 ≤ q.exponent := q.exponent_pos
    obtain ⟨e, -⟩ : ∃ e : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom, True :=
      ⟨eS.trans eC, trivial⟩
    have hconj : ∀ y : S, MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
      intro y
      refine MulEquiv.ext fun z => ?_
      show e (y * e.symm z * y⁻¹) = e y * z * (e y)⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    obtain ⟨β, hβdef⟩ : ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        β = MulAut.congr e φ := ⟨_, rfl⟩
    have hβx : ∀ x : S, β (e x) = e (φ x) := by
      intro x
      rw [hβdef]
      show e (φ (e.symm (e x))) = e (φ x)
      rw [e.symm_apply_apply]
    have hβ3 : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hφ3, map_one]
    have hβi : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      intro h
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 h
      apply hφi
      refine MonoidHom.mem_range.2 ⟨e.symm x, ?_⟩
      apply (MulAut.congr e).injective
      rw [hconj, e.apply_symm_apply, ← hβdef]
      exact hx
    obtain ⟨g₀, δ, hδ, hgδ⟩ := sfm4_twist hf K hK σ hσ β hβ3 hβi
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : MulAut S, ψ = MulAut.conj (e.symm g₀) * φ := ⟨_, rfl⟩
    have hrel : ∀ x : S, e (ψ x) = fieldActor (t := TwistTag.D4) σ δ (e x) := by
      intro x
      rw [← hgδ, hψdef, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
        hβx]
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    have hδ3 : δ ^ 3 = 1 := by
      rcases hδ with rfl | rfl
      · exact sfm4_cube_eq_one hK hσ
      · rw [← pow_mul, mul_comm, pow_mul, sfm4_cube_eq_one hK hσ, one_pow]
    have hF3 : fieldActor (t := TwistTag.D4) σ δ ^ 3 = 1 := by
      rw [← sfm4_fieldActor_pow, hδ3, fieldActor_one]
    have hcongr : MulAut.congr e ψ = fieldActor (t := TwistTag.D4) σ δ := by
      refine MulEquiv.ext fun y => ?_
      have h := hrel (e.symm y)
      rw [e.apply_symm_apply] at h
      exact h
    have hψ3 : ψ ^ 3 = 1 := by
      apply (MulAut.congr e).injective
      rw [map_pow, hcongr, hF3, map_one]
    have hcount : Nat.card {x : S // ψ x = x} =
        (2 ^ q.exponent) ^ 6 * (((2 ^ q.exponent) ^ 6 - 1) * ((2 ^ q.exponent) ^ 2 - 1)) := by
      rw [← sfm4_card_fix hf K hK σ hσ hδ]
      refine Nat.card_congr ((Equiv.subtypeEquiv e.toEquiv (fun x => ?_)).trans
        (Equiv.subtypeEquivRight fun y => Iff.rfl))
      show ψ x = x ↔ fieldActor (t := TwistTag.D4) σ δ (e x) = e x
      rw [← hrel x, e.injective.eq_iff]
    refine ⟨e.symm g₀, ?_, ?_, ?_⟩
    · rw [← hψdef]
      exact hψ3
    · rw [← hψdef, hcount]
      exact sfm4_factorization_two hf
    · rw [← hψdef]
      obtain ⟨ι₁, ι₂, hi₁, hi₂, hc, hfix₁, hfix₂⟩ := sfm4_commuting_fix hf K hK σ hσ
      have hfixψ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          fieldActor (t := TwistTag.D4) σ σ y = y → ψ (e.symm y) = e.symm y := by
        intro y hy
        apply e.injective
        rw [hrel (e.symm y), e.apply_symm_apply]
        rcases hδ with rfl | rfl
        · exact hy
        · rw [sfm4_fieldActor_pow, sq, MulAut.mul_apply, hy, hy]
      obtain ⟨P, hPH, hPab, hPcard⟩ := sfm4_e9_of_commuting
        ((e.symm : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* S).toMonoidHom.comp ι₁)
        ((e.symm : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* S).toMonoidHom.comp ι₂)
        (e.symm.injective.comp hi₁) (e.symm.injective.comp hi₂)
        (fun A B => by
          show e.symm (ι₁ A) * e.symm (ι₂ B) = e.symm (ι₂ B) * e.symm (ι₁ A)
          rw [← map_mul, ← map_mul, hc A B])
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup ψ)
        (fun A => hfixψ _ (hfix₁ A)) (fun A => hfixψ _ (hfix₂ A))
      exact ⟨P, hPab, hPcard, fun z hz => hPH hz⟩
  | _ => exact hP.elim

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
