module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrame6Mono
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrame6Vec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrame6Orth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrame6NFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrame6Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrame6Monom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrame6Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fk_fr_core (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (t : Fin 6 → OGroup Q) (ht2 : ∀ i, t i * t i = 1) (ht1 : ∀ i, invDim (t i) = 1)
    (hcomm : ∀ i j, phiSim Q (t i) * phiSim Q (t j) = phiSim Q (t j) * phiSim Q (t i))
    (hne : ∀ i j, i ≠ j → phiSim Q (t i) ≠ phiSim Q (t j))
    (hinn : ∀ i j, i ≠ j → t i * t j ∈ omegaGroup hQ)
    (g : OGroup Q) (hg : g ∈ omegaGroup hQ) (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ i, phiSim Q (g * t i * g⁻¹) = phiSim Q (t (σ i))) :
    Equiv.Perm.sign σ = 1 := by
  choose v hv hvt using fun i => fk_fr_exists_vec hQ (ht2 i) (ht1 i)
  have hcomm' : ∀ i j,
      phiSim Q (reflOf Q (v i) (hv i)) * phiSim Q (reflOf Q (v j) (hv j)) =
        phiSim Q (reflOf Q (v j) (hv j)) * phiSim Q (reflOf Q (v i) (hv i)) := by
    intro i j
    have h := hcomm i j
    rwa [hvt i, hvt j] at h
  have hne' : ∀ i j, i ≠ j → phiSim Q (reflOf Q (v i) (hv i)) ≠
      phiSim Q (reflOf Q (v j) (hv j)) := by
    intro i j hij
    have h := hne i j hij
    rwa [hvt i, hvt j] at h
  have hinn' : ∀ i j, i ≠ j →
      reflOf Q (v i) (hv i) * reflOf Q (v j) (hv j) ∈ omegaGroup hQ := by
    intro i j hij
    have h := hinn i j hij
    rwa [hvt i, hvt j] at h
  have horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (v i) (v j) = 0 := by
    intro i j hij
    exact fk_fr_polar_eq_zero hQ hdim (hv i) (hv j) (hcomm' i j) (hne' i j hij)
  have hnorm_eq : ∀ i j, i ≠ j → Q (v i) = Q (v j) := by
    intro i j hij
    exact fk_fr_norm_eq hQ (hv i) (hv j) (hinn' i j hij)
  have hnorm0 : ∀ i, Q (v i) = Q (v 0) := by
    intro i
    by_cases hi : i = 0
    · subst hi; rfl
    · exact hnorm_eq i 0 hi
  have hc0 : Q (v 0) ≠ 0 := hv 0
  have hc : Q (v 0) = 1 ∨ Q (v 0) = -1 :=
    (by decide : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1) (Q (v 0)) (hv 0)
  obtain ⟨fr, hfr⟩ := fk_fr_exists_nframe hdim hc0 v hnorm0 horth
  have hmon : ∀ i, ∃ a : ZMod 3, a ≠ 0 ∧
      (g : V ≃ₗ[ZMod 3] V) (fr.b i) = a • fr.b (σ i) := by
    intro i
    have hσi := hσ i
    rw [hvt i, hvt (σ i)] at hσi
    obtain ⟨a, ha, hga⟩ := fk_fr_conj_vec hQ hdim (hv i) (hv (σ i)) g hσi
    exact ⟨a, ha, by rw [hfr i, hfr (σ i)]; exact hga⟩
  obtain ⟨K, hK⟩ := fk_fr_monomial fr g σ hmon
  have hmem : fr.permOrth σ * fr.signChange K ∈ omegaGroup hQ := by
    rw [← hK]; exact hg
  exact fk_fr_sign_of_mem_omega hQ hc fr σ K hmem

end CFSG.OddStandard.SmallF3.Omega
