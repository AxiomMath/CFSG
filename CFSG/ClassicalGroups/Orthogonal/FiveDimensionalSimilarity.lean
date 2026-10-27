module

public import CFSG.ClassicalGroups.Symplectic.OrthogonalFiveModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSimilarity

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal

open Matrix QuadraticMap
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalFive

variable {K : Type} [Field K] [Finite K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_five_dimensional_orthogonal_similarity
    (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 5) :
    ∃ (d : Kˣ) (psi : V ≃ₗ[K] selfAdjointSubmodule K)
      (eO : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)),
      (∀ v, Q v = (d : K) * selfAdjointForm K (psi v)) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : selfAdjointSubmodule K),
        (eO g).val X = psi (g.val (psi.symm X))) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) (v : V),
        (eO.symm g).val v = psi.symm (g.val (psi v))) ∧
      (∀ g : TauCeti.QuadraticMap.orthogonalGroup Q,
        LinearEquiv.det (eO g).val = LinearEquiv.det g.val) ∧
      (QuadraticMap.specialOrthogonalWithin Q).map eO.toMonoidHom =
        QuadraticMap.specialOrthogonalWithin (selfAdjointForm K) ∧
      (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map eO.toMonoidHom =
        commutator (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) := by
  obtain ⟨d, psi, eO, hpsi, happly, hsymm⟩ :=
    finite_odd_five_selfAdjoint_form_similarity hodd Q hQ hdim
  have hdet : ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q,
      LinearEquiv.det (eO g).val = LinearEquiv.det g.val := by
    intro g
    have hconj : (eO g).val = (psi.symm.trans g.val).trans psi := by
      apply LinearEquiv.ext
      intro X
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
      exact happly g X
    rw [hconj, LinearEquiv.det_conj]
  refine ⟨d, psi, eO, hpsi, happly, hsymm, hdet, ?_, ?_⟩
  · apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro g hg
      rw [Subgroup.mem_comap]
      rw [QuadraticMap.mem_specialOrthogonalWithin_iff] at hg ⊢
      change LinearEquiv.det (eO g).val = 1
      rw [hdet g, hg]
    · intro g hg
      rw [Subgroup.mem_map]
      refine ⟨eO.symm g, ?_, eO.apply_symm_apply g⟩
      rw [QuadraticMap.mem_specialOrthogonalWithin_iff] at hg ⊢
      have h := hdet (eO.symm g)
      rw [eO.apply_symm_apply, hg] at h
      exact h.symm
  · have htop : (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).map
        eO.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]
      exact eO.surjective
    calc
      (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map eO.toMonoidHom =
          (⁅(⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
            (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))⁆ :
            Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).map eO.toMonoidHom := by
        rw [commutator_def]
      _ = ⁅(⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).map eO.toMonoidHom,
            (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).map eO.toMonoidHom⁆ :=
        Subgroup.map_commutator _ _ _
      _ = ⁅(⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K))),
            (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)))⁆ := by
        rw [htop]
      _ = commutator (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) := by
        rw [commutator_def]

theorem commutator_relIndex_specialOrthogonalWithin_five
    (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 5) :
    (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).relIndex
      (QuadraticMap.specialOrthogonalWithin Q) = 2 := by
  obtain ⟨d, psi, eO, hpsi, happly, hsymm, hdet, hSO, hD⟩ :=
    exists_five_dimensional_orthogonal_similarity hodd Q hQ hdim
  rw [← Subgroup.relIndex_map_map_of_injective (f := eO.toMonoidHom)
    (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))
    (QuadraticMap.specialOrthogonalWithin Q) eO.injective]
  rw [hD, hSO]
  exact CFSG.ClassicalGroups.Symplectic.commutator_relIndex_specialOrthogonalWithin hodd

end CFSG.ClassicalGroups.Orthogonal
