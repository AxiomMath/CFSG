module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutSimDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutPerm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private instance ffOutSimTabDecMem : DecidablePred (· ∈ monoD) := fun σ =>
  decidable_of_iff'
    ((∏ j : Fin 6, ∏ i ∈ Finset.Iio j,
        (if σ i < σ j then (1 : ℤˣ) else -1)) = 1 ∧ monoG * σ = σ * monoG)
    (by
      show (σ ∈ alternatingGroup (Fin 6) ⊓
        Subgroup.centralizer ({monoG} : Set (Equiv.Perm (Fin 6)))) ↔
        ((∏ j : Fin 6, ∏ i ∈ Finset.Iio j,
          (if σ i < σ j then (1 : ℤˣ) else -1)) = 1 ∧ monoG * σ = σ * monoG)
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_eq_prod_prod_Iio]
      simp only [Set.mem_singleton_iff, forall_eq])

private def ffOutSimTabC : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5

private def ffOutSimTabList : Finset (Equiv.Perm (Fin 6)) :=
  {1, Equiv.swap 1 3 * Equiv.swap 4 5, Equiv.swap 0 1 * Equiv.swap 2 3, ffOutSimTabC,
    Equiv.swap 0 2 * Equiv.swap 4 5, Equiv.swap 0 2 * Equiv.swap 1 3,
    ffOutSimTabC * ffOutSimTabC * ffOutSimTabC, Equiv.swap 0 3 * Equiv.swap 1 2}

private theorem ffOutSimTab_mem_iff :
    ∀ σ : Equiv.Perm (Fin 6), σ ∈ monoD ↔ σ ∈ ffOutSimTabList := by
  unfold ffOutSimTabList ffOutSimTabC
  decide +kernel

theorem ffH_mul_signChange (J : Finset (Fin 6)) :
    ffH * ffMat 1 J = ffMat (ffConjPerm J) (ffConjSign J) * ffH := by
  revert J
  decide

theorem ffH_mul_monoD {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ monoD) :
    ∃ τ ∈ monoD, ∃ K : Finset (Fin 6), Even K.card ∧ ffH * ffMat σ ∅ = ffMat τ K * ffH := by
  have hmem : σ ∈ ffOutSimTabList := (ffOutSimTab_mem_iff σ).mp hσ
  simp only [ffOutSimTabList, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by decide, ∅, by decide, by decide⟩
  · exact ⟨1, by decide, {3, 5}, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide, ∅, by decide, by decide⟩
  · refine ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide, {3, 5}, by decide, ?_⟩
    unfold ffOutSimTabC
    decide
  · exact ⟨1, by decide, {2, 5}, by decide, by decide⟩
  · exact ⟨1, by decide, {2, 3}, by decide, by decide⟩
  · refine ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide, {2, 5}, by decide, ?_⟩
    unfold ffOutSimTabC
    decide
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide, {2, 3}, by decide, by decide⟩

theorem ffH_mul_rho :
    ffH * ffMat ffRhoPerm ffRhoSet = -(ffMat ffRhoPerm ffRhoSet * ffH) := by
  decide

theorem ffH_mul_a : ffH * ffMat 1 {0} = ffMat ffBeta {0, 2} * ffH := by
  decide

theorem ffH_mul_b : ffH * ffMat ffBeta ∅ = ffMat 1 {2} * ffH := by
  decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffX0_conj_signChange (fr : NFrame Q (Fin 6) 1) (J : Finset (Fin 6)) :
    ffX0 fr * ffM fr 1 J = ffM fr (ffConjPerm J) (ffConjSign J) * ffX0 fr :=
  ffX0_conj_of_mat fr (Or.inl (ffH_mul_signChange J))

theorem ffX0_conj_monoD (fr : NFrame Q (Fin 6) 1) {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ monoD) :
    ∃ τ ∈ monoD, ∃ K : Finset (Fin 6), Even K.card ∧
      ffX0 fr * ffM fr σ ∅ = ffM fr τ K * ffX0 fr := by
  obtain ⟨τ, hτ, K, hK, h⟩ := ffH_mul_monoD hσ
  exact ⟨τ, hτ, K, hK, ffX0_conj_of_mat fr (Or.inl h)⟩

theorem ffX0_conj_rho (fr : NFrame Q (Fin 6) 1) :
    ffX0 fr * ffM fr ffRhoPerm ffRhoSet = ffM fr ffRhoPerm ffRhoSet * ffX0 fr :=
  ffX0_conj_of_mat fr (Or.inr ffH_mul_rho)

theorem ffX0_conj_a (fr : NFrame Q (Fin 6) 1) :
    ffX0 fr * ffM fr 1 {0} = ffM fr ffBeta {0, 2} * ffX0 fr :=
  ffX0_conj_of_mat fr (Or.inl ffH_mul_a)

theorem ffX0_conj_b (fr : NFrame Q (Fin 6) 1) :
    ffX0 fr * ffM fr ffBeta ∅ = ffM fr 1 {2} * ffX0 fr :=
  ffX0_conj_of_mat fr (Or.inl ffH_mul_b)

theorem ffRho_mul_self (fr : NFrame Q (Fin 6) 1) :
    ffM fr ffRhoPerm ffRhoSet * ffM fr ffRhoPerm ffRhoSet = 1 := by
  rw [ffM_mul, ff_rho_perm_sq, ff_rho_symmDiff, ffM_univ]

theorem ffX0_normalizes_ffPS (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) {g : ProjSim Q}
    (hg : g ∈ ffPS hQ fr) : ffX0 fr * g * (ffX0 fr)⁻¹ ∈ ffPS hQ fr := by
  obtain ⟨σ, hσ, J, hJ, rfl⟩ := (mem_ffPS_iff hQ fr).mp hg
  obtain ⟨τ, hτ, K, hK, hτK⟩ := ffX0_conj_monoD fr hσ
  have hsym : symmDiff (∅ : Finset (Fin 6)) J = J := bot_symmDiff J
  have hprod : ffM fr σ J = ffM fr σ ∅ * ffM fr 1 J := by
    rw [ffM_mul fr σ 1 ∅ J]
    simp only [mul_one, Finset.map_empty]
    rw [hsym]
  have hJ1 := ffX0_conj_signChange fr J
  have key : ffX0 fr * ffM fr σ J * (ffX0 fr)⁻¹ =
      ffM fr τ K * ffM fr (ffConjPerm J) (ffConjSign J) := by
    rw [hprod]
    calc ffX0 fr * (ffM fr σ ∅ * ffM fr 1 J) * (ffX0 fr)⁻¹
        = (ffX0 fr * ffM fr σ ∅) * (ffM fr 1 J * (ffX0 fr)⁻¹) := by group
      _ = (ffM fr τ K * ffX0 fr) * (ffM fr 1 J * (ffX0 fr)⁻¹) := by rw [hτK]
      _ = ffM fr τ K * (ffX0 fr * ffM fr 1 J) * (ffX0 fr)⁻¹ := by group
      _ = ffM fr τ K * (ffM fr (ffConjPerm J) (ffConjSign J) * ffX0 fr) *
            (ffX0 fr)⁻¹ := by rw [hJ1]
      _ = ffM fr τ K * ffM fr (ffConjPerm J) (ffConjSign J) := by group
  have hEven : Even (symmDiff (K.map (ffConjPerm J)⁻¹.toEmbedding)
      (ffConjSign J)).card :=
    (ffOut_even_symmDiff_iff _ _).mpr
      (iff_of_true (by rw [Finset.card_map]; exact hK) (ff_conjSign_even J))
  rw [key, ffM_mul]
  exact (ffM_mem_ffPS_iff hQ fr (τ * ffConjPerm J)
    (symmDiff (K.map (ffConjPerm J)⁻¹.toEmbedding) (ffConjSign J))).mpr
    ⟨monoD.mul_mem hτ (ff_conjPerm_mem hJ), hEven⟩

theorem ffX0_mem_normalizer_ffPS (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) :
    ffX0 fr ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact ffX0_normalizes_ffPS hQ fr hg
  · intro hg
    have h1 : ffX0 fr * (ffX0 fr * g * (ffX0 fr)⁻¹) * (ffX0 fr)⁻¹ ∈ ffPS hQ fr :=
      ffX0_normalizes_ffPS hQ fr hg
    have heq : ffX0 fr * (ffX0 fr * g * (ffX0 fr)⁻¹) * (ffX0 fr)⁻¹ = g := by
      rw [ffX0_inv fr]
      calc ffX0 fr * (ffX0 fr * g * ffX0 fr) * ffX0 fr
          = (ffX0 fr * ffX0 fr) * g * (ffX0 fr * ffX0 fr) := by group
        _ = g := by rw [ffX0_mul_self fr]; group
    rw [heq] at h1
    exact h1

end CFSG.OddStandard.SmallF3.Omega
