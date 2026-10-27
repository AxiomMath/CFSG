module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HUnits
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoE16

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

private instance decidableMemMonoDCompl : DecidablePred (· ∈ monoD) := fun σ =>
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

private lemma monoD_eq_ffK0_mul_hF :
    ∀ σ : Equiv.Perm (Fin 6), σ ∈ monoD →
      ∃ κ ∈ ffK0, ∃ φ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6))), σ = κ * φ := by
  decide +kernel

private lemma even_eq_symmDiff_ffF0_hE4 :
    ∀ J : Finset (Fin 6), Even J.card →
      ∃ F ∈ ffF0, ∃ K ∈ hE4, J = symmDiff F K := by
  decide +kernel

private lemma ffK0_hF_eq_one :
    ∀ σ : Equiv.Perm (Fin 6), σ ∈ ffK0 →
      σ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6))) → σ = 1 := by
  decide +kernel

private lemma ffF0_hE4_eq_empty :
    ∀ J : Finset (Fin 6), J ∈ ffF0 → J ∈ hE4 → J = ∅ := by
  decide +kernel

private lemma ffF0_map_mem :
    ∀ φ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6))), ∀ F ∈ ffF0,
      F.map φ.toEmbedding ∈ ffF0 := by
  decide +kernel

private lemma monoD_eq_invol_mul :
    ∀ σ : Equiv.Perm (Fin 6), σ ∈ monoD →
      ∃ σ₁ ∈ monoD, ∃ σ₂ ∈ monoD, σ₁ * σ₁ = 1 ∧ σ₂ * σ₂ = 1 ∧ σ = σ₁ * σ₂ := by
  decide +kernel

theorem hB0_inf_hD1 (fr : NFrame Q (Fin 6) c) : ffB0 fr ⊓ hD1 fr = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨hgB, hgD⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨J, hJ, rfl⟩ := (mem_ffB0_iff fr).mp hgB
  obtain ⟨σ, hσ, hσg⟩ := (mem_hD1_iff fr).mp hgD
  have h : fr.permOrth 1 * fr.signChange J = fr.permOrth σ * fr.signChange ∅ := by
    rw [fr.permOrth_one, fr.signChange_empty, one_mul, mul_one]
    exact hσg
  obtain ⟨-, hJ0⟩ := ffMono_unique fr h
  rw [hJ0, fr.signChange_empty]

theorem ffP0_eq_B0_mul_D1 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) {g : OGroup Q}
    (hg : g ∈ ffP0 hQ fr) : ∃ b ∈ ffB0 fr, ∃ d ∈ hD1 fr, g = b * d := by
  obtain ⟨σ, hσ, J, hJ, rfl⟩ := (mem_ffP0_iff hQ fr).mp hg
  refine ⟨fr.signChange (J.map σ.toEmbedding), signChange_mem_ffB0 fr ?_, fr.permOrth σ,
    (mem_hD1_iff fr).mpr ⟨σ, hσ, rfl⟩, ?_⟩
  · rwa [Finset.card_map]
  · exact fr.permOrth_mul_signChange σ J

theorem hU2_inf_hD2 (fr : NFrame Q (Fin 6) c) : hU2 fr ⊓ hD2 fr = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨hgU, hgD⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨σ, hσ, J, hJ, rfl⟩ := (mem_hU2_iff fr).mp hgU
  obtain ⟨τ, hτ, K, hK, hτg⟩ := (mem_hD2_iff fr).mp hgD
  obtain ⟨hστ, hJK⟩ := ffMono_unique fr hτg
  have hσ1 : σ = 1 := ffK0_hF_eq_one σ hσ (by simpa [hστ] using hτ)
  have hJ0 : J = ∅ := ffF0_hE4_eq_empty J hJ (by simpa [hJK] using hK)
  rw [hσ1, hJ0, fr.permOrth_one, fr.signChange_empty, one_mul]

theorem ffP0_eq_U2_mul_D2 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) {g : OGroup Q}
    (hg : g ∈ ffP0 hQ fr) : ∃ u ∈ hU2 fr, ∃ d ∈ hD2 fr, g = u * d := by
  obtain ⟨σ, hσ, J, hJ, rfl⟩ := (mem_ffP0_iff hQ fr).mp hg
  obtain ⟨κ, hκ, φ, hφ, rfl⟩ := monoD_eq_ffK0_mul_hF σ hσ
  obtain ⟨F', hF', K, hK, rfl⟩ := even_eq_symmDiff_ffF0_hE4 J hJ
  refine ⟨fr.permOrth κ * fr.signChange (F'.map φ.toEmbedding), ?_,
    fr.permOrth φ * fr.signChange K, ?_, ?_⟩
  · exact (mem_hU2_iff fr).mpr
      ⟨κ, hκ, F'.map φ.toEmbedding, ffF0_map_mem φ hφ F' hF', rfl⟩
  · exact (mem_hD2_iff fr).mpr ⟨φ, hφ, K, hK, rfl⟩
  · have hmap : (F'.map φ.toEmbedding).map φ⁻¹.toEmbedding = F' := by
      ext x
      simp only [Finset.mem_map, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
        rw [← hy]
        simpa using hz
      · intro hx
        exact ⟨φ x, ⟨x, hx, rfl⟩, by simp⟩
    rw [ffMono_mul fr κ φ (F'.map φ.toEmbedding) K, hmap]

theorem lift_cases (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) {U : Subgroup (OGroup Q)}
    (hU : IsLiftE16 hQ fr U) : U = ffB0 fr ∨ U = hU2 fr := by
  by_cases h : U = ffB0 fr
  · exact Or.inl h
  · right
    have hle : U ≤ hU2 fr := by
      intro u hu
      obtain ⟨σ, hσ, J, hJ, rfl⟩ := ff_liftE16_subset hQ fr hU h hu
      exact (mem_hU2_iff fr).mpr ⟨σ, hσ, J, hJ, rfl⟩
    haveI : Finite (hU2 fr) := Nat.finite_of_card_ne_zero (by rw [hU2_card fr]; norm_num)
    exact Subgroup.eq_of_le_of_card_ge hle (by simp [hU2_card fr, hU.2.2.1])

theorem ffP0_le_closure_involutions (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    ffP0 hQ fr ≤ Subgroup.closure {g : OGroup Q | g ∈ ffP0 hQ fr ∧ g * g = 1} := by
  intro g hg
  obtain ⟨b, hbB, d, hdD, rfl⟩ := ffP0_eq_B0_mul_D1 hQ fr hg
  apply Subgroup.mul_mem
  · exact Subgroup.subset_closure ⟨ffB0_le_ffP0 hQ fr hbB, ffB0_mul_self fr hbB⟩
  · obtain ⟨σ, hσ, rfl⟩ := (mem_hD1_iff fr).mp hdD
    obtain ⟨σ₁, hσ₁, σ₂, hσ₂, h21, h22, rfl⟩ := monoD_eq_invol_mul σ hσ
    rw [fr.permOrth_mul]
    apply Subgroup.mul_mem
    · apply Subgroup.subset_closure
      refine ⟨(mem_ffP0_iff hQ fr).mpr
        ⟨σ₁, hσ₁, ∅, by decide, by rw [fr.signChange_empty, mul_one]⟩, ?_⟩
      rw [← fr.permOrth_mul, h21, fr.permOrth_one]
    · apply Subgroup.subset_closure
      refine ⟨(mem_ffP0_iff hQ fr).mpr
        ⟨σ₂, hσ₂, ∅, by decide, by rw [fr.signChange_empty, mul_one]⟩, ?_⟩
      rw [← fr.permOrth_mul, h22, fr.permOrth_one]

end CFSG.OddStandard.SmallF3.Omega
