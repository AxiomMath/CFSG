module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

section Bridge

variable {p : ℕ} {K : Type} [Field K]

theorem isPrimeFormGram_one {n : ℕ} : IsPrimeFormGram (1 : GL (Fin n) K) := by
  refine ⟨by rw [Units.val_one, transpose_one], fun i j => ?_⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

variable (h : UnitaryFieldData p 1 K)

abbrev SUI : Subgroup (GL (Fin 3) K) :=
  gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

abbrev PUI : Type :=
  primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem statedSU_eq_SUI : StatedSU 3 (p ^ 1) K = SUI h := unitarySU_eq_gramSU h 3

@[expose] def eSU : ↥(StatedSU 3 (p ^ 1) K) ≃* ↥(SUI h) :=
  MulEquiv.subgroupCongr (statedSU_eq_SUI h)

theorem coe_eSU (g : ↥(StatedSU 3 (p ^ 1) K)) : ((eSU h g : ↥(SUI h)) : GL (Fin 3) K) = g := rfl

theorem map_normOneScalars_subgroupCongr {H₁ H₂ : Subgroup (GL (Fin 3) K)} (heq : H₁ = H₂)
    (m : ℕ) :
    (normOneScalars h H₁ m).map (MulEquiv.subgroupCongr heq).toMonoidHom =
      normOneScalars h H₂ m := by
  subst heq
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem map_scalars_eSU :
    ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ 1) K)).map (eSU h).toMonoidHom =
      normOneScalars h (SUI h) 3 := by
  rw [← unitaryScalars_eq h (by norm_num : 1 ≤ 3)]
  exact map_normOneScalars_subgroupCongr h (statedSU_eq_SUI h) 3

@[expose] noncomputable def projEquivPUI : StatedProj (StatedSU 3 (p ^ 1) K) ≃* PUI h :=
  QuotientGroup.congr ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ 1) K))
    (normOneScalars h (SUI h) 3) (eSU h) (map_scalars_eSU h)

theorem projEquivPUI_mk (g : ↥(StatedSU 3 (p ^ 1) K)) :
    projEquivPUI h (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf
      (StatedSU 3 (p ^ 1) K)) g) = (QuotientGroup.mk (eSU h g) : PUI h) :=
  QuotientGroup.congr_mk' _ _ _ _ g

end Bridge

section Cover

variable {p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p 1 K) {X : Type*} [Group X]

structure CoverDataU (L : Subgroup X) where
  φ : ↥(SUI h) →* ↥L
  surj : Function.Surjective φ
  ker_scalar : ∀ g ∈ φ.ker, ∃ r : Kˣ, (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) r
  ψ : (↥L ⧸ Subgroup.center ↥L) ≃* PUI h
  hψ : ∀ g, ψ (QuotientGroup.mk (φ g)) = (QuotientGroup.mk g : PUI h)

@[expose] noncomputable def coverDataU_of_cover {L : Subgroup X}
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU 3 (p ^ 1) K))
    (φ : ↥(StatedSU 3 (p ^ 1) K) →* ↥L) (hφs : Function.Surjective φ)
    (hφc : ∀ g : ↥(StatedSU 3 (p ^ 1) K),
      QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ 1) K)) g =
        θ (QuotientGroup.mk' (Subgroup.center ↥L) (φ g)))
    (hφk : φ.ker ≤ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ 1) K)) :
    CoverDataU h L where
  φ := φ.comp (eSU h).symm.toMonoidHom
  surj := hφs.comp (eSU h).symm.surjective
  ker_scalar := by
    intro g hg
    have h1 : (eSU h).symm g ∈ φ.ker := hg
    have h2 := hφk h1
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h2
    obtain ⟨r, hr⟩ := h2
    exact ⟨r, hr.symm⟩
  ψ := θ.trans (projEquivPUI h)
  hψ := by
    intro g
    have h1 := hφc ((eSU h).symm g)
    show projEquivPUI h (θ (QuotientGroup.mk' (Subgroup.center ↥L) (φ ((eSU h).symm g)))) = _
    rw [← h1, projEquivPUI_mk, MulEquiv.apply_symm_apply]

end Cover

end CFSG.QuasithinUnique.Setup.Family
