module

public import CFSG.LieType.SpecialLinear.SLModel.CoverType
public import CFSG.LieType.SpecialLinear.SLModel.Simple
public import CFSG.LieType.SpecialLinear.TypeLabel

public section

namespace CFSG.LieType.SpecialLinear.SLModel

open Matrix CFSG.LieType.SpecialLinear.ExteriorModel CFSG.LieType.SpecialLinear
  CFSG.LieType.Universal.SpecialLinear CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.Quasithin.SmithCurtis
open scoped MatrixGroups

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {m f : ℕ}

omit [Fintype F] [CharP k 2] [Algebra F k] in
theorem isCoverType_congr_H [Finite F] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} {y : V}
    {χ χ' : SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F 2) ρ y χ J)
    (hχ : ∀ g ∈ (curtisDatum m F 2).H, χ g = χ' g) :
    IsCoverType (rankOne m F 2) ρ y χ' J := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  have hhh : ∀ (s : Fin m) (u : Fˣ),
      χ ((rankOne m F 2).hh s u) = χ' ((rankOne m F 2).hh s u) := fun s u =>
    hχ _ (hdiag_mem_H m F s u)
  refine ⟨h1, h2, fun g hg => ?_, fun s => ?_⟩
  · rw [← hχ g (by simpa using hg)]
    exact h3 g hg
  · rw [h4 s]
    simp only [hhh]

theorem exists_iso_slModelRep (hF : Fintype.card F = 2 ^ f) {V : Type} [AddCommGroup V]
    [Module k V] {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : SpecialLinearGroup (Fin (m + 1)) F → k}
    {J : Finset (Fin m)} (ht : IsCoverType (rankOne m F 2) ρ y χ J) :
    ∃ ε : Fin f → Finset (Fin (m + 1)), (∀ r, (0 : Fin (m + 1)) ∉ ε r) ∧
      (∀ g ∈ (curtisDatum m F 2).H, χ g = slChiEps m (algebraMap F k) ε g) ∧
      (∀ s : Fin m, s ∈ J ↔ ∀ r, s.succ ∉ ε r) ∧
      ∃ β : V ≃ₗ[k] BModel k ε, ∀ g v,
        β (ρ g v) = slModelRep (F := F) (k := k) ε g (β v) := by
  obtain ⟨ε, h0, hε, hJ⟩ :=
    exists_eps_of_isCoverType m (by rwa [Nat.card_eq_fintype_card]) ht
  refine ⟨ε, h0, hε, hJ, ?_⟩
  have hJ' : (Finset.univ.filter fun s : Fin m => bR0 ε s = ∅) = J := by
    ext s
    rw [Finset.mem_filter, hJ s, bR0, Finset.filter_eq_empty_iff]
    simp
  have ht' : IsCoverType (rankOne m F 2) (slModelRep (F := F) (k := k) ε) (bTop ε) χ J := by
    have h := isCoverType_slModelRep (F := F) (k := k) hF ε
    rw [hJ'] at h
    exact isCoverType_congr_H h fun g hg => (hε g hg).symm
  exact iso_of_isCoverType_sl m F 2 hρ (isSimpleRep_slModelRep hF ε) ht ht'

end CFSG.LieType.SpecialLinear.SLModel
