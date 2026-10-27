module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Base
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6PSp

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Cat7E6

open CatFactsSp4 Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

theorem out_model {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : Cat8.IsAdmQ (StatedProj (StatedSp 2 K)) (p ^ f) α) :
    (Cat8.innA (StatedProj (StatedSp 2 K)) α).Normal ∧
      ∃ φ : MulAut (StatedProj (StatedSp 2 K)), ∀ ψ : MulAut (StatedProj (StatedSp 2 K)),
        ∃ k : ℤ, (φ ^ k)⁻¹ * ψ ∈ Cat8.innA (StatedProj (StatedSp 2 K)) α := by
  have hodd := ringChar_ne_two_of_card (K := K) hp hp2 hK
  rw [innA_eq_range hp hp2 hf hK hα]
  have hN := range_conjAut_normal (K := K) hodd
  refine ⟨hN, ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := exists_zpow_ringEquiv K
  refine ⟨fieldAut 2 K φ₀, fun ψ => ?_⟩
  obtain ⟨X, σ, rfl⟩ := exists_eq_conjAut_mul_fieldAut hodd ψ
  obtain ⟨k, rfl⟩ := hφ₀ σ
  refine ⟨k, ?_⟩
  have h1 := hN.conj_mem _ ⟨X, rfl⟩ (fieldAut 2 K (φ₀ ^ k))⁻¹
  rw [inv_inv] at h1
  rw [← map_zpow]
  convert h1 using 1
  group

end Cat7E6

open Cat7E6 in
theorem cf81E6OutPSp : CF81E6OutPSp := by
  intro K₀ _ _ p f hp hp2 hf _ hL α hα
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hL
  obtain ⟨hN, φ', hφ'⟩ := out_model hp hp2 hf hK (isAdmQ_congr e hα)
  refine ⟨?_, (MulAut.congr e).symm φ', fun ψ => ?_⟩
  · have h2 : Cat8.innA K₀ α =
        (Cat8.innA _ (MulAut.congr e α)).map (MulAut.congr e).symm.toMonoidHom := by
      rw [← map_innA, Subgroup.map_map]
      ext x
      simp only [Subgroup.mem_map]
      constructor
      · intro hx
        exact ⟨x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [h2]
    exact hN.map _ (MulAut.congr e).symm.surjective
  · obtain ⟨k, hk⟩ := hφ' (MulAut.congr e ψ)
    refine ⟨k, ?_⟩
    rwa [← map_innA, Subgroup.mem_map_equiv, map_mul, map_inv, map_zpow,
      MulEquiv.symm_apply_apply] at hk

end CFSG.ComponentClassification.GSThmB
