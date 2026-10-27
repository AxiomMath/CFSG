module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQGen
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem exists_zpow_mul_mem_inner_linear (hn : 1 ≤ n) :
    ∃ g ∈ linearAutGroup n K, ∀ x ∈ linearAutGroup n K,
      ∃ k : ℤ, g ^ k * x ∈ inner (projectiveSL n K) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨B₀, hB₀⟩ := GeneralLinearGroup.det_surjective (n := Fin n) (R := K) ζ
  refine ⟨conjAut n K B₀, conjAut_mem_linearAutGroup B₀, fun x hx => ?_⟩
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hx
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hζ (GeneralLinearGroup.det A))
  refine ⟨-m, ?_⟩
  set B := B₀ ^ (-m) * A with hB
  have hdet : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, map_zpow, hB₀, ← hm, _root_.zpow_neg, inv_mul_cancel]
  have hBmem : (B : Matrix (Fin n) (Fin n) K).det = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hdet
    simpa using this
  let g' : SpecialLinearGroup (Fin n) K := ⟨(B : Matrix (Fin n) (Fin n) K), hBmem⟩
  have hg' : SpecialLinearGroup.toGL g' = B := by
    ext1
    rfl
  refine MonoidHom.mem_range.mpr ⟨proj n K g', ?_⟩
  rw [← conjAut_toGL, hg', hB, map_mul, map_zpow]

theorem outNoA4_projectiveSL (hn : 3 ≤ n) : OutNoA4 (projectiveSL n K) := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, hDn, hEn, -, hE, ⟨g, -, hg⟩, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hnorm : ∀ H : Subgroup (MulAut (projectiveSL n K)),
      (H.subgroupOf (standardAutGroup n K)).Normal → H.Normal := by
    intro H hH
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    exact mem_subgroupOf.mp (hH.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩)
  have := hnorm _ hDn
  have := hnorm _ hEn
  exact outNoA4_of_chain_zpow (exists_zpow_mul_mem_inner_linear (by omega)) hE
    ⟨g, fun x => hg x (hgenTop ▸ Subgroup.mem_top x)⟩

theorem outNoA4_of_lieModel_PSL {S : Type} [Group S] {n p f : ℕ} (hn : 3 ≤ n)
    (h : CFSG.Blueprint.LieModel S .PSL n p f) : OutNoA4 S := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  exact OutNoA4.of_mulEquiv e.symm (outNoA4_projectiveSL hn)

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
