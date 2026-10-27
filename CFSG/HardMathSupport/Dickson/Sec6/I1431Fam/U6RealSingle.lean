module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealArith
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealComp

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne

section Single

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem u6r_single (hf : Odd f) (g : primeFormUnitary h (idGram K 6)) {μ : Kˣ}
    (hg3 : (g : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) μ)
    (hμ : ∀ a : Kˣ, a ^ 3 ≠ μ) :
    ∃ i₀ : t6psub_Idx h 6 g, (∀ i, i = i₀) ∧
      IsTypeL2 ((2 ^ f) ^ 3) ↥((t6psub_block g i₀).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6))) := by
  classical
  haveI := h.finite
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin g) :=
    t6psuh_primaryData_toLin' h g.2 Nat.prime_three (by norm_num) hg3
  set x : Module.End K (Fin 6 → K) := ((t6psub_toLin g : LinearMap.GeneralLinearGroup K
    (Fin 6 → K)) : Module.End K (Fin 6 → K)) with hx
  set p : K[X] := X ^ 3 - C (μ : K) with hp
  have hpirr : Irreducible p := u6r_irreducible hμ
  have hpmon : p.Monic := monic_X_pow_sub_C _ (by norm_num)
  have hpdeg : p.natDegree = 3 := natDegree_X_pow_sub_C
  have hx3 : x ^ 3 = algebraMap K (Module.End K (Fin 6 → K)) (μ : K) := by
    have e : (t6psub_toLin g) ^ 3 = Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.scalar (Fin 6) μ) := by
      unfold t6psub_toLin
      rw [← map_pow, hg3]
    apply LinearMap.ext
    intro v
    rw [hx, ← Units.val_pow_eq_pow_val, e, t6psub_glA_scalar_apply, Module.algebraMap_end_apply]
  have hpx : aeval x p = 0 := by
    rw [hp, map_sub, map_pow, aeval_X, aeval_C, hx3, sub_self]
  have hmin : p = minpoly K x := minpoly.eq_of_irreducible_of_monic hpirr hpx hpmon
  have hpmem : p ∈ primaryFactors x := by
    rw [mem_primaryFactors]
    exact ⟨hpirr, hpmon, hmin ▸ dvd_refl _⟩
  have honly : ∀ b ∈ primaryFactors x, b = p := by
    intro b hb
    obtain ⟨hbirr, hbmon, hbdvd⟩ := mem_primaryFactors.1 hb
    rw [← hmin] at hbdvd
    exact eq_of_monic_of_associated hbmon hpmon (hbirr.associated_of_dvd hpirr hbdvd)
  have hcomp : primaryComponent x p = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_primaryComponent, hpx]
    rfl
  have hmult : primaryMultiplicity x p = 2 := by
    haveI : Fact (Irreducible p) := ⟨hpirr⟩
    have h1 := finrank_primaryComponent x (a := p)
    have h6 : Module.finrank K (primaryComponent x p) = 6 := by
      rw [hcomp, finrank_top, Module.finrank_fin_fun]
    rw [h6, hpdeg] at h1
    show Module.finrank (AdjoinRoot p) (primaryComponent x p) = 2
    omega
  have hself : dualPoly h.bar p = p := honly _ (dualPoly_mem_primaryFactors H hpmem)
  have h8 : 8 ≤ 2 ^ (f * 3) := by
    have hf1 : 1 ≤ f := h.one_le
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (f * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hgood : IsGoodBlock h (t6psub_toLin g) ⟨p, hpmem⟩ := by
    refine ⟨by rw [hmult], fun _ => ?_⟩
    change (primaryMultiplicity x p, 2 ^ (f * p.natDegree)) ∉
      ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))
    rw [hmult, hpdeg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    omega
  refine ⟨⟨⟨p, hpmem⟩, hgood⟩, fun i => Subtype.ext (Subtype.ext (honly _ i.1.2)), ?_⟩
  have hT := u6r_isTypeL2_block g H ⟨⟨p, hpmem⟩, hgood⟩ hself hmult
  rwa [show (2 : ℕ) ^ (f * (p : K[X]).natDegree) = (2 ^ f) ^ 3 by rw [hpdeg, pow_mul]] at hT

end Single

end CFSG.HardMathSupport.Dickson.Sec6.I1431
