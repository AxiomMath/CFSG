module

public import CFSG.LargeExtraspecial.AS35WComp
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearFourThree

public section

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.RankThree.PartTwo.Census
open scoped MatrixGroups

namespace AS35W

theorem nineSL_comm (B : SL(2, GaloisField 3 2)) :
    nineSL B * nineInvolution = nineInvolution * nineSL B := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_nineInvolution]
  change (nineBlock (B : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) *
    nineBlock (nineI • (1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)))) i j =
    (nineBlock (nineI • (1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))) *
      nineBlock (B : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))) i j
  rw [← map_mul, ← map_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

@[expose] noncomputable def nineProj :
    SL(2, GaloisField 3 2) →* ProjectiveSpecialLinearGroup (Fin 2 × Fin 2) nineBase :=
  (QuotientGroup.mk' (center (SpecialLinearGroup (Fin 2 × Fin 2) nineBase))).comp nineSL

theorem ker_nineProj : nineProj.ker = center SL(2, GaloisField 3 2) := by
  ext B
  rw [MonoidHom.mem_ker, nineProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · intro hB
    rw [Subgroup.mem_center_iff] at hB ⊢
    intro B'
    exact nineSL_injective (by rw [map_mul, map_mul, hB])
  · intro hB
    obtain ⟨r, hr, hBr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hB
    rw [Fintype.card_fin] at hr
    have hr' : r = 1 ∨ r = -1 := mul_self_eq_one_iff.1 (by rw [← sq]; exact hr)
    have hval : ((nineSL B : SpecialLinearGroup (Fin 2 × Fin 2) nineBase) :
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) nineBase) = 1 ∨
        ((nineSL B : SpecialLinearGroup (Fin 2 × Fin 2) nineBase) :
          Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) nineBase) = -1 := by
      change nineBlock (B : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) = 1 ∨
        nineBlock (B : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) = -1
      rw [← hBr]
      rcases hr' with rfl | rfl
      · left
        rw [scalar_apply, ← smul_one_eq_diagonal, one_smul, map_one]
      · right
        rw [scalar_apply, ← smul_one_eq_diagonal, neg_one_smul, map_neg, map_one]
    rw [Subgroup.mem_center_iff]
    intro g
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rcases hval with h | h <;> rw [h]
    · rw [Matrix.mul_one, Matrix.one_mul]
    · rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul]

theorem isSimpleGroup_nineRange : IsSimpleGroup nineProj.range := by
  have e : nineProj.range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 2) :=
    (QuotientGroup.quotientKerEquivRange nineProj).symm.trans
      (QuotientGroup.quotientMulEquivOfEq ker_nineProj)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 2)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
      (by rw [card_galoisField_three_two]; norm_num)
  exact e.isSimpleGroup_congr.mpr inferInstance

theorem nineRange_perfect : ⁅nineProj.range, nineProj.range⁆ = nineProj.range := by
  have := isPerfect_sl2_nine
  have htop : ⁅(⊤ : Subgroup SL(2, GaloisField 3 2)), ⊤⁆ = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  rw [MonoidHom.range_eq_map, ← map_commutator, htop]

theorem false_of_nineInvolution [Finite (ProjectiveSpecialLinearGroup (Fin 2 × Fin 2) nineBase)]
    (hz : W2Data (ProjectiveSpecialLinearGroup (Fin 2 × Fin 2) nineBase)
      (QuotientGroup.mk' (center (SpecialLinearGroup (Fin 2 × Fin 2) nineBase)) nineInvolution)) :
    False := by
  set mk := QuotientGroup.mk' (center (SpecialLinearGroup (Fin 2 × Fin 2) nineBase))
  set T := nineInvolution
  set H₀ := (centralizer ({T} : Set (SpecialLinearGroup (Fin 2 × Fin 2) nineBase))).map mk
  have hs := isSimpleGroup_nineRange
  refine hz.false_of_component H₀ nineProj.range ?_ ?_ ?_ ?_ hs ?_
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : g * T = T * g := mem_centralizer_singleton_iff.1 hg
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg']
  · intro c hc x hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ c
    obtain ⟨g, hg, rfl⟩ := hx
    replace hg : g * T = T * g := mem_centralizer_singleton_iff.1 hg
    rw [mem_centralizer_singleton_iff] at hc
    rw [← map_mul, ← map_mul] at hc
    set κ := (h * T)⁻¹ * (T * h) with hκdef
    have hκ : κ ∈ center (SpecialLinearGroup (Fin 2 × Fin 2) nineBase) :=
      (QuotientGroup.eq).1 hc
    have hκc := Subgroup.mem_center_iff.1 hκ
    have e1 : h⁻¹ * T * h = T * κ := by rw [hκdef]; group
    have e2 : h * T * κ = T * h := by rw [hκdef]; group
    refine ⟨h * g * h⁻¹, mem_centralizer_singleton_iff.2 ?_, by rw [map_mul, map_mul, map_inv]⟩
    calc h * g * h⁻¹ * T = h * g * (h⁻¹ * T * h) * h⁻¹ := by group
      _ = h * g * (T * κ) * h⁻¹ := by rw [e1]
      _ = h * (g * T) * κ * h⁻¹ := by group
      _ = h * (T * g) * κ * h⁻¹ := by rw [hg]
      _ = h * T * (g * κ) * h⁻¹ := by group
      _ = h * T * (κ * g) * h⁻¹ := by rw [hκc g]
      _ = h * T * κ * g * h⁻¹ := by group
      _ = T * h * g * h⁻¹ := by rw [e2]
      _ = T * (h * g * h⁻¹) := by group
  · rintro _ ⟨B, rfl⟩
    exact ⟨nineSL B, mem_centralizer_singleton_iff.2 (nineSL_comm B), rfl⟩
  · rintro c ⟨g, hg, rfl⟩ x ⟨B, rfl⟩
    replace hg : g * T = T * g := mem_centralizer_singleton_iff.1 hg
    obtain ⟨B', hB'⟩ := conj_mem_range_nineSL hg B
    refine ⟨B', ?_⟩
    change mk (nineSL B') = mk g * mk (nineSL B) * (mk g)⁻¹
    rw [hB', map_mul, map_mul, map_inv]
  · refine exists_noncomm_of_perfect nineRange_perfect ?_
    have := hs
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance

end AS35W

end CFSG.LargeExtraspecial
