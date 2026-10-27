module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinElem
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoConj

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatFactsSp4

variable {K : Type} [Field K]

@[expose] def gPrime {a b : K} (hab : a ^ 2 + b ^ 2 = -1) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![a, b; b, -a], by rw [det_fin_two_of]; linear_combination -hab⟩

theorem eq_smul_of_mem_center {g : Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : g ∈ center (Matrix.SpecialLinearGroup (Fin 2) K)) :
    ∃ r : K, (g : Matrix (Fin 2) (Fin 2) K) = r • 1 := by
  obtain ⟨r, -, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp hg
  refine ⟨r, ?_⟩
  rw [← hr]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

theorem mem_center_of_eq_smul {g : Matrix.SpecialLinearGroup (Fin 2) K} {r : K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = r • 1) :
    g ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨r, ?_, ?_⟩
  · have h := g.2
    rw [hg, det_smul, det_one, mul_one, Fintype.card_fin] at h
    exact h
  · rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

variable {G : Type*} [Group G]

theorem exists_E4_of_hom [Finite G] (h2 : (2 : K) ≠ 0) (hodd : Odd (Nat.card K)) [Finite K]
    (ψ : Matrix.SpecialLinearGroup (Fin 2) K →* G)
    (hker : ψ.ker = center (Matrix.SpecialLinearGroup (Fin 2) K)) :
    ∃ E : Subgroup G, E ≤ ψ.range ∧ ElemTwo E ∧ 4 ≤ Nat.card E := by
  obtain ⟨a, b, hab⟩ := OddClassSelector.exists_sq_add_sq hodd (-1)
  set g := gPrime hab
  set J := (J₁SL : Matrix.SpecialLinearGroup (Fin 2) K)
  have hJm : (J : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl
  have hgm : (g : Matrix (Fin 2) (Fin 2) K) = !![a, b; b, -a] := rfl
  have hc : ∀ x : Matrix.SpecialLinearGroup (Fin 2) K, (∃ r : K, (x : Matrix (Fin 2) (Fin 2) K) =
      r • 1) → ψ x = 1 := fun x ⟨r, hr⟩ => by
    rw [← MonoidHom.mem_ker, hker]
    exact mem_center_of_eq_smul hr
  have hnc : ∀ x : Matrix.SpecialLinearGroup (Fin 2) K, ψ x = 1 →
      ∃ r : K, (x : Matrix (Fin 2) (Fin 2) K) = r • 1 := fun x hx => by
    rw [← MonoidHom.mem_ker, hker] at hx
    exact eq_smul_of_mem_center hx
  have hJJ : ψ J * ψ J = 1 := by
    rw [← map_mul]
    refine hc _ ⟨-1, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hJm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hgg : ψ g * ψ g = 1 := by
    rw [← map_mul]
    refine hc _ ⟨-1, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hgm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination | linear_combination hab
  have hJg : ψ J * ψ g = ψ g * ψ J := by
    have h1 : ψ (J * g * (g * J)⁻¹) = 1 := by
      refine hc _ ⟨-1, ?_⟩
      have hinv : ((g * J)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) = J⁻¹ * g⁻¹ := mul_inv_rev g J
      rw [hinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.SpecialLinearGroup.coe_inv, hJm, hgm]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] <;>
        first | linear_combination | linear_combination hab
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [← map_mul, ← map_mul]
    exact h1
  have hJ1 : ψ J ≠ 1 := by
    intro h
    obtain ⟨r, hr⟩ := hnc _ h
    have := congrFun (congrFun hr 0) 1
    simp [hJm] at this
  have hg1 : ψ g ≠ 1 := by
    intro h
    obtain ⟨r, hr⟩ := hnc _ h
    have e1 := congrFun (congrFun hr 0) 0
    have e2 := congrFun (congrFun hr 1) 1
    have e3 := congrFun (congrFun hr 0) 1
    simp [hgm] at e1 e2 e3
    rw [e3] at hab
    have ha0 : a = 0 := by
      have : (2 : K) * a = 0 := by linear_combination e1 - e2
      exact (mul_eq_zero.mp this).resolve_left h2
    rw [ha0] at hab
    norm_num at hab
  have hJg' : ψ J ≠ ψ g := by
    intro h
    have h1 : ψ (J⁻¹ * g) = 1 := by rw [map_mul, map_inv, ← h, inv_mul_cancel]
    obtain ⟨r, hr⟩ := hnc _ h1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hJm, hgm] at hr
    have e1 := congrFun (congrFun hr 0) 1
    have e2 := congrFun (congrFun hr 1) 0
    have e3 := congrFun (congrFun hr 0) 0
    have e4 := congrFun (congrFun hr 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] at e1 e2 e3 e4
    have ha : a = 0 := by linear_combination e1
    have hr0 : r = 0 := by
      have : (2 : K) * r = 0 := by linear_combination -(e3 + e4)
      exact (mul_eq_zero.mp this).resolve_left h2
    have hb : b = 0 := by rw [e4, hr0]
    rw [ha, hb] at hab
    norm_num at hab
  obtain ⟨hE, hcard⟩ := elemTwo_pair hJg hJJ hgg hJ1 hg1 hJg'
  refine ⟨_, sup_le ?_ ?_, hE, hcard⟩
  · exact (zpowers_le).mpr ⟨J, rfl⟩
  · exact (zpowers_le).mpr ⟨g, rfl⟩

theorem elemTwo_of_centralizer [Finite G] {R E B : Subgroup G} (hRs : IsSimpleGroup R)
    (hRnab : ∃ x y : R, x * y ≠ y * x) (hER : E ≤ R) (hE : ElemTwo E) (hB : ElemTwo B)
    (hBR : ∀ b ∈ B, ∀ r ∈ R, b * r = r * b) :
    ElemTwo (E ⊔ B) ∧ Nat.card E * Nat.card B ≤ Nat.card ↥(E ⊔ B) := by
  have hZ : center R = ⊥ := CatLeaf.center_eq_bot_of_simple hRnab
  refine elemTwo_sup hE hB (fun a ha b hb => (hBR b hb a (hER ha)).symm) ?_
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxB⟩
  rw [mem_bot]
  have hxc : (⟨x, hER hxE⟩ : R) ∈ center R := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hBR x hxB y y.2).symm
  rw [hZ, mem_bot] at hxc
  exact congrArg Subtype.val hxc

end CFSG.ComponentClassification.HarrisLit.Hin
