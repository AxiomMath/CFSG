module

public import CFSG.LocalAnalysis.EvenBN.U5.LinModelDefs
public import CFSG.LocalAnalysis.EvenBN.U5.ModelThreeTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover

namespace LinCase

variable (K : Type) [Field K]

@[expose] noncomputable def l3tor_tau : Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun l := ⟨diagonal ![(l : K), ((l⁻¹ : Kˣ) : K), 1], by
    simp [det_diagonal, Fin.prod_univ_three]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' l l' := by
    apply Subtype.ext
    show diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    fin_cases j <;> simp [mul_comm]

theorem l3tor_coe_tau (l : Kˣ) :
    (l3tor_tau K l : Matrix (Fin 3) (Fin 3) K) = diagonal ![(l : K), ((l⁻¹ : Kˣ) : K), 1] :=
  rfl

theorem l3tor_mul_unipU (l : Kˣ) (a b c : K) :
    l3tor_tau K l * unipU K a b c =
      unipU K ((l : K) ^ 2 * a) (((l⁻¹ : Kˣ) : K) * b) ((l : K) * c) * l3tor_tau K l := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, l3tor_coe_tau,
    diagonal_mul, mul_diagonal, coe_unipU, coe_unipU]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem l3tor_conj_unipU (l : Kˣ) (a b c : K) :
    l3tor_tau K l * unipU K a b c * (l3tor_tau K l)⁻¹ =
      unipU K ((l : K) ^ 2 * a) (((l⁻¹ : Kˣ) : K) * b) ((l : K) * c) := by
  rw [l3tor_mul_unipU, mul_assoc, mul_inv_cancel, mul_one]

theorem l3tor_conj_mem (l : Kˣ) {x : projectiveSL 3 K} (hx : x ∈ projUnip K) :
    proj 3 K (l3tor_tau K l) * x * (proj 3 K (l3tor_tau K l))⁻¹ ∈ projUnip K := by
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hx
  rw [← map_inv, ← map_mul, ← map_mul, l3tor_conj_unipU]
  exact mem_projUnip.2 ⟨_, _, _, rfl⟩

theorem l3tor_mem_normalizer_projUnip (l : Kˣ) :
    proj 3 K (l3tor_tau K l) ∈
      normalizer ((projUnip K : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) := by
  refine FieldFourCover.mem_normalizer_of_conj_mem (fun x hx => l3tor_conj_mem K l hx)
    (fun x hx => ?_)
  simpa only [map_inv, inv_inv] using l3tor_conj_mem K l⁻¹ hx

theorem l3tor_conj_center (l : Kˣ) (c : K) :
    proj 3 K (l3tor_tau K l) * proj 3 K (unipU K 0 0 c) * (proj 3 K (l3tor_tau K l))⁻¹ =
      proj 3 K (unipU K 0 0 ((l : K) * c)) := by
  rw [← map_inv, ← map_mul, ← map_mul, l3tor_conj_unipU]
  simp only [mul_zero]

variable {G : Type} [Group G] {A V : Subgroup G}

theorem l3tor_center_mem [Finite K] [CharP K 2] (F : LinearThree.Frame A V K) {x : G}
    (hx : x ∈ V ⊓ centralizer (V : Set G)) :
    ∃ c : K, F.φ (proj 3 K (unipU K 0 0 c)) = x := by
  have h : x ∈ (projRad K 0).map F.φ ⊓ (projRad K 1).map F.φ := by
    rw [F.radicals.inf_eq]
    exact hx
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 h).1
  obtain ⟨p', hp', hpx'⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 h).2
  have hpp : p = p' := F.injective (hpx.trans hpx'.symm)
  have hpc : p ∈ projCenterW K := by
    rw [← projRad_inf_eq]
    exact Subgroup.mem_inf.2 ⟨hp, by rw [hpp]; exact hp'⟩
  obtain ⟨c, hc⟩ := mem_projCenterW.1 hpc
  exact ⟨c, by rw [hc]; exact hpx⟩

theorem l3tor_ne_zero (F : LinearThree.Frame A V K) {c : K}
    (hx : F.φ (proj 3 K (unipU K 0 0 c)) ≠ 1) : c ≠ 0 := by
  rintro rfl
  exact hx (by rw [unipU_zero, map_one, map_one])

theorem l3Torus : L3TorusStatement := by
  intro f hf G _ _ A hA V hV
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_three_sq hf hA
  obtain ⟨F⟩ := LinearThree.exists_frame e hV
  have hodd : Odd (Nat.card Kˣ) := by
    have hK1 : 1 ≤ Nat.card K := Nat.card_pos
    have hev : Even (Nat.card K) := by
      rw [hK]
      exact Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, two_ne_zero⟩
    rw [Nat.card_units]
    exact Nat.Even.sub_odd hK1 hev odd_one
  refine ⟨(F.φ.comp ((proj 3 K).comp (l3tor_tau K))).range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨l, rfl⟩
    exact F.mem_A _
  · rintro _ ⟨l, rfl⟩
    have h := LinearThree.mem_normalizer_map_iff F.injective (proj 3 K (l3tor_tau K l)) (projUnip K)
    rw [F.map_projUnip] at h
    exact h.2 (l3tor_mem_normalizer_projUnip K l)
  · exact Odd.of_dvd_nat hodd (Subgroup.card_range_dvd _)
  · intro x hx hx1 y hy hy1
    obtain ⟨c, rfl⟩ := l3tor_center_mem K F hx
    obtain ⟨c', rfl⟩ := l3tor_center_mem K F hy
    have hc : c ≠ 0 := l3tor_ne_zero K F hx1
    have hc' : c' ≠ 0 := l3tor_ne_zero K F hy1
    obtain ⟨l, hl⟩ : ∃ l : Kˣ, (l : K) = c' * c⁻¹ :=
      ⟨Units.mk0 _ (mul_ne_zero hc' (inv_ne_zero hc)), Units.val_mk0 _⟩
    have hlc : (l : K) * c = c' := by
      rw [hl, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    refine ⟨F.φ (proj 3 K (l3tor_tau K l)), MonoidHom.mem_range.2 ⟨l, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, l3tor_conj_center, hlc]

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
