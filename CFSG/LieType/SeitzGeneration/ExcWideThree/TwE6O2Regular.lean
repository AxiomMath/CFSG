module

public import Certificates.Certificate214104

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem e6O2Regular_holds : E6O2Regular :=
  Certificates.certificate214104

theorem e6O2_fix_shift_of_congr {q : ℕ} (hq : q % 3 = 2) (w : WeylGroup Tag.E6)
    (k m : Fin Tag.E6.rank → ℤ) (hm : ∀ j, ∑ l, Tag.E6.cartan l j * m l = 3 * k j)
    (h9 : ∀ l, (9 : ℤ) ∣ (q : ℤ) * (w • m) l + m l) :
    w ∈ charStabilizer (triChar (fun i => (k i : ZMod 3))) ∧
      triPairing (fun i => (k i : ZMod 3)) (e6Shift w) =
        -(((q + 1) / 3 : ℕ) : ZMod 3) * triPairing (fun i => (k i : ZMod 3)) e6Omega3 := by
  have hsym : Tag.E6.symmetrizedCartan = Tag.E6.cartan := symmetrizedCartan_eq_of_E (Or.inl rfl)
  have hif : ∀ x y : Fin Tag.E6.rank → ℤ,
      iform x y = ∑ j, y j * ∑ l, Tag.E6.cartan l j * x l := by
    intro x y
    simp only [iform, hsym]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmK : ∀ γ : Fin Tag.E6.rank → ℤ, iform m γ = 3 * ∑ j, k j * γ j := by
    intro γ
    rw [hif, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hm j]; ring
  obtain ⟨u, hu⟩ : ∃ u : Fin Tag.E6.rank → ℤ, (q : ℤ) • (w • m) + m = (9 : ℤ) • u :=
    ⟨fun l => ((q : ℤ) * (w • m) l + m l) / 9, funext fun l => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (Int.mul_ediv_cancel' (h9 l)).symm⟩
  have hwinv : w⁻¹ • m = (9 : ℤ) • (w⁻¹ • u) - (q : ℤ) • m := by
    have h1 : w⁻¹ • ((q : ℤ) • (w • m) + m) = w⁻¹ • ((9 : ℤ) • u) := by rw [hu]
    rw [smul_add, smul_comm w⁻¹ (q : ℤ) (w • m), inv_smul_smul, smul_comm w⁻¹ (9 : ℤ) u] at h1
    exact eq_sub_of_add_eq' h1
  set z : Fin Tag.E6.rank → ℤ := w⁻¹ • u with hz
  have hinv : ∀ γ : Fin Tag.E6.rank → ℤ, iform m (w • γ) = iform (w⁻¹ • m) γ := by
    intro γ
    have := iform_smul w⁻¹ m (w • γ)
    rw [inv_smul_smul] at this
    exact this.symm
  have hform : ∀ γ : Fin Tag.E6.rank → ℤ,
      iform m (w • γ) = 9 * iform z γ - (q : ℤ) * iform m γ := by
    intro γ
    rw [hinv, hwinv, iform_sub_left, iform_smul_left, iform_smul_left]
  have tp : ∀ v : Fin Tag.E6.rank → ℤ,
      triPairing (fun i => (k i : ZMod 3)) v = ((∑ j, k j * v j : ℤ) : ZMod 3) := by
    intro v
    simp [triPairing, Int.cast_sum, Int.cast_mul]
  have h3 : (3 : ZMod 3) = 0 := by decide
  have hq3 : (q : ZMod 3) = 2 := by
    have h1 : (q : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod q 3).symm
    rw [h1, hq]
    rfl
  have hfix : ∀ γ : Fin Tag.E6.rank → ℤ,
      ∑ j, k j * (w • γ) j = 3 * iform z γ - (q : ℤ) * ∑ j, k j * γ j := by
    intro γ
    have h1 := hform γ
    rw [hmK, hmK] at h1
    have h2 : (3 : ℤ) * ∑ j, k j * (w • γ) j =
        3 * (3 * iform z γ - (q : ℤ) * ∑ j, k j * γ j) := by
      linear_combination h1
    exact mul_left_cancel₀ (by norm_num) h2
  refine ⟨fun γ => ?_, ?_⟩
  · rw [triChar_apply, triChar_apply, tp, tp, hfix γ]
    refine congrArg Z3.ofAdd ?_
    push_cast
    rw [hq3]
    linear_combination
      (((iform z γ : ℤ) : ZMod 3) - ∑ j, (k j : ZMod 3) * (γ j : ZMod 3)) * h3
  · obtain ⟨s, hsq⟩ : ∃ s : ℕ, (q + 1) / 3 = s := ⟨_, rfl⟩
    rw [hsq]
    have hs : (3 : ℤ) • e6Shift w = w • e6Omega3 - e6Omega3 := three_smul_e6Shift w
    have hsymm : ∀ j, ∑ l, Tag.E6.cartan l j * e6Omega3 l = ∑ l, Tag.E6.cartan j l * e6Omega3 l :=
      fun j => Finset.sum_congr rfl fun l _ => by rw [cartan_symm_of_E (Or.inl rfl) l j]
    have hz3 : (3 : ℤ) ∣ iform z e6Omega3 := by
      rw [iform_comm, hif]
      exact Finset.dvd_sum fun j _ =>
        Dvd.dvd.mul_left (by rw [hsymm j]; exact three_dvd_cartan_e6Omega3 j) _
    have h1 : iform m ((3 : ℤ) • e6Shift w) = iform m (w • e6Omega3) - iform m e6Omega3 := by
      rw [hs, iform_sub_right]
    rw [hmK ((3 : ℤ) • e6Shift w), hform e6Omega3, hmK e6Omega3] at h1
    have hK3 : ∑ j, k j * ((3 : ℤ) • e6Shift w) j = 3 * ∑ j, k j * e6Shift w j := by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hK3] at h1
    have hq' : q + 1 = 3 * s := by omega
    have hq'Z : (q : ℤ) + 1 = 3 * (s : ℤ) := by exact_mod_cast hq'
    have h2 : (9 : ℤ) * ∑ j, k j * e6Shift w j =
        9 * (iform z e6Omega3 - (s : ℤ) * ∑ j, k j * e6Omega3 j) := by
      linear_combination h1 + (-3 * ∑ j, k j * e6Omega3 j) * hq'Z
    have h3' := mul_left_cancel₀ (show (9 : ℤ) ≠ 0 by norm_num) h2
    have hX : ((iform z e6Omega3 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast hz3)
    rw [tp, tp, h3', Int.cast_sub, Int.cast_mul, Int.cast_natCast, hX]
    exact (zero_sub _).trans (neg_mul _ _).symm

end CFSG.LieType.SeitzGeneration.ExcWideThree
