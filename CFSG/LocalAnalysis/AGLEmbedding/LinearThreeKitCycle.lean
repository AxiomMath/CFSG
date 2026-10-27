module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab
import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.AGLEmbedding.LinearThreeKit

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped commutatorElement

variable {K : Type*} [Field K]

@[expose] def minorSum (M : Matrix (Fin 3) (Fin 3) K) : K :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0 + M 0 0 * M 2 2 - M 0 2 * M 2 0 + M 1 1 * M 2 2 - M 1 2 * M 2 1

theorem cayleyHamilton_fin_three (M : Matrix (Fin 3) (Fin 3) K) :
    M ^ 3 - M.trace • M ^ 2 + minorSum M • M - M.det • (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_fin_three,
      Matrix.trace_fin_three, minorSum] <;> ring

theorem det_smul_one_sub_fin_three (M : Matrix (Fin 3) (Fin 3) K) (l : K) :
    (l • (1 : Matrix (Fin 3) (Fin 3) K) - M).det =
      l ^ 3 - M.trace * l ^ 2 + minorSum M * l - M.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_three, Matrix.trace_fin_three]
  simp [minorSum]
  ring

theorem trace_eq_zero_of_pow_three {U : Matrix (Fin 3) (Fin 3) K} (h3 : U ^ 3 = 1)
    (hdet : U.det = 1) (hns : ∀ c : K, U ≠ c • 1) : U.trace = 0 ∧ minorSum U = 0 := by
  have hch := cayleyHamilton_fin_three U
  rw [h3, hdet, one_smul] at hch
  have hU : IsUnit U.det := by rw [hdet]; exact isUnit_one
  have h2 : minorSum U • (1 : Matrix (Fin 3) (Fin 3) K) - U.trace • U = 0 := by
    have h1 : U * (minorSum U • (1 : Matrix (Fin 3) (Fin 3) K) - U.trace • U) = 0 := by
      rw [← hch, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, ← sq]
      abel
    have := congrArg (U⁻¹ * ·) h1
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul,
      Matrix.mul_zero] using this
  have ht : U.trace = 0 := by
    by_contra ht
    apply hns (U.trace⁻¹ * minorSum U)
    calc U = U.trace⁻¹ • (U.trace • U) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = (U.trace⁻¹ * minorSum U) • 1 := by rw [← (sub_eq_zero.mp h2), smul_smul]
  refine ⟨ht, ?_⟩
  rw [ht, zero_smul, sub_zero] at h2
  simpa using congrFun (congrFun h2 0) 0

theorem exists_mulVec_eq_smul_of_pow_three {U : Matrix (Fin 3) (Fin 3) K} (h3 : U ^ 3 = 1)
    (hdet : U.det = 1) (hns : ∀ c : K, U ≠ c • 1) {l : K} (hl : l ^ 3 = 1) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ U *ᵥ v = l • v := by
  obtain ⟨ht, hc⟩ := trace_eq_zero_of_pow_three h3 hdet hns
  have hd : (l • (1 : Matrix (Fin 3) (Fin 3) K) - U).det = 0 := by
    rw [det_smul_one_sub_fin_three, ht, hc, hdet, hl]
    ring
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv.symm

theorem cubeRoots_injective {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    Function.Injective ![(1 : K), ω, ω ^ 2] := by
  have h2 : ω ^ 2 ≠ 1 := fun h => hω1 (by
    calc ω = ω * ω ^ 2 := by rw [h, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3)
  have h21 : ω ^ 2 ≠ ω := fun h => hω1 (by
    have : ω * (ω - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · rw [h0] at hω3; simp at hω3
    · exact sub_eq_zero.mp h0)
  have h1' : (1 : K) ≠ ω := Ne.symm hω1
  have h2' : (1 : K) ≠ ω ^ 2 := Ne.symm h2
  have h21' : ω ≠ ω ^ 2 := Ne.symm h21
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem exists_eigenbasis_of_pow_three {U : Matrix (Fin 3) (Fin 3) K} (h3 : U ^ 3 = 1)
    (hdet : U.det = 1) (hns : ∀ c : K, U ≠ c • 1) {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    ∃ b : Fin 3 → Fin 3 → K, LinearIndependent K b ∧ U *ᵥ b 0 = b 0 ∧ U *ᵥ b 1 = ω • b 1 ∧
      U *ᵥ b 2 = ω ^ 2 • b 2 := by
  obtain ⟨b₀, hb₀, h₀⟩ := exists_mulVec_eq_smul_of_pow_three h3 hdet hns (one_pow 3)
  obtain ⟨b₁, hb₁, h₁⟩ := exists_mulVec_eq_smul_of_pow_three h3 hdet hns hω3
  obtain ⟨b₂, hb₂, h₂⟩ := exists_mulVec_eq_smul_of_pow_three h3 hdet hns (l := ω ^ 2)
    (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow])
  refine ⟨![b₀, b₁, b₂], ?_, by simpa using h₀, h₁, h₂⟩
  refine Module.End.eigenvectors_linearIndependent' (mulVecLin U) ![(1 : K), ω, ω ^ 2]
    (cubeRoots_injective hω1 hω3) _ (forall_fin_three ?_ ?_ ?_)
  · exact Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr h₀, hb₀⟩
  · exact Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr h₁, hb₁⟩
  · exact Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr h₂, hb₂⟩

theorem exists_cycle {U : Matrix (Fin 3) (Fin 3) K} {ω : K} (hω3 : ω ^ 3 = 1)
    {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b) (h0 : U *ᵥ b 0 = b 0)
    (h1 : U *ᵥ b 1 = ω • b 1) (h2 : U *ᵥ b 2 = ω ^ 2 • b 2) :
    ∃ S : Matrix (Fin 3) (Fin 3) K, S.det = 1 ∧ S *ᵥ b 0 = b 1 ∧ S *ᵥ b 1 = b 2 ∧
      S *ᵥ b 2 = b 0 ∧ S * U = ω ^ 2 • (U * S) := by
  obtain ⟨S, hS⟩ := exists_mulVec_eq_sum hb !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  have hS0 : S *ᵥ b 0 = b 1 := by simpa [Fin.sum_univ_three] using hS 0
  have hS1 : S *ᵥ b 1 = b 2 := by simpa [Fin.sum_univ_three] using hS 1
  have hS2 : S *ᵥ b 2 = b 0 := by simpa [Fin.sum_univ_three] using hS 2
  refine ⟨S, ?_, hS0, hS1, hS2, eq_of_mulVec_eq hb (forall_fin_three ?_ ?_ ?_)⟩
  · rw [det_eq_of_mulVec_eq_sum hb hS, Matrix.det_fin_three]
    simp
  · rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h0, hS0, h1,
      smul_smul, show ω ^ 2 * ω = 1 by rw [← pow_succ, hω3], one_smul]
  · rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1,
      Matrix.mulVec_smul, hS1, h2, smul_smul, show ω ^ 2 * ω ^ 2 = ω by
        linear_combination ω * hω3]
  · rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2,
      Matrix.mulVec_smul, hS2, h0]

theorem eq_top_of_invariant {U S : Matrix (Fin 3) (Fin 3) K} {ω : K} (hω1 : ω ≠ 1)
    (hω3 : ω ^ 3 = 1) {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b)
    (h0 : U *ᵥ b 0 = b 0) (h1 : U *ᵥ b 1 = ω • b 1) (h2 : U *ᵥ b 2 = ω ^ 2 • b 2)
    (hS0 : S *ᵥ b 0 = b 1) (hS1 : S *ᵥ b 1 = b 2) (hS2 : S *ᵥ b 2 = b 0)
    {W : Submodule K (Fin 3 → K)} (hUW : ∀ v ∈ W, U *ᵥ v ∈ W) (hSW : ∀ v ∈ W, S *ᵥ v ∈ W)
    (hW : W ≠ ⊥) : W = ⊤ := by
  have hinj := cubeRoots_injective hω1 hω3
  have hne : ∀ i j : Fin 3, i ≠ j → ![(1 : K), ω, ω ^ 2] i - ![(1 : K), ω, ω ^ 2] j ≠ 0 :=
    fun i j hij => sub_ne_zero.mpr fun h => hij (hinj h)
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW
  obtain ⟨c, hc⟩ := exists_sum_smul_eq hb w
  simp only [Fin.sum_univ_three] at hc
  have hQ : ∀ a e : K, U *ᵥ (U *ᵥ w) - (a + e) • (U *ᵥ w) + (a * e) • w ∈ W := fun a e =>
    W.add_mem (W.sub_mem (hUW _ (hUW _ hwW)) (W.smul_mem _ (hUW _ hwW))) (W.smul_mem _ hwW)
  have hUw : U *ᵥ w = c 0 • b 0 + (c 1 * ω) • b 1 + (c 2 * ω ^ 2) • b 2 := by
    rw [← hc, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h0, h1, h2, smul_smul, smul_smul]
  have hUUw : U *ᵥ (U *ᵥ w) = c 0 • b 0 + (c 1 * ω * ω) • b 1 +
      (c 2 * ω ^ 2 * ω ^ 2) • b 2 := by
    rw [hUw, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h0, h1, h2, smul_smul, smul_smul]
  have hmem : ∀ (i : Fin 3) (k : K), k ≠ 0 → k • b i ∈ W → b i ∈ W := fun i k hk h => by
    have := W.smul_mem k⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hk, one_smul] at this
  have hQ0 : U *ᵥ (U *ᵥ w) - (ω + ω ^ 2) • (U *ᵥ w) + (ω * ω ^ 2) • w =
      (c 0 * ((1 - ω) * (1 - ω ^ 2))) • b 0 := by
    rw [hUUw, hUw, ← hc]
    module
  have hQ1 : U *ᵥ (U *ᵥ w) - (1 + ω ^ 2) • (U *ᵥ w) + (1 * ω ^ 2) • w =
      (c 1 * ((ω - 1) * (ω - ω ^ 2))) • b 1 := by
    rw [hUUw, hUw, ← hc]
    module
  have hQ2 : U *ᵥ (U *ᵥ w) - (1 + ω) • (U *ᵥ w) + (1 * ω) • w =
      (c 2 * ((ω ^ 2 - 1) * (ω ^ 2 - ω))) • b 2 := by
    rw [hUUw, hUw, ← hc]
    module
  have hall : b 0 ∈ W ∧ b 1 ∈ W ∧ b 2 ∈ W := by
    have h01 : b 0 ∈ W → b 1 ∈ W := fun h => hS0 ▸ hSW _ h
    have h12 : b 1 ∈ W → b 2 ∈ W := fun h => hS1 ▸ hSW _ h
    have h20 : b 2 ∈ W → b 0 ∈ W := fun h => hS2 ▸ hSW _ h
    by_cases hc0 : c 0 = 0
    · by_cases hc1 : c 1 = 0
      · have hc2 : c 2 ≠ 0 := fun hc2 => hw0 (by rw [← hc, hc0, hc1, hc2]; simp)
        have hb2 := hmem 2 _ (mul_ne_zero hc2 (mul_ne_zero (hne 2 0 (by decide))
          (hne 2 1 (by decide)))) (hQ2 ▸ hQ 1 ω)
        exact ⟨h20 hb2, h01 (h20 hb2), hb2⟩
      · have hb1 := hmem 1 _ (mul_ne_zero hc1 (mul_ne_zero (hne 1 0 (by decide))
          (hne 1 2 (by decide)))) (hQ1 ▸ hQ 1 (ω ^ 2))
        exact ⟨h20 (h12 hb1), hb1, h12 hb1⟩
    · have hb0 := hmem 0 _ (mul_ne_zero hc0 (mul_ne_zero (hne 0 1 (by decide))
        (hne 0 2 (by decide)))) (hQ0 ▸ hQ ω (ω ^ 2))
      exact ⟨hb0, h01 hb0, h12 (h01 hb0)⟩
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨d, hd⟩ := exists_sum_smul_eq hb v
  rw [← hd, Fin.sum_univ_three]
  exact W.add_mem (W.add_mem (W.smul_mem _ hall.1) (W.smul_mem _ hall.2.1))
    (W.smul_mem _ hall.2.2)

theorem ne_smul_one_of_notMem_scalars {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∉ scalars 3 K) (c : K) : (u : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
  intro h
  have hc3 : c ^ 3 = 1 := by
    have := u.prop
    rwa [h, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at this
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc3
  exact hu ⟨Units.mk0 c hc0, Units.ext (by simpa using hc3), by
    rw [h, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply, Units.val_mk0]⟩

theorem not_centralizer_le_projStabilizer {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {u : SpecialLinearGroup (Fin 3) K} (hu3 : u ^ 3 = 1) (hus : u ∉ scalars 3 K)
    {W : Submodule K (Fin 3 → K)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) (huW : u ∈ stabilizer W) :
    ¬ Subgroup.centralizer ({proj 3 K u} : Set (projectiveSL 3 K)) ≤ projStabilizer W := by
  intro hle
  obtain ⟨b, hb, h0, h1, h2⟩ := exists_eigenbasis_of_pow_three (coe_pow_eq_one hu3) u.prop
    (ne_smul_one_of_notMem_scalars hus) hω1 hω3
  obtain ⟨S, hSdet, hS0, hS1, hS2, hSU⟩ := exists_cycle hω3 hb h0 h1 h2
  have hz : (Units.mk0 (ω ^ 2) (pow_ne_zero 2 fun h => by simp [h] at hω3)) ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul, mul_comm, pow_mul, hω3,
      one_pow, Units.val_one])
  let σ : SpecialLinearGroup (Fin 3) K := ⟨S, hSdet⟩
  have hσu : σ * u = scalarElement _ hz * (u * σ) := Subtype.ext (by
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      coe_scalarElement, Units.val_mk0, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      Matrix.smul_mul, Matrix.one_mul]
    exact hSU)
  have hmem : proj 3 K σ ∈ Subgroup.centralizer ({proj 3 K u} : Set (projectiveSL 3 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [show proj 3 K σ * proj 3 K u = proj 3 K (σ * u) from (map_mul _ _ _).symm, hσu,
      map_mul, map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars _ hz), one_mul]
  have hσW : σ ∈ stabilizer W := by
    rw [← comap_projStabilizer]
    exact hle hmem
  exact hWt (eq_top_of_invariant hω1 hω3 hb h0 h1 h2 hS0 hS1 hS2
    (fun v hv => (mem_stabilizer.mp huW) ▸ ⟨v, hv, rfl⟩)
    (fun v hv => (mem_stabilizer.mp hσW) ▸ ⟨v, hv, rfl⟩) hW0)

theorem commutator_le_self' {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem exists_mem_commutator_of_mem {W : Submodule K (Fin 3 → K)} {x : projectiveSL 3 K}
    (hx : x ∈ ⁅projStabilizer W, projStabilizer W⁆) :
    ∃ u ∈ ⁅stabilizer W, stabilizer W⁆, proj 3 K u = x := by
  rw [projStabilizer, ← Subgroup.map_commutator] at hx
  exact hx

theorem pow_eq_one_of_lift {n m : ℕ} {u : SpecialLinearGroup (Fin n) K}
    (hum : proj n K u ^ m = 1) {M : Submodule K (Fin n → K)} {v : Fin n → K} (hv : v ∉ M)
    (hM : ((u ^ m : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ M) :
    u ^ m = 1 := by
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.mp (by rw [map_pow, hum] : proj n K (u ^ m) = 1)
  rw [hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
    Matrix.one_mulVec] at hM
  have hc1 : (c : K) = 1 := by
    by_contra h
    have h' : ((c : K) - 1) • v ∈ M := by rwa [sub_smul, one_smul]
    have := M.smul_mem ((c : K) - 1)⁻¹ h'
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr h), one_smul] at this
    exact hv this
  exact Subtype.ext (by rw [hc, hc1, map_one, SpecialLinearGroup.coe_one])

theorem exists_lift_of_mem_commutator_one {m : ℕ} {x : projectiveSL 3 K} (hxm : x ^ m = 1)
    (hx : x ∈ ⁅projStabilizer (flagSpace 3 K 1), projStabilizer (flagSpace 3 K 1)⁆) :
    ∃ u ∈ ⁅stabilizer (flagSpace 3 K 1), stabilizer (flagSpace 3 K 1)⁆, proj 3 K u = x ∧
      u ^ m = 1 ∧ (u : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  obtain ⟨u, hu, rfl⟩ := exists_mem_commutator_of_mem hx
  have he := mulVec_single_zero_of_mem_commutator hu
  refine ⟨u, hu, rfl, pow_eq_one_of_lift hxm (M := ⊥) (v := Pi.single 0 1) (by simp) ?_, he⟩
  rw [SpecialLinearGroup.coe_pow, pow_mulVec_of_mulVec_eq_smul (a := 1)
    (by rw [one_smul]; exact he), one_pow, one_smul, sub_self]
  exact Submodule.zero_mem _

theorem exists_lift_of_mem_commutator_two {m : ℕ} {x : projectiveSL 3 K} (hxm : x ^ m = 1)
    (hx : x ∈ ⁅projStabilizer (flagSpace 3 K 2), projStabilizer (flagSpace 3 K 2)⁆) :
    ∃ u ∈ ⁅stabilizer (flagSpace 3 K 2), stabilizer (flagSpace 3 K 2)⁆, proj 3 K u = x ∧
      u ^ m = 1 ∧ ∀ v : Fin 3 → K, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ flagSpace 3 K 2 := by
  obtain ⟨u, hu, rfl⟩ := exists_mem_commutator_of_mem hx
  have hq := mulVec_sub_mem_of_mem_commutator hu
  refine ⟨u, hu, rfl, pow_eq_one_of_lift hxm (M := flagSpace 3 K 2) (v := Pi.single 2 1)
    (fun h => by simpa using mem_flagSpace_two_iff.mp h) ?_, hq⟩
  rw [SpecialLinearGroup.coe_pow]
  exact pow_mulVec_sub_mem hq _ m

theorem not_centralizer_le_projStabilizer_one {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {x : projectiveSL 3 K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hx : x ∈ ⁅projStabilizer (flagSpace 3 K 1), projStabilizer (flagSpace 3 K 1)⁆) :
    ¬ Subgroup.centralizer ({x} : Set (projectiveSL 3 K)) ≤ projStabilizer (flagSpace 3 K 1) := by
  obtain ⟨u, hu, rfl, hu3, -⟩ := exists_lift_of_mem_commutator_one hx3 hx
  refine not_centralizer_le_projStabilizer hω1 hω3 hu3 (fun h => hx1 (proj_eq_one_iff.mpr h)) ?_
    ?_ (commutator_le_self' _ hu)
  · rw [Submodule.ne_bot_iff]
    exact ⟨_, single_zero_mem_flagSpace_one, Pi.single_ne_zero_iff.mpr one_ne_zero⟩
  · intro htop
    have := mem_flagSpace.mp (htop ▸ Submodule.mem_top : Pi.single 2 (1 : K) ∈ flagSpace 3 K 1)
      2 (by simp)
    simp at this

theorem not_centralizer_le_projStabilizer_two {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {x : projectiveSL 3 K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hx : x ∈ ⁅projStabilizer (flagSpace 3 K 2), projStabilizer (flagSpace 3 K 2)⁆) :
    ¬ Subgroup.centralizer ({x} : Set (projectiveSL 3 K)) ≤ projStabilizer (flagSpace 3 K 2) := by
  obtain ⟨u, hu, rfl, hu3, -⟩ := exists_lift_of_mem_commutator_two hx3 hx
  refine not_centralizer_le_projStabilizer hω1 hω3 hu3 (fun h => hx1 (proj_eq_one_iff.mpr h)) ?_
    ?_ (commutator_le_self' _ hu)
  · rw [Submodule.ne_bot_iff]
    exact ⟨Pi.single 0 1, mem_flagSpace_two_iff.mpr (by simp),
      Pi.single_ne_zero_iff.mpr one_ne_zero⟩
  · intro htop
    have := mem_flagSpace_two_iff.mp (htop ▸ Submodule.mem_top : Pi.single 2 (1 : K) ∈
      flagSpace 3 K 2)
    simp at this

theorem not_centralizer_le_projStabilizer_one_of_perfect {ω : K} (hω1 : ω ≠ 1)
    (hω3 : ω ^ 3 = 1) {V : Subgroup (projectiveSL 3 K)}
    (hV : V ≤ projStabilizer (flagSpace 3 K 1)) (hVp : ⁅V, V⁆ = V) {x : projectiveSL 3 K}
    (hxV : x ∈ V) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ¬ Subgroup.centralizer ({x} : Set (projectiveSL 3 K)) ≤ projStabilizer (flagSpace 3 K 1) :=
  not_centralizer_le_projStabilizer_one hω1 hω3 hx3 hx1
    (Subgroup.commutator_mono hV hV (hVp.symm ▸ hxV))

theorem not_centralizer_le_projStabilizer_two_of_perfect {ω : K} (hω1 : ω ≠ 1)
    (hω3 : ω ^ 3 = 1) {V : Subgroup (projectiveSL 3 K)}
    (hV : V ≤ projStabilizer (flagSpace 3 K 2)) (hVp : ⁅V, V⁆ = V) {x : projectiveSL 3 K}
    (hxV : x ∈ V) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ¬ Subgroup.centralizer ({x} : Set (projectiveSL 3 K)) ≤ projStabilizer (flagSpace 3 K 2) :=
  not_centralizer_le_projStabilizer_two hω1 hω3 hx3 hx1
    (Subgroup.commutator_mono hV hV (hVp.symm ▸ hxV))

end CFSG.AGLEmbedding.LinearThreeKit
