module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Block
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.Chevalley (SL2 WSL coe_WSL)
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open scoped commutatorElement MatrixGroups

theorem fixedBlocks_of_hom {G Q : Type*} [Group G] [Group Q] (φ : G →* Q) {α : MulAut Q}
    {p r : ℕ} (a b : Fin r → G)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ ({a i, b i} : Set G), ∀ y ∈ ({a j, b j} : Set G), Commute x y)
    (ha : ∀ i, α (φ (a i)) = φ (a i)) (hb : ∀ i, α (φ (b i)) = φ (b i))
    (hp : ∀ i, ⁅a i, b i⁆ ^ p = 1) (hnc : ∀ i, ⁅⁅a i, b i⁆, b i⁆ ∉ φ.ker) :
    FixedBlocks p α r := by
  refine fixedBlocks_of_generators (fun i => φ (a i)) (fun i => φ (b i)) ?_ ha hb
    (fun i => by rw [← map_commutatorElement, ← map_pow, hp i, map_one]) fun i hc => hnc i ?_
  · rintro i j hij _ (rfl | rfl) _ (rfl | rfl) <;>
      exact (hcomm i j hij _ (by simp) _ (by simp)).map φ
  · rw [MonoidHom.mem_ker, map_commutatorElement, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 hc

variable {n : ℕ} {K : Type} [Field K]

theorem map_omegaSL {ω : K} (hω : ω ^ 3 = 1) {σ : K →+* K} (hσω : σ ω = ω) :
    Matrix.SpecialLinearGroup.map σ (omegaSL ω hω) = omegaSL ω hω := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_omegaSL]
  ext k l
  fin_cases k <;> fin_cases l <;> simp [hσω]

theorem fixedBlocks_fieldAut (hn : 8 ≤ n) {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (σ : K ≃+* K) (hσω : σ ω = ω) : FixedBlocks 3 (fieldAut n K σ) 4 := by
  have hW : Matrix.SpecialLinearGroup.map σ.toRingHom (WSL : SL2 K) = WSL := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_WSL]
    ext k l
    fin_cases k <;> fin_cases l <;> simp
  refine fixedBlocks_of_hom (proj n K)
    (fun i => blockSL K n 2 (2 * i) (two_mul_add_two_le hn i) (omegaSL ω hω))
    (fun i => blockSL K n 2 (2 * i) (two_mul_add_two_le hn i) WSL) ?_ (fun i => ?_)
    (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · rintro i j hij _ (rfl | rfl) _ (rfl | rfl) <;> exact blockSL_two_mul_commute hn hij _ _
  · simp only [fieldAut_proj, map_blockSL, map_omegaSL hω (σ := σ.toRingHom) hσω]
  · simp only [fieldAut_proj, map_blockSL, hW]
  · simp only [← map_commutatorElement, ← map_pow, comm_omegaSL_WSL_pow_three, map_one]
  · simp only [← map_commutatorElement, ker_proj]
    rintro ⟨c, -, hc⟩
    exact not_commute_comm_omegaSL_WSL ω hω hω1
      (commutatorElement_eq_one_iff_commute.1 (eq_one_of_blockSL_eq_scalar _ (by omega) hc))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
