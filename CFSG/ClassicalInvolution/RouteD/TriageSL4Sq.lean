module

public import CFSG.ClassicalInvolution.RouteD.TriageSL4Class
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.RouteD.GapsAut
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open scoped MatrixGroups Matrix
open CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction CFSG.ClassicalInvolution.Models

section Blocks

variable {F : Type} [Field F]

theorem slConjugation_blockEnt_sq (μ : Fˣ) (x : SL(3 + 1, F)) :
    slConjugation (3 + 1) F (diagGL (blockEnt μ)) (slConjugation (3 + 1) F (diagGL (blockEnt μ)) x)
      = slConjugation (3 + 1) F (diagGL (blockEnt (μ * μ))) x := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slConjugation_diagGL_apply, slConjugation_diagGL_apply, slConjugation_diagGL_apply]
  have hμ : (μ : F) ≠ 0 := μ.ne_zero
  fin_cases i <;> fin_cases j <;> simp [blockEnt] <;> field_simp

theorem blocks_sq_classification [Finite F] (h5 : 5 ≤ Nat.card F)
    (hcl : LinearAutClassification F (3 + 1)) {Y : Type} [Group Y] (θ : SL(3 + 1, F) →* Y)
    (hker : θ.ker ≤ Subgroup.center SL(3 + 1, F)) (σ : Y ≃* Y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix₀ : ∀ A : SL(2, F), σ (θ (blockSL2 F 3 0 A)) = θ (blockSL2 F 3 0 A))
    (hfix₂ : ∀ A : SL(2, F), σ (θ (blockSL2 F 3 2 A)) = θ (blockSL2 F 3 2 A)) [Finite Y] :
    ∃ ν : Fˣ, ∀ x, σ (σ (θ x)) = θ (slConjugation (3 + 1) F (diagGL (blockEnt ν)) x) := by
  rcases blocks_classification h5 hcl θ hker σ hstab hfix₀ hfix₂ with ⟨μ, hμ⟩ | ⟨-, hsq⟩
  · refine ⟨μ * μ, fun x => ?_⟩
    rw [hμ, hμ, slConjugation_blockEnt_sq]
  · refine ⟨1, fun x => ?_⟩
    rw [hsq, slConjugation_blockEnt_one]

end Blocks

section Pair

variable {F : Type} [Field F] {X : Type} [Group X]

theorem torusHom_neg_one : torusHom F (-1 : Fˣ) = -1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_torusHom]

theorem exists_sqrt_of_standardPair [Finite X] (h2 : (2 : F) ≠ 0) {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) {i : Fˣ} (hi : i * i = -1) {a b : X} (ha : a ∈ U)
    (hb : b ∈ V) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) :
    ∃ s ∈ V, s * s = b ∧ s * a = a * s ∧ conjSub s U = U := by
  obtain ⟨θ, -, hker, hU, hV⟩ := pair_normalize h
  have ha' : a ∈ (blockSL F 3 2 0 (by omega)).range.map θ := by
    rw [show (blockSL F 3 2 0 (by omega)).range = B12 F from rfl, hU]
    exact ha
  have hb' : b ∈ (blockSL F 3 2 1 (by omega)).range.map θ := by
    rw [show (blockSL F 3 2 1 (by omega)).range = B23 F from rfl, hV]
    exact hb
  have haθ := eq_block_neg_one h2 hker (by omega : 0 + 2 ≤ 3) ha' ha2
  have hbθ := eq_block_neg_one h2 hker (by omega : 1 + 2 ≤ 3) hb' hb2
  set s : X := θ (blockSL F 3 2 1 (by omega) (torusHom F i)) with hs
  have hsV : s ∈ V := by
    rw [← hV]
    exact ⟨_, ⟨torusHom F i, rfl⟩, rfl⟩
  have hneg : torusHom F (i * i) = -1 := by rw [hi, torusHom_neg_one]
  refine ⟨s, hsV, ?_, ?_, ?_⟩
  · rw [hs, ← map_mul, ← map_mul, ← map_mul, hneg, hbθ]
  · rw [hs, haθ, ← map_mul, ← map_mul]
    congr 1
    rw [← torusHom_neg_one (F := F)]
    exact (blockSL_torus_comm (-1 : Fˣ) i).symm
  · have key : ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
      intro u hu
      rw [← hU] at hu
      obtain ⟨m, hm, rfl⟩ := hu
      have hc : blockSL F 3 2 1 (by omega) (torusHom F i) ∈ D23 F := mem_D23_iff.mpr ⟨i, rfl⟩
      have := D23_conj_mem_B12 hc hm
      rw [← hU]
      exact ⟨_, this, by simp [hs, map_mul, map_inv]⟩
    have hle : conjSub s U ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      exact key u hu
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    unfold conjSub
    rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]

end Pair

section LocAut

variable {G : Type} [Group G]

theorem locAut_congr {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {w g g' : G} (h : g = g')
    (hg : g * w * g⁻¹ = w) (hg' : g' * w * g'⁻¹ = w) (a : locQuot Ω w) :
    locAut hΩ hg a = locAut hΩ hg' a := by
  subst h
  rfl

end LocAut

end CFSG.ClassicalInvolution.RouteD.Gaps
