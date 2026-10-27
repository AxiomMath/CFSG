module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2UniConj
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrTorus

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Decomp

theorem mem_iff_of_aut_mem {Y : Type*} [Group Y] [Finite Y] {S : Subgroup Y} {φ : MulAut Y}
    (hφ : ∀ w ∈ S, φ w ∈ S) (w : Y) : w ∈ S ↔ φ w ∈ S := by
  refine ⟨hφ w, fun hw => ?_⟩
  have hle : S.map φ.toMonoidHom ≤ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact hφ z hz
  have heq : S.map φ.toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective φ.injective])
  rw [← heq] at hw
  obtain ⟨z, hz, hzw⟩ := hw
  have : z = w := φ.injective hzw
  rwa [← this]

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ} {h : UnitaryFieldData p f K}

theorem exists_aut_decomp_diagonal (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε)
    (hq : ¬(2 * r + ε = 3 ∧ p ^ f = 2)) (α : MulAut (hypPSU h r ε)) :
    ∃ (s : hypSU h r ε) (y : semilinearSimilitudes h r ε) (d : HypIndex r ε → Kˣ),
      (y : SemiGL (HypIndex r ε) K).left = diagGL d ∧
        α = MulAut.conj (hypProj h r ε s) * semilinearAutHom h hr hε y := by
  obtain ⟨x₀, rfl⟩ := semilinearAutHom_surjective_of_admissible h hr hε hn hq α
  obtain ⟨x, hxΦ, -, hxU⟩ := exists_unitary_rep h hr hε hn x₀
  rw [← hxΦ]
  obtain ⟨⟨A, σ⟩, hx⟩ := x
  change A ∈ hypUnitary h r ε at hxU
  obtain ⟨d, hdU, hdet⟩ := exists_diagGL_mem_hypUnitary hr hxU
  have hs : A * (diagGL d)⁻¹ ∈ hypSU h r ε := by
    refine mem_hypSU.mpr ⟨mem_hypUnitary.mp (mul_mem hxU (inv_mem hdU)), ?_⟩
    have h1 : ((diagGL d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).det *
        (((diagGL d)⁻¹ : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [Units.val_mul, Matrix.det_mul, ← hdet]
    exact h1
  refine ⟨⟨A * (diagGL d)⁻¹, hs⟩, isometrySim (diagGL d) hdU σ, d, rfl, ?_⟩
  have e : (⟨⟨A, σ⟩, hx⟩ : semilinearSimilitudes h r ε) =
      ⟨SemidirectProduct.inl (A * (diagGL d)⁻¹),
        inl_mem_semilinearSimilitudes (⟨A * (diagGL d)⁻¹, hs⟩ : hypSU h r ε)⟩ *
        isometrySim (diagGL d) hdU σ := by
    refine Subtype.ext (SemidirectProduct.ext ?_ ?_)
    · simp [isometrySim]
    · simp [isometrySim]
  rw [e, map_mul]
  exact congrArg (· * _) (semilinearAutHom_inl hr hε ⟨A * (diagGL d)⁻¹, hs⟩)

end Decomp

section Hyperbolic

variable {f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem autScalarTorus_hypPSU (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (hq : ¬(2 * r + ε = 3 ∧ 2 ^ f = 2)) :
    AutScalarTorus (hypPSU h r ε) := by
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  obtain ⟨-, -, -, -, ⟨S₁, hS₁⟩, -⟩ := unitary_order_and_Sylow h hr hε
  have hN : Subgroup.normalizer ((S₁ : Subgroup (hypPSU h r ε)) : Set (hypPSU h r ε)) =
      hypProjBorel h r ε := by
    rw [hS₁]
    exact normalizer_hypProjUnitriangular h hr hε
  refine AutScalarTorus.of_decomp S₁ ?_ ?_
  · intro b hb c hc
    rw [hN] at hb hc
    rw [hS₁]
    exact commutator_mem_hypProjUnitriangular hε hb hc
  · intro α _
    obtain ⟨s, y, d, hy, hα⟩ := exists_aut_decomp_diagonal hr hε hn hq α
    obtain ⟨j, hj⟩ := exists_pow_two_of_ringEquiv (y : SemiGL (HypIndex r ε) K).right
    refine ⟨hypProj h r ε s, semilinearAutHom h hr hε y, 2 ^ j, hα, fun w => ?_, fun b hb => ?_⟩
    · rw [hS₁]
      exact mem_iff_of_aut_mem (fun w hw => aut_mem_hypProjUnitriangular hr hε hy hw) w
    · rw [hN] at hb
      rw [hS₁]
      exact aut_power_map hr hε hy hj hb

end Hyperbolic

section Model

open CFSG.Assembly.LowTwoRank

theorem autScalarTorus_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) : AutScalarTorus Y := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 2 f K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε : ℕ, ε ≤ 1 ∧ n = 2 * r + ε := by
    obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n
    · exact ⟨r, 0, by omega, by omega⟩
    · exact ⟨r, 1, le_rfl, by omega⟩
  have hq : ¬(2 * r + ε = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) hU
  exact AutScalarTorus.of_mulEquiv ((hypPSUEquivStatedProj hU hR (by omega)).trans e.symm)
    (autScalarTorus_hypPSU hU (by omega) hε hn3 hq)

end Model

end CFSG.AGLEmbedding.ParabAutIrr
