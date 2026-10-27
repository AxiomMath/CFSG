module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismRealization

public section

namespace CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem exists_isometry_hypPSU_of_odd (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (β : MulAut (hypPSU h r ε)) :
    ∃ (σ : K ≃+* K) (B : GL (HypIndex r ε) K),
      ((B : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
          (B : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K ∧
        (∀ g : hypSU h r ε, ∃ hg : B * glAut σ (g : GL (HypIndex r ε) K) * B⁻¹ ∈ hypSU h r ε,
          β (hypProj h r ε g) = hypProj h r ε ⟨_, hg⟩) ∧
        ((∀ y, β (β y) = y) → σ = RingEquiv.refl K ∨ ∀ c, σ c = h.bar c) := by
  obtain ⟨-, hsurj, -, -⟩ := odd_unitary_automorphism_semilinear_representation h hp hr hε hn
  obtain ⟨x₀, rfl⟩ := hsurj β
  obtain ⟨x, hxΦ, -, hxU⟩ := exists_unitary_rep h hr hε hn x₀
  refine ⟨(x : SemiGL (HypIndex r ε) K).right, (x : SemiGL (HypIndex r ε) K).left, hxU,
    fun g => ⟨conj_mem_hypSU x.2 g, ?_⟩, fun hβ => ?_⟩
  · rw [← hxΦ]
    exact semilinearAutHom_apply h hr hε x g
  · have hsq : semilinearAutHom h hr hε (x * x) = 1 := by
      rw [map_mul, hxΦ]
      exact MulEquiv.ext fun y => by simpa using hβ y
    obtain ⟨hσσ, -⟩ := (semilinearAutHom_eq_one_iff h hr hε hn (x * x)).mp hsq
    exact ringEquiv_eq_refl_or_bar h hσσ

theorem exists_unitary_semilinear_psu (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (β : MulAut (unitaryPSU h (2 * r + ε))) :
    ∃ (σ : K ≃+* K) (A : GL (Fin (2 * r + ε)) K),
      ((A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).map h.bar)ᵀ *
          (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) = 1 ∧
        (∀ g : unitarySU p f K (2 * r + ε),
          ∃ hg : A * glAut σ (g : GL (Fin (2 * r + ε)) K) * A⁻¹ ∈ unitarySU p f K (2 * r + ε),
            β (unitaryProj h (2 * r + ε) g) = unitaryProj h (2 * r + ε) ⟨_, hg⟩) ∧
        ((∀ y, β (β y) = y) → σ = RingEquiv.refl K ∨ ∀ c, σ c = h.bar c) := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  set e := hypProjTransport h hR
  obtain ⟨σ, B, hB, hBg, hinv⟩ :=
    exists_isometry_hypPSU_of_odd h hp hr hε hn ((e.trans β).trans e.symm)
  refine ⟨σ, semiTransportGL hR B σ, semiTransportGL_unitary hR hB σ, fun g' => ?_,
    fun hβ => hinv fun y => ?_⟩
  · set g := (hypTransport h hR).symm g'
    have hg' : hypTransport h hR g = g' := MulEquiv.apply_symm_apply _ _
    obtain ⟨hg, hα⟩ := hBg g
    have hconj : transportGL hR (B * glAut σ (g : GL (HypIndex r ε) K) * B⁻¹) =
        semiTransportGL hR B σ * glAut σ (g' : GL (Fin (2 * r + ε)) K) *
          (semiTransportGL hR B σ)⁻¹ := by
      rw [transportGL_conj, ← hg']
      rfl
    have hmem := transportGL_mem hR ⟨_, hg⟩
    rw [hconj] at hmem
    refine ⟨hmem, ?_⟩
    have h1 : unitaryProj h (2 * r + ε) g' = e (hypProj h r ε g) := by
      rw [hypProjTransport_hypProj, hg']
    have h2 : e.symm (β (e (hypProj h r ε g))) = hypProj h r ε ⟨_, hg⟩ := hα
    rw [h1, ← e.apply_symm_apply (β (e (hypProj h r ε g))), h2, hypProjTransport_hypProj]
    congr 1
    exact Subtype.ext hconj
  · simpa using congrArg e.symm (hβ (e y))

end CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
