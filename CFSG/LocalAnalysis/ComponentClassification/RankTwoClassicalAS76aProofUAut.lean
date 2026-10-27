module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismRealization

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
  CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem exists_isometry_hypPSU_of_admissible (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (hq : ¬(2 * r + ε = 3 ∧ p ^ f = 2))
    (β : MulAut (hypPSU h r ε)) :
    ∃ (σ : K ≃+* K) (B : GL (HypIndex r ε) K),
      ((B : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
          (B : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K ∧
        ∀ g : hypSU h r ε, ∃ hg : B * glAut σ (g : GL (HypIndex r ε) K) * B⁻¹ ∈ hypSU h r ε,
          β (hypProj h r ε g) = hypProj h r ε ⟨_, hg⟩ := by
  obtain ⟨x₀, rfl⟩ := semilinearAutHom_surjective_of_admissible h hr hε hn hq β
  obtain ⟨x, hxΦ, -, hxU⟩ := exists_unitary_rep h hr hε hn x₀
  refine ⟨(x : SemiGL (HypIndex r ε) K).right, (x : SemiGL (HypIndex r ε) K).left, hxU,
    fun g => ⟨conj_mem_hypSU x.2 g, ?_⟩⟩
  rw [← hxΦ]
  exact semilinearAutHom_apply h hr hε x g

theorem exists_unitary_semilinear_psu_of_admissible (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (hq : ¬(2 * r + ε = 3 ∧ p ^ f = 2))
    (β : MulAut (unitaryPSU h (2 * r + ε))) :
    ∃ (σ : K ≃+* K) (A : GL (Fin (2 * r + ε)) K),
      ((A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).map h.bar)ᵀ *
          (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) = 1 ∧
        ∀ g : unitarySU p f K (2 * r + ε),
          ∃ hg : A * glAut σ (g : GL (Fin (2 * r + ε)) K) * A⁻¹ ∈ unitarySU p f K (2 * r + ε),
            β (unitaryProj h (2 * r + ε) g) = unitaryProj h (2 * r + ε) ⟨_, hg⟩ := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  set e := hypProjTransport h hR
  obtain ⟨σ, B, hB, hBg⟩ :=
    exists_isometry_hypPSU_of_admissible h hr hε hn hq ((e.trans β).trans e.symm)
  refine ⟨σ, semiTransportGL hR B σ, semiTransportGL_unitary hR hB σ, fun g' => ?_⟩
  set g := (hypTransport h hR).symm g'
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

theorem exists_unitary_semilinear_statedProj (h : UnitaryFieldData p f K) {n : ℕ} (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) (β : MulAut (StatedProj (StatedSU n (p ^ f) K))) :
    ∃ (σ : K ≃+* K) (A : GL (Fin n) K),
      ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 ∧
        ∀ g : StatedSU n (p ^ f) K,
          ∃ hg : A * glAut σ (g : GL (Fin n) K) * A⁻¹ ∈ StatedSU n (p ^ f) K,
            β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩ := by
  obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  set E := unitaryPSUEquiv h (n := 2 * r + ε) (by omega)
  obtain ⟨σ, A, hA, hAg⟩ := exists_unitary_semilinear_psu_of_admissible h hr hε hn hq
    ((E.trans β).trans E.symm)
  refine ⟨σ, A, hA, fun g => ?_⟩
  obtain ⟨hg, hβ⟩ := hAg g
  refine ⟨hg, ?_⟩
  have h1 := congrArg E hβ
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
  rwa [unitaryPSUEquiv_unitaryProj, unitaryPSUEquiv_unitaryProj] at h1

end CFSG.ComponentClassification.RankTwoClassical
