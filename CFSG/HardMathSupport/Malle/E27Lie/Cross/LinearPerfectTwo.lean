module

public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace CFSG.HardMathSupport.Malle.E27Lie

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_perfect_three_dvd_centralizer_PSL_two (hK : Nat.card K = 2) (hn : 5 ≤ n)
    {z : projectiveSL n K} (hz : z ^ 3 = 1) :
    ∃ Q : Subgroup (projectiveSL n K), Q ≤ Subgroup.centralizer ({z} : Set (projectiveSL n K)) ∧
      ⁅Q, Q⁆ = Q ∧ 3 ∣ Nat.card Q := by
  have hU : ∀ u : Kˣ, u = 1 := by
    intro u
    have : Nat.card Kˣ = 1 := by
      rw [Nat.card_units, hK]
    exact (Nat.card_eq_one_iff_unique.1 this).1.elim u 1
  obtain ⟨g, rfl⟩ := proj_surjective n K z
  have hg : g ^ 3 ∈ scalars n K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_pow]; exact hz
  obtain ⟨c, -, hc⟩ := hg
  have hc1 : c = 1 := hU c
  subst hc1
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hc
  have ha : (SpecialLinearGroup.toGL g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  obtain ⟨P, hPc, hPp, hP3⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.exists_perfect_three_dvd_centralizer_gl_two hK hn
      (SpecialLinearGroup.toGL g) ha
  let ψ : SpecialLinearGroup (Fin n) K →* GL (Fin n) K := SpecialLinearGroup.toGL
  have hψi : Function.Injective ψ := SpecialLinearGroup.toGL_injective
  have hψs : Function.Surjective ψ := by
    intro a
    have hd : (a : Matrix (Fin n) (Fin n) K).det = 1 := by
      have := hU (Matrix.GeneralLinearGroup.det a)
      simpa using congrArg Units.val this
    exact ⟨⟨a, hd⟩, Units.ext rfl⟩
  have hφi : Function.Injective (proj n K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, eq_bot_iff]
    rintro A ⟨c, -, hA⟩
    have hc1 : c = 1 := hU c
    subst hc1
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    simpa using hA
  have hPr : (P.comap ψ).map ψ = P := Subgroup.map_comap_eq_self_of_surjective hψs P
  have hcomm : ⁅P.comap ψ, P.comap ψ⁆ = P.comap ψ := by
    apply Subgroup.map_injective hψi
    rw [Subgroup.map_commutator, hPr, hPp]
  refine ⟨(P.comap ψ).map (proj n K), ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hPc hx)
    have h2 : x * g = g * x := hψi (by simpa [ψ] using h1)
    rw [← map_mul, ← map_mul, h2]
  · rw [← Subgroup.map_commutator, hcomm]
  · rw [Subgroup.card_map_of_injective hφi]
    rw [← hPr, Subgroup.card_map_of_injective hψi] at hP3
    exact hP3

end CFSG.HardMathSupport.Malle.E27Lie
