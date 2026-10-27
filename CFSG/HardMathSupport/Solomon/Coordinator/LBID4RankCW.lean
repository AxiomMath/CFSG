module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankSplit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LBID4

open QuadraticMap Module MvPolynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem q_three (Q : QuadraticForm K V) (e : Fin 3 → V) (t : Fin 3 → K) :
    Q (t 0 • e 0 + t 1 • e 1 + t 2 • e 2) =
      Q (e 0) * t 0 * t 0 + Q (e 1) * t 1 * t 1 + Q (e 2) * t 2 * t 2 +
        polar Q (e 0) (e 1) * t 0 * t 1 + polar Q (e 0) (e 2) * t 0 * t 2 +
          polar Q (e 1) (e 2) * t 1 * t 2 := by
  simp only [q_add, q_smul, polar_add_left, polar_smul_left, polar_smul_right, smul_eq_mul]
  ring

theorem totalDegree_CXX_le (a : K) (i j : Fin 3) :
    (C a * X i * X j : MvPolynomial (Fin 3) K).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (C a * X i : MvPolynomial (Fin 3) K).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
  rw [totalDegree_X]
  omega

theorem totalDegree_add_le_two {f g : MvPolynomial (Fin 3) K} (hf : f.totalDegree ≤ 2)
    (hg : g.totalDegree ≤ 2) : (f + g).totalDegree ≤ 2 :=
  (totalDegree_add f g).trans (max_le hf hg)

theorem exists_isotropic_three [Finite K] (Q : QuadraticForm K V) (e : Fin 3 → V) :
    ∃ t : Fin 3 → K, t ≠ 0 ∧ Q (t 0 • e 0 + t 1 • e 1 + t 2 • e 2) = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let f : MvPolynomial (Fin 3) K :=
    C (Q (e 0)) * X 0 * X 0 + C (Q (e 1)) * X 1 * X 1 + C (Q (e 2)) * X 2 * X 2 +
      C (polar Q (e 0) (e 1)) * X 0 * X 1 + C (polar Q (e 0) (e 2)) * X 0 * X 2 +
        C (polar Q (e 1) (e 2)) * X 1 * X 2
  have heval : ∀ t, MvPolynomial.eval t f = Q (t 0 • e 0 + t 1 • e 1 + t 2 • e 2) := by
    intro t
    rw [q_three]
    simp [f]
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have h : f.totalDegree ≤ 2 := by
      simp only [f]
      repeat' apply totalDegree_add_le_two
      all_goals exact totalDegree_CXX_le _ _ _
    simp only [Fintype.card_fin]
    omega
  have hdvd := char_dvd_card_solutions (ringChar K) hdeg
  have h0 : MvPolynomial.eval 0 f = 0 := by rw [heval]; simp
  obtain ⟨n, hprime, -⟩ := FiniteField.card K (ringChar K)
  have hcard : 1 < Fintype.card {x : Fin 3 → K // MvPolynomial.eval x f = 0} := by
    have hpos : 0 < Fintype.card {x : Fin 3 → K // MvPolynomial.eval x f = 0} :=
      Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
    have := Nat.le_of_dvd hpos hdvd
    have := hprime.two_le
    omega
  obtain ⟨⟨t, ht⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨0, h0⟩
  refine ⟨t, fun h => hne (Subtype.ext h), ?_⟩
  rw [← heval]
  exact ht

theorem finrank_inf_ker_pol [FiniteDimensional K V] (M : Submodule K V) (v : V) :
    finrank K M ≤ finrank K ↥(M ⊓ LinearMap.ker (pol Q v)) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq M (LinearMap.ker (pol Q v))
  have h2 := LinearMap.finrank_range_add_finrank_ker (pol Q v)
  have h3 : finrank K (LinearMap.range (pol Q v)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (pol Q v))
    rwa [finrank_self] at this
  have h4 := Submodule.finrank_le (M ⊔ LinearMap.ker (pol Q v))
  omega

theorem exists_frame_of_nDeg [Finite K] [FiniteDimensional K V] {M : Submodule K V}
    (hM : NDeg Q M) (h4 : 4 ≤ finrank K M) : ∃ F : EFrame Q, F.b ∈ M ∧ F.b' ∈ M := by
  classical
  have hne : M ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h4
    omega
  obtain ⟨v, hvM, hQv⟩ := hM.exists_ne_zero hne
  have hL0 := finrank_inf_ker_pol (Q := Q) M v
  have hL : 3 ≤ finrank K ↥(M ⊓ LinearMap.ker (pol Q v)) := by omega
  have memL : ∀ x : V, x ∈ M ⊓ LinearMap.ker (pol Q v) ↔ x ∈ M ∧ polar Q x v = 0 := by
    intro x
    rw [Submodule.mem_inf, LinearMap.mem_ker, pol_apply]
  let bL := Module.finBasis K ↥(M ⊓ LinearMap.ker (pol Q v))
  let e : Fin 3 → V := fun i => (bL (Fin.castLE hL i) : V)
  have he : LinearIndependent K e :=
    (bL.linearIndependent.comp _ (Fin.castLE_injective hL)).map' _
      (Submodule.ker_subtype _)
  have heL : ∀ i, e i ∈ M ⊓ LinearMap.ker (pol Q v) := fun i => (bL (Fin.castLE hL i)).2
  obtain ⟨t, ht0, htQ⟩ := exists_isotropic_three Q e
  have huL : t 0 • e 0 + t 1 • e 1 + t 2 • e 2 ∈ M ⊓ LinearMap.ker (pol Q v) :=
    Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (heL 0))
      (Submodule.smul_mem _ _ (heL 1))) (Submodule.smul_mem _ _ (heL 2))
  obtain ⟨huM, huv⟩ := (memL _).mp huL
  generalize hu : t 0 • e 0 + t 1 • e 1 + t 2 • e 2 = u at huM huv htQ
  have hu0 : u ≠ 0 := by
    intro h
    apply ht0
    have := (Fintype.linearIndependent_iff.mp he) t (by
      rw [Fin.sum_univ_three, hu, h])
    funext i
    exact this i
  have hv0 : v ≠ 0 := by
    intro h
    exact hQv (by rw [h, QuadraticMap.map_zero])
  obtain ⟨y, hyM, hyv⟩ : ∃ y ∈ M, polar Q y v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (hM v hvM fun w hw => by rw [polar_comm]; exact h w hw)
  have hy₀M : (-Q v / polar Q y v) • y ∈ M := M.smul_mem _ hyM
  have hy₀v : polar Q ((-Q v / polar Q y v) • y) v = -Q v := by
    rw [polar_smul_left, smul_eq_mul]
    field_simp
  generalize (-Q v / polar Q y v) • y = y₀ at hy₀M hy₀v
  obtain ⟨l, hlM, hlv, hl⟩ : ∃ l, l ∈ M ∧ polar Q l v = 0 ∧ polar Q (y₀ + l) u ≠ 0 := by
    by_contra h
    push Not at h
    have hy₀u : polar Q y₀ u = 0 := by simpa using h 0 M.zero_mem (polar_zero_left Q v)
    apply hu0
    refine hM u huM fun m hm => ?_
    have hc : polar Q y₀ v ≠ 0 := by rw [hy₀v]; exact neg_ne_zero.mpr hQv
    have hmv : polar Q (m - (polar Q m v / polar Q y₀ v) • y₀) v = 0 := by
      rw [polar_sub_left, polar_smul_left, smul_eq_mul]
      field_simp
      ring
    have h1 : polar Q (m - (polar Q m v / polar Q y₀ v) • y₀) u = 0 := by
      have := h _ (M.sub_mem hm (M.smul_mem _ hy₀M)) hmv
      rw [polar_add_left, hy₀u, zero_add] at this
      exact this
    rw [polar_comm]
    have e : m = (m - (polar Q m v / polar Q y₀ v) • y₀) + (polar Q m v / polar Q y₀ v) • y₀ := by
      abel
    rw [e, polar_add_left, polar_smul_left, h1, hy₀u, smul_zero, add_zero]
  have hzM : y₀ + l ∈ M := M.add_mem hy₀M hlM
  have hzv : polar Q (y₀ + l) v = -Q v := by rw [polar_add_left, hy₀v, hlv, add_zero]
  generalize y₀ + l = z at hzM hzv hl
  have hwM : z + ((Q v - Q z) / polar Q z u) • u ∈ M := M.add_mem hzM (M.smul_mem _ huM)
  have hQw : Q (z + ((Q v - Q z) / polar Q z u) • u) = Q v := by
    rw [q_add, q_smul, htQ, polar_smul_right, smul_eq_mul]
    field_simp
    ring
  have hvw : polar Q v (z + ((Q v - Q z) / polar Q z u) • u) = -Q v := by
    rw [polar_comm, polar_add_left, polar_smul_left, huv, hzv]
    simp
  exact ⟨⟨v, _, Q v, hQv, rfl, hQw, hvw⟩, hvM, hwM⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LBID4
