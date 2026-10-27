module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open QuadraticMap

theorem l2_om_joint {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) {x : Fin 4 → V ≃ₗ[K] V}
    (hxO : ∀ i, x i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx2 : ∀ i, x i * x i = 1)
    (hxc : ∀ i j, x i * x j = x j * x i) {ι : Type} (e : ι → V)
    (he : ∀ i j, ∃ s : K, x i (e j) = s • e j) {u : V} (hu : Q u ≠ 0)
    (hort : ∀ j, polar Q (e j) u = 0) :
    ∃ v : V, Q v ≠ 0 ∧ (∀ i, ∃ s : K, x i v = s • v) ∧ ∀ j, polar Q (e j) v = 0 := by
  classical
  have h2a : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have step : ∀ k : ℕ, k ≤ 4 →
      ∃ v : V, Q v ≠ 0 ∧ (∀ i : Fin 4, i.val < k → ∃ s : K, x i v = s • v) ∧
        ∀ j, polar Q (e j) v = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨u, hu, fun i hi => absurd hi (Nat.not_lt_zero i.val), hort⟩
    | succ k ih =>
      intro hk
      have hk4 : k < 4 := by omega
      obtain ⟨v, hv, hve, hortv⟩ := ih (by omega)
      let i0 : Fin 4 := ⟨k, hk4⟩
      have hyy' : ∀ w : V, x i0 (x i0 w) = w := by
        intro w
        have h := congrArg (fun f : V ≃ₗ[K] V => f w) (hx2 i0)
        simpa [LinearEquiv.mul_apply] using h
      set vp : V := (2 : K)⁻¹ • (v + x i0 v) with hvp
      set vm : V := (2 : K)⁻¹ • (v - x i0 v) with hvm
      have hyp : x i0 vp = vp := by
        rw [hvp]
        simp only [map_smul, map_add, hyy' v]
        rw [add_comm (x i0 v) v]
      have hym : x i0 vm = -vm := by
        rw [hvm]
        simp only [map_smul, map_sub, hyy' v]
        rw [← neg_sub, smul_neg]
      have hcomm : ∀ i : Fin 4, x i (x i0 v) = x i0 (x i v) := by
        intro i
        have h := congrArg (fun f : V ≃ₗ[K] V => f v) (hxc i i0)
        simpa [LinearEquiv.mul_apply] using h
      have hyve : ∀ j, polar Q (e j) (x i0 v) = 0 := by
        intro j
        obtain ⟨s, hs⟩ := he i0 j
        have h :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hxO i0) (x i0 (e j)) v
        rw [hyy' (e j), hs, polar_smul_left, hortv j, smul_zero] at h
        exact h
      have hvpe : ∀ j, polar Q (e j) vp = 0 := by
        intro j
        rw [hvp, polar_smul_right, polar_add_right, hortv j, hyve j, add_zero, smul_zero]
      have hvme : ∀ j, polar Q (e j) vm = 0 := by
        intro j
        rw [hvm, polar_smul_right, polar_sub_right, hortv j, hyve j, sub_zero, smul_zero]
      have hpvm : polar Q vp vm = 0 := by
        rw [hvp, hvm, polar_smul_left, polar_smul_right]
        rw [polar_add_left, polar_sub_right, polar_sub_right,
          polar_comm Q (x i0 v) v,
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hxO i0) v v,
          smul_eq_mul, smul_eq_mul]
        ring
      have hvsum : vp + vm = v := by
        rw [hvp, hvm, ← smul_add]
        have hmid : v + x i0 v + (v - x i0 v) = (2 : K) • v := by
          rw [two_smul]; abel
        rw [hmid, smul_smul, h2a, one_smul]
      have hQsum : Q v = Q vp + Q vm := by
        calc Q v = Q (vp + vm) := by rw [hvsum]
          _ = Q vp + Q vm + polar Q vp vm := QuadraticMap.map_add Q vp vm
          _ = Q vp + Q vm := by rw [hpvm, add_zero]
      by_cases hQp : Q vp = 0
      · have hQm : Q vm ≠ 0 := by
          intro h0
          exact hv (by rw [hQsum, hQp, h0, add_zero])
        refine ⟨vm, hQm, ?_, hvme⟩
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · obtain ⟨s, hs⟩ := hve i hlt
          refine ⟨s, ?_⟩
          rw [hvm]
          simp only [map_smul, map_sub, hs, hcomm i]
          rw [← smul_sub, smul_smul, smul_smul, mul_comm ((2 : K)⁻¹) s]
        · have hii : i = i0 := Fin.ext (by change i.val = k; exact heq)
          rw [hii]
          exact ⟨-1, by rw [hym, neg_one_smul]⟩
      · refine ⟨vp, hQp, ?_, hvpe⟩
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · obtain ⟨s, hs⟩ := hve i hlt
          refine ⟨s, ?_⟩
          rw [hvp]
          simp only [map_smul, map_add, hs, hcomm i]
          rw [← smul_add, smul_smul, smul_smul, mul_comm ((2 : K)⁻¹) s]
        · have hii : i = i0 := Fin.ext (by change i.val = k; exact heq)
          rw [hii]
          exact ⟨1, by rw [hyp, one_smul]⟩
  obtain ⟨v, hv, hve, hortv⟩ := step 4 le_rfl
  exact ⟨v, hv, fun i => hve i i.isLt, hortv⟩

end CFSG.OddStandard.HigherRank.YamadaG23
