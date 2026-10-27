module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.SwapFrame
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.SwapGood

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open QuadraticMap Module Matrix

section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [CharP K 2] [Finite K]
  [FiniteDimensional K V] {σ : K ≃+* K} {Q : QuadraticForm K V} {T : V →ₛₗ[(σ : K →+* K)] V}
  {r : ℕ}

theorem T_mem_framePerp_swap (hTQ : ∀ v, Q (T v) = σ (Q v)) (F : HFrame Q r)
    (hs : ∀ i, T (F.e i) = F.f i ∧ T (F.f i) = F.e i) {v : V} (hv : v ∈ framePerp F) :
    T v ∈ framePerp F := by
  rw [mem_framePerp] at hv ⊢
  intro p
  have h1 := hv (Sum.swap p)
  rcases p with i | i
  · have hg : T (F.f i) = F.e i := (hs i).2
    calc polar Q (T v) (Sum.elim F.e F.f (Sum.inl i)) = polar Q (T v) (T (F.f i)) := by
          simp [hg]
      _ = σ (polar Q v (F.f i)) := polar_semilinear T hTQ _ _
      _ = 0 := by simpa using congrArg σ h1
  · have hg : T (F.e i) = F.f i := (hs i).1
    calc polar Q (T v) (Sum.elim F.e F.f (Sum.inr i)) = polar Q (T v) (T (F.e i)) := by
          simp [hg]
      _ = σ (polar Q v (F.e i)) := polar_semilinear T hTQ _ _
      _ = 0 := by simpa using congrArg σ h1

theorem framePerp_nd (hQ : (polarBilin Q).Nondegenerate) (F : HFrame Q r) {w : V}
    (hw : w ∈ framePerp F) (h : ∀ u ∈ framePerp F, polar Q w u = 0) : w = 0 := by
  classical
  refine hQ.1 w (fun y => ?_)
  have hy : y - ∑ i, polar Q y (F.f i) • F.e i - ∑ i, polar Q y (F.e i) • F.f i ∈ framePerp F := by
    rw [mem_framePerp]
    rintro (j | j)
    · exact (polar_frame_cases F y j).1
    · exact (polar_frame_cases F y j).2
  have hwe : ∀ i, polar Q w (F.e i) = 0 := fun i => (mem_framePerp F w).mp hw (Sum.inl i)
  have hwf : ∀ i, polar Q w (F.f i) = 0 := fun i => (mem_framePerp F w).mp hw (Sum.inr i)
  have hy2 : y = (y - ∑ i, polar Q y (F.f i) • F.e i - ∑ i, polar Q y (F.e i) • F.f i) +
      ∑ i, polar Q y (F.f i) • F.e i + ∑ i, polar Q y (F.e i) • F.f i := by abel
  rw [polarBilin_apply_apply]
  conv_lhs => rw [hy2]
  rw [polar_add_right, polar_add_right, polar_sum_smul_right, polar_sum_smul_right, h _ hy]
  simp [hwe, hwf]

theorem exists_swap_frame_succ (hK : Nat.card K = 4) (hσ : ∀ x, σ x = x ^ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hTT : ∀ v, T (T v) = v)
    (hTQ : ∀ v, Q (T v) = σ (Q v)) (F : HFrame Q r)
    (hs : ∀ i, T (F.e i) = F.f i ∧ T (F.f i) = F.e i) (hdim : 2 * r + 4 ≤ finrank K V) :
    ∃ F' : HFrame Q (r + 1), ∀ i, T (F'.e i) = F'.f i ∧ T (F'.f i) = F'.e i := by
  classical
  have h4 : 4 ≤ finrank K (framePerp F) := by
    have := finrank_framePerp F
    omega
  obtain ⟨e, heW, hQe, hee⟩ := exists_good_vector hK σ hσ Q T hTT hTQ (framePerp F)
    (fun v hv => T_mem_framePerp_swap hTQ F hs hv) (fun w hw h => framePerp_nd hQ F hw h) h4
  have hTe : T e ∈ framePerp F := T_mem_framePerp_swap hTQ F hs heW
  have hQTe : Q (T e) = 0 := by rw [hTQ, hQe, map_zero]
  have hpe : ∀ i, polar Q e (F.e i) = 0 := fun i => (mem_framePerp F e).mp heW (Sum.inl i)
  have hpf : ∀ i, polar Q e (F.f i) = 0 := fun i => (mem_framePerp F e).mp heW (Sum.inr i)
  have hqe : ∀ i, polar Q (T e) (F.e i) = 0 := fun i => (mem_framePerp F (T e)).mp hTe (Sum.inl i)
  have hqf : ∀ i, polar Q (T e) (F.f i) = 0 := fun i => (mem_framePerp F (T e)).mp hTe (Sum.inr i)
  have hsTT : T (T e) = e := hTT e
  refine ⟨⟨Fin.snoc F.e e, Fin.snoc F.f (T e), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i; rfl
  · intro i; rfl
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hQe
    · simpa using F.Qe i
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hQTe
    · simpa using F.Qf i
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using polar_self_char_two Q e
    · simpa using hpe j
    · simpa [polar_comm Q (F.e i) e] using hpe i
    · simpa using F.ee i j
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using polar_self_char_two Q (T e)
    · simpa using hqf j
    · simpa [polar_comm Q (F.f i) (T e)] using hqf i
    · simpa using F.ff i j
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hee
    · simpa [(Fin.castSucc_lt_last j).ne'] using hpf j
    · simpa [polar_comm Q (F.e i) (T e), (Fin.castSucc_lt_last i).ne] using hqe i
    · simpa [Fin.castSucc_inj] using F.ef i j
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · constructor <;> simp [hsTT]
    · simpa using hs i

theorem exists_swap_frame (hK : Nat.card K = 4) (hσ : ∀ x, σ x = x ^ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hTT : ∀ v, T (T v) = v)
    (hTQ : ∀ v, Q (T v) = σ (Q v)) :
    ∀ r : ℕ, 2 * r + 2 ≤ finrank K V →
      ∃ F : HFrame Q r, ∀ i, T (F.e i) = F.f i ∧ T (F.f i) = F.e i := by
  intro r
  induction r with
  | zero =>
    intro _
    exact ⟨⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
      fun i => i.elim0⟩
  | succ r ih =>
    intro h
    obtain ⟨F, hF⟩ := ih (by omega)
    exact exists_swap_frame_succ hK hσ hQ hTT hTQ F hF (by omega)

end

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
