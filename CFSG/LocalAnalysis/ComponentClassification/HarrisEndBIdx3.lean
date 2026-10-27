module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBIdx2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBIdx
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSubGen

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup
open scoped commutatorElement

namespace IdxModel

variable {G : Type*} [Group G] {m : ℕ} {e : ℕ → G} {T : ℕ → ℕ → ℕ} {I : ℕ → ℕ} {o : ℕ}
  (h : IdxModel m e T I o)
include h

theorem mem_commutator_iff {C : List ℕ} (hC2 : ∀ i < m, ∀ j < m, ci T I i j ∈ C)
    (hC3 : ∀ c ∈ C, ∃ i < m, ∃ j < m, ci T I i j = c)
    (hC4 : ∀ c ∈ C, ∀ c' ∈ C, T c c' ∈ C) {x : G} :
    x ∈ ⁅h.sub, h.sub⁆ ↔ ∃ c ∈ C, e c = x := by
  have hCm : ∀ c ∈ C, c < m := fun c hc => by
    obtain ⟨i, hi, j, hj, rfl⟩ := hC3 c hc
    exact h.ci_lt hi hj
  let D : Subgroup G :=
    { carrier := {x | ∃ c ∈ C, e c = x}
      mul_mem' := by
        rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
        exact ⟨T c c', hC4 c hc c' hc', h.e_T c (hCm c hc) c' (hCm c' hc')⟩
      one_mem' := ⟨ci T I o o, hC2 o h.o_lt o h.o_lt, by
        rw [h.e_ci h.o_lt h.o_lt, h.e_o, commutatorElement_def]; group⟩
      inv_mem' := by
        rintro _ ⟨c, hc, rfl⟩
        obtain ⟨i, hi, j, hj, rfl⟩ := hC3 c hc
        refine ⟨ci T I j i, hC2 j hj i hi, ?_⟩
        rw [h.e_ci hj hi, h.e_ci hi hj, commutatorElement_inv] }
  have hle : ⁅h.sub, h.sub⁆ ≤ D := by
    rw [commutator_le]
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact ⟨ci T I i j, hC2 i hi j hj, h.e_ci hi hj⟩
  constructor
  · intro hx
    exact hle hx
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨i, hi, j, hj, rfl⟩ := hC3 c hc
    rw [h.e_ci hi hj]
    exact commutator_mem_commutator (h.e_mem hi) (h.e_mem hj)

theorem mem_zW_iff {z : ℕ} (hzm : z < m) (hzc : ∀ j < m, T z j = T j z)
    (hc : ∀ i < m, (∀ j < m, T i j = T j i) → i = o ∨ i = z) {x : G} :
    x ∈ zW h.sub ↔ x = 1 ∨ x = e z := by
  constructor
  · intro hx
    exact h.center_eq hc (mem_inf.mp hx).1 fun y hy => (mem_centralizer_iff.mp (mem_inf.mp hx).2
      y hy).symm
  · have hzC : ∀ y ∈ h.sub, y * e z = e z * y := by
      rintro _ ⟨j, hj, rfl⟩
      rw [← h.e_T j hj z hzm, ← h.e_T z hzm j hj, hzc j hj]
    rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_inf.mpr ⟨h.e_mem hzm, mem_centralizer_iff.mpr hzC⟩

theorem mem_cModZ_iff {C : List ℕ} (hC2 : ∀ i < m, ∀ j < m, ci T I i j ∈ C)
    (hC3 : ∀ c ∈ C, ∃ i < m, ∃ j < m, ci T I i j = c)
    (hC4 : ∀ c ∈ C, ∀ c' ∈ C, T c c' ∈ C) {z : ℕ} (hzm : z < m)
    (hzc : ∀ j < m, T z j = T j z) (hcen : ∀ i < m, (∀ j < m, T i j = T j i) → i = o ∨ i = z)
    {L : List ℕ} (hLm : ∀ i ∈ L, i < m)
    (hL : ∀ i < m, i ∈ L ↔ ∀ c ∈ C, ci T I i c = o ∨ ci T I i c = z) {x : G} :
    x ∈ cModZ h.sub ↔ ∃ i ∈ L, e i = x := by
  have hCm : ∀ c ∈ C, c < m := fun c hc => by
    obtain ⟨i, hi, j, hj, rfl⟩ := hC3 c hc
    exact h.ci_lt hi hj
  have hiff : ∀ i < m, (∀ a ∈ ⁅h.sub, h.sub⁆, ⁅e i, a⁆ ∈ zW h.sub) ↔ i ∈ L := by
    intro i hi
    rw [hL i hi]
    constructor
    · intro H c hc
      have := (h.mem_zW_iff hzm hzc hcen).mp
        (H _ ((h.mem_commutator_iff hC2 hC3 hC4).mpr ⟨c, hc, rfl⟩))
      rw [← h.e_ci hi (hCm c hc), ← h.e_o] at this
      rcases this with h1 | h1
      · exact Or.inl (h.inj _ (h.ci_lt hi (hCm c hc)) _ h.o_lt h1)
      · exact Or.inr (h.inj _ (h.ci_lt hi (hCm c hc)) _ hzm h1)
    · intro H a ha
      obtain ⟨c, hc, rfl⟩ := (h.mem_commutator_iff hC2 hC3 hC4).mp ha
      rw [h.mem_zW_iff hzm hzc hcen, ← h.e_ci hi (hCm c hc)]
      rcases H c hc with h1 | h1
      · left
        rw [h1, h.e_o]
      · right
        rw [h1]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hx⟩
    exact ⟨i, (hiff i hi).mp hx, rfl⟩
  · rintro ⟨i, hiL, rfl⟩
    exact ⟨h.e_mem (hLm i hiL), (hiff i (hLm i hiL)).mpr hiL⟩

theorem e_sigProdIdx {z : ℕ} (hzm : z < m) {a : ℕ × ℕ × ℕ × ℕ} (ha : ∀ k, quadFun a k < m)
    (p : (Fin 4 → Bool) × Bool) :
    e (sigProdIdx T o z a p) = sigProd (e z) (fun k => e (quadFun a k)) p ∧
      sigProdIdx T o z a p < m := by
  have hsel : ∀ (b : Bool) (k : Fin 4), (if b then quadFun a k else o) < m ∧
      e (if b then quadFun a k else o) = if b then e (quadFun a k) else 1 := by
    intro b k
    cases b
    · exact ⟨h.o_lt, by simp [h.e_o]⟩
    · exact ⟨ha k, by simp⟩
  have hz' : (if p.2 then z else o) < m ∧ e (if p.2 then z else o) = if p.2 then e z else 1 := by
    cases p.2
    · exact ⟨h.o_lt, by simp [h.e_o]⟩
    · exact ⟨hzm, by simp⟩
  obtain ⟨h0, e0⟩ := hsel (p.1 0) 0
  obtain ⟨h1, e1⟩ := hsel (p.1 1) 1
  obtain ⟨h2, e2⟩ := hsel (p.1 2) 2
  obtain ⟨h3, e3⟩ := hsel (p.1 3) 3
  have q0 : quadFun a 0 = a.1 := rfl
  have q1 : quadFun a 1 = a.2.1 := rfl
  have q2 : quadFun a 2 = a.2.2.1 := rfl
  have q3 : quadFun a 3 = a.2.2.2 := rfl
  rw [q0] at h0 e0
  rw [q1] at h1 e1
  rw [q2] at h2 e2
  rw [q3] at h3 e3
  have t1 := h.T_lt _ h0 _ h1
  have t2 := h.T_lt _ t1 _ h2
  have t3 := h.T_lt _ t2 _ h3
  refine ⟨?_, h.T_lt _ t3 _ hz'.1⟩
  rw [sigProdIdx, h.e_T _ t3 _ hz'.1, h.e_T _ t2 _ h3, h.e_T _ t1 _ h2, h.e_T _ h0 _ h1, e0, e1,
    e2, e3, hz'.2, sigProd, q0, q1, q2, q3]

theorem sigIdx_iff {z : ℕ} (hzm : z < m) {sq cm} {a : ℕ × ℕ × ℕ × ℕ}
    (ha : ∀ k, quadFun a k < m) :
    sigIdx T I o z sq cm a = true ↔ SigRel (e z) sq cm (fun k => e (quadFun a k)) := by
  have hite : ∀ b : Bool, (if b then z else o) < m ∧
      e (if b then z else o) = if b then e z else 1 := by
    intro b
    cases b
    · exact ⟨h.o_lt, by simp [h.e_o]⟩
    · exact ⟨hzm, by simp⟩
  rw [sigIdx, decide_eq_true_iff, SigRel]
  refine and_congr (forall_congr' fun k => ?_) (and_congr (forall_congr' fun k =>
    forall_congr' fun l => ?_) ?_)
  · rw [pow_two, ← h.e_T _ (ha k) _ (ha k), ← (hite (sq k)).2]
    exact ⟨fun H => by rw [H], fun H => h.inj _ (h.T_lt _ (ha k) _ (ha k)) _ (hite _).1 H⟩
  · rw [← h.e_ci (ha k) (ha l), ← (hite (cm k l)).2]
    exact ⟨fun H => by rw [H], fun H => h.inj _ (h.ci_lt (ha k) (ha l)) _ (hite _).1 H⟩
  · constructor
    · intro H p q hpq
      apply H
      apply h.inj _ (h.e_sigProdIdx hzm ha p).2 _ (h.e_sigProdIdx hzm ha q).2
      rw [(h.e_sigProdIdx hzm ha p).1, (h.e_sigProdIdx hzm ha q).1]
      exact hpq
    · intro H p q hpq
      apply H
      rw [← (h.e_sigProdIdx hzm ha p).1, ← (h.e_sigProdIdx hzm ha q).1, hpq]

end IdxModel

end CFSG.ComponentClassification.HarrisLit.EndB
