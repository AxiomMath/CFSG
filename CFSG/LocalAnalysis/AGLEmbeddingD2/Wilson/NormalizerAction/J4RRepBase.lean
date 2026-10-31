
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Gam
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4RRepData
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Q

@[expose] public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4.Native CFSG.Quasithin.J4M2
  CFSG.Quasithin.J4Loc
  CFSG.Sporadic.J4.QT

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace RRepNF

variable {G : Type*} [Group G]

def Z2 (z a : G) : Prop := a = 1 ∨ a = z

theorem Z2.one {z : G} : Z2 z 1 := Or.inl rfl

theorem Z2.mul {z a b : G} (hz : z * z = 1) (ha : Z2 z a) (hb : Z2 z b) : Z2 z (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left; simp
  · right; simp
  · right; simp
  · left; exact hz

theorem Z2.commute {z a x : G} (hx : Commute z x) (ha : Z2 z a) : Commute a x := by
  rcases ha with rfl | rfl
  · exact Commute.one_left x
  · exact hx

theorem comm_of_pow (a b z : G) (n : ℕ) (hn : n = 0 ∨ n = 1) (h : a * b = b * a * z ^ n) :
    a * b = b * a ∨ a * b = b * a * z := by
  rcases hn with rfl | rfl
  · left; simpa using h
  · right; simpa using h

structure NFHyp (q : ℕ → G) (z : G) : Prop where
  zz : z * z = 1
  zc : ∀ k < 12, Commute z (q k)
  sq : ∀ k < 12, q k * q k = 1 ∨ q k * q k = z
  comm : ∀ i < 12, ∀ j < 12, q i * q j = q j * q i ∨ q i * q j = q j * q i * z

variable {q : ℕ → G} {z : G}

theorem eta_zero_n (n : ℕ) : eta q 0 n = 1 := by simp [eta]

theorem eta_commute (h : NFHyp q z) : ∀ m, m ≤ 12 → ∀ c, Commute z (eta q m c) := by
  intro m
  induction m with
  | zero => intro _ c; rw [eta_zero_n]; exact Commute.one_right z
  | succ m ih =>
    intro hm c
    rw [eta_succ]
    refine (ih (by omega) c).mul_right ?_
    split_ifs
    · exact h.zc m (by omega)
    · exact Commute.one_right z

theorem eta_congr_low (u : ℕ → G) : ∀ m (c d : ℕ), (∀ j < m, c.testBit j = d.testBit j) →
    eta u m c = eta u m d := by
  intro m
  induction m with
  | zero => intro c d _; simp [eta]
  | succ m ih =>
    intro c d hcd
    rw [eta_succ, eta_succ, ih c d (fun j hj => hcd j (by omega)), hcd m (by omega)]

theorem q_mul_eta (h : NFHyp q z) {k : ℕ} (hk : k < 12) : ∀ m, m ≤ 12 → ∀ c : ℕ,
    (k < m → ∃ a, Z2 z a ∧ q k * eta q m c = a * eta q m (c ^^^ 2 ^ k)) ∧
    (m ≤ k → ∃ a, Z2 z a ∧ q k * eta q m c = a * (eta q m c * q k)) := by
  intro m
  induction m with
  | zero =>
    intro _ c
    refine ⟨fun h0 => absurd h0 (by omega), fun _ => ⟨1, Z2.one, ?_⟩⟩
    simp [eta_zero_n]
  | succ m ih =>
    intro hm c
    obtain ⟨ihlt, ihge⟩ := ih (by omega) c
    have hE := eta_commute h m (by omega) c
    constructor
    · intro hkm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hkm with hlt | rfl
      · obtain ⟨a, ha, he⟩ := ihlt hlt
        refine ⟨a, ha, ?_⟩
        have hb : (c ^^^ 2 ^ k).testBit m = c.testBit m := by
          rw [Nat.testBit_xor, Nat.testBit_two_pow]
          have : k ≠ m := by omega
          simp [this]
        rw [eta_succ, eta_succ, hb, ← mul_assoc, he, mul_assoc]
      · obtain ⟨a, ha, he⟩ := ihge le_rfl
        have hlow : eta q k (c ^^^ 2 ^ k) = eta q k c := by
          refine (eta_congr_low q k c (c ^^^ 2 ^ k) fun j hj => ?_).symm
          rw [Nat.testBit_xor, Nat.testBit_two_pow]
          have : k ≠ j := by omega
          simp [this]
        have hb : (c ^^^ 2 ^ k).testBit k = !c.testBit k := by
          rw [Nat.testBit_xor, Nat.testBit_two_pow]
          simp
        rw [eta_succ, eta_succ, hlow, hb]
        cases hc : c.testBit k
        · refine ⟨a, ha, ?_⟩
          simpa using he
        · simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false, mul_one]
          rcases h.sq k hk with hs | hs
          · refine ⟨a, ha, ?_⟩
            rw [← mul_assoc, he]
            simp only [mul_assoc]
            rw [hs, mul_one]
          · refine ⟨a * z, Z2.mul h.zz ha (Or.inr rfl), ?_⟩
            rw [← mul_assoc, he]
            simp only [mul_assoc]
            rw [hs, ← hE.eq]
    · intro hmk
      obtain ⟨a, ha, he⟩ := ihge (by omega)
      rw [eta_succ]
      cases hc : c.testBit m
      · refine ⟨a, ha, ?_⟩
        simpa using he
      · simp only [ite_true]
        have hkm : q k * eta q m c * q m = a * (eta q m c * q k) * q m := by rw [he]
        rcases h.comm k hk m (by omega) with hq | hq
        · refine ⟨a, ha, ?_⟩
          rw [← mul_assoc, he]
          simp only [mul_assoc]
          rw [hq]
        · refine ⟨a * z, Z2.mul h.zz ha (Or.inr rfl), ?_⟩
          rw [← mul_assoc, he]
          have hW : Commute z (eta q m c * q m * q k) :=
            (hE.mul_right (h.zc m (by omega))).mul_right (h.zc k hk)
          calc a * (eta q m c * q k) * q m = a * (eta q m c * (q k * q m)) := by
                simp only [mul_assoc]
            _ = a * (eta q m c * (q m * q k * z)) := by rw [hq]
            _ = a * ((eta q m c * q m * q k) * z) := by simp only [mul_assoc]
            _ = a * (z * (eta q m c * q m * q k)) := by rw [hW.eq]
            _ = a * z * (eta q m c * q m * q k) := by simp only [mul_assoc]
            _ = _ := by simp only [mul_assoc]

def IsNF (q : ℕ → G) (z : G) (y : G) : Prop := ∃ a, Z2 z a ∧ ∃ c < 4096, y = a * eta q 12 c

theorem IsNF.q_mul (h : NFHyp q z) {k : ℕ} (hk : k < 12) {y : G} (hy : IsNF q z y) :
    IsNF q z (q k * y) := by
  obtain ⟨a, ha, c, hc, rfl⟩ := hy
  obtain ⟨b, hb, he⟩ := (q_mul_eta h hk 12 le_rfl c).1 hk
  have hlt : c ^^^ 2 ^ k < 4096 := by
    have h1 : c ^^^ 2 ^ k < 2 ^ 12 :=
      Nat.xor_lt_two_pow (by simpa using hc) (Nat.pow_lt_pow_right (by norm_num) hk)
    simpa using h1
  refine ⟨a * b, Z2.mul h.zz ha hb, c ^^^ 2 ^ k, hlt, ?_⟩
  rw [← mul_assoc, ← (Z2.commute (h.zc k hk) ha).eq, mul_assoc, he, mul_assoc]

theorem IsNF.z_mul (h : NFHyp q z) {y : G} (hy : IsNF q z y) : IsNF q z (z * y) := by
  obtain ⟨a, ha, c, hc, rfl⟩ := hy
  exact ⟨z * a, Z2.mul h.zz (Or.inr rfl) ha, c, hc, by rw [mul_assoc]⟩

theorem closure_NF (h : NFHyp q z) {x : G} (hx : x ∈ Subgroup.closure {y | ∃ k < 12, y = q k}) :
    (∀ y, IsNF q z y → IsNF q z (x * y)) ∧ (∀ y, IsNF q z y → IsNF q z (x⁻¹ * y)) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨fun y hy => hy.q_mul h hk, fun y hy => ?_⟩
    rcases h.sq k hk with hs | hs
    · rw [inv_eq_of_mul_eq_one_right hs]
      exact hy.q_mul h hk
    · have : (q k)⁻¹ = q k * z := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← mul_assoc, hs, h.zz]
      rw [this, mul_assoc]
      exact (hy.z_mul h).q_mul h hk
  | one => exact ⟨fun y hy => by simpa using hy, fun y hy => by simpa using hy⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [mul_assoc]; exact hx.1 _ (hy.1 w hw)
    · rw [mul_inv_rev, mul_assoc]; exact hy.2 _ (hx.2 w hw)
  | inv x _ hx =>
    exact ⟨fun y hy => hx.2 y hy, fun y hy => by rw [inv_inv]; exact hx.1 y hy⟩

theorem isNF_of_mem_closure (h : NFHyp q z) {p : G}
    (hp : p ∈ Subgroup.closure {y | ∃ k < 12, y = q k}) : IsNF q z p := by
  have h1 : IsNF q z (1 : G) := ⟨1, Z2.one, 0, by norm_num, by simp [eta_zero]⟩
  simpa using (closure_NF h hp).1 1 h1

end RRepNF

theorem nfHyp_gE :
    RRepNF.NFHyp gE z0 where
  zz := z0_mul_self matFacts
  zc k hk := Qgens_comm_z0 matFacts hk
  sq k hk := Qgens_sq matFacts hk
  comm i hi j hj :=
    @RRepNF.comm_of_pow J (Subgroup.toGroup J) _ _ _ _
      (by have := ZMod.val_lt (Qform ⟨i, hi⟩ ⟨j, hj⟩); omega)
      (Qgens_comm matFacts ⟨i, hi⟩ ⟨j, hj⟩)

theorem mem_Qgrp_nf
    {p : J} (hp : p ∈ Qgrp) :
    ∃ e : Bool, ∃ c < 4096, p = Coordinator.qNF e c := by
  obtain ⟨a, ha, c, hc, rfl⟩ := RRepNF.isNF_of_mem_closure nfHyp_gE hp
  rcases ha with rfl | rfl
  · exact ⟨false, c, hc, by simp [Coordinator.qNF]⟩
  · exact ⟨true, c, hc, by simp [Coordinator.qNF]⟩

section Matrices

def nfOf (idx : ℕ) : J := Coordinator.qNF (decide (4096 ≤ idx)) (idx % 4096)

end Matrices

theorem conj_step' {G : Type*} [Group G] (w g p p' : G) (h : g * p = p' * g) :
    w * g * p * (w * g)⁻¹ = w * p' * w⁻¹ := by
  rw [mul_assoc w g p, h]
  group

def genEl (g : ℕ) : J :=
  if g = 0 then Coordinator.cA else if g = 1 then Coordinator.cB else Coordinator.cZ

theorem genEl_mem (g : ℕ) : genEl g ∈ Coordinator.C0p := by
  unfold genEl
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem Mx_genEl
    (g : ℕ) :
    Mx (genEl g) = CFSG.Sporadic.J4.rowsMatrix (rrGen g) := by
  unfold genEl rrGen
  split_ifs
  · exact Mx_cA
  · exact Mx_cB
  · exact Mx_cZ

def Good (p : J) : Prop :=
  ∃ i : Fin 7, ∃ w ∈ Coordinator.C0p, ∃ q ∈ Coordinator.Q8set,
    w * p * w⁻¹ = Coordinator.rRep i * q

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
