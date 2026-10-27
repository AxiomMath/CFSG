module

public import Certificates.Data.Kernel.ThLocal.E81Defs
public import CFSG.Certificates.Kernel.ThLocal.Sound
import CFSG.Certificates.Kernel.Th.Spec.DceMat

public section

namespace CFSG.KC.ThLocal.Sound

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThCensus CFSG.KC.ThCensus.Sound
  CFSG.KC.ThLocal Subgroup

section Group

variable {G : Type*} [Group G]

@[expose] def quadP (x1 x2 x3 x4 : G) (u : (Fin 3 × Fin 3) × (Fin 3 × Fin 3)) : G :=
  pairP x1 x2 u.1 * pairP x3 x4 u.2

theorem pairP_commute {x1 x2 x3 x4 : G} (h13 : x1 * x3 = x3 * x1) (h14 : x1 * x4 = x4 * x1)
    (h23 : x2 * x3 = x3 * x2) (h24 : x2 * x4 = x4 * x2) (u v : Fin 3 × Fin 3) :
    pairP x1 x2 u * pairP x3 x4 v = pairP x3 x4 v * pairP x1 x2 u := by
  have c13 : Commute x1 x3 := h13
  have c14 : Commute x1 x4 := h14
  have c23 : Commute x2 x3 := h23
  have c24 : Commute x2 x4 := h24
  have hc : Commute (pairP x1 x2 u) (pairP x3 x4 v) := by
    unfold pairP
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact c13.pow_pow _ _
    · exact c14.pow_pow _ _
    · exact c23.pow_pow _ _
    · exact c24.pow_pow _ _
  exact hc.eq

@[expose] def addP (u v : Fin 3 × Fin 3) : Fin 3 × Fin 3 :=
  (⟨(u.1.val + v.1.val) % 3, Nat.mod_lt _ (by norm_num)⟩,
    ⟨(u.2.val + v.2.val) % 3, Nat.mod_lt _ (by norm_num)⟩)

theorem pairP_addP {x y : G} (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (u v : Fin 3 × Fin 3) : pairP x y u * pairP x y v = pairP x y (addP u v) :=
  pairP_mul hxy hx hy u v

theorem eq_of_add_negP {u v : Fin 3 × Fin 3} (h0 : addP u (negP v) = (0, 0)) : u = v := by
  have a1 : (u.1.val + (3 - v.1.val) % 3) % 3 = 0 :=
    congrArg (fun p : Fin 3 × Fin 3 => p.1.val) h0
  have a2 : (u.2.val + (3 - v.2.val) % 3) % 3 = 0 :=
    congrArg (fun p : Fin 3 × Fin 3 => p.2.val) h0
  have hu1 := u.1.isLt
  have hu2 := u.2.isLt
  have hv1 := v.1.isLt
  have hv2 := v.2.isLt
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> omega

theorem quadP_injective {x1 x2 x3 x4 : G} (h12 : x1 * x2 = x2 * x1) (h13 : x1 * x3 = x3 * x1)
    (h14 : x1 * x4 = x4 * x1) (h23 : x2 * x3 = x3 * x2) (h24 : x2 * x4 = x4 * x2)
    (h34 : x3 * x4 = x4 * x3) (hx1 : x1 ^ 3 = 1) (hx2 : x2 ^ 3 = 1) (hx3 : x3 ^ 3 = 1)
    (hx4 : x4 ^ 3 = 1) (hne : ∀ u, u ≠ ((0, 0), (0, 0)) → quadP x1 x2 x3 x4 u ≠ 1) :
    Function.Injective (quadP x1 x2 x3 x4) := by
  intro u v e
  have hc := pairP_commute h13 h14 h23 h24
  have hA := pairP_negP h12 hx1 hx2 v.1
  have hB := pairP_negP h34 hx3 hx4 v.2
  have key : quadP x1 x2 x3 x4 (addP u.1 (negP v.1), addP u.2 (negP v.2)) = 1 := by
    unfold quadP
    rw [← pairP_addP h12 hx1 hx2 u.1 (negP v.1), ← pairP_addP h34 hx3 hx4 u.2 (negP v.2)]
    have e' : pairP x1 x2 u.1 * pairP x3 x4 u.2 = pairP x1 x2 v.1 * pairP x3 x4 v.2 := e
    calc pairP x1 x2 u.1 * pairP x1 x2 (negP v.1) * (pairP x3 x4 u.2 * pairP x3 x4 (negP v.2))
        = pairP x1 x2 u.1 * (pairP x1 x2 (negP v.1) * pairP x3 x4 u.2) *
            pairP x3 x4 (negP v.2) := by group
      _ = pairP x1 x2 u.1 * (pairP x3 x4 u.2 * pairP x1 x2 (negP v.1)) *
            pairP x3 x4 (negP v.2) := by rw [hc]
      _ = pairP x1 x2 u.1 * pairP x3 x4 u.2 * pairP x1 x2 (negP v.1) *
            pairP x3 x4 (negP v.2) := by group
      _ = pairP x1 x2 v.1 * pairP x3 x4 v.2 * pairP x1 x2 (negP v.1) *
            pairP x3 x4 (negP v.2) := by rw [e']
      _ = pairP x1 x2 v.1 * (pairP x3 x4 v.2 * pairP x1 x2 (negP v.1)) *
            pairP x3 x4 (negP v.2) := by group
      _ = pairP x1 x2 v.1 * (pairP x1 x2 (negP v.1) * pairP x3 x4 v.2) *
            pairP x3 x4 (negP v.2) := by rw [hc]
      _ = pairP x1 x2 v.1 * pairP x1 x2 (negP v.1) *
            (pairP x3 x4 v.2 * pairP x3 x4 (negP v.2)) := by group
      _ = 1 := by rw [hA, hB, one_mul]
  by_contra huv
  refine hne _ ?_ key
  intro h0
  apply huv
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  exact Prod.ext (eq_of_add_negP h1) (eq_of_add_negP h2)

theorem quadP_mem (x1 x2 x3 x4 : G) (u : (Fin 3 × Fin 3) × (Fin 3 × Fin 3)) :
    quadP x1 x2 x3 x4 u ∈ Subgroup.closure ({x1, x2, x3, x4} : Set G) := by
  have m1 : x1 ∈ Subgroup.closure ({x1, x2, x3, x4} : Set G) := Subgroup.subset_closure (by simp)
  have m2 : x2 ∈ Subgroup.closure ({x1, x2, x3, x4} : Set G) := Subgroup.subset_closure (by simp)
  have m3 : x3 ∈ Subgroup.closure ({x1, x2, x3, x4} : Set G) := Subgroup.subset_closure (by simp)
  have m4 : x4 ∈ Subgroup.closure ({x1, x2, x3, x4} : Set G) := Subgroup.subset_closure (by simp)
  unfold quadP pairP
  exact mul_mem (mul_mem (pow_mem m1 _) (pow_mem m2 _)) (mul_mem (pow_mem m3 _) (pow_mem m4 _))

theorem e81_closure [Finite G] {x1 x2 x3 x4 : G} (h12 : x1 * x2 = x2 * x1)
    (h13 : x1 * x3 = x3 * x1) (h14 : x1 * x4 = x4 * x1) (h23 : x2 * x3 = x3 * x2)
    (h24 : x2 * x4 = x4 * x2) (h34 : x3 * x4 = x4 * x3) (hx1 : x1 ^ 3 = 1) (hx2 : x2 ^ 3 = 1)
    (hx3 : x3 ^ 3 = 1) (hx4 : x4 ^ 3 = 1)
    (hne : ∀ u, u ≠ ((0, 0), (0, 0)) → quadP x1 x2 x3 x4 u ≠ 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({x1, x2, x3, x4} : Set G)) ∧
      81 ≤ Nat.card (Subgroup.closure ({x1, x2, x3, x4} : Set G)) := by
  refine ⟨isElemAbelian_closure_comm ?_ ?_, ?_⟩
  · intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first | rfl | assumption | exact Eq.symm (by assumption)
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  · have hinj := quadP_injective h12 h13 h14 h23 h24 h34 hx1 hx2 hx3 hx4 hne
    have hc : Nat.card ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) = 81 := by simp
    rw [← hc]
    exact Nat.card_le_card_of_injective (fun u => ⟨quadP x1 x2 x3 x4 u, quadP_mem x1 x2 x3 x4 u⟩)
      (fun u v e => hinj (congrArg Subtype.val e))

end Group

section Perm

variable {G : Type*} [Group G] {φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)} {g : ℕ → G}
  {vec : ℕ → Fin 248 → ZMod 2} {TT : ℕ}
  (hstep : ∀ k < 10, ∀ d < 3, ∀ p < 243, permStep TT k d p < 243 ∧
      vec (permStep TT k d p) = Matrix.vecMul (vec p) (φ (g k ^ d)))
  (hinj : ∀ p < 243, ∀ q < 243, vec p = vec q → p = q)
include hstep hinj

theorem moveAt_spec {o r x y v : ℕ} (ho : o < 243) (h : moveAt TT o r x y v = true) :
    nfFrom g 10 0 r ^ (v % 3) * nfFrom g 10 0 19683 ^ (v / 3 % 3) *
      (nfFrom g 10 0 x ^ (v / 9 % 3) * nfFrom g 10 0 y ^ (v / 27)) ≠ 1 := by
  intro e1
  obtain ⟨a1, a2⟩ := iterW_spec hstep r (v % 3) o ho
  obtain ⟨b1, b2⟩ := iterW_spec hstep 19683 (v / 3 % 3) _ a1
  obtain ⟨c1, c2⟩ := iterW_spec hstep x (v / 9 % 3) _ b1
  obtain ⟨d1, d2⟩ := iterW_spec hstep y (v / 27) _ c1
  have hv : vec (iterW TT y (v / 27) (iterW TT x (v / 9 % 3) (iterW TT 19683 (v / 3 % 3)
      (iterW TT r (v % 3) o)))) = vec o := by
    rw [d2, c2, b2, a2, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
      ← map_mul, ← map_mul, ← map_mul, ← mul_assoc, e1, map_one, Matrix.vecMul_one]
  have hp := hinj _ d1 o ho hv
  have h' : notB (Nat.beq (iterW TT y (v / 27) (iterW TT x (v / 9 % 3)
      (iterW TT 19683 (v / 3 % 3) (iterW TT r (v % 3) o)))) o) = true := h
  rw [hp, Nat.beq_refl] at h'
  exact Bool.noConfusion h'

end Perm

section Dec

variable {TT o0 o1 o2 : ℕ}

theorem movesOK_dec {r x y m : ℕ} (h : movesOK TT o0 o1 o2 r x y m = true) :
    ∀ i < m, orB (moveAt TT o0 r x y (i + 1))
      (orB (moveAt TT o1 r x y (i + 1)) (moveAt TT o2 r x y (i + 1))) = true :=
  rec_all (fun i => orB (moveAt TT o0 r x y (Nat.succ i))
    (orB (moveAt TT o1 r x y (Nat.succ i)) (moveAt TT o2 r x y (Nat.succ i)))) m h

theorem e81OK_dec {r x y : ℕ} (h : e81OK TT o0 o1 o2 r x y = true) :
    key3 TT o0 o1 o2 x r r = true ∧ key3 TT o0 o1 o2 y r r = true ∧
      key3 TT o0 o1 o2 x y y = true ∧ cube3 TT o0 o1 o2 x = true ∧
      cube3 TT o0 o1 o2 y = true ∧ movesOK TT o0 o1 o2 r x y 80 = true := by
  have h' : bAnd(key3 TT o0 o1 o2 x r r, bAnd(key3 TT o0 o1 o2 y r r,
      bAnd(key3 TT o0 o1 o2 x y y, bAnd(cube3 TT o0 o1 o2 x, bAnd(cube3 TT o0 o1 o2 y,
        movesOK TT o0 o1 o2 r x y 80))))) = true := h
  obtain ⟨u1, t1⟩ := rec_and h'
  obtain ⟨u2, t2⟩ := rec_and t1
  obtain ⟨u3, t3⟩ := rec_and t2
  obtain ⟨u4, t4⟩ := rec_and t3
  obtain ⟨u5, u6⟩ := rec_and t4
  exact ⟨u1, u2, u3, u4, u5, u6⟩

theorem e81RepOK_dec {reps : List (List ℕ)} {m : ℕ} {E : List ℕ}
    (h : e81RepOK TT o0 o1 o2 reps m E = true) :
    isZ (permNfNum (reps.getD m [])) = true ∨
      e81OK TT o0 o1 o2 (permNfNum (reps.getD m [])) (E.getD 0 0) (E.getD 1 0) = true :=
  Dce.orB_iff.1 h

end Dec

end CFSG.KC.ThLocal.Sound

end
