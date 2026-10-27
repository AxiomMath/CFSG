module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData

public section

namespace CFSG.AGLEmbedding.BCox

@[expose] def edges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (4, 8), (8, 9), (9, 10)]

@[expose] def adj (i j : Fin 11) : Bool :=
  edges.any fun e => (e.1 == i.val && e.2 == j.val) || (e.1 == j.val && e.2 == i.val)

theorem adj_irrefl : ∀ i : Fin 11, adj i i = false := by decide

theorem adj_symm : ∀ i j : Fin 11, adj i j = adj j i := by decide

structure Gens (G : Type) [Group G] where
  t : Fin 11 → G
  sq : ∀ i, t i * t i = 1
  comm_lt : ∀ i j, i < j → adj i j = false → t i * t j = t j * t i
  braid_lt : ∀ i j, i < j → adj i j = true → (t i * t j) ^ 3 = 1
  gen : Subgroup.closure (Set.range t) = ⊤

variable {G : Type} [Group G]

namespace Gens

variable (g : Gens G)

theorem inv_t (i : Fin 11) : (g.t i)⁻¹ = g.t i := inv_eq_of_mul_eq_one_right (g.sq i)

theorem comm {i j : Fin 11} (hij : adj i j = false) : g.t i * g.t j = g.t j * g.t i := by
  rcases lt_trichotomy i j with h | h | h
  · exact g.comm_lt i j h hij
  · rw [h]
  · exact (g.comm_lt j i h (by rw [adj_symm]; exact hij)).symm

theorem braid {i j : Fin 11} (hij : adj i j = true) : (g.t i * g.t j) ^ 3 = 1 := by
  rcases lt_trichotomy i j with h | h | h
  · exact g.braid_lt i j h hij
  · subst h
    exact absurd (hij.symm.trans (adj_irrefl i)) (by decide)
  · have h1 := g.braid_lt j i h (by rw [adj_symm]; exact hij)
    have hxy : g.t i * g.t j = (g.t j * g.t i)⁻¹ := by
      rw [mul_inv_rev, g.inv_t, g.inv_t]
    rw [hxy, inv_pow, h1, inv_one]

theorem inv_mul_t (i j : Fin 11) : (g.t i * g.t j)⁻¹ = g.t j * g.t i := by
  rw [mul_inv_rev, g.inv_t, g.inv_t]

theorem step_eq {u v w : Fin 11} (huv : g.t u = g.t v) (hvw : adj v w = true)
    (huw : adj u w = false) : g.t v = g.t w := by
  have hc : g.t v * g.t w = g.t w * g.t v := by
    have := g.comm huw
    rwa [huv] at this
  have h3 := g.braid hvw
  have h2 : (g.t v * g.t w) ^ 2 = 1 := by
    calc (g.t v * g.t w) ^ 2 = g.t v * (g.t w * g.t v) * g.t w := by
          rw [pow_two]; simp only [mul_assoc]
      _ = g.t v * (g.t v * g.t w) * g.t w := by rw [← hc]
      _ = (g.t v * g.t v) * (g.t w * g.t w) := by simp only [mul_assoc]
      _ = 1 := by rw [g.sq, g.sq, one_mul]
  have h1 : g.t v * g.t w = 1 := by
    have := h3
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul] at this
    exact this
  rw [eq_inv_of_mul_eq_one_left h1, g.inv_t]

end Gens

@[expose] def stepOK (known : List (Fin 11)) (w : Fin 11) : Bool :=
  known.any fun u => known.any fun v => adj v w && !adj u w

@[expose] def grow (known : List (Fin 11)) : List (Fin 11) :=
  known ++ (List.finRange 11).filter fun w => !known.contains w && stepOK known w

@[expose] def growN : ℕ → List (Fin 11) → List (Fin 11)
  | 0, known => known
  | n + 1, known => growN n (grow known)

theorem growN_all : ∀ i j : Fin 11, adj i j = true → ∀ w : Fin 11, w ∈ growN 11 [i, j] := by
  decide +kernel

namespace Gens

variable (g : Gens G)

theorem grow_inv {ref : G} (known : List (Fin 11)) (h : ∀ k ∈ known, g.t k = ref) :
    ∀ k ∈ grow known, g.t k = ref := by
  intro k hk
  rw [grow, List.mem_append] at hk
  rcases hk with hk | hk
  · exact h k hk
  · rw [List.mem_filter] at hk
    obtain ⟨-, hk2⟩ := hk
    simp only [Bool.and_eq_true, stepOK, List.any_eq_true, Bool.not_eq_true'] at hk2
    obtain ⟨-, u, hu, v, hv, hvk⟩ := hk2
    have := g.step_eq (u := u) (v := v) (w := k) ((h u hu).trans (h v hv).symm) hvk.1 hvk.2
    exact this.symm.trans (h v hv)

theorem growN_inv {ref : G} :
    ∀ (n : ℕ) (known : List (Fin 11)), (∀ k ∈ known, g.t k = ref) →
      ∀ k ∈ growN n known, g.t k = ref
  | 0, _, h => h
  | n + 1, known, h => growN_inv n (grow known) (g.grow_inv known h)

theorem all_eq_of_adj_eq {i j : Fin 11} (hij : adj i j = true) (h : g.t i = g.t j) :
    ∀ k, g.t k = g.t i := by
  intro k
  refine g.growN_inv (ref := g.t i) 11 [i, j] ?_ k (growN_all i j hij k)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · rfl
  · exact h.symm

theorem ne_of_adj (hcard : 2 < Nat.card G) {i j : Fin 11} (hij : adj i j = true) :
    g.t i ≠ g.t j := by
  intro h
  have hall := g.all_eq_of_adj_eq hij h
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have hle : (⊤ : Subgroup G) ≤ Subgroup.zpowers (g.t i) := by
    rw [← g.gen]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, rfl⟩
    rw [hall k]
    exact Subgroup.mem_zpowers _
  have h1 : Nat.card (Subgroup.zpowers (g.t i)) = orderOf (g.t i) := Nat.card_zpowers _
  have h2 : orderOf (g.t i) ≤ 2 :=
    orderOf_le_of_pow_eq_one two_pos (by rw [pow_two]; exact g.sq i)
  have h3 : Nat.card (⊤ : Subgroup G) ≤ Nat.card (Subgroup.zpowers (g.t i)) :=
    Subgroup.card_le_of_le hle
  rw [Subgroup.card_top] at h3
  omega

@[expose] def w (i j : Fin 11) : G := g.t i * g.t j

theorem w_pow_three {i j : Fin 11} (hij : adj i j = true) : g.w i j ^ 3 = 1 := g.braid hij

theorem w_ne_one (hcard : 2 < Nat.card G) {i j : Fin 11} (hij : adj i j = true) :
    g.w i j ≠ 1 := fun h =>
  g.ne_of_adj hcard hij ((eq_inv_of_mul_eq_one_left h).trans (g.inv_t j))

theorem orderOf_w (hcard : 2 < Nat.card G) {i j : Fin 11} (hij : adj i j = true) :
    orderOf (g.w i j) = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime (g.w_pow_three hij) (g.w_ne_one hcard hij)

theorem w_sq_eq_inv {i j : Fin 11} (hij : adj i j = true) : g.w i j ^ 2 = (g.w i j)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ]
  exact g.w_pow_three hij

end Gens

@[expose] def kind (m i j : Fin 11) : ℕ :=
  if m = i ∨ m = j then 2 else if adj m i = false ∧ adj m j = false then 1 else 0

theorem kind_lt (m i j : Fin 11) : kind m i j < 3 := by
  unfold kind
  split_ifs <;> omega

namespace Gens

variable (g : Gens G)

theorem pair_conj {m i j : Fin 11} (hij : adj i j = true) (hk : kind m i j ≠ 0) :
    g.t m * g.w i j * (g.t m)⁻¹ = g.w i j ^ kind m i j := by
  unfold kind at hk ⊢
  split_ifs at hk ⊢ with h1 h2
  · rw [g.w_sq_eq_inv hij, g.inv_t]
    unfold w
    rw [g.inv_mul_t]
    rcases h1 with rfl | rfl
    · calc g.t m * (g.t m * g.t j) * g.t m = (g.t m * g.t m) * g.t j * g.t m := by
            simp only [mul_assoc]
        _ = g.t j * g.t m := by rw [g.sq, one_mul]
    · calc g.t m * (g.t i * g.t m) * g.t m = g.t m * g.t i * (g.t m * g.t m) := by
            simp only [mul_assoc]
        _ = g.t m * g.t i := by rw [g.sq, mul_one]
  · have hmi := g.comm h2.1
    have hmj := g.comm h2.2
    have hc : g.t m * g.w i j = g.w i j * g.t m := by
      unfold w
      calc g.t m * (g.t i * g.t j) = (g.t m * g.t i) * g.t j := by rw [mul_assoc]
        _ = (g.t i * g.t m) * g.t j := by rw [hmi]
        _ = g.t i * (g.t m * g.t j) := by rw [mul_assoc]
        _ = g.t i * (g.t j * g.t m) := by rw [hmj]
        _ = (g.t i * g.t j) * g.t m := by rw [mul_assoc]
    rw [pow_one, mul_inv_eq_iff_eq_mul, hc]
  · exact absurd rfl hk

theorem w_comm {i j i' j' : Fin 11} (h1 : adj i i' = false) (h2 : adj i j' = false)
    (h3 : adj j i' = false) (h4 : adj j j' = false) :
    g.w i j * g.w i' j' = g.w i' j' * g.w i j := by
  have c1 : Commute (g.t i) (g.t i') := g.comm h1
  have c2 : Commute (g.t i) (g.t j') := g.comm h2
  have c3 : Commute (g.t j) (g.t i') := g.comm h3
  have c4 : Commute (g.t j) (g.t j') := g.comm h4
  exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq

end Gens

theorem list_prod_single {ι M : Type*} [Monoid M] (l : List ι) (f : ι → M) (i : ι)
    (hnd : l.Nodup) (hi : i ∈ l) (h1 : ∀ k ∈ l, k ≠ i → f k = 1) : (l.map f).prod = f i := by
  induction l with
  | nil => exact absurd hi List.not_mem_nil
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.prod_cons]
    by_cases hx : x = i
    · subst hx
      have : (xs.map f).prod = 1 := by
        apply List.prod_eq_one
        intro y hy
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
        exact h1 k (List.mem_cons_of_mem _ hk) (fun h => hnd.1 (h ▸ hk))
      rw [this, mul_one]
    · rw [h1 x List.mem_cons_self hx, one_mul]
      exact ih hnd.2 ((List.mem_cons.1 hi).resolve_left (Ne.symm hx))
        (fun k hk => h1 k (List.mem_cons_of_mem _ hk))

structure PairData (n m : ℕ) where
  bp : Fin n → Fin 11 × Fin 11
  acts : Fin m → Fin 11
  adj_ok : ∀ k, adj (bp k).1 (bp k).2 = true
  cross_ok : ∀ k l, k ≠ l → adj (bp k).1 (bp l).1 = false ∧ adj (bp k).1 (bp l).2 = false ∧
    adj (bp k).2 (bp l).1 = false ∧ adj (bp k).2 (bp l).2 = false
  act_ok : ∀ j k, kind (acts j) (bp k).1 (bp k).2 ≠ 0
  coord : ∀ k, ∃ s : Fin 11, kind s (bp k).1 (bp k).2 = 2 ∧
    ∀ l, l ≠ k → kind s (bp l).1 (bp l).2 = 1

namespace PairData

variable {n m : ℕ} (d : PairData n m)

@[expose] def eps (j : Fin m) (k : Fin n) : ZMod 3 :=
  ((kind (d.acts j) (d.bp k).1 (d.bp k).2 : ℕ) : ZMod 3)

theorem eps_val (j : Fin m) (k : Fin n) :
    (d.eps j k).val = kind (d.acts j) (d.bp k).1 (d.bp k).2 :=
  ZMod.val_natCast_of_lt (kind_lt _ _ _)

theorem indep_aux (gs : Gens G) (hcard : 2 < Nat.card G) (c : Fin n → ZMod 3)
    (hc : ((List.finRange n).map fun k => gs.w (d.bp k).1 (d.bp k).2 ^ (c k).val).prod = 1) :
    c = 0 := by
  funext k0
  obtain ⟨s, hs2, hs1⟩ := d.coord k0
  set f : Fin n → G := fun k => gs.w (d.bp k).1 (d.bp k).2 ^ (c k).val with hf
  have hk_ne : ∀ k, kind s (d.bp k).1 (d.bp k).2 ≠ 0 := by
    intro k
    by_cases h : k = k0
    · subst h; rw [hs2]; norm_num
    · rw [hs1 k h]; norm_num
  have hconjgen : ∀ k, gs.t s * f k * (gs.t s)⁻¹ =
      (gs.w (d.bp k).1 (d.bp k).2 ^ kind s (d.bp k).1 (d.bp k).2) ^ (c k).val := by
    intro k
    rw [← gs.pair_conj (d.adj_ok k) (hk_ne k), conj_pow]
  have hconj1 : ∀ k, k ≠ k0 → gs.t s * f k * (gs.t s)⁻¹ = f k := by
    intro k h
    rw [hconjgen k, hs1 k h, pow_one]
  have hf3 : f k0 ^ 3 = 1 := by
    rw [hf]
    dsimp only
    rw [← pow_mul, mul_comm, pow_mul, gs.w_pow_three (d.adj_ok k0), one_pow]
  have hconj0 : gs.t s * f k0 * (gs.t s)⁻¹ = (f k0)⁻¹ := by
    rw [hconjgen k0, hs2]
    have h2' : (gs.w (d.bp k0).1 (d.bp k0).2 ^ 2) ^ (c k0).val = f k0 ^ 2 := by
      rw [hf]
      dsimp only
      rw [← pow_mul, mul_comm, pow_mul]
    rw [h2']
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact hf3
  have h1 : (List.map f (List.finRange n)).prod = 1 := hc
  have h2 : (List.map (fun k => gs.t s * f k * (gs.t s)⁻¹) (List.finRange n)).prod = 1 := by
    have := map_list_prod (MulAut.conj (gs.t s)) (List.map f (List.finRange n))
    simp only [MulAut.conj_apply, h1, mul_one, mul_inv_cancel, List.map_map] at this
    rw [this]
    rfl
  obtain ⟨L1, L2, hsplit⟩ := List.append_of_mem (List.mem_finRange k0)
  have hnd := List.nodup_finRange n
  rw [hsplit, List.nodup_middle, List.nodup_cons, List.mem_append, not_or] at hnd
  obtain ⟨⟨hk1, hk2⟩, -⟩ := hnd
  rw [hsplit, List.map_append, List.map_cons, List.prod_append, List.prod_cons] at h1 h2
  have e1 : (List.map (fun k => gs.t s * f k * (gs.t s)⁻¹) L1).prod = (List.map f L1).prod := by
    congr 1
    refine List.map_congr_left fun k hk => ?_
    exact hconj1 k (by rintro rfl; exact hk1 hk)
  have e2 : (List.map (fun k => gs.t s * f k * (gs.t s)⁻¹) L2).prod = (List.map f L2).prod := by
    congr 1
    refine List.map_congr_left fun k hk => ?_
    exact hconj1 k (by rintro rfl; exact hk2 hk)
  rw [e1, e2, hconj0] at h2
  have h3 : f k0 = (f k0)⁻¹ := by
    have := h1.trans h2.symm
    exact mul_right_cancel (mul_left_cancel this)
  have h4 : f k0 = 1 := by
    have h5 : f k0 * f k0 = 1 := mul_eq_one_iff_eq_inv.2 h3
    have h6 := hf3
    rw [pow_three, h5, mul_one] at h6
    exact h6
  have h4' : gs.w (d.bp k0).1 (d.bp k0).2 ^ (c k0).val = 1 := h4
  have h7 : orderOf (gs.w (d.bp k0).1 (d.bp k0).2) ∣ (c k0).val :=
    orderOf_dvd_of_pow_eq_one h4'
  rw [gs.orderOf_w hcard (d.adj_ok k0)] at h7
  have h8 : (c k0).val < 3 := ZMod.val_lt _
  have h9 : (c k0).val = 0 := by
    rcases h7 with ⟨q, hq⟩
    omega
  exact (ZMod.val_eq_zero _).1 h9

theorem act_aux (gs : Gens G) (j : Fin m) (i : Fin n) :
    gs.t (d.acts j) * gs.w (d.bp i).1 (d.bp i).2 * (gs.t (d.acts j))⁻¹ =
      ((List.finRange n).map fun k => gs.w (d.bp k).1 (d.bp k).2 ^
        ((Matrix.diagonal (d.eps j)) k i).val).prod := by
  rw [gs.pair_conj (d.adj_ok i) (d.act_ok j i)]
  symm
  rw [list_prod_single (List.finRange n) _ i (List.nodup_finRange n) (List.mem_finRange i)]
  · simp [Matrix.diagonal_apply_eq, d.eps_val]
  · intro k _ hk
    simp [Matrix.diagonal_apply_ne _ hk]

@[expose] noncomputable def module (gs : Gens G) (hcard : 2 < Nat.card G) : ModuleSpec G 3 where
  n := n
  m := m
  a k := gs.w (d.bp k).1 (d.bp k).2
  g j := gs.t (d.acts j)
  M j := Matrix.diagonal (d.eps j)
  comm k l := by
    by_cases hkl : k = l
    · rw [hkl]
    · obtain ⟨h1, h2, h3, h4⟩ := d.cross_ok k l hkl
      exact gs.w_comm h1 h2 h3 h4
  pow k := gs.w_pow_three (d.adj_ok k)
  indep c hc := d.indep_aux gs hcard c hc
  act j i := d.act_aux gs j i

end PairData

theorem noFun_of_diag {n m : ℕ} (e : Fin m → Fin n → ZMod 3) (hF : ∀ k, ∃ j, e j k ≠ 1) :
    ∀ v : Fin n → ZMod 3, (∀ j, Matrix.vecMul v (Matrix.diagonal (e j)) = v) → v = 0 := by
  intro v hv
  funext k
  obtain ⟨j, hj⟩ := hF k
  have h := congrFun (hv j) k
  rw [Matrix.vecMul_diagonal] at h
  have h2 : v k * (e j k - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hj)

namespace PairData

variable {n m : ℕ} (d : PairData n m)

theorem noFun (gs : Gens G) (hcard : 2 < Nat.card G) (hF : ∀ k, ∃ j, d.eps j k ≠ 1) :
    (d.module gs hcard).NoFun := noFun_of_diag d.eps hF

theorem span_le {n' m' : ℕ} (gs : Gens G) (hcard : 2 < Nat.card G) (d' : PairData n' m')
    (h : ∀ k, ∃ l, d.bp k = d'.bp l) : (d.module gs hcard).span ≤ (d'.module gs hcard).span := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨l, hl⟩ := h k
  exact ⟨l, by
    show gs.w (d'.bp l).1 (d'.bp l).2 = gs.w (d.bp k).1 (d.bp k).2
    rw [hl]⟩

end PairData

end CFSG.AGLEmbedding.BCox
