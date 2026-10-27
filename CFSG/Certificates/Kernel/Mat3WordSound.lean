module

public import Certificates.Data.Kernel.Mat3
public import CFSG.Certificates.CosetTablePresented
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.KC.Mat3

open scoped Matrix

variable (p : ℕ)

@[expose] def toM (a : List ℕ) : Matrix (Fin 3) (Fin 3) (ZMod p) := fun i j => (ent a i j : ZMod p)

@[expose] def toV (x : List ℕ) : Fin 3 → ZMod p := fun j => (x.getD j 0 : ZMod p)

theorem toM_mul (a b : List ℕ) : toM p (mul p a b) = toM p a * toM p b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toM, mul, ent, Matrix.mul_apply, Fin.sum_univ_three, ZMod.natCast_mod]

theorem toM_one : toM p one3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM, one3, ent, Matrix.one_apply]

theorem toV_vec (x M : List ℕ) : toV p (vec p x M) = toV p x ᵥ* toM p M := by
  ext j
  fin_cases j <;>
    simp [toV, vec, toM, ent, Matrix.vecMul, dotProduct, Fin.sum_univ_three, ZMod.natCast_mod]

theorem toM_foldl {m : ℕ} (G Gi : List (List ℕ)) :
    ∀ (w : List (Fin m × Bool)) (acc : List ℕ),
      toM p (w.foldl (fun M l => mul p M (letter G Gi l)) acc) =
        toM p acc * (w.map fun l => toM p (letter G Gi l)).prod
  | [], acc => by simp
  | l :: w, acc => by
    rw [List.foldl_cons, toM_foldl G Gi w, toM_mul, List.map_cons, List.prod_cons, mul_assoc]

theorem toM_word {m : ℕ} (G Gi : List (List ℕ)) (w : List (Fin m × Bool)) :
    toM p (word p G Gi w) = (w.map fun l => toM p (letter G Gi l)).prod := by
  rw [word, toM_foldl, toM_one, one_mul]

theorem iterate_toV (M x : List ℕ) :
    ∀ k : ℕ, (fun v => v ᵥ* toM p M)^[k] (toV p x) = toV p (iter p M x k)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', iterate_toV M x k, iter, toV_vec]

variable {p}

theorem canon_vec (hp : 0 < p) (x M : List ℕ) : canon p 3 (vec p x M) = true := by
  simp [canon, vec, Nat.mod_lt _ hp]

theorem canon_iter (hp : 0 < p) (M x : List ℕ) (k : ℕ) : canon p 3 (iter p M x (k + 1)) = true :=
  canon_vec hp _ _

theorem toV_inj {x y : List ℕ} (hx : canon p 3 x = true) (hy : canon p 3 y = true)
    (h : toV p x = toV p y) : x = y := by
  simp only [canon, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hx hy
  obtain ⟨hxl, hxp⟩ := hx
  obtain ⟨hyl, hyp⟩ := hy
  match x, y, hxl, hyl with
  | [x0, x1, x2], [y0, y1, y2], _, _ =>
    have e : ∀ a b : ℕ, a < p → b < p → (a : ZMod p) = b → a = b := fun a b ha hb e => by
      rw [ZMod.natCast_eq_natCast_iff'] at e
      rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [toV] at h0 h1 h2
    rw [e x0 y0 (hxp _ (by simp)) (hyp _ (by simp)) h0, e x1 y1 (hxp _ (by simp)) (hyp _ (by simp)) h1,
      e x2 y2 (hxp _ (by simp)) (hyp _ (by simp)) h2]

theorem minimalPeriod_of_periodIs {M b : List ℕ} {ℓ : ℕ} (hb : canon p 3 b = true) (hℓ : 0 < ℓ)
    (h : periodIs p M b ℓ = true) :
    Function.minimalPeriod (fun v => v ᵥ* toM p M) (toV p b) = ℓ := by
  have hp : 0 < p := by
    simp only [canon, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hb
    match b, hb with
    | x :: _, ⟨_, hb⟩ => exact Nat.lt_of_le_of_lt (Nat.zero_le x) (hb x (by simp))
  simp only [periodIs, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hfix, hne⟩ := h
  have hper : Function.IsPeriodicPt (fun v => v ᵥ* toM p M) ℓ (toV p b) := by
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [iterate_toV, hfix]
  have hle := hper.minimalPeriod_le hℓ
  have hpos := hper.minimalPeriod_pos hℓ
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have hmp := Function.isPeriodicPt_minimalPeriod (fun v => v ᵥ* toM p M) (toV p b)
  unfold Function.IsPeriodicPt Function.IsFixedPt at hmp
  rw [iterate_toV] at hmp
  obtain ⟨k, hk⟩ : ∃ k, Function.minimalPeriod (fun v => v ᵥ* toM p M) (toV p b) = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have := hne _ hlt
  rw [hk] at this hmp
  rcases this with h0 | h1
  · omega
  · exact h1 (toV_inj (canon_iter hp M b k) hb hmp)

theorem lift_val {m : ℕ} {G Gi : List (List ℕ)} (g : Fin m → (Matrix (Fin 3) (Fin 3) (ZMod p))ˣ)
    (hg : ∀ i, (g i : Matrix (Fin 3) (Fin 3) (ZMod p)) = toM p (G.getD i.val []))
    (hgi : ∀ i, ((g i)⁻¹ : (Matrix (Fin 3) (Fin 3) (ZMod p))ˣ) = toM p (Gi.getD i.val []))
    (w : List (Fin m × Bool)) :
    ((FreeGroup.lift g (FreeGroup.mk w) : (Matrix (Fin 3) (Fin 3) (ZMod p))ˣ) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) = toM p (word p G Gi w) := by
  rw [FreeGroup.lift_mk, toM_word, ← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  obtain ⟨i, b⟩ := l
  cases b
  · simp [letter, hgi]
  · simp [letter, hg]

theorem check_sound {m : ℕ} {G Gi : List (List ℕ)} {b : List ℕ}
    {rels : List (List (Fin m × Bool))} {walks : List (List (Fin m × Bool) × ℕ)}
    (h : check p m G Gi b rels walks = true) :
    ∃ g : Fin m → (Matrix (Fin 3) (Fin 3) (ZMod p))ˣ,
      (∀ r ∈ rels, FreeGroup.lift g (FreeGroup.mk r) = 1) ∧
      ∀ w ℓ, (w, ℓ) ∈ walks → 0 < ℓ →
        Function.minimalPeriod (fun v => v ᵥ* ((FreeGroup.lift g (FreeGroup.mk w) :
          (Matrix (Fin 3) (Fin 3) (ZMod p))ˣ) : Matrix (Fin 3) (Fin 3) (ZMod p))) (toV p b) = ℓ := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hb⟩, hinv⟩, hrels⟩, hwalks⟩ := h
  have hinv' : ∀ i : Fin m, toM p (G.getD i.val []) * toM p (Gi.getD i.val []) = 1 ∧
      toM p (Gi.getD i.val []) * toM p (G.getD i.val []) = 1 := fun i => by
    obtain ⟨h1, h2⟩ := hinv i.val i.isLt
    rw [← toM_mul, ← toM_mul, h1, h2, toM_one]
    exact ⟨rfl, rfl⟩
  let g : Fin m → (Matrix (Fin 3) (Fin 3) (ZMod p))ˣ := fun i =>
    ⟨toM p (G.getD i.val []), toM p (Gi.getD i.val []), (hinv' i).1, (hinv' i).2⟩
  have hval := lift_val g (fun _ => rfl) (fun _ => rfl)
  refine ⟨g, fun r hr => Units.ext ?_, fun w ℓ hw hℓ => ?_⟩
  · rw [hval, hrels r hr, toM_one]
    rfl
  · rw [hval]
    rcases hwalks (w, ℓ) hw with h0 | h1
    · omega
    · exact minimalPeriod_of_periodIs hb hℓ h1

@[expose] noncomputable def rowAct :
    (Matrix (Fin 3) (Fin 3) (ZMod p))ˣ →* (Equiv.Perm (Fin 3 → ZMod p))ᵐᵒᵖ where
  toFun g := MulOpposite.op
    { toFun := fun v => v ᵥ* (g : Matrix (Fin 3) (Fin 3) (ZMod p))
      invFun := fun v => v ᵥ* ((g⁻¹ : (Matrix (Fin 3) (Fin 3) (ZMod p))ˣ) :
        Matrix (Fin 3) (Fin 3) (ZMod p))
      left_inv := fun v => by
        simp only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
      right_inv := fun v => by
        simp only [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one] }
  map_one' := by
    apply MulOpposite.unop_injective
    ext v
    simp
  map_mul' g h := by
    apply MulOpposite.unop_injective
    ext v
    simp [Matrix.vecMul_vecMul]

theorem check_presented {m : ℕ} {G Gi : List (List ℕ)} {b : List ℕ}
    {rels : List (List (Fin m × Bool))} {walks : List (List (Fin m × Bool) × ℕ)}
    (h : check p m G Gi b rels walks = true) {ws : List (List (Fin m × Bool))}
    (hws : ∀ r ∈ ws, r ∈ rels) :
    ∃ (Ω : Type) (ψ : CFSG.CosetTable.PG m ws →* (Equiv.Perm Ω)ᵐᵒᵖ) (b : Ω), ∀ u ℓ,
      (u, ℓ) ∈ walks → 0 < ℓ →
        Function.minimalPeriod (ψ (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
          (FreeGroup.mk u))).unop b = ℓ := by
  obtain ⟨g, hrel, hper⟩ := check_sound h
  have hrel' : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}, FreeGroup.lift g r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hrel w (hws w hw)
  exact ⟨Fin 3 → ZMod p, rowAct.comp (PresentedGroup.toGroup hrel'), toV p b,
    fun u ℓ hu hℓ => hper u ℓ hu hℓ⟩

end CFSG.KC.Mat3

end
