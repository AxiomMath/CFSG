module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.KS.SporSch.FibOrb

open Finset

theorem fib_sum (f OJ RP : Nat → Nat) {c nr : Nat} (hJ : ∀ k < c, OJ k < nr)
    (hT : ∀ k < c, f k = f (RP (OJ k))) :
    ∑ k ∈ range c, f k = ∑ j ∈ range nr, #((range c).filter fun k => OJ k = j) * f (RP j) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := OJ) (t := range nr)
    (fun k hk => mem_range.2 (hJ k (mem_range.1 hk)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun k hk => by
    obtain ⟨hk, e⟩ := Finset.mem_filter.1 hk
    rw [hT k (mem_range.1 hk), e], Finset.sum_const, smul_eq_mul]

theorem sum_cls_card (g OJ : Nat → Nat) {c nr : Nat} (hJ : ∀ k < c, OJ k < nr) :
    ∑ j ∈ range nr, #((range c).filter fun k => OJ k = j) * g j = ∑ k ∈ range c, g (OJ k) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := OJ) (t := range nr)
    (fun k hk => mem_range.2 (hJ k (mem_range.1 hk)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun k hk => by rw [(Finset.mem_filter.1 hk).2], Finset.sum_const,
    smul_eq_mul]

theorem tree_root_eq {α : Type*} (f : Nat → α) (OJ RP par dep : Nat → Nat) {c : Nat}
    (h0 : ∀ k < c, dep k = 0 → RP (OJ k) = k)
    (hs : ∀ k < c, dep k ≠ 0 → par k < c ∧ OJ (par k) = OJ k ∧ dep (par k) + 1 = dep k ∧
      f k = f (par k)) : ∀ k < c, f k = f (RP (OJ k)) := by
  suffices ∀ e, ∀ k < c, dep k = e → f k = f (RP (OJ k)) from fun k hk => this _ k hk rfl
  intro e
  induction e with
  | zero => exact fun k hk he => by rw [h0 k hk he]
  | succ e ih =>
    intro k hk he
    obtain ⟨hp, hj, hd, hf⟩ := hs k hk (by omega)
    rw [hf, ih _ hp (by omega), hj]

theorem sum_range_reindex (F img : Nat → Nat) {c : Nat} (hlt : ∀ k < c, img k < c)
    (hinj : ∀ k < c, ∀ k' < c, img k = img k' → k = k') :
    ∑ k ∈ range c, F (img k) = ∑ a ∈ range c, F a := by
  have hi : Set.InjOn img (range c : Set Nat) := fun k hk k' hk' e =>
    hinj k (mem_range.1 hk) k' (mem_range.1 hk') e
  have hsub : (range c).image img ⊆ range c := fun a ha => by
    obtain ⟨k, hk, rfl⟩ := mem_image.1 ha
    exact mem_range.2 (hlt k (mem_range.1 hk))
  have heq : (range c).image img = range c :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_image_of_injOn hi])
  rw [← Finset.sum_image (f := F) fun k hk k' hk' e => hi hk hk' e, heq]

variable {n : Nat}

theorem card_fib_conj (G : Subgroup (Equiv.Perm (Fin n))) (P : Equiv.Perm (Fin n) → Prop)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ G) {b : Fin n} (a : Fin n) (hgb : g b = b)
    (hP : ∀ y, P (g * y * g⁻¹) ↔ P y) :
    Nat.card {y : G // (y : Equiv.Perm (Fin n)) b = a ∧ P y} =
      Nat.card {y : G // (y : Equiv.Perm (Fin n)) b = g a ∧ P y} := by
  have hgi : g⁻¹ b = b := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hgb.symm
  have hP' : ∀ y, P (g⁻¹ * y * g) ↔ P y := fun y => by
    rw [← hP]
    group
  refine Nat.card_congr
    { toFun := fun y => ⟨⟨g * y.1 * g⁻¹, G.mul_mem (G.mul_mem hg y.1.2) (G.inv_mem hg)⟩, ?_⟩
      invFun := fun y => ⟨⟨g⁻¹ * y.1 * g, G.mul_mem (G.mul_mem (G.inv_mem hg) y.1.2) hg⟩, ?_⟩
      left_inv := fun y => ?_
      right_inv := fun y => ?_ }
  · refine ⟨?_, (hP _).2 y.2.2⟩
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hgi, y.2.1]
  · refine ⟨?_, (hP' _).2 y.2.2⟩
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hgb, y.2.1]
    exact Equiv.Perm.inv_eq_iff_eq.2 rfl
  · refine Subtype.ext (Subtype.ext ?_)
    simp only
    group
  · refine Subtype.ext (Subtype.ext ?_)
    simp only
    group

theorem card_conj_par (G : Subgroup (Equiv.Perm (Fin n)))
    (Q : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop) {c : Equiv.Perm (Fin n)} (hc : c ∈ G)
    (x : Equiv.Perm (Fin n)) (hQ : ∀ y, Q (c * x * c⁻¹) (c * y * c⁻¹) ↔ Q x y) :
    Nat.card {y : G // Q x y} = Nat.card {y : G // Q (c * x * c⁻¹) y} := by
  refine Nat.card_congr
    { toFun := fun y => ⟨⟨c * y.1 * c⁻¹, G.mul_mem (G.mul_mem hc y.1.2) (G.inv_mem hc)⟩,
        (hQ _).2 y.2⟩
      invFun := fun y => ⟨⟨c⁻¹ * y.1 * c, G.mul_mem (G.mul_mem (G.inv_mem hc) y.1.2) hc⟩, ?_⟩
      left_inv := fun y => ?_
      right_inv := fun y => ?_ }
  · rw [← hQ]
    have e : c * (c⁻¹ * (y.1 : Equiv.Perm (Fin n)) * c) * c⁻¹ = y.1 := by group
    rw [e]
    exact y.2
  · refine Subtype.ext (Subtype.ext ?_)
    simp only
    group
  · refine Subtype.ext (Subtype.ext ?_)
    simp only
    group

theorem patProd_conjY {M : Type*} [Group M] (g x y : M) (hgx : g * x * g⁻¹ = x) :
    ∀ pat : List Bool, (pat.map fun b => if b then g * y * g⁻¹ else x).prod =
      g * (pat.map fun b => if b then y else x).prod * g⁻¹
  | [] => by simp
  | b :: pat => by
    rw [List.map_cons, List.prod_cons, patProd_conjY g x y hgx pat, List.map_cons, List.prod_cons]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      calc x * (g * (pat.map fun b => if b then y else x).prod * g⁻¹)
          = g * x * g⁻¹ * (g * (pat.map fun b => if b then y else x).prod * g⁻¹) := by rw [hgx]
        _ = _ := by group
    · simp only [↓reduceIte]
      group

theorem card_eq_sum_fibB (G : Subgroup (Equiv.Perm (Fin n))) (b : Fin n)
    (P : Equiv.Perm (Fin n) → Prop) (pt : Nat → Fin n) (hpt : ∀ a < n, (pt a : Nat) = a) :
    Nat.card {y : G // P y} =
      ∑ a ∈ range n, Nat.card {y : G // (y : Equiv.Perm (Fin n)) b = pt a ∧ P y} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun y : G => ((y : Equiv.Perm (Fin n)) b : Nat))
    (t := range n) fun y _ => mem_range.2 ((y : Equiv.Perm (Fin n)) b).2]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.filter_filter]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, hpt a (mem_range.1 ha)]
  exact and_comm

theorem card_conds_conj (G : Subgroup (Equiv.Perm (Fin n))) {c : Equiv.Perm (Fin n)} (hc : c ∈ G)
    (xg : Equiv.Perm (Fin n)) (m : Nat) (conds : List (List Bool × Nat)) :
    Nat.card {y : G // orderOf (y : Equiv.Perm (Fin n)) = m ∧ ∀ d ∈ conds,
        orderOf (d.1.map fun t => if t then (y : Equiv.Perm (Fin n)) else xg).prod = d.2} =
      Nat.card {y : G // orderOf (y : Equiv.Perm (Fin n)) = m ∧ ∀ d ∈ conds,
        orderOf (d.1.map fun t => if t then (y : Equiv.Perm (Fin n)) else c * xg * c⁻¹).prod =
          d.2} := by
  have oc : ∀ y : Equiv.Perm (Fin n), orderOf (c * y * c⁻¹) = orderOf y := fun y =>
    (MulAut.conj c).orderOf_eq y
  have pc : ∀ (y : Equiv.Perm (Fin n)) (pat : List Bool),
      (pat.map fun t => if t then c * y * c⁻¹ else c * xg * c⁻¹).prod =
        c * (pat.map fun t => if t then y else xg).prod * c⁻¹ := fun y pat => by
    have e : (fun t : Bool => if t then c * y * c⁻¹ else c * xg * c⁻¹) =
        (MulAut.conj c) ∘ fun t => if t then y else xg := by
      funext t
      cases t <;> rfl
    rw [e, ← List.map_map, ← map_list_prod]
    rfl
  exact card_conj_par G (fun x y => orderOf y = m ∧ ∀ d ∈ conds,
    orderOf (d.1.map fun t => if t then y else x).prod = d.2) hc xg fun y => by
      simp only [oc, pc]

theorem card_fib_conds (G : Subgroup (Equiv.Perm (Fin n))) {g : Equiv.Perm (Fin n)} (hg : g ∈ G)
    {b : Fin n} (a : Fin n) (hgb : g b = b) {xg : Equiv.Perm (Fin n)} (hgx : g * xg * g⁻¹ = xg)
    (m : Nat) (conds : List (List Bool × Nat)) :
    Nat.card {y : G // (y : Equiv.Perm (Fin n)) b = a ∧ (orderOf (y : Equiv.Perm (Fin n)) = m ∧
        ∀ c ∈ conds, orderOf (c.1.map fun t => if t then (y : Equiv.Perm (Fin n)) else xg).prod =
          c.2)} =
      Nat.card {y : G // (y : Equiv.Perm (Fin n)) b = g a ∧ (orderOf (y : Equiv.Perm (Fin n)) = m ∧
        ∀ c ∈ conds, orderOf (c.1.map fun t => if t then (y : Equiv.Perm (Fin n)) else xg).prod =
          c.2)} := by
  have oc : ∀ y : Equiv.Perm (Fin n), orderOf (g * y * g⁻¹) = orderOf y := fun y =>
    (MulAut.conj g).orderOf_eq y
  refine card_fib_conj G (fun y => orderOf y = m ∧ ∀ c ∈ conds,
    orderOf (c.1.map fun t => if t then y else xg).prod = c.2) hg a hgb fun y => ?_
  simp only [oc, patProd_conjY g xg y hgx]

theorem card_fib_ord (G : Subgroup (Equiv.Perm (Fin n))) {g : Equiv.Perm (Fin n)} (hg : g ∈ G)
    {b : Fin n} (a : Fin n) (hgb : g b = b) (m : Nat) :
    Nat.card {y : G // (y : Equiv.Perm (Fin n)) b = a ∧ orderOf (y : Equiv.Perm (Fin n)) = m} =
      Nat.card {y : G // (y : Equiv.Perm (Fin n)) b = g a ∧
        orderOf (y : Equiv.Perm (Fin n)) = m} :=
  card_fib_conj G (fun y => orderOf y = m) hg a hgb fun y => by
    rw [← (MulAut.conj g).orderOf_eq y]
    rfl

theorem forest_sum (G : Subgroup (Equiv.Perm (Fin n))) {b : Fin n} {xg : Equiv.Perm (Fin n)}
    (hs : Nat → Equiv.Perm (Fin n)) (hsG : ∀ i, hs i ∈ G) (hsb : ∀ i, hs i b = b)
    (hsx : ∀ i, hs i * xg * (hs i)⁻¹ = xg) (pt : Nat → Fin n) (m : Nat)
    (conds : List (List Bool × Nat)) (OJ RP par gi dep : Nat → Nat) {nr : Nat}
    (hJ : ∀ a < n, OJ a < nr) (h0 : ∀ a < n, dep a = 0 → RP (OJ a) = a)
    (hst : ∀ a < n, dep a ≠ 0 → par a < n ∧ OJ (par a) = OJ a ∧ dep (par a) + 1 = dep a ∧
      hs (gi a) (pt (par a)) = pt a) :
    ∑ a ∈ range n, Nat.card {y : G // (y : Equiv.Perm (Fin n)) b = pt a ∧
        (orderOf (y : Equiv.Perm (Fin n)) = m ∧ ∀ c ∈ conds,
          orderOf (c.1.map fun t => if t then (y : Equiv.Perm (Fin n)) else xg).prod = c.2)} =
      ∑ j ∈ range nr, #((range n).filter fun a => OJ a = j) *
        Nat.card {y : G // (y : Equiv.Perm (Fin n)) b = pt (RP j) ∧
          (orderOf (y : Equiv.Perm (Fin n)) = m ∧ ∀ c ∈ conds,
            orderOf (c.1.map fun t => if t then (y : Equiv.Perm (Fin n)) else xg).prod = c.2)} := by
  refine fib_sum _ OJ RP hJ (tree_root_eq _ OJ RP par dep h0 fun a ha hd => ?_)
  obtain ⟨hp, hj, hdp, he⟩ := hst a ha hd
  refine ⟨hp, hj, hdp, ?_⟩
  rw [card_fib_conds G (hsG (gi a)) (pt (par a)) (hsb (gi a)) (hsx (gi a)) m conds, he]

end CFSG.KS.SporSch.FibOrb


end
