module

public import CFSG.ClassicalInvolution.Q3.Sec13EndPolar16
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13.Polar

variable {V : Type*} [CommGroup V]

@[expose] def wt6 (x : Fin 6 → ZMod 2) : ℕ := (Finset.univ.filter fun i => x i ≠ 0).card

@[expose] def dot6 (x y : Fin 6 → ZMod 2) : ZMod 2 := ∑ i, x i * y i

@[expose] def ind6 (α : Finset (Fin 6)) : Fin 6 → ZMod 2 := fun i => if i ∈ α then 1 else 0

theorem card_dot_zero_wt3 : ∀ v : Fin 6 → ZMod 2, wt6 v = 3 →
    ((Finset.univ : Finset (Finset (Fin 6))).filter
      (fun α => α.card = 4 ∧ dot6 v (ind6 α) = 0)).card = 9 := by
  decide +kernel

theorem card_dot_zero_wt1 : ∀ v : Fin 6 → ZMod 2, wt6 v = 1 →
    ((Finset.univ : Finset (Finset (Fin 6))).filter
      (fun α => α.card = 4 ∧ dot6 v (ind6 α) = 0)).card = 5 := by
  decide +kernel

theorem card_dot_zero_wt5 : ∀ v : Fin 6 → ZMod 2, wt6 v = 5 →
    ((Finset.univ : Finset (Finset (Fin 6))).filter
      (fun α => α.card = 4 ∧ dot6 v (ind6 α) = 0)).card = 5 := by
  decide +kernel

theorem card_inter_even : ∀ α : Finset (Fin 6), α.card = 4 →
    ((Finset.univ : Finset (Finset (Fin 6))).filter
      (fun β => β.card = 4 ∧ (α ∩ β).card % 2 = 0)).card = 7 := by
  decide +kernel

private theorem p8a_wt_ind : ∀ α : Finset (Fin 6), wt6 (ind6 α) = α.card := by
  decide +kernel

private theorem p8a_sum_ind :
    ∀ α : Finset (Fin 6), ∑ i, ind6 α i = ((α.card : ℕ) : ZMod 2) := by
  decide +kernel

private theorem p8a_dot_ind : ∀ α β : Finset (Fin 6),
    dot6 (ind6 α) (ind6 β) = ((α ∩ β).card : ZMod 2) := by
  decide +kernel

private theorem p8a_even_decomp : ∀ w : Fin 6 → ZMod 2, (∑ j, w j = 0) →
    w = ∑ i ∈ Finset.univ.filter (fun i : Fin 5 => w i.castSucc = 1), ind6 {i.castSucc, 5} := by
  decide +kernel

private theorem p8a_wt_odd : ∀ v : Fin 6 → ZMod 2, (∑ j, v j = 1) →
    wt6 v = 1 ∨ wt6 v = 3 ∨ wt6 v = 5 := by
  decide +kernel

private theorem p8a_dot_pair : ∀ (v : Fin 6 → ZMod 2) (i : Fin 5),
    dot6 v (ind6 {i.castSucc, 5}) = v i.castSucc + v 5 := by
  decide +kernel

private theorem p8a_even_pair : ∀ i : Fin 5, ∑ j, ind6 {i.castSucc, 5} j = 0 := by
  decide +kernel

private theorem p8a_castSucc_ne : ∀ i : Fin 5, i.castSucc ≠ 5 := by decide

private theorem p8a_zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem p8a_zmod2_self : ∀ c : ZMod 2, c = c + c → c = 0 := by decide

private theorem p8a_dot6_add (v w w' : Fin 6 → ZMod 2) :
    dot6 v (w + w') = dot6 v w + dot6 v w' := by
  simp only [dot6, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem p8a_dot6_sum {ι : Type*} [DecidableEq ι] (v : Fin 6 → ZMod 2) (T : Finset ι)
    (g : ι → Fin 6 → ZMod 2) : dot6 v (∑ i ∈ T, g i) = ∑ i ∈ T, dot6 v (g i) := by
  induction T using Finset.induction_on with
  | empty => simp [dot6]
  | insert x T hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, p8a_dot6_add, ih]

private theorem p8a_ncard_filter (P : Finset (Fin 6) → Prop) [DecidablePred P] :
    {α : Finset (Fin 6) | P α}.ncard = (Finset.univ.filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext α
  simp

structure Cfg9 (B : V → V → ZMod 2) (S : Set V) (A : Subgroup V)
    (e : A →* Multiplicative (Fin 6 → ZMod 2)) (u : V) (a : ℕ) : Prop where
  symp : SympForm B
  pointSet : PointSet B S a
  three_dvd : 3 ∣ a
  gen : Subgroup.closure S = ⊤
  e_inj : Function.Injective e
  e_range : ∀ x : Multiplicative (Fin 6 → ZMod 2), x ∈ e.range ↔ ∑ i, x.toAdd i = 0
  e_form : ∀ x y : A, B x y = dot6 (e x).toAdd (e y).toAdd
  mem : u ∈ A
  e_u : e ⟨u, mem⟩ = Multiplicative.ofAdd (fun _ => 1)
  perp_u : ∀ p : V, (p ∈ S ∧ B u p = 0) ↔ ∃ x : A, (x : V) = p ∧ wt6 (e x).toAdd = 4
  count_perp : ∀ x : A, (x : V) ∈ S → {p | p ∈ S ∧ B (u * x) p = 0}.ncard = 15

@[expose] def fibre (B : V → V → ZMod 2) (S : Set V) (A : Subgroup V) (u b : V) : Set V :=
  {p | p ∈ S ∧ B u p = 1 ∧ ∀ x : A, B p x = B b x}

private def p8aSupp {A : Subgroup V} (e : A →* Multiplicative (Fin 6 → ZMod 2)) (x : A) :
    Finset (Fin 6) :=
  Finset.univ.filter fun i => (e x).toAdd i ≠ 0

private theorem p8aSupp_card {A : Subgroup V} {e : A →* Multiplicative (Fin 6 → ZMod 2)}
    (x : A) : (p8aSupp e x).card = wt6 (e x).toAdd := rfl

private theorem p8a_ind_supp {A : Subgroup V} {e : A →* Multiplicative (Fin 6 → ZMod 2)}
    (x : A) : ind6 (p8aSupp e x) = (e x).toAdd := by
  funext i
  simp only [ind6, p8aSupp, Finset.mem_filter, Finset.mem_univ, true_and]
  generalize (e x).toAdd i = c
  rcases p8a_zmod2_cases c with rfl | rfl <;> decide

private theorem p8a_supp_of_ind {A : Subgroup V} {e : A →* Multiplicative (Fin 6 → ZMod 2)}
    {x : A} {α : Finset (Fin 6)} (hx : (e x).toAdd = ind6 α) : p8aSupp e x = α := by
  ext i
  simp only [p8aSupp, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hx]
  by_cases hi : i ∈ α <;> simp [ind6, hi]

private theorem p8a_B_one {B : V → V → ZMod 2} (hB : SympForm B) (b : V) : B b 1 = 0 := by
  have h := hB.mul_right b 1 1
  rw [mul_one] at h
  exact p8a_zmod2_self _ h

private theorem p8a_B_prod {ι : Type*} [DecidableEq ι] {B : V → V → ZMod 2} (hB : SympForm B)
    (b : V) (f : ι → V) (T : Finset ι) : B b (∏ i ∈ T, f i) = ∑ i ∈ T, B b (f i) := by
  induction T using Finset.induction_on with
  | empty => simp [p8a_B_one hB b]
  | insert x T hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, hB.mul_right, ih]

namespace Cfg9

variable [Finite V] {B : V → V → ZMod 2} {S : Set V} {A : Subgroup V}
  {e : A →* Multiplicative (Fin 6 → ZMod 2)} {u : V} {a : ℕ}

private theorem p8a_B_u (h : Cfg9 B S A e u a) (x : A) : B u x = 0 := by
  have h1 : B u (x : V) = dot6 (fun _ => 1) (e x).toAdd := by
    have h0 := h.e_form ⟨u, h.mem⟩ x
    rw [h.e_u, toAdd_ofAdd] at h0
    exact h0
  have h2 := (h.e_range (e x)).mp (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  rw [h1]
  simpa [dot6] using h2

private theorem p8a_mem_iff (h : Cfg9 B S A e u a) (x : A) :
    (x : V) ∈ S ↔ wt6 (e x).toAdd = 4 := by
  constructor
  · intro hx
    obtain ⟨y, hy, hw⟩ := (h.perp_u x).mp ⟨hx, p8a_B_u h x⟩
    have hyx : y = x := Subtype.ext hy
    rw [← hyx]
    exact hw
  · intro hw
    exact ((h.perp_u x).mpr ⟨x, rfl, hw⟩).1

private theorem p8a_exists_mem (h : Cfg9 B S A e u a) {α : Finset (Fin 6)} (hα : α.card = 4) :
    ∃ x : A, (e x).toAdd = ind6 α := by
  have hr : Multiplicative.ofAdd (ind6 α) ∈ e.range := by
    rw [h.e_range, toAdd_ofAdd, p8a_sum_ind, hα]
    decide
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hr
  exact ⟨x, by rw [hx, toAdd_ofAdd]⟩

private theorem p8a_B_iff (h : Cfg9 B S A e u a) (x y : A) :
    B x y = 0 ↔ (p8aSupp e x ∩ p8aSupp e y).card % 2 = 0 := by
  rw [h.e_form x y, ← p8a_ind_supp x, ← p8a_ind_supp y, p8a_dot_ind,
    ZMod.natCast_eq_zero_iff_even, Nat.even_iff]

private theorem p8a_count (h : Cfg9 B S A e u a) (Q : Finset (Fin 6) → Prop) :
    {x : A | (x : V) ∈ S ∧ Q (p8aSupp e x)}.ncard =
      {α : Finset (Fin 6) | α.card = 4 ∧ Q α}.ncard := by
  refine Set.ncard_congr (fun x _ => p8aSupp e x) ?_ ?_ ?_
  · rintro x ⟨hxS, hQ⟩
    refine ⟨?_, hQ⟩
    rw [p8aSupp_card]
    exact (p8a_mem_iff h x).mp hxS
  · intro x y _ _ hxy
    have hxy' : (e x).toAdd = (e y).toAdd := by
      rw [← p8a_ind_supp x, ← p8a_ind_supp y, hxy]
    exact h.e_inj (Multiplicative.toAdd.injective hxy')
  · rintro α ⟨hα, hQ⟩
    obtain ⟨x, hx⟩ := p8a_exists_mem h hα
    refine ⟨x, ⟨(p8a_mem_iff h x).mpr ?_, ?_⟩, p8a_supp_of_ind hx⟩
    · rw [hx, p8a_wt_ind, hα]
    · rw [p8a_supp_of_ind hx]
      exact hQ

private theorem p8a_vec (h : Cfg9 B S A e u a) (b : V) :
    ∃ v : Fin 6 → ZMod 2, ∀ x : A, B b x = dot6 v (e x).toAdd := by
  have hy : ∀ i : Fin 5, ∃ x : A, e x = Multiplicative.ofAdd (ind6 {i.castSucc, 5}) := by
    intro i
    have hr : Multiplicative.ofAdd (ind6 {i.castSucc, 5}) ∈ e.range := by
      rw [h.e_range, toAdd_ofAdd, p8a_even_pair i]
    exact MonoidHom.mem_range.mp hr
  choose y hy using hy
  obtain ⟨v, hv1, hv5⟩ : ∃ v : Fin 6 → ZMod 2,
      (∀ i : Fin 5, v i.castSucc = B b (y i)) ∧ v 5 = 0 := by
    refine ⟨fun j => ∑ i : Fin 5, if i.castSucc = j then B b (y i) else 0, fun i => ?_, ?_⟩
    · simp [Fin.castSucc_inj]
    · exact Finset.sum_eq_zero (fun i _ => if_neg (p8a_castSucc_ne i))
  refine ⟨v, fun x => ?_⟩
  have hgen : ∀ T : Finset (Fin 5), (e x).toAdd = ∑ i ∈ T, ind6 {i.castSucc, 5} →
      B b x = ∑ i ∈ T, B b (y i) := by
    intro T hT
    have hxT : x = ∏ i ∈ T, y i := by
      apply h.e_inj
      rw [map_prod]
      simp_rw [hy]
      rw [← ofAdd_sum, ← hT, ofAdd_toAdd]
    rw [hxT, SubmonoidClass.coe_finsetProd]
    exact p8a_B_prod h.symp b (fun i => (y i : V)) T
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin 5), (e x).toAdd = ∑ i ∈ T, ind6 {i.castSucc, 5} :=
    ⟨_, p8a_even_decomp _ ((h.e_range (e x)).mp (MonoidHom.mem_range.mpr ⟨x, rfl⟩))⟩
  rw [hgen T hT, hT, p8a_dot6_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [p8a_dot_pair, hv1 i, hv5, add_zero]

private theorem p8a_sum_of_u (h : Cfg9 B S A e u a) {b : V} {v : Fin 6 → ZMod 2}
    (hv : ∀ x : A, B b x = dot6 v (e x).toAdd) : B b u = ∑ j, v j := by
  have h1 : B b u = dot6 v (e ⟨u, h.mem⟩).toAdd := hv ⟨u, h.mem⟩
  rw [h.e_u, toAdd_ofAdd] at h1
  rw [h1]
  simp [dot6]

private theorem p8a_card_T (h : Cfg9 B S A e u a) {b : V} {v : Fin 6 → ZMod 2}
    (hv : ∀ x : A, B b x = dot6 v (e x).toAdd) :
    {x : A | (x : V) ∈ S ∧ B x b = 0}.ncard =
      ((Finset.univ : Finset (Finset (Fin 6))).filter
        (fun α => α.card = 4 ∧ dot6 v (ind6 α) = 0)).card := by
  have hset : {x : A | (x : V) ∈ S ∧ B x b = 0} =
      {x : A | (x : V) ∈ S ∧ dot6 v (ind6 (p8aSupp e x)) = 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [h.symp.symm (x : V) b, hv x, p8a_ind_supp x]
  rw [hset]
  exact (p8a_count h (fun α => dot6 v (ind6 α) = 0)).trans
    (p8a_ncard_filter (fun α => α.card = 4 ∧ dot6 v (ind6 α) = 0))

theorem exists_far (h : Cfg9 B S A e u a) : ∃ b, b ∈ far B S u := by
  have hu1 : u ≠ 1 := by
    intro hu
    have h1 : e ⟨u, h.mem⟩ = 1 := by
      rw [show (⟨u, h.mem⟩ : A) = 1 from Subtype.ext hu, map_one]
    rw [h.e_u] at h1
    have h3 := congrFun (congrArg Multiplicative.toAdd h1) 0
    simp at h3
  obtain ⟨c, hc⟩ : ∃ c : V, B u c ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hu1 (h.symp.nondeg u hne)
  have hc1 : B u c = 1 := (p8a_zmod2_cases (B u c)).resolve_left hc
  by_contra hno
  push Not at hno
  have hS0 : ∀ s ∈ S, B u s = 0 := fun s hs =>
    (p8a_zmod2_cases (B u s)).resolve_right (fun h1 => hno s (show s ∈ far B S u from ⟨hs, h1⟩))
  have hall : ∀ g ∈ Subgroup.closure S, B u g = 0 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hS0 x hx
    | one => exact p8a_B_one h.symp u
    | mul x y _ _ ihx ihy => rw [h.symp.mul_right, ihx, ihy, add_zero]
    | inv x _ ihx =>
      rw [inv_eq_of_mul_eq_one_right (h.symp.sq_eq_one x)]
      exact ihx
  have htop : c ∈ Subgroup.closure S := by
    rw [h.gen]
    exact Subgroup.mem_top c
  rw [hall c htop] at hc1
  exact absurd hc1 (by decide)

theorem card_nbr_far (h : Cfg9 B S A e u a) {b : V} (hb : b ∈ far B S u) :
    (nbr B S b).ncard = 2 * {x : A | (x : V) ∈ S ∧ B x b = 0}.ncard := by
  have hbS : b ∈ S := hb.1
  have hbu : B u b = 1 := hb.2
  have hne : ∀ x : A, (x : V) ∈ S → B x b = 0 → (x : V) ≠ b := by
    intro x _ _ hxb
    have h1 := p8a_B_u h x
    rw [hxb, hbu] at h1
    exact absurd h1 (by decide)
  have hnbr : nbr B S b = (fun x : A => (x : V)) '' {x : A | (x : V) ∈ S ∧ B x b = 0} ∪
      (fun x : A => b * (x : V)) '' {x : A | (x : V) ∈ S ∧ B x b = 0} := by
    ext q
    constructor
    · rintro ⟨hqS, hqb, hbq⟩
      rcases p8a_zmod2_cases (B u q) with h0 | h1
      · obtain ⟨x, hxq, -⟩ := (h.perp_u q).mp ⟨hqS, h0⟩
        refine Or.inl ⟨x, ⟨?_, ?_⟩, hxq⟩
        · rw [hxq]
          exact hqS
        · rw [h.symp.symm (x : V) b, hxq]
          exact hbq
      · have hbq' : b * q ∈ S := h.pointSet.mul_mem_of_orth b hbS q hqS (Ne.symm hqb) hbq
        have hBu : B u (b * q) = 0 := by
          rw [h.symp.mul_right, hbu, h1]
          decide
        obtain ⟨x, hxq, -⟩ := (h.perp_u (b * q)).mp ⟨hbq', hBu⟩
        refine Or.inr ⟨x, ⟨?_, ?_⟩, ?_⟩
        · rw [hxq]
          exact hbq'
        · rw [hxq, h.symp.mul_left, h.symp.alt, zero_add, h.symp.symm q b]
          exact hbq
        · show b * (x : V) = q
          rw [hxq, ← mul_assoc, h.symp.sq_eq_one b, one_mul]
    · rintro (⟨x, ⟨hxS, hxb⟩, rfl⟩ | ⟨x, ⟨hxS, hxb⟩, rfl⟩)
      · exact ⟨hxS, hne x hxS hxb, by rw [h.symp.symm]; exact hxb⟩
      · have hx1 : (x : V) ≠ 1 := fun h1 => h.pointSet.one_notMem (h1 ▸ hxS)
        refine ⟨h.pointSet.mul_mem_of_orth b hbS x hxS (Ne.symm (hne x hxS hxb)) ?_, ?_, ?_⟩
        · rw [h.symp.symm]
          exact hxb
        · intro hbx
          exact hx1 (mul_eq_left.mp hbx)
        · rw [h.symp.mul_right, h.symp.alt, zero_add, h.symp.symm]
          exact hxb
  have hinj1 : Function.Injective (fun x : A => (x : V)) := Subtype.val_injective
  have hinj2 : Function.Injective (fun x : A => b * (x : V)) :=
    fun x y hxy => Subtype.ext (mul_left_cancel hxy)
  have hdisj : Disjoint ((fun x : A => (x : V)) '' {x : A | (x : V) ∈ S ∧ B x b = 0})
      ((fun x : A => b * (x : V)) '' {x : A | (x : V) ∈ S ∧ B x b = 0}) := by
    rw [Set.disjoint_left]
    rintro q ⟨x, -, rfl⟩ ⟨y, -, hxy⟩
    dsimp only at hxy ⊢
    have h1 := p8a_B_u h x
    have h2 : B u (b * (y : V)) = 1 := by
      rw [h.symp.mul_right, hbu, p8a_B_u h y, add_zero]
    rw [hxy, h1] at h2
    exact absurd h2 (by decide)
  rw [hnbr, Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _ hinj1,
    Set.ncard_image_of_injective _ hinj2]
  omega

theorem a_eq_nine (h : Cfg9 B S A e u a) : a = 9 := by
  obtain ⟨b, hb⟩ := exists_far h
  obtain ⟨v, hv⟩ := p8a_vec h b
  have hcf := card_nbr_far h hb
  have hn := h.pointSet.card_nbr b hb.1
  have hT := p8a_card_T h hv
  have hd := h.three_dvd
  have hsum : ∑ j, v j = 1 := by
    rw [← p8a_sum_of_u h hv, h.symp.symm]
    exact hb.2
  rcases p8a_wt_odd v hsum with h1 | h3 | h5
  · rw [card_dot_zero_wt1 v h1] at hT
    omega
  · rw [card_dot_zero_wt3 v h3] at hT
    omega
  · rw [card_dot_zero_wt5 v h5] at hT
    omega

theorem wt_three_of_far (h : Cfg9 B S A e u a) {b : V} (hb : b ∈ far B S u) :
    ∃ v : Fin 6 → ZMod 2, wt6 v = 3 ∧ ∀ x : A, B b x = dot6 v (e x).toAdd := by
  obtain ⟨v, hv⟩ := p8a_vec h b
  refine ⟨v, ?_, hv⟩
  have hcf := card_nbr_far h hb
  have hn := h.pointSet.card_nbr b hb.1
  have hT := p8a_card_T h hv
  have ha := a_eq_nine h
  have hsum : ∑ j, v j = 1 := by
    rw [← p8a_sum_of_u h hv, h.symp.symm]
    exact hb.2
  rcases p8a_wt_odd v hsum with h1 | h3 | h5
  · rw [card_dot_zero_wt1 v h1] at hT
    omega
  · exact h3
  · rw [card_dot_zero_wt5 v h5] at hT
    omega

theorem card_far_eq (h : Cfg9 B S A e u a) : (far B S u).ncard = 20 := by
  have ha := a_eq_nine h
  obtain ⟨x0, hx0⟩ := p8a_exists_mem h (α := {0, 1, 2, 3}) (by decide)
  have hw0 : wt6 (e x0).toAdd = 4 := by
    rw [hx0, p8a_wt_ind]
    decide
  have hx0S : (x0 : V) ∈ S := (p8a_mem_iff h x0).mpr hw0
  have hcard0 : (p8aSupp e x0).card = 4 := by
    rw [p8aSupp_card, hw0]
  have hZ : {p : V | p ∈ S ∧ B x0 p = 0}.ncard = 19 := by
    have hset : {p : V | p ∈ S ∧ B x0 p = 0} = insert (x0 : V) (nbr B S x0) := by
      ext p
      constructor
      · rintro ⟨hpS, hpB⟩
        by_cases hp : p = x0
        · exact Or.inl hp
        · exact Or.inr ⟨hpS, hp, hpB⟩
      · rintro (rfl | ⟨hpS, _, hpB⟩)
        · exact ⟨hx0S, h.symp.alt _⟩
        · exact ⟨hpS, hpB⟩
    have hnot : (x0 : V) ∉ nbr B S x0 := fun hm => hm.2.1 rfl
    rw [hset, Set.ncard_insert_of_notMem hnot, h.pointSet.card_nbr x0 hx0S, ha]
  have hG0 : {p : V | p ∈ S ∧ B u p = 0 ∧ B x0 p = 0}.ncard = 7 := by
    have himg : {p : V | p ∈ S ∧ B u p = 0 ∧ B x0 p = 0} =
        Subtype.val '' {y : A | (y : V) ∈ S ∧ B x0 y = 0} := by
      ext p
      constructor
      · rintro ⟨hpS, hpu, hpx⟩
        obtain ⟨y, hy, -⟩ := (h.perp_u p).mp ⟨hpS, hpu⟩
        refine ⟨y, ⟨?_, ?_⟩, hy⟩
        · rw [hy]
          exact hpS
        · rw [hy]
          exact hpx
      · rintro ⟨y, ⟨hyS, hyx⟩, rfl⟩
        exact ⟨hyS, p8a_B_u h y, hyx⟩
    rw [himg, Set.ncard_image_of_injective _ Subtype.val_injective]
    have hset : {y : A | (y : V) ∈ S ∧ B x0 y = 0} =
        {y : A | (y : V) ∈ S ∧ (p8aSupp e x0 ∩ p8aSupp e y).card % 2 = 0} := by
      ext y
      simp only [Set.mem_setOf_eq]
      rw [p8a_B_iff h x0 y]
    rw [hset]
    exact (p8a_count h (fun α => (p8aSupp e x0 ∩ α).card % 2 = 0)).trans
      ((p8a_ncard_filter (fun α => α.card = 4 ∧ (p8aSupp e x0 ∩ α).card % 2 = 0)).trans
        (card_inter_even _ hcard0))
  have hG : {p : V | p ∈ S ∧ B (u * x0) p = 0}.ncard = 15 := h.count_perp x0 hx0S
  have hsub1 : {p : V | p ∈ S ∧ B u p = 0 ∧ B x0 p = 0} ⊆ {p : V | p ∈ S ∧ B x0 p = 0} :=
    fun p hp => ⟨hp.1, hp.2.2⟩
  have hsub2 : {p : V | p ∈ S ∧ B u p = 0 ∧ B x0 p = 0} ⊆
      {p : V | p ∈ S ∧ B (u * x0) p = 0} :=
    fun p hp => ⟨hp.1, by rw [h.symp.mul_left, hp.2.1, hp.2.2, add_zero]⟩
  have hdec : far B S u =
      ({p : V | p ∈ S ∧ B x0 p = 0} \ {p : V | p ∈ S ∧ B u p = 0 ∧ B x0 p = 0}) ∪
      ({p : V | p ∈ S ∧ B (u * x0) p = 0} \ {p : V | p ∈ S ∧ B u p = 0 ∧ B x0 p = 0}) := by
    ext p
    simp only [far, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hpS, hpu⟩
      rcases p8a_zmod2_cases (B x0 p) with h0 | h1
      · left
        refine ⟨⟨hpS, h0⟩, ?_⟩
        rintro ⟨-, h2, -⟩
        rw [hpu] at h2
        exact absurd h2 (by decide)
      · right
        refine ⟨⟨hpS, ?_⟩, ?_⟩
        · rw [h.symp.mul_left, hpu, h1]
          decide
        · rintro ⟨-, h2, -⟩
          rw [hpu] at h2
          exact absurd h2 (by decide)
    · rintro (⟨⟨hpS, h0⟩, hn⟩ | ⟨⟨hpS, h1⟩, hn⟩)
      · rcases p8a_zmod2_cases (B u p) with h2 | h2
        · exact absurd ⟨hpS, h2, h0⟩ hn
        · exact ⟨hpS, h2⟩
      · rw [h.symp.mul_left] at h1
        rcases p8a_zmod2_cases (B u p) with h2 | h2
        · exfalso
          apply hn
          refine ⟨hpS, h2, ?_⟩
          rw [h2, zero_add] at h1
          exact h1
        · exact ⟨hpS, h2⟩
  have hdisj : Disjoint ({p : V | p ∈ S ∧ B x0 p = 0} \ {p : V | p ∈ S ∧ B u p = 0 ∧ B x0 p = 0})
      ({p : V | p ∈ S ∧ B (u * x0) p = 0} \ {p : V | p ∈ S ∧ B u p = 0 ∧ B x0 p = 0}) := by
    rw [Set.disjoint_left]
    rintro p ⟨⟨hpS, h0⟩, hn⟩ ⟨⟨_, h1⟩, _⟩
    rw [h.symp.mul_left, h0, add_zero] at h1
    exact hn ⟨hpS, h1, h0⟩
  rw [hdec, Set.ncard_union_eq hdisj, Set.ncard_sdiff hsub1, Set.ncard_sdiff hsub2, hZ, hG,
    hG0]

private theorem p8b_z2 : ∀ c d : ZMod 2, c + d + d = c := by decide

private theorem p8b_z2_pair : ∀ c d f g : ZMod 2, c = d + f → c = d + g → f + g = 0 := by
  decide

private theorem p8b_wt_zero : wt6 0 = 0 := by decide

private theorem p8b_wt_one : wt6 (fun _ => 1) = 6 := by decide

private theorem p8b_wt_ind : ∀ α : Finset (Fin 6), wt6 (ind6 α) = α.card := by
  decide +kernel

private theorem p8b_four_sum : ∀ α : Finset (Fin 6), α.card = 4 → ∑ i, ind6 α i = 0 := by
  decide +kernel

private theorem p8b_add_eq_self : ∀ d f : ZMod 2, d = d + f → f = 0 := by decide

private theorem p8b_key : ∀ v : Fin 6 → ZMod 2, wt6 v = 3 → ∀ w : Fin 6 → ZMod 2, wt6 w = 3 →
    v ≠ w → v ≠ w + (fun _ => 1) →
    ∃ α : Finset (Fin 6), α.card = 4 ∧ dot6 v (ind6 α) = 0 ∧
      (v + ind6 α = w ∨ v + ind6 α = w + (fun _ => 1)) := by
  decide +kernel

private theorem p8b_rad6 : ∀ w : Fin 6 → ZMod 2,
    (∀ y : Fin 6 → ZMod 2, ∑ i, y i = 0 → dot6 w y = 0) → w = 0 ∨ w = fun _ => 1 := by
  decide +kernel

private theorem p8b_wt4_inj : ∀ v w : Fin 6 → ZMod 2, wt6 v = 4 → wt6 w = 4 →
    (v + w = 0 ∨ v + w = fun _ => 1) → v = w := by
  decide +kernel

private theorem p8b_dot_add_left (p q w : Fin 6 → ZMod 2) :
    dot6 (p + q) w = dot6 p w + dot6 q w := by
  simp [dot6, add_mul, Finset.sum_add_distrib]

private theorem p8b_dot_one_even (w : Fin 6 → ZMod 2) (hw : ∑ i, w i = 0) :
    dot6 (fun _ => 1) w = 0 := by
  simpa [dot6] using hw

private theorem p8b_B_u (h : Cfg9 B S A e u a) (x : A) : B u x = 0 := by
  have h1 := h.e_form ⟨u, h.mem⟩ x
  rw [h.e_u] at h1
  have hx : ∑ i, (e x).toAdd i = 0 := (h.e_range (e x)).mp (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hdot : dot6 (Multiplicative.ofAdd (fun _ => (1 : ZMod 2))).toAdd (e x).toAdd = 0 := by
    simpa [dot6] using hx
  exact h1.trans hdot

private theorem p8b_wt_of_S (h : Cfg9 B S A e u a) {x : A} (hx : (x : V) ∈ S) :
    wt6 (e x).toAdd = 4 := by
  obtain ⟨y, hy, hw⟩ := (h.perp_u (x : V)).mp ⟨hx, p8b_B_u h x⟩
  have hyx : y = x := Subtype.ext hy
  subst hyx
  exact hw

private theorem p8b_exists_four (h : Cfg9 B S A e u a) (α : Finset (Fin 6))
    (hα : α.card = 4) : ∃ x : A, (x : V) ∈ S ∧ (e x).toAdd = ind6 α := by
  obtain ⟨x, hx⟩ := (MonoidHom.mem_range).mp
    ((h.e_range (Multiplicative.ofAdd (ind6 α))).mpr (p8b_four_sum α hα))
  have hx' : (e x).toAdd = ind6 α := by rw [hx]; rfl
  have hw : wt6 (e x).toAdd = 4 := by rw [hx', p8b_wt_ind, hα]
  exact ⟨x, ((h.perp_u (x : V)).mpr ⟨x, rfl, hw⟩).1, hx'⟩

private theorem p8b_radical (h : Cfg9 B S A e u a) {x : A} (hx : ∀ y : A, B x y = 0) :
    (e x).toAdd = 0 ∨ (e x).toAdd = fun _ => 1 := by
  refine p8b_rad6 (e x).toAdd (fun y hy => ?_)
  obtain ⟨z, hz⟩ := (MonoidHom.mem_range).mp ((h.e_range (Multiplicative.ofAdd y)).mpr hy)
  have hBz := hx z
  rw [h.e_form x z, hz] at hBz
  exact hBz

private theorem p8b_self_mem {b : V} (hb : b ∈ far B S u) :
    b ∈ fibre B S A u b :=
  ⟨hb.1, hb.2, fun _ => rfl⟩

private theorem p8b_mul_fibre (h : Cfg9 B S A e u a) {b : V} {x : A} (hxS : (x : V) ∈ S)
    (hx : B x b = 0) {p : V} (hp : p ∈ fibre B S A u (b * x)) :
    p * x ∈ fibre B S A u b := by
  obtain ⟨hpS, hpu, hpy⟩ := hp
  have hpx : p ≠ (x : V) := by
    rintro rfl
    rw [p8b_B_u h x] at hpu
    exact zero_ne_one hpu
  have hbx : B b x = 0 := by
    rw [SympForm.symm h.symp b x]
    exact hx
  have hBpx : B p x = 0 := by
    rw [hpy x, h.symp.mul_left, h.symp.alt, hbx, add_zero]
  refine ⟨h.pointSet.mul_mem_of_orth p hpS x hxS hpx hBpx, ?_, fun y => ?_⟩
  · rw [h.symp.mul_right, hpu, p8b_B_u h x, add_zero]
  · rw [h.symp.mul_left, hpy y, h.symp.mul_left]
    exact p8b_z2 _ _

private theorem p8b_fibre_mul' (h : Cfg9 B S A e u a) {b : V} {x : A} (hxS : (x : V) ∈ S)
    (hx : B x b = 0) {q : V} (hq : q ∈ fibre B S A u b) :
    q * x ∈ fibre B S A u (b * x) := by
  obtain ⟨hqS, hqu, hqy⟩ := hq
  have hqx : q ≠ (x : V) := by
    rintro rfl
    rw [p8b_B_u h x] at hqu
    exact zero_ne_one hqu
  have hbx : B b x = 0 := by
    rw [SympForm.symm h.symp b x]
    exact hx
  have hBqx : B q x = 0 := by
    rw [hqy x, hbx]
  refine ⟨h.pointSet.mul_mem_of_orth q hqS x hxS hqx hBqx, ?_, fun y => ?_⟩
  · rw [h.symp.mul_right, hqu, p8b_B_u h x, add_zero]
  · rw [h.symp.mul_left, h.symp.mul_left, hqy y]

private theorem p8b_fibre_mul_eq (h : Cfg9 B S A e u a) {b : V} {x : A} (hxS : (x : V) ∈ S)
    (hx : B x b = 0) :
    fibre B S A u (b * x) = (fun p => p * (x : V)) '' fibre B S A u b := by
  ext p
  constructor
  · intro hp
    refine ⟨p * x, p8b_mul_fibre h hxS hx hp, ?_⟩
    show p * (x : V) * (x : V) = p
    rw [mul_assoc, h.symp.sq_eq_one, mul_one]
  · rintro ⟨q, hq, rfl⟩
    exact p8b_fibre_mul' h hxS hx hq

private theorem p8b_ncard_fibre_mul (h : Cfg9 B S A e u a) {b : V} {x : A} (hxS : (x : V) ∈ S)
    (hx : B x b = 0) :
    (fibre B S A u (b * x)).ncard = (fibre B S A u b).ncard := by
  rw [p8b_fibre_mul_eq h hxS hx, Set.ncard_image_of_injective _ (mul_left_injective (x : V))]

private theorem p8b_disj_self (h : Cfg9 B S A e u a) {b : V} {x : A} (hxS : (x : V) ∈ S)
    (hx : B x b = 0) : Disjoint (fibre B S A u b) (fibre B S A u (b * x)) := by
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨_, _, hpy⟩ := hp
  obtain ⟨_, _, hpy'⟩ := hp'
  have hxy : ∀ y : A, B x y = 0 := by
    intro y
    have h1 := hpy y
    have h2 := hpy' y
    rw [h.symp.mul_left] at h2
    exact p8b_add_eq_self _ _ (h1.symm.trans h2)
  have hw := p8b_wt_of_S h hxS
  rcases p8b_radical h hxy with h0 | h1
  · rw [h0, p8b_wt_zero] at hw
    exact absurd hw (by decide)
  · rw [h1, p8b_wt_one] at hw
    exact absurd hw (by decide)

private theorem p8b_disj_pair (h : Cfg9 B S A e u a) {b : V} {x x' : A}
    (hxS : (x : V) ∈ S) (hx'S : (x' : V) ∈ S) (hx : B x b = 0) (hx' : B x' b = 0)
    (hne : x ≠ x') :
    Disjoint (fibre B S A u (b * x)) (fibre B S A u (b * x')) := by
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨_, _, hpy⟩ := hp
  obtain ⟨_, _, hpy'⟩ := hp'
  have hxy : ∀ y : A, B ((x * x' : A) : V) y = 0 := by
    intro y
    have h1 := hpy y
    have h2 := hpy' y
    rw [h.symp.mul_left] at h1
    rw [h.symp.mul_left] at h2
    rw [show ((x * x' : A) : V) = (x : V) * (x' : V) from rfl, h.symp.mul_left]
    exact p8b_z2_pair _ _ _ _ h1 h2
  have hr := p8b_radical h hxy
  rw [map_mul, toAdd_mul] at hr
  have heq := p8b_wt4_inj _ _ (p8b_wt_of_S h hxS) (p8b_wt_of_S h hx'S) hr
  exact hne (h.e_inj (Multiplicative.toAdd.injective heq))

private theorem p8b_cover (h : Cfg9 B S A e u a) {b p : V} (hb : b ∈ far B S u)
    (hp : p ∈ far B S u) (hne : ¬ ∀ y : A, B p y = B b y) :
    ∃ x : A, (x : V) ∈ S ∧ B x b = 0 ∧ p ∈ fibre B S A u (b * x) := by
  obtain ⟨vb, hvb, hBb⟩ := wt_three_of_far h hb
  obtain ⟨vp, hvp, hBp⟩ := wt_three_of_far h hp
  have hne1 : vb ≠ vp := by
    intro heq
    apply hne
    intro y
    rw [hBp y, hBb y, heq]
  have hne2 : vb ≠ vp + (fun _ => 1) := by
    intro heq
    apply hne
    intro y
    have hy : ∑ i, (e y).toAdd i = 0 :=
      (h.e_range (e y)).mp (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
    rw [hBp y, hBb y, heq, p8b_dot_add_left, p8b_dot_one_even _ hy, add_zero]
  obtain ⟨α, hα4, hdot, hsum⟩ := p8b_key vb hvb vp hvp hne1 hne2
  obtain ⟨x, hxS, hxe⟩ := p8b_exists_four h α hα4
  have hBxb : B x b = 0 := by
    rw [SympForm.symm h.symp x b, hBb x, hxe]
    exact hdot
  refine ⟨x, hxS, hBxb, ?_⟩
  obtain ⟨hpS, hpu⟩ := hp
  refine ⟨hpS, hpu, fun y => ?_⟩
  have hy : ∑ i, (e y).toAdd i = 0 :=
    (h.e_range (e y)).mp (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
  rw [h.symp.mul_left, hBp y, hBb y, h.e_form x y, hxe]
  rcases hsum with hs | hs
  · rw [← hs, p8b_dot_add_left]
  · have hw : dot6 vp (e y).toAdd = dot6 (vp + (fun _ => 1)) (e y).toAdd := by
      rw [p8b_dot_add_left, p8b_dot_one_even _ hy, add_zero]
    rw [hw, ← hs, p8b_dot_add_left]

private theorem p8b_X_card (h : Cfg9 B S A e u a) {b : V} (hb : b ∈ far B S u) :
    {x : A | (x : V) ∈ S ∧ B x b = 0}.ncard = 9 := by
  have h1 := card_nbr_far h hb
  have h2 := h.pointSet.card_nbr b hb.1
  have h3 := a_eq_nine h
  omega

theorem card_fibre_eq_two (h : Cfg9 B S A e u a) {b : V} (hb : b ∈ far B S u) :
    (fibre B S A u b).ncard = 2 := by
  classical
  have hXc := p8b_X_card h hb
  have hT := card_far_eq h
  have hXs : ((Set.toFinite {x : A | (x : V) ∈ S ∧ B x b = 0}).toFinset).card = 9 := by
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    exact hXc
  have hFb : ((Set.toFinite (fibre B S A u b)).toFinset).card = (fibre B S A u b).ncard :=
    (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
  have hFt : ((Set.toFinite (far B S u)).toFinset).card = 20 := by
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    exact hT
  have hsplit : (Set.toFinite (far B S u)).toFinset =
      (Set.toFinite (fibre B S A u b)).toFinset ∪
        (Set.toFinite {x : A | (x : V) ∈ S ∧ B x b = 0}).toFinset.biUnion
          (fun x : A => (Set.toFinite (fibre B S A u (b * x))).toFinset) := by
    ext p
    simp only [Set.Finite.mem_toFinset, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · intro hp
      by_cases hpb : ∀ y : A, B p y = B b y
      · exact Or.inl ⟨hp.1, hp.2, hpb⟩
      · obtain ⟨x, hxS, hBxb, hpx⟩ := p8b_cover h hb hp hpb
        exact Or.inr ⟨x, ⟨hxS, hBxb⟩, hpx⟩
    · rintro (hp | ⟨x, _, hpx⟩)
      · exact ⟨hp.1, hp.2.1⟩
      · exact ⟨hpx.1, hpx.2.1⟩
  have hdisj : Disjoint (Set.toFinite (fibre B S A u b)).toFinset
      ((Set.toFinite {x : A | (x : V) ∈ S ∧ B x b = 0}).toFinset.biUnion
        (fun x : A => (Set.toFinite (fibre B S A u (b * x))).toFinset)) := by
    rw [Finset.disjoint_biUnion_right]
    intro x hx
    obtain ⟨hxS, hBx⟩ := (Set.Finite.mem_toFinset _).mp hx
    exact Set.Finite.disjoint_toFinset.mpr (p8b_disj_self h hxS hBx)
  have hpw : ((Set.toFinite {x : A | (x : V) ∈ S ∧ B x b = 0}).toFinset : Set A).PairwiseDisjoint
      (fun x : A => (Set.toFinite (fibre B S A u (b * x))).toFinset) := by
    intro x hx x' hx' hne
    obtain ⟨hxS, hBx⟩ := (Set.Finite.mem_toFinset _).mp (Finset.mem_coe.mp hx)
    obtain ⟨hx'S, hBx'⟩ := (Set.Finite.mem_toFinset _).mp (Finset.mem_coe.mp hx')
    exact Set.Finite.disjoint_toFinset.mpr (p8b_disj_pair h hxS hx'S hBx hBx' hne)
  have hFf : ∀ x ∈ (Set.toFinite {x : A | (x : V) ∈ S ∧ B x b = 0}).toFinset,
      ((Set.toFinite (fibre B S A u (b * x))).toFinset).card = (fibre B S A u b).ncard := by
    intro x hx
    obtain ⟨hxS, hBx⟩ := (Set.Finite.mem_toFinset _).mp hx
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    exact p8b_ncard_fibre_mul h hxS hBx
  have hbi : ((Set.toFinite {x : A | (x : V) ∈ S ∧ B x b = 0}).toFinset.biUnion
        (fun x : A => (Set.toFinite (fibre B S A u (b * x))).toFinset)).card
      = 9 * (fibre B S A u b).ncard := by
    rw [Finset.card_biUnion hpw, Finset.sum_congr rfl hFf, Finset.sum_const, hXs, smul_eq_mul]
  have hu := Finset.card_union_of_disjoint hdisj
  rw [← hsplit, hFt, hFb, hbi] at hu
  omega

private theorem p8b_two_elems {s : Set V} (hs : s.ncard = 2) {x y z w : V}
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hw : w ∈ s) (hxy : x ≠ y) (hzw : z ≠ w) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  obtain ⟨p, q, hpq, rfl⟩ := Set.ncard_eq_two.mp hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz hw
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;> simp_all

private theorem p8b_fibre_eq_of_mem {p q : V} (hq : q ∈ fibre B S A u p) :
    fibre B S A u q = fibre B S A u p := by
  obtain ⟨_, _, hqy⟩ := hq
  ext r
  simp only [fibre, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun y => (h3 y).trans (hqy y)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun y => (h3 y).trans (hqy y).symm⟩

private theorem p8b_partner (h : Cfg9 B S A e u a) {b : V} (hb : b ∈ far B S u) :
    ∃ c, c ∈ fibre B S A u b ∧ c ≠ b := by
  obtain ⟨p, q, hpq, hs⟩ := Set.ncard_eq_two.mp (card_fibre_eq_two h hb)
  have hbmem : b ∈ fibre B S A u b := p8b_self_mem hb
  rw [hs] at hbmem
  rcases hbmem with h1 | h1
  · refine ⟨q, ?_, ?_⟩
    · rw [hs]; simp
    · rw [h1]; exact hpq.symm
  · refine ⟨p, ?_, ?_⟩
    · rw [hs]; simp
    · rw [h1]; exact hpq

private theorem p8b_far_mul (h : Cfg9 B S A e u a) {b : V} (hb : b ∈ far B S u) {x : A}
    (hxS : (x : V) ∈ S) (hx : B x b = 0) : b * x ∈ far B S u := by
  have hbx : b ≠ (x : V) := by
    intro hbx
    have h1 := hb.2
    rw [hbx, p8b_B_u h x] at h1
    exact zero_ne_one h1
  have hbx' : B b x = 0 := by
    rw [SympForm.symm h.symp b x]
    exact hx
  refine ⟨h.pointSet.mul_mem_of_orth b hb.1 x hxS hbx hbx', ?_⟩
  rw [h.symp.mul_right, hb.2, p8b_B_u h x, add_zero]

theorem exists_const_prod (h : Cfg9 B S A e u a) :
    ∃ f : V, ∀ b ∈ far B S u, ∃ b' ∈ fibre B S A u b, b' ≠ b ∧ b * b' = f := by
  obtain ⟨b₀, hb₀⟩ := exists_far h
  obtain ⟨c₀, hc₀, hc₀ne⟩ := p8b_partner h hb₀
  have key : ∀ b ∈ far B S u, ∀ c ∈ fibre B S A u b, c ≠ b → b * c = b₀ * c₀ := by
    intro b hb c hc hcb
    by_cases hfun : ∀ y : A, B b y = B b₀ y
    · have hfb : fibre B S A u b = fibre B S A u b₀ :=
        p8b_fibre_eq_of_mem (show b ∈ fibre B S A u b₀ from ⟨hb.1, hb.2, hfun⟩)
      have hc' : c ∈ fibre B S A u b₀ := by rw [← hfb]; exact hc
      have hb' : b ∈ fibre B S A u b₀ := by rw [← hfb]; exact p8b_self_mem hb
      rcases p8b_two_elems (card_fibre_eq_two h hb₀) hb' hc' (p8b_self_mem hb₀) hc₀
          hcb.symm hc₀ne.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, mul_comm]
    · obtain ⟨x, hxS, hBx, hbx⟩ := p8b_cover h hb₀ hb hfun
      have hfb : fibre B S A u b = fibre B S A u (b₀ * x) :=
        p8b_fibre_eq_of_mem hbx
      have hc' : c ∈ fibre B S A u (b₀ * x) := by rw [← hfb]; exact hc
      have hc₀x : c₀ * x ∈ fibre B S A u (b₀ * x) := p8b_fibre_mul' h hxS hBx hc₀
      have hb₀x : b₀ * x ∈ fibre B S A u (b₀ * x) :=
        p8b_self_mem (p8b_far_mul h hb₀ hxS hBx)
      have hcard : (fibre B S A u (b₀ * x)).ncard = 2 := by
        rw [p8b_ncard_fibre_mul h hxS hBx]
        exact card_fibre_eq_two h hb₀
      have hne12 : b₀ * x ≠ c₀ * x := fun h' => hc₀ne (mul_right_cancel h').symm
      rcases p8b_two_elems hcard hbx hc' hb₀x hc₀x hcb.symm hne12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, mul_mul_mul_comm, h.symp.sq_eq_one, mul_one]
      · rw [h1, h2, mul_mul_mul_comm, h.symp.sq_eq_one, mul_one, mul_comm]
  refine ⟨b₀ * c₀, fun b hb => ?_⟩
  obtain ⟨c, hc, hcb⟩ := p8b_partner h hb
  exact ⟨c, hc, hcb, key b hb c hc hcb⟩

private theorem p8b_z2_one : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

private theorem p8b_mem_two {s : Set V} (hs : s.ncard = 2) {x y p : V} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) (hp : p ∈ s) : p = x ∨ p = y := by
  obtain ⟨q, r, hqr, rfl⟩ := Set.ncard_eq_two.mp hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hp
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hp with rfl | rfl <;> simp_all

private theorem p8b_card_A (h : Cfg9 B S A e u a) : Nat.card A ≤ 32 := by
  have hmem : ∀ x : A, ∑ i, (e x).toAdd i = 0 := fun x =>
    (h.e_range (e x)).mp (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hinj : Function.Injective
      (fun x : A => (⟨(e x).toAdd, hmem x⟩ : {w : Fin 6 → ZMod 2 // ∑ i, w i = 0})) := by
    intro x y hxy
    have h1 : (e x).toAdd = (e y).toAdd := congrArg Subtype.val hxy
    exact h.e_inj (Multiplicative.toAdd.injective h1)
  have h32 : Nat.card {w : Fin 6 → ZMod 2 // ∑ i, w i = 0} = 32 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  have := Nat.card_le_card_of_injective _ hinj
  omega

private theorem p8b_far_mem_sup (h : Cfg9 B S A e u a) {b₀ f c₀ : V} (hb₀ : b₀ ∈ far B S u)
    (hc₀ : c₀ ∈ fibre B S A u b₀) (hc₀ne : c₀ ≠ b₀) (hf₀ : b₀ * c₀ = f) {p : V}
    (hp : p ∈ far B S u) :
    p ∈ A ⊔ Subgroup.closure ({b₀, f} : Set V) := by
  have hbC : b₀ ∈ Subgroup.closure ({b₀, f} : Set V) := Subgroup.subset_closure (by simp)
  have hfC : f ∈ Subgroup.closure ({b₀, f} : Set V) := Subgroup.subset_closure (by simp)
  have hc₀eq : c₀ = b₀ * f := by rw [← hf₀, ← mul_assoc, h.symp.sq_eq_one, one_mul]
  have hc₀C : c₀ ∈ Subgroup.closure ({b₀, f} : Set V) := hc₀eq ▸ mul_mem hbC hfC
  by_cases hfun : ∀ y : A, B p y = B b₀ y
  · have hpfib : p ∈ fibre B S A u b₀ := ⟨hp.1, hp.2, hfun⟩
    rcases p8b_mem_two (card_fibre_eq_two h hb₀) (p8b_self_mem hb₀) hc₀ (Ne.symm hc₀ne)
      hpfib with h1 | h1
    · rw [h1]; exact Subgroup.mem_sup_right hbC
    · rw [h1]; exact Subgroup.mem_sup_right hc₀C
  · obtain ⟨z, hzS, hBz, hpz⟩ := p8b_cover h hb₀ hp hfun
    have hcard : (fibre B S A u (b₀ * z)).ncard = 2 := by
      rw [p8b_ncard_fibre_mul h hzS hBz]
      exact card_fibre_eq_two h hb₀
    have hb₀z : b₀ * z ∈ fibre B S A u (b₀ * z) :=
      p8b_self_mem (p8b_far_mul h hb₀ hzS hBz)
    have hc₀z : c₀ * z ∈ fibre B S A u (b₀ * z) := p8b_fibre_mul' h hzS hBz hc₀
    have hne : b₀ * z ≠ c₀ * z := fun h' => hc₀ne (mul_right_cancel h').symm
    rcases p8b_mem_two hcard hb₀z hc₀z hne hpz with h1 | h1
    · rw [h1, mul_comm]; exact Subgroup.mul_mem_sup z.2 hbC
    · rw [h1, mul_comm]; exact Subgroup.mul_mem_sup z.2 hc₀C

theorem card_le_128 (h : Cfg9 B S A e u a) : Nat.card V ≤ 128 := by
  obtain ⟨b₀, hb₀⟩ := exists_far h
  obtain ⟨f, hf⟩ := exists_const_prod h
  obtain ⟨c₀, hc₀, hc₀ne, hf₀⟩ := hf b₀ hb₀
  have hK : Subgroup.closure S ≤ A ⊔ Subgroup.closure ({b₀, f} : Set V) := by
    rw [Subgroup.closure_le]
    intro p hp
    by_cases hu : B u p = 0
    · obtain ⟨z, hz, _⟩ := (h.perp_u p).mp ⟨hp, hu⟩
      rw [← hz]
      exact Subgroup.mem_sup_left z.2
    · exact p8b_far_mem_sup h hb₀ hc₀ hc₀ne hf₀ ⟨hp, p8b_z2_one _ hu⟩
  have htop : A ⊔ Subgroup.closure ({b₀, f} : Set V) = ⊤ := top_le_iff.mp (h.gen ▸ hK)
  have hA : Nat.card A ≤ 32 := p8b_card_A h
  have hCc : Nat.card (Subgroup.closure ({b₀, f} : Set V)) ≤ 4 := by
    classical
    have h2 := natCard_closure_le h.symp.sq_eq_one ({b₀, f} : Finset V)
    have h3 : ({b₀, f} : Finset V).card ≤ 2 := Finset.card_le_two
    rw [Finset.coe_insert, Finset.coe_singleton] at h2
    have h4 : 2 ^ ({b₀, f} : Finset V).card ≤ 2 ^ 2 := Nat.pow_le_pow_right two_pos h3
    have h5 : (2 : ℕ) ^ 2 = 4 := rfl
    omega
  have hprod : Nat.card (A ⊔ Subgroup.closure ({b₀, f} : Set V) : Subgroup V) ≤
      Nat.card A * Nat.card (Subgroup.closure ({b₀, f} : Set V)) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_surjective
      (fun p : A × Subgroup.closure ({b₀, f} : Set V) =>
        (⟨(p.1 : V) * (p.2 : V), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ :
          (A ⊔ Subgroup.closure ({b₀, f} : Set V) : Subgroup V))) ?_
    rintro ⟨v, hv⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hv
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), Subtype.ext hyz⟩
  calc Nat.card V = Nat.card (A ⊔ Subgroup.closure ({b₀, f} : Set V) : Subgroup V) := by
        rw [htop, Subgroup.card_top]
    _ ≤ Nat.card A * Nat.card (Subgroup.closure ({b₀, f} : Set V)) := hprod
    _ ≤ 32 * 4 := Nat.mul_le_mul hA hCc
    _ = 128 := rfl

private theorem p8b_z2_eq : ∀ c d : ZMod 2, c + d = 0 → c = d := by decide

private theorem p8b_z2_dup : ∀ c : ZMod 2, c + c = 0 := by decide

private theorem p8b_z2_self : ∀ c : ZMod 2, c = c + c → c = 0 := by decide

private theorem p8b_sum_rad : ∀ z : Fin 6 → ZMod 2, (z = 0 ∨ z = fun _ => 1) →
    ∑ i, z i = 0 := by
  decide +kernel

private theorem p8b_W_card :
    (Finset.univ.filter (fun w : Fin 6 → ZMod 2 => ∑ i, w i = 0 ∧ w 0 = 0)).card = 16 := by
  decide +kernel

private theorem p8b_wt3_sum : ∀ v : Fin 6 → ZMod 2, wt6 v = 3 → ∑ i, v i = 1 := by
  decide +kernel

private theorem p8b_sum3 (v₁ v₂ v₃ : Fin 6 → ZMod 2) :
    ∑ i, (v₁ + v₂ + v₃) i = ∑ i, v₁ i + ∑ i, v₂ i + ∑ i, v₃ i := by
  simp [Finset.sum_add_distrib]

private theorem p8b_one_ne_zero : (fun _ : Fin 6 => (1 : ZMod 2)) ≠ 0 := by decide

private theorem p8b_u_ne_one (h : Cfg9 B S A e u a) : u ≠ 1 := by
  intro h1
  have h2 := h.e_u
  have h3 : (⟨u, h.mem⟩ : A) = 1 := Subtype.ext h1
  rw [h3, map_one] at h2
  have h4 := congrArg Multiplicative.toAdd h2
  have h5 : (0 : Fin 6 → ZMod 2) = fun _ => 1 := h4
  exact p8b_one_ne_zero h5.symm

private theorem p8b_B_one (h : Cfg9 B S A e u a) (y : A) : B 1 y = 0 := by
  have h1 := h.symp.mul_left 1 1 (y : V)
  rw [mul_one] at h1
  exact p8b_z2_self _ h1

private theorem p8b_rad_A (h : Cfg9 B S A e u a) {z : Fin 6 → ZMod 2}
    (hz : ∀ y : A, dot6 z (e y).toAdd = 0) : z = 0 ∨ z = fun _ => 1 := by
  refine p8b_rad6 z (fun y' hy' => ?_)
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ((h.e_range (Multiplicative.ofAdd y')).mpr hy')
  have hzx := hz x
  rw [hx] at hzx
  exact hzx

private theorem p8b_parity (h : Cfg9 B S A e u a) {b₀ : V} (hb₀ : b₀ ∈ far B S u) {x x' : A}
    {r r' : V} (hr : ∀ y : A, B r y = 0) (hr' : ∀ y : A, B r' y = 0)
    (heq : b₀ * (x : V) * r = (x' : V) * r') : False := by
  obtain ⟨v₀, hv₀, hBb⟩ := wt_three_of_far h hb₀
  have hsum : ∀ x : A, ∑ i, (e x).toAdd i = 0 := fun x =>
    (h.e_range (e x)).mp (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hz : ∀ y : A, dot6 (v₀ + (e x).toAdd + (e x').toAdd) (e y).toAdd = 0 := by
    intro y
    have h1 : B (b₀ * (x : V) * r) (y : V) = B ((x' : V) * r') (y : V) := by rw [heq]
    have e1 : B (b₀ * (x : V) * r) (y : V) = B b₀ y + B x y + B r y := by
      rw [h.symp.mul_left, h.symp.mul_left]
    have e2 : B ((x' : V) * r') (y : V) = B x' y + B r' y := h.symp.mul_left _ _ _
    rw [e1, e2, hr y, hr' y, add_zero, add_zero] at h1
    rw [p8b_dot_add_left, p8b_dot_add_left, ← hBb y, ← h.e_form x y, ← h.e_form x' y]
    rw [h1]
    exact p8b_z2_dup _
  have hs := p8b_sum_rad _ (p8b_rad_A h hz)
  rw [p8b_sum3, p8b_wt3_sum v₀ hv₀, hsum x, hsum x'] at hs
  exact absurd hs (by decide)

private theorem p8b_cancel_A (h : Cfg9 B S A e u a) {x x' : A} {r r' : V}
    (hr : ∀ y : A, B r y = 0) (hr' : ∀ y : A, B r' y = 0)
    (hx0 : (e x).toAdd 0 = 0) (hx0' : (e x').toAdd 0 = 0)
    (heq : (x : V) * r = (x' : V) * r') : x = x' ∧ r = r' := by
  have hz : ∀ y : A, B ((x * x' : A) : V) (y : V) = 0 := by
    intro y
    have k : B ((x : V) * r) (y : V) = B ((x' : V) * r') (y : V) := by rw [heq]
    rw [h.symp.mul_left, h.symp.mul_left, hr y, hr' y, add_zero, add_zero] at k
    show B ((x : V) * (x' : V)) (y : V) = 0
    rw [h.symp.mul_left, k]
    exact p8b_z2_dup _
  have hr0 := p8b_radical h hz
  rw [map_mul, toAdd_mul] at hr0
  rcases hr0 with h0 | h1
  · have hxx : (e x).toAdd = (e x').toAdd := by
      funext i
      have hi := congrFun h0 i
      simp only [Pi.add_apply, Pi.zero_apply] at hi
      exact p8b_z2_eq _ _ hi
    have hex : x = x' := h.e_inj (Multiplicative.toAdd.injective hxx)
    subst hex
    exact ⟨rfl, mul_left_cancel heq⟩
  · exfalso
    have hi := congrFun h1 0
    simp only [Pi.add_apply] at hi
    rw [hx0, hx0'] at hi
    exact absurd hi (by decide)

private theorem p8b_natCard_le_64 (h : Cfg9 B S A e u a) : Nat.card V ≤ 64 := by
  obtain ⟨m, hm⟩ := SympForm.exists_natCard_eq_four_pow h.symp
  have h128 := card_le_128 h
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · calc Nat.card V = 4 ^ m := hm
      _ ≤ 4 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 64 := rfl
  · have h256 : 4 ^ 4 ≤ 4 ^ m := Nat.pow_le_pow_right (by decide) hm4
    rw [← hm] at h256
    have e256 : (4 : ℕ) ^ 4 = 256 := rfl
    rw [e256] at h256
    omega

private theorem p8b_inj_triple (h : Cfg9 B S A e u a) {b₀ : V} (hb₀ : b₀ ∈ far B S u)
    {ε ε' : Bool} {x x' : A} {r r' : V}
    (hx0 : (e x).toAdd 0 = 0) (hx0' : (e x').toAdd 0 = 0)
    (hr : ∀ y : A, B r y = 0) (hr' : ∀ y : A, B r' y = 0)
    (heq : (if ε then b₀ else 1) * (x : V) * r = (if ε' then b₀ else 1) * (x' : V) * r') :
    ε = ε' ∧ x = x' ∧ r = r' := by
  rcases ε with _ | _ <;> rcases ε' with _ | _
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at heq
    obtain ⟨h2, h3⟩ := p8b_cancel_A h hr hr' hx0 hx0' heq
    exact ⟨rfl, h2, h3⟩
  · exfalso
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at heq
    exact p8b_parity h hb₀ hr' hr heq.symm
  · exfalso
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at heq
    exact p8b_parity h hb₀ hr hr' heq
  · simp only [↓reduceIte] at heq
    have h1 : b₀ * ((x : V) * r) = b₀ * ((x' : V) * r') := by
      rw [← mul_assoc, ← mul_assoc]
      exact heq
    obtain ⟨h2, h3⟩ := p8b_cancel_A h hr hr' hx0 hx0' (mul_left_cancel h1)
    exact ⟨rfl, h2, h3⟩

open scoped Classical in
private theorem p8b_R_card [Fintype V] (h : Cfg9 B S A e u a) {b₀ : V}
    (hb₀ : b₀ ∈ far B S u) :
    (Finset.univ.filter (fun r : V => ∀ y : A, B r y = 0)).card ≤ 2 := by
  have hV : Fintype.card V ≤ 64 := by
    rw [← Nat.card_eq_fintype_card]
    exact p8b_natCard_le_64 h
  have hlift : ∀ w : Fin 6 → ZMod 2, ∃ x : A, ∑ i, w i = 0 → e x = Multiplicative.ofAdd w := by
    intro w
    by_cases hw : ∑ i, w i = 0
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ((h.e_range (Multiplicative.ofAdd w)).mpr hw)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨1, fun h' => absurd h' hw⟩
  choose g hg using hlift
  set W : Finset (Fin 6 → ZMod 2) :=
    Finset.univ.filter (fun w => ∑ i, w i = 0 ∧ w 0 = 0) with hWdef
  set R : Finset V := Finset.univ.filter (fun r : V => ∀ y : A, B r y = 0) with hRdef
  set F : Bool × (Fin 6 → ZMod 2) × V → V :=
    fun p => (if p.1 then b₀ else 1) * (g p.2.1 : V) * p.2.2 with hF
  have hmem : ∀ p ∈ (Finset.univ : Finset Bool) ×ˢ (W ×ˢ R), F p ∈ (Finset.univ : Finset V) :=
    fun p _ => Finset.mem_univ _
  have hinj : Set.InjOn F ↑((Finset.univ : Finset Bool) ×ˢ (W ×ˢ R)) := by
    rintro ⟨ε, w, r⟩ hp ⟨ε', w', r'⟩ hq hpq
    have hp' := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_product.mp (Finset.mem_coe.mp hq)
    obtain ⟨hw, hr⟩ := Finset.mem_product.mp hp'.2
    obtain ⟨hw', hr'⟩ := Finset.mem_product.mp hq'.2
    have hw0 := (Finset.mem_filter.mp hw).2
    have hw0' := (Finset.mem_filter.mp hw').2
    have hr0 := (Finset.mem_filter.mp hr).2
    have hr0' := (Finset.mem_filter.mp hr').2
    have heq : (if ε then b₀ else 1) * (g w : V) * r =
        (if ε' then b₀ else 1) * (g w' : V) * r' := hpq
    have hx0 : (e (g w)).toAdd 0 = 0 := by
      rw [hg w hw0.1]
      exact hw0.2
    have hx0' : (e (g w')).toAdd 0 = 0 := by
      rw [hg w' hw0'.1]
      exact hw0'.2
    obtain ⟨hε, hgg, hrr⟩ := p8b_inj_triple h hb₀ hx0 hx0' hr0 hr0' heq
    have hww : w = w' := by
      have hee := congrArg e hgg
      rw [hg w hw0.1, hg w' hw0'.1] at hee
      exact Multiplicative.ofAdd.injective hee
    have hrr' : r = r' := hrr
    subst hε
    subst hww
    subst hrr'
    rfl
  have hcard := Finset.card_le_card_of_injOn F hmem hinj
  have hWc : W.card = 16 := p8b_W_card
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool, hWc] at hcard
  omega

theorem ker_le (h : Cfg9 B S A e u a) :
    ∀ x : V, (∀ y : A, B x y = 0) → x = 1 ∨ x = u := by
  classical
  intro x hx
  haveI : Fintype V := Fintype.ofFinite V
  obtain ⟨b₀, hb₀⟩ := exists_far h
  have hR := p8b_R_card h hb₀
  by_contra hcon
  push_neg at hcon
  have h3 : 2 < (Finset.univ.filter (fun r : V => ∀ y : A, B r y = 0)).card := by
    rw [Finset.two_lt_card_iff]
    refine ⟨1, x, u, ?_, ?_, ?_, ?_, ?_, hcon.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y => p8b_B_one h y⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y => p8b_B_u h y⟩
    · exact fun h' => hcon.1 h'.symm
    · exact fun h' => p8b_u_ne_one h h'.symm
  omega

end Cfg9

end CFSG.ClassicalInvolution.Q3.Sec13.Polar
