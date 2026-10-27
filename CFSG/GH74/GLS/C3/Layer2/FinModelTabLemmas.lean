module

public import CFSG.GH74.GLS.C3.Layer2.FinModelClaim
public import CFSG.GH74.GLS.C3.Layer2.FinModelCard

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

structure Tab.Valid {n : ℕ} [NeZero n] (t : Tab n) : Prop where
  el_mem : ∀ i, t.el.get i ∈ Tl n
  el_surj : ∀ g ∈ Tl n, ∃ i, t.el.get i = g
  el_inj : ∀ i j, t.el.get i = t.el.get j → i = j
  mul_spec : ∀ i j, t.el.get (t.mulT i j) = t.el.get i * t.el.get j
  one_spec : t.el.get t.one = 1
  inv_spec : ∀ i, t.el.get (t.inv.get i) = (t.el.get i)⁻¹
  x0_spec : t.el.get t.x0i = x0 n
  words_spec : ∀ i, evalW t.mulT t.one t.gens.get (t.words.get i) = i
  rep_spec : ∀ i j, t.isInv i = true → t.isInv j = true → t.cls.get i = t.cls.get j →
    t.rep.get i = t.rep.get j
  cls_spec : ∀ j, t.isInv j = true →
    ∃ σ : Perm (Fin n), σ * (t.el.get (t.rep.get j)).1 * σ⁻¹ = (t.el.get j).1 ∧
      ∃ d ∈ Dl, d * (t.el.get (t.rep.get j)).2 * d⁻¹ = (t.el.get j).2 ∧ sign σ = sign d
  isQ_spec : ∀ i, t.isQ.get i = true ↔ (t.el.get i).1 = 1
  nm_spec : ∀ i, t.nm.get i = numMoved (emb n (t.el.get i))
  astar_spec : ∀ i, a0perm n * emb n (t.el.get i) * (a0perm n)⁻¹ =
    emb n (t.el.get (t.astar.get i))
  o3_complete : ∀ σ : Perm (Fin n), σ ≠ 1 → σ * σ * σ = 1 → σ ∈ t.o3
  o3_sound : ∀ σ ∈ t.o3, σ ≠ 1 ∧ σ * σ * σ = 1
  useW_spec : t.useW = true ↔ n = 7

theorem imp_eq_true {p q : Bool} : imp p q = true ↔ (p = true → q = true) := by
  cases p <;> simp [imp]

theorem Tab.valid_of_validB {n : ℕ} [NeZero n] (t : Tab n) (h : t.validB = true) : t.Valid := by
  simp only [Tab.validB, Tab.checks, List.all_cons, List.all_nil, Bool.and_eq_true, id,
    Bool.and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [List.all_eq_true] using h1
  · simpa [List.all_eq_true] using h2
  · simpa [List.all_eq_true, imp_eq_true] using h3
  · simpa [List.all_eq_true] using h4
  · simpa using h5
  · simpa [List.all_eq_true] using h6
  · simpa using h7
  · simpa [List.all_eq_true] using h8
  · simpa [List.all_eq_true, imp_eq_true] using h9
  · simpa [List.all_eq_true, imp_eq_true] using h10
  · intro i
    have h := (by simpa [List.all_eq_true] using h11 :
      ∀ i, t.isQ.get i = decide ((t.el.get i).1 = 1)) i
    rw [h]; exact decide_eq_true_iff
  · simpa [List.all_eq_true] using h12
  · simpa [List.all_eq_true] using h13
  · simpa using h14
  · simpa [List.all_eq_true] using h15
  · rw [(by simpa using h16 : t.useW = decide (n = 7))]; exact decide_eq_true_iff

theorem vget_ofFn {α : Type*} {m : ℕ} (f : Fin m → α) (i : Fin m) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]
  rfl

theorem vec_ext {α : Type*} {m : ℕ} {a b : Vector α m} (h : ∀ i : Fin m, a.get i = b.get i) :
    a = b := Vector.ext fun i hi => h ⟨i, hi⟩

namespace Tab

variable {n : ℕ} [NeZero n]

@[expose] def iT
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (i : Fin 64) : T0 n :=
  ⟨t.el.get i, (mem_T0_iff n hn _).2 (hv.el_mem i)⟩

theorem iT_coe
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (i : Fin 64) :
    ((t.iT hn hv i : T0 n) : Amb n) = t.el.get i := rfl

theorem iT_injective
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) :
    Function.Injective (t.iT hn hv) := fun i j h => hv.el_inj i j (congrArg Subtype.val h)

theorem iT_surjective
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) :
    Function.Surjective (t.iT hn hv) := by
  intro x
  obtain ⟨i, hi⟩ := hv.el_surj x.1 ((mem_T0_iff n hn x.1).1 x.2)
  exact ⟨i, Subtype.ext hi⟩

theorem iT_mul
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (i j : Fin 64) :
    t.iT hn hv (t.mulT i j) = t.iT hn hv i * t.iT hn hv j := Subtype.ext (hv.mul_spec i j)

theorem iT_one
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) : t.iT hn hv t.one = 1 :=
  Subtype.ext hv.one_spec

theorem iT_inv
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (i : Fin 64) :
    t.iT hn hv (t.inv.get i) = (t.iT hn hv i)⁻¹ := Subtype.ext (hv.inv_spec i)

theorem iT_x0
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) : t.iT hn hv t.x0i = x0T n :=
  Subtype.ext hv.x0_spec

@[expose] noncomputable def eT
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) : Fin 64 ≃ T0 n :=
  Equiv.ofBijective (t.iT hn hv) ⟨t.iT_injective hn hv, t.iT_surjective hn hv⟩

theorem eT_apply
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (i : Fin 64) :
    t.eT hn hv i = t.iT hn hv i := rfl

noncomputable def tabOf
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (α : T0 n ≃* T0 n) :
    Tbl :=
  Vector.ofFn fun i => (t.eT hn hv).symm (α (t.iT hn hv i))

theorem iT_tabOf
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (α : T0 n ≃* T0 n)
    (i : Fin 64) : t.iT hn hv ((t.tabOf hn hv α).get i) = α (t.iT hn hv i) := by
  simp only [tabOf, vget_ofFn]
  exact (t.eT hn hv).apply_symm_apply _

structure IsAutT (t : Tab n) (a : Tbl) : Prop where
  one : a.get t.one = t.one
  hom : ∀ i j, a.get (t.mulT i j) = t.mulT (a.get i) (a.get j)
  inj : ∀ i j, a.get i = a.get j → i = j

theorem isAutB_iff (t : Tab n) (a : Tbl) : t.isAutB a = true ↔ t.IsAutT a := by
  simp only [isAutB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    true_implies, imp_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun i j => h2 i j, fun i j h => h3 i j h⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, fun i j => h2 i j⟩, fun i j h => h3 i j h⟩

theorem tabOf_isAut
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (α : T0 n ≃* T0 n) :
    t.IsAutT (t.tabOf hn hv α) := by
  refine ⟨?_, ?_, ?_⟩
  · apply t.iT_injective hn hv
    rw [iT_tabOf, iT_one, map_one]
  · intro i j
    apply t.iT_injective hn hv
    rw [iT_tabOf, iT_mul, map_mul, iT_mul, iT_tabOf, iT_tabOf]
  · intro i j h
    apply t.iT_injective hn hv
    have := congrArg (t.iT hn hv) h
    rw [iT_tabOf, iT_tabOf] at this
    exact α.injective this

theorem IsAutT.evalW {t : Tab n} {a : Tbl} (h : t.IsAutT a) (g : Fin 4 → Fin 64)
    (w : List (Fin 4)) :
    a.get (Model.evalW t.mulT t.one g w) = Model.evalW t.mulT t.one (fun k => a.get (g k)) w := by
  induction w with
  | nil => simp [Model.evalW, h.one]
  | cons k w ih => simp [Model.evalW, h.hom, ih]

theorem IsAutT.eq_ofImages {t : Tab n} {a : Tbl} (hv : t.Valid) (h : t.IsAutT a) :
    a = t.ofImages (fun k => a.get (t.gens.get k)) := by
  apply vec_ext
  intro i
  simp only [ofImages, vget_ofFn]
  conv_lhs => rw [← hv.words_spec i]
  exact h.evalW _ _

theorem IsAutT.cls3_eq {t : Tab n} {a : Tbl} (h : t.IsAutT a) (i : Fin 64) :
    t.cls3 (a.get i) = t.cls3 i := by
  have h1 : a.get i = t.one ↔ i = t.one :=
    ⟨fun e => h.inj _ _ (e.trans h.one.symm), fun e => by rw [e, h.one]⟩
  have h2 : t.mulT (a.get i) (a.get i) = t.one ↔ t.mulT i i = t.one := by
    rw [← h.hom]
    exact ⟨fun e => h.inj _ _ (e.trans h.one.symm), fun e => by rw [e, h.one]⟩
  simp only [cls3, h1, h2]

theorem IsAutT.pairOK {t : Tab n} {a : Tbl} (h : t.IsAutT a) (x y : Fin 64) :
    t.pairOK (a.get x) (a.get y) x y = true := by
  simp only [Tab.pairOK, Bool.and_eq_true, beq_iff_eq]
  rw [← h.hom, ← h.hom, h.cls3_eq, h.cls3_eq]
  exact ⟨rfl, rfl⟩

theorem isAutB_of_mem_autsOf (t : Tab n) {ψ : Tbl} (hψ : ψ ∈ t.autsOf) : t.isAutB ψ = true := by
  simp only [autsOf, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_finRange,
    true_and] at hψ
  obtain ⟨h0, -, h1, -, h2, -, h3, ⟨-, hh⟩, rfl⟩ := hψ
  exact hh

theorem claim_apply (t : Tab n) (hc : t.claimB = true) {h0 h1 h2 h3 : Fin 64}
    (o0 : t.ok0 h0 = true) (o1 : t.ok1 h0 h1 = true) (o2 : t.ok2 h0 h1 h2 = true)
    (o3 : t.ok3 h0 h1 h2 h3 = true) (ha : t.isAutB (t.ofImages ![h0, h1, h2, h3]) = true) :
    t.finalB t.autsOf (t.ofImages ![h0, h1, h2, h3]) = true := by
  simp only [claimB, List.all_eq_true, List.mem_finRange, true_implies, imp_eq_true] at hc
  exact hc h0 o0 h1 o1 h2 o2 h3 o3 ha

theorem certB_spec (t : Tab n) {a : Tbl} {X0 V0 : Vector Bool 64} {s : Fin 64} {ψ : Tbl}
    (h : t.certB a X0 V0 s ψ = true) :
    ψ.get t.x0i = t.x0i ∧
    (∀ i, ψ.get (t.mulT (t.mulT s (a.get i)) (t.inv.get s)) = t.astar.get (ψ.get i)) ∧
    (∀ i, t.isInv i = true → (X0.get i = true → t.nm.get (ψ.get i) = 4) ∧
      (V0.get i = true → t.nm.get (ψ.get i) = 8)) := by
  simp only [certB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    true_implies, imp_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, fun i hi => ⟨fun hx => (h3 i hi).1 hx, fun hv => (h3 i hi).2 hv⟩⟩

theorem step_sound
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (a : Tbl) (X : Set (T0 n))
    (hcl : ∀ i j, t.edge a i j = true → t.iT hn hv i ∈ X → t.iT hn hv j ∈ X)
    (S : Vector Bool 64) (hS : ∀ i, S.get i = true → t.iT hn hv i ∈ X) :
    ∀ j, (t.step a S).get j = true → t.iT hn hv j ∈ X := by
  intro j hj
  simp only [step, vget_ofFn, Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true] at hj
  rcases hj with hj | ⟨i, hi, hedge⟩
  · exact hS j hj
  · exact hcl i j hedge (hS i hi)

theorem reach_sound
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (a : Tbl) (X : Set (T0 n))
    (hcl : ∀ i j, t.edge a i j = true → t.iT hn hv i ∈ X → t.iT hn hv j ∈ X)
    (s0 : Fin 64) (hs0 : t.iT hn hv s0 ∈ X) :
    ∀ j, (t.reach a s0).get j = true → t.iT hn hv j ∈ X := by
  have key : ∀ k : ℕ, ∀ j, ((t.step a)^[k] (Vector.ofFn fun j => j == s0)).get j = true →
      t.iT hn hv j ∈ X := by
    intro k
    induction k with
    | zero =>
      intro j hj
      simp only [Function.iterate_zero, id, vget_ofFn, beq_iff_eq] at hj
      subst hj
      exact hs0
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact step_sound t hn hv a X hcl _ ih
  exact key 12

theorem orderOf_iT_of_isInv
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) {i : Fin 64}
    (hi : t.isInv i = true) : orderOf (t.iT hn hv i) = 2 := by
  simp only [isInv, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hi
  obtain ⟨h1, h2⟩ := hi
  apply orderOf_eq_prime
  · rw [pow_two, ← iT_mul, h2, iT_one]
  · intro h
    apply h1
    apply t.iT_injective hn hv
    rw [iT_one]; exact h

theorem isInv_of_orderOf
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) {x : T0 n}
    (hx : orderOf x = 2) : t.isInv ((t.eT hn hv).symm x) = true := by
  have hx1 : x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx; omega
  have hx2 : x * x = 1 := by rw [← pow_two]; rw [← hx]; exact pow_orderOf_eq_one x
  simp only [isInv, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  constructor
  · intro h
    apply hx1
    have := congrArg (t.eT hn hv) h
    rw [Equiv.apply_symm_apply, eT_apply, iT_one] at this
    exact this
  · apply t.iT_injective hn hv
    rw [iT_mul, iT_one, ← eT_apply, Equiv.apply_symm_apply, hx2]

theorem exists_conj (t : Tab n) (hv : t.Valid) {i j : Fin 64}
    (hi : t.isInv i = true) (hj : t.isInv j = true) (hc : t.cls.get i = t.cls.get j) :
    ∃ g ∈ Fgrp n, g * t.el.get i * g⁻¹ = t.el.get j := by
  have hr : t.rep.get i = t.rep.get j := hv.rep_spec i j hi hj hc
  obtain ⟨σ₁, hσ₁, d₁, hd₁, hd₁', hs₁⟩ := hv.cls_spec i hi
  obtain ⟨σ₂, hσ₂, d₂, hd₂, hd₂', hs₂⟩ := hv.cls_spec j hj
  rw [hr] at hσ₁ hd₁'
  have hg₁ : ((σ₁, d₁) : Amb n) ∈ Fgrp n := ⟨(Dl_spec d₁).2 hd₁, hs₁⟩
  have hg₂ : ((σ₂, d₂) : Amb n) ∈ Fgrp n := ⟨(Dl_spec d₂).2 hd₂, hs₂⟩
  refine ⟨(σ₂, d₂) * (σ₁, d₁)⁻¹, mul_mem hg₂ (inv_mem hg₁), ?_⟩
  apply Prod.ext
  · show σ₂ * σ₁⁻¹ * (t.el.get i).1 * (σ₂ * σ₁⁻¹)⁻¹ = (t.el.get j).1
    rw [← hσ₁, ← hσ₂]
    group
  · show d₂ * d₁⁻¹ * (t.el.get i).2 * (d₂ * d₁⁻¹)⁻¹ = (t.el.get j).2
    rw [← hd₁', ← hd₂']
    group

theorem edge_closed
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (α : T0 n ≃* T0 n)
    (X : Set (T0 n))
    (hcl : ∀ s t' : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t' : Amb n)) ∨ t' = α s) → s ∈ X → t' ∈ X) :
    ∀ i j, t.edge (t.tabOf hn hv α) i j = true → t.iT hn hv i ∈ X → t.iT hn hv j ∈ X := by
  intro i j hedge hi
  simp only [edge, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hedge
  obtain ⟨⟨hii, hij⟩, hcase⟩ := hedge
  refine hcl _ _ (orderOf_iT_of_isInv t hn hv hii) ?_ hi
  rcases hcase with hc | hc
  · left
    obtain ⟨g, hg, hgc⟩ := exists_conj t hv hii hij hc
    exact ⟨g, hg, hgc⟩
  · right
    rw [← hc, iT_tabOf]

theorem all_not_and {x y : Fin 64 → Bool} (h : ∀ i, x i = true → y i = true → False) :
    (List.finRange 64).all (fun i => !(x i && y i)) = true := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies]
  intro i
  cases hx : x i <;> cases hy : y i <;> simp_all

theorem all_imp {x y : Fin 64 → Bool} (h : ∀ i, x i = true → y i = true) :
    (List.finRange 64).all (fun i => imp (x i) (y i)) = true := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, imp_eq_true]
  exact h

theorem final_unpack (t : Tab n) {L : List Tbl} {a : Tbl} (h : t.finalB L a = true)
    (hx : a.get t.x0i ≠ t.x0i) (u : Fin 64) (hu : a.get u = u)
    (hsq : ∀ i, a.get (a.get i) = t.mulT (t.mulT u i) (t.inv.get u))
    (hdisj : ∀ i, (t.reach a t.x0i).get i = true →
      (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = true → False)
    (hQ : ∀ i, t.isQ.get i = true → i ≠ t.one →
      (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = false)
    (hW : t.wB a = true) :
    (∀ i, t.isInv i = true → (t.reach a t.x0i).get i = true ∨
      (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = true) ∧
    ∃ s, t.mulT (t.mulT s (a.get s)) u = t.one ∧ ∃ ψ ∈ L,
      t.certB a (t.reach a t.x0i) (t.reach a (t.mulT t.x0i (a.get t.x0i))) s ψ = true := by
  unfold finalB at h
  have e1 : (a.get t.x0i != t.x0i) = true := bne_iff_ne.2 hx
  have h1 := (imp_eq_true.1 h) e1
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h1
  have e2 : (a.get u == u && (List.finRange 64).all fun i =>
      a.get (a.get i) == t.mulT (t.mulT u i) (t.inv.get u)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange, true_implies]
    exact ⟨hu, hsq⟩
  have h2 := (imp_eq_true.1 (h1 u)) e2
  have e3 := all_not_and hdisj
  have h3 := (imp_eq_true.1 h2) e3
  have e4 : ((List.finRange 64).all fun i => imp (t.isQ.get i && i != t.one)
      (!(t.reach a (t.mulT t.x0i (a.get t.x0i))).get i)) = true := by
    apply all_imp
    intro i hi
    simp only [Bool.and_eq_true, bne_iff_ne] at hi
    simp [hQ i hi.1 hi.2]
  have h4 := (imp_eq_true.1 h3) e4
  have h5 := (imp_eq_true.1 h4) hW
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, imp_eq_true,
    List.any_eq_true, beq_iff_eq] at h5
  obtain ⟨hcov, s, -, hs, hψ⟩ := h5
  refine ⟨fun i hi => ?_, s, hs, ?_⟩
  · have := hcov i hi
    simpa [Bool.or_eq_true] using this
  · simpa [List.any_eq_true] using hψ

theorem eq_one_of_pow_three {d : Perm (Fin 4)} (hd : d * x4 = x4 * d) (h3 : d * d * d = 1) :
    d = 1 := by
  have hmem : d ∈ Subgroup.centralizer ({x4} : Set (Perm (Fin 4))) :=
    Subgroup.mem_centralizer_singleton_iff.2 hd
  have h1 : orderOf (⟨d, hmem⟩ : Subgroup.centralizer ({x4} : Set (Perm (Fin 4)))) ∣ 8 := by
    rw [← card_centralizer_x4]; exact orderOf_dvd_natCard _
  have h2 : orderOf (⟨d, hmem⟩ : Subgroup.centralizer ({x4} : Set (Perm (Fin 4)))) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [pow_succ, mul_assoc] using h3
  have h3' : orderOf (⟨d, hmem⟩ : Subgroup.centralizer ({x4} : Set (Perm (Fin 4)))) = 1 := by
    have := Nat.dvd_gcd h1 h2
    simpa using this
  rw [orderOf_eq_one_iff] at h3'
  exact congrArg Subtype.val h3'

theorem sign_eq_one_of_pow_three {m : ℕ} {σ : Perm (Fin m)} (h : σ * σ * σ = 1) : sign σ = 1 := by
  have h' : sign σ * sign σ * sign σ = 1 := by rw [← map_mul, ← map_mul, h, map_one]
  rcases Int.units_eq_one_or (sign σ) with h1 | h1
  · exact h1
  · rw [h1] at h'; exact absurd h' (by decide)

theorem wB_of_ext
    (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid) (α : T0 n ≃* T0 n)
    (hext : n = 7 →
      ∃ β : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)) ≃* ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)),
        ∀ (x : T0 n) (hx : (x : Amb n) ∈ Hgrp n ((α (x0T n) : T0 n) : Amb n)),
          ((β ⟨(x : Amb n), hx⟩ : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n))) : Amb n) =
            ((α x : T0 n) : Amb n)) :
    t.wB (t.tabOf hn hv α) = true := by
  by_cases hW : t.useW = true
  swap
  · simp [wB, hW]
  have h7 : n = 7 := hv.useW_spec.1 hW
  have hz : t.el.get ((t.tabOf hn hv α).get t.x0i) = ((α (x0T n) : T0 n) : Amb n) := by
    rw [← iT_coe t hn hv, iT_tabOf, iT_x0]
  simp only [wB, hW, Bool.not_true, Bool.false_or, hz]
  set z : Amb n := ((α (x0T n) : T0 n) : Amb n) with hzdef
  obtain ⟨β, hβ⟩ := hext h7
  set O : List (Perm (Fin n)) := t.o3.filter fun σ => decide (σ * z.1 = z.1 * σ) with hO
  rw [Bool.or_eq_true]
  by_cases hemp : O.isEmpty = true
  · exact Or.inl hemp
  right
  have hne : O ≠ [] := by
    intro h; rw [h] at hemp; simp at hemp
  obtain ⟨σ, hσ⟩ := List.exists_mem_of_ne_nil O hne
  simp only [hO, List.mem_filter, decide_eq_true_eq] at hσ
  obtain ⟨hσo, hσz⟩ := hσ
  obtain ⟨hσ1, hσ3⟩ := hv.o3_sound σ hσo
  have hwF : ((σ, 1) : Amb n) ∈ Fgrp n := ⟨by simp, by simpa using sign_eq_one_of_pow_three hσ3⟩
  have hwz : ((σ, 1) : Amb n) * z = z * (σ, 1) := Prod.ext hσz (by simp)
  have hwH : ((σ, 1) : Amb n) ∈ Hgrp n z :=
    ⟨hwF, Subgroup.mem_centralizer_singleton_iff.2 hwz⟩
  have hww : (⟨(σ, 1), hwH⟩ : ↥(Hgrp n z)) * ⟨(σ, 1), hwH⟩ * ⟨(σ, 1), hwH⟩ = 1 := by
    apply Subtype.ext
    show ((σ, 1) : Amb n) * (σ, 1) * (σ, 1) = 1
    apply Prod.ext
    · show σ * σ * σ = 1
      exact hσ3
    · show (1 : Perm (Fin 4)) * 1 * 1 = 1
      simp
  obtain ⟨w, hwdef⟩ : ∃ w : ↥(Hgrp n z), w = ⟨(σ, 1), hwH⟩ := ⟨_, rfl⟩
  rw [← hwdef] at hww
  set w' : Amb n := ((β w : ↥(Hgrp n z)) : Amb n) with hw'
  have hw'H : w' ∈ Hgrp n z := (β w).2
  have hw'3 : w' * w' * w' = 1 := by
    have : β w * β w * β w = 1 := by
      rw [← map_mul, ← map_mul, hww, map_one]
    exact congrArg Subtype.val this
  have hw'1 : w' ≠ 1 := by
    intro h
    have h1 : β w = 1 := Subtype.ext h
    have h2 : w = 1 := by
      apply β.injective
      rw [h1, map_one]
    have h3 := congrArg (fun x : ↥(Hgrp n z) => (x : Amb n).1) h2
    rw [hwdef] at h3
    exact hσ1 h3
  have hd1 : w'.2 = 1 := by
    apply eq_one_of_pow_three hw'H.1.1
    have := congrArg Prod.snd hw'3
    simpa using this
  have hσ'3 : w'.1 * w'.1 * w'.1 = 1 := by
    have := congrArg Prod.fst hw'3
    simpa using this
  have hσ'1 : w'.1 ≠ 1 := by
    intro h
    apply hw'1
    exact Prod.ext h hd1
  have hσ'z : w'.1 * z.1 = z.1 * w'.1 := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hw'H.2
    exact congrArg Prod.fst this
  have hσ'O : w'.1 ∈ O := by
    simp only [hO, List.mem_filter, decide_eq_true_eq]
    exact ⟨hv.o3_complete _ hσ'1 hσ'3, hσ'z⟩
  rw [List.any_eq_true]
  refine ⟨w'.1, hσ'O, ?_⟩
  simp only [List.all_eq_true, List.mem_finRange, true_implies, imp_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  rintro q ⟨hq, hqz⟩
  have hq1 : (t.el.get q).1 = 1 := (hv.isQ_spec q).1 hq
  set x : T0 n := t.iT hn hv q with hx
  have hxc : (x : Amb n) = t.el.get q := rfl
  have hxH : (x : Amb n) ∈ Hgrp n z :=
    ⟨T0_le_Fgrp n x.2, Subgroup.mem_centralizer_singleton_iff.2 (by rw [hxc]; exact hqz)⟩
  have hcomm : (⟨(x : Amb n), hxH⟩ : ↥(Hgrp n z)) * w = w * ⟨(x : Amb n), hxH⟩ := by
    rw [hwdef]
    apply Subtype.ext
    show (x : Amb n) * (σ, 1) = (σ, 1) * (x : Amb n)
    apply Prod.ext
    · show (x : Amb n).1 * σ = σ * (x : Amb n).1
      rw [hxc, hq1]; simp
    · simp
  have h1 := congrArg (fun y : ↥(Hgrp n z) => (β y : Amb n)) hcomm
  simp only [map_mul, Subgroup.coe_mul] at h1
  rw [hβ x hxH] at h1
  have h2 := congrArg Prod.fst h1
  have hαx : ((α x : T0 n) : Amb n) = t.el.get ((t.tabOf hn hv α).get q) := by
    rw [← iT_tabOf t hn hv α q]; rfl
  rw [hαx] at h2
  exact h2

end Tab

end CFSG.GH74.GLS.C3.Layer2.Model
