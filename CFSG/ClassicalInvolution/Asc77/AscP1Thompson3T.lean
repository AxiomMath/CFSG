module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.ClassicalInvolution.Asc77.Star3T

variable {Q : Type*} [Group Q]

structure IsTT (Δ : Set Q) : Prop where
  mul_self : ∀ d ∈ Δ, d * d = 1
  ne_one : ∀ d ∈ Δ, d ≠ 1
  conj_mem : ∀ d ∈ Δ, ∀ g : Q, g * d * g⁻¹ ∈ Δ
  closure_eq_top : Subgroup.closure Δ = ⊤
  comm_or_cube : ∀ a ∈ Δ, ∀ b ∈ Δ, a * b = b * a ∨ (a * b) ^ 3 = 1

@[expose] def IsStar (Δ : Set Q) : Prop :=
  ∀ a ∈ Δ, ∀ b ∈ Δ, a * b ≠ b * a → ∀ c ∈ Δ,
    c * a = a * c ∨ c * b = b * c ∨ c * (a * b * a) = (a * b * a) * c

@[expose] def Adj (Δ : Set Q) (x y : Q) : Prop := x ∈ Δ ∧ y ∈ Δ ∧ x * y = y * x

@[expose] def Conn (Δ : Set Q) : Q → Q → Prop := Relation.ReflTransGen (Adj Δ)

@[expose] def cent (Δ : Set Q) (x : Q) : Set Q := {y | y ∈ Δ ∧ y * x = x * y}

structure IsPlane (Δ : Set Q) (p q r : Q) : Prop where
  mem_left : p ∈ Δ
  mem_right : q ∈ Δ
  not_conn : ¬ Conn Δ p q
  eq_third : r = p * q * p

variable {Δ : Set Q}

theorem Adj.symm {x y : Q} (h : Adj Δ x y) : Adj Δ y x := ⟨h.2.1, h.1, h.2.2.symm⟩

theorem Conn.symm {x y : Q} (h : Conn Δ x y) : Conn Δ y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (Adj.symm hbc) ih

theorem Conn.trans {x y z : Q} (h : Conn Δ x y) (h' : Conn Δ y z) : Conn Δ x z :=
  Relation.ReflTransGen.trans h h'

theorem conn_of_commute {x y : Q} (hx : x ∈ Δ) (hy : y ∈ Δ) (hxy : x * y = y * x) :
    Conn Δ x y :=
  Relation.ReflTransGen.single ⟨hx, hy, hxy⟩

theorem self_mem_cent {x : Q} (hx : x ∈ Δ) : x ∈ cent Δ x := ⟨hx, rfl⟩

theorem conn_of_mem_cent {x y : Q} (hx : x ∈ Δ) (hy : y ∈ cent Δ x) : Conn Δ x y :=
  conn_of_commute hx hy.1 hy.2.symm

theorem IsPlane.noncomm {p q r : Q} (hpl : IsPlane Δ p q r) : p * q ≠ q * p :=
  fun e => hpl.not_conn (conn_of_commute hpl.mem_left hpl.mem_right e)

theorem disjoint_cent {p q : Q} (hp : p ∈ Δ) (hq : q ∈ Δ) (hpq : ¬ Conn Δ p q) :
    Disjoint (cent Δ p) (cent Δ q) :=
  Set.disjoint_left.mpr fun _ hxp hxq =>
    hpq ((conn_of_mem_cent hp hxp).trans (conn_of_mem_cent hq hxq).symm)

theorem commute_mul_mul {x u v : Q} (hu : x * u = u * x) (hv : x * v = v * x) :
    x * (u * v * u) = (u * v * u) * x := by
  calc x * (u * v * u) = (x * u) * v * u := by simp only [mul_assoc]
    _ = u * (x * v) * u := by rw [hu]; simp only [mul_assoc]
    _ = u * (v * x) * u := by rw [hv]
    _ = u * v * (x * u) := by simp only [mul_assoc]
    _ = u * v * (u * x) := by rw [hu]
    _ = (u * v * u) * x := by simp only [mul_assoc]

namespace IsTT

theorem inv_eq (h : IsTT Δ) {x : Q} (hx : x ∈ Δ) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_left (h.mul_self x hx)

theorem conj_mem' (h : IsTT Δ) {x : Q} (hx : x ∈ Δ) (g : Q) : g * x * g⁻¹ ∈ Δ :=
  h.conj_mem x hx g

theorem mul_mul_mem (h : IsTT Δ) {x y : Q} (hx : x ∈ Δ) (hy : y ∈ Δ) : x * y * x ∈ Δ := by
  have := h.conj_mem y hy x
  rwa [h.inv_eq hx] at this

theorem braid (h : IsTT Δ) {x y : Q} (hx : x ∈ Δ) (hy : y ∈ Δ) (hxy : x * y ≠ y * x) :
    x * y * x = y * x * y := by
  rcases h.comm_or_cube x hx y hy with h1 | h3
  · exact absurd h1 hxy
  · have h6 : x * y * x * (y * x * y) = 1 := by
      have : (x * y) ^ 3 = x * y * x * (y * x * y) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [← this]
      exact h3
    have h7 := eq_inv_of_mul_eq_one_left h6
    rw [h7]
    simp only [mul_inv_rev, h.inv_eq hx, h.inv_eq hy, mul_assoc]

theorem mul_mul_self_of_commute (h : IsTT Δ) {x y : Q} (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hxy : x * y = y * x) : (x * y) * (x * y) = 1 := by
  calc (x * y) * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
    _ = x * (x * y) * y := by rw [← hxy]
    _ = (x * x) * (y * y) := by simp only [mul_assoc]
    _ = 1 := by rw [h.mul_self x hx, h.mul_self y hy, one_mul]

theorem cube_of_noncomm (h : IsTT Δ) {x y : Q} (hx : x ∈ Δ) (hy : y ∈ Δ) (hxy : x * y ≠ y * x) :
    (x * y) ^ 3 = 1 := by
  rcases h.comm_or_cube x hx y hy with h1 | h3
  · exact absurd h1 hxy
  · exact h3

theorem conn_conj (h : IsTT Δ) {x y : Q} (hxy : Conn Δ x y) (g : Q) :
    Conn Δ (g * x * g⁻¹) (g * y * g⁻¹) := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    refine ih.tail ⟨h.conj_mem' hbc.1 g, h.conj_mem' hbc.2.1 g, ?_⟩
    have hbc' : b * c = c * b := hbc.2.2
    calc g * b * g⁻¹ * (g * c * g⁻¹) = g * (b * c) * g⁻¹ := by group
      _ = g * (c * b) * g⁻¹ := by rw [hbc']
      _ = g * c * g⁻¹ * (g * b * g⁻¹) := by group

theorem isPlane_swap (h : IsTT Δ) {p q r : Q} (hpl : IsPlane Δ p q r) : IsPlane Δ q p r :=
  ⟨hpl.mem_right, hpl.mem_left, fun hc => hpl.not_conn hc.symm, by
    rw [hpl.eq_third]; exact h.braid hpl.mem_left hpl.mem_right hpl.noncomm⟩

theorem mem_third (h : IsTT Δ) {p q r : Q} (hpl : IsPlane Δ p q r) : r ∈ Δ :=
  hpl.eq_third ▸ h.mul_mul_mem hpl.mem_left hpl.mem_right

theorem isPlane_rot (h : IsTT Δ) {p q r : Q} (hpl : IsPlane Δ p q r) : IsPlane Δ p r q := by
  have hr : r ∈ Δ := h.mem_third hpl
  have hpp := h.mul_self p hpl.mem_left
  have hq : q = p * r * p := by
    rw [hpl.eq_third]
    calc q = (p * p) * q * (p * p) := by rw [hpp, one_mul, mul_one]
      _ = p * (p * q * p) * p := by simp only [mul_assoc]
  refine ⟨hpl.mem_left, hr, fun hc => hpl.not_conn ?_, hq⟩
  have := h.conn_conj hc p
  have h1 : p * p * p = p := by rw [hpp, one_mul]
  rw [h.inv_eq hpl.mem_left, h1, ← hq] at this
  exact this

theorem not_conn_third_left (h : IsTT Δ) {p q r : Q} (hpl : IsPlane Δ p q r) :
    ¬ Conn Δ p r := (h.isPlane_rot hpl).not_conn

theorem not_conn_third_right (h : IsTT Δ) {p q r : Q} (hpl : IsPlane Δ p q r) :
    ¬ Conn Δ q r := (h.isPlane_rot (h.isPlane_swap hpl)).not_conn

theorem isClique_cent (h : IsTT Δ) (hS : IsStar Δ) {p q : Q} (hp : p ∈ Δ) (hq : q ∈ Δ)
    (hpq : ¬ Conn Δ p q) {u v : Q} (hu : u ∈ cent Δ p) (hv : v ∈ cent Δ p) :
    u * v = v * u := by
  by_contra huv
  rcases hS u hu.1 v hv.1 huv q hq with h1 | h2 | h3
  · exact hpq ((conn_of_mem_cent hp hu).trans (conn_of_commute hu.1 hq h1.symm))
  · exact hpq ((conn_of_mem_cent hp hv).trans (conn_of_commute hv.1 hq h2.symm))
  · have hw : u * v * u ∈ Δ := h.mul_mul_mem hu.1 hv.1
    have hwp : u * v * u ∈ cent Δ p :=
      ⟨hw, (commute_mul_mul hu.2.symm hv.2.symm).symm⟩
    exact hpq ((conn_of_mem_cent hp hwp).trans (conn_of_commute hw hq h3.symm))

theorem cent_conj_mem (h : IsTT Δ) (hS : IsStar Δ) {p q r : Q} (hpl : IsPlane Δ p q r) {x y : Q}
    (hx : x ∈ cent Δ p) (hy : y ∈ cent Δ q) : x * y * x ∈ cent Δ r := by
  have hp := hpl.mem_left
  have hq := hpl.mem_right
  have hxy : x * y ≠ y * x := fun e =>
    hpl.not_conn ((conn_of_mem_cent hp hx).trans
      ((conn_of_commute hx.1 hy.1 e).trans (conn_of_mem_cent hq hy).symm))
  have hw : x * y * x ∈ Δ := h.mul_mul_mem hx.1 hy.1
  have hxx := h.mul_self x hx.1
  have hyy := h.mul_self y hy.1
  have hxx' : ∀ w : Q, x * (x * w) = w := fun w => by rw [← mul_assoc, hxx, one_mul]
  have hyy' : ∀ w : Q, y * (y * w) = w := fun w => by rw [← mul_assoc, hyy, one_mul]
  have e1 : x * (x * y * x) * x = y := by
    calc x * (x * y * x) * x = (x * x) * y * (x * x) := by simp only [mul_assoc]
      _ = y := by rw [hxx, one_mul, mul_one]
  refine ⟨hw, ?_⟩
  rcases hS p hp q hq hpl.noncomm _ hw with h1 | h2 | h3
  ·
    exfalso
    have e2 : x * p * x = p := by
      calc x * p * x = (p * x) * x := by rw [hx.2]
        _ = p := by simp only [mul_assoc, hxx, mul_one]
    have hy' : y * p = p * y := by
      calc y * p = (x * (x * y * x) * x) * (x * p * x) := by rw [e1, e2]
        _ = x * ((x * y * x) * p) * x := by simp only [mul_assoc, hxx, hxx', mul_one]
        _ = x * (p * (x * y * x)) * x := by rw [h1]
        _ = (x * p * x) * (x * (x * y * x) * x) := by simp only [mul_assoc, hxx, hxx', mul_one]
        _ = p * y := by rw [e1, e2]
    exact hpl.not_conn ((conn_of_mem_cent hp ⟨hy.1, hy'⟩).trans (conn_of_mem_cent hq hy).symm)
  ·
    exfalso
    have hyx3 : (y * x) ^ 3 = 1 := h.cube_of_noncomm hy.1 hx.1 (fun e => hxy e.symm)
    have h6 : y * x * y * x * y * x = 1 := by
      have : (y * x) ^ 3 = y * x * y * x * y * x := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [← this]; exact hyx3
    have hxe : x = y * (x * y * x) * y := by
      have h7 : y * x * y * x * y = x⁻¹ :=
        eq_inv_of_mul_eq_one_left (by simpa only [mul_assoc] using h6)
      rw [h.inv_eq hx.1] at h7
      calc x = y * x * y * x * y := h7.symm
        _ = y * (x * y * x) * y := by simp only [mul_assoc]
    have hxq : x * q = q * x := by
      calc x * q = (y * (x * y * x) * y) * q := by rw [← hxe]
        _ = y * (x * y * x) * (y * q) := by simp only [mul_assoc]
        _ = y * (x * y * x) * (q * y) := by rw [hy.2]
        _ = y * ((x * y * x) * q) * y := by simp only [mul_assoc]
        _ = y * (q * (x * y * x)) * y := by rw [h2]
        _ = (y * q) * (x * y * x) * y := by simp only [mul_assoc]
        _ = (q * y) * (x * y * x) * y := by rw [hy.2]
        _ = q * (y * (x * y * x) * y) := by simp only [mul_assoc]
        _ = q * x := by rw [← hxe]
    exact hpl.not_conn ((conn_of_mem_cent hp hx).trans (conn_of_mem_cent hq ⟨hx.1, hxq⟩).symm)
  · rw [hpl.eq_third]; exact h3

theorem cent_union_eq (hS : IsStar Δ) {p q r : Q} (hpl : IsPlane Δ p q r) :
    Δ = cent Δ p ∪ cent Δ q ∪ cent Δ r := by
  ext c
  constructor
  · intro hc
    rcases hS p hpl.mem_left q hpl.mem_right hpl.noncomm c hc with h1 | h2 | h3
    · exact Or.inl (Or.inl ⟨hc, h1⟩)
    · exact Or.inl (Or.inr ⟨hc, h2⟩)
    · exact Or.inr ⟨hc, by rw [hpl.eq_third]; exact h3⟩
  · rintro ((hc | hc) | hc) <;> exact hc.1

theorem cent_eq_image (h : IsTT Δ) (hS : IsStar Δ) {p q r : Q} (hpl : IsPlane Δ p q r) :
    cent Δ r = (fun x => p * x * p) '' cent Δ q := by
  have hpp := h.mul_self p hpl.mem_left
  ext z
  constructor
  · intro hz
    refine ⟨p * z * p, h.cent_conj_mem hS (h.isPlane_rot hpl) (self_mem_cent hpl.mem_left) hz, ?_⟩
    show p * (p * z * p) * p = z
    calc p * (p * z * p) * p = (p * p) * z * (p * p) := by simp only [mul_assoc]
      _ = z := by rw [hpp, one_mul, mul_one]
  · rintro ⟨y, hy, rfl⟩
    exact h.cent_conj_mem hS hpl (self_mem_cent hpl.mem_left) hy

theorem ncard_cent_eq (h : IsTT Δ) (hS : IsStar Δ) {p q r : Q} (hpl : IsPlane Δ p q r) :
    (cent Δ r).ncard = (cent Δ q).ncard := by
  have hpp := h.mul_self p hpl.mem_left
  rw [h.cent_eq_image hS hpl]
  refine Set.ncard_image_of_injective _ fun x y hxy => ?_
  have hxy' : p * x * p = p * y * p := hxy
  have := mul_right_cancel hxy'
  exact mul_left_cancel this

theorem closure_insert_cent_eq_top (h : IsTT Δ) (hS : IsStar Δ) {p q r : Q}
    (hpl : IsPlane Δ p q r) : Subgroup.closure (insert q (cent Δ p)) = ⊤ := by
  set H := Subgroup.closure (insert q (cent Δ p)) with hH
  have hpp := h.mul_self p hpl.mem_left
  have hqq := h.mul_self q hpl.mem_right
  have hcp : cent Δ p ⊆ H := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have hqH : q ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hpH : p ∈ H := hcp (self_mem_cent hpl.mem_left)
  have hr : cent Δ r ⊆ H := by
    intro z hz
    have hpl' : IsPlane Δ q r p := h.isPlane_rot (h.isPlane_swap hpl)
    have h1 : q * z * q ∈ cent Δ p :=
      h.cent_conj_mem hS hpl' (self_mem_cent hpl.mem_right) hz
    have h2 : z = q * (q * z * q) * q := by
      calc z = (q * q) * z * (q * q) := by rw [hqq, one_mul, mul_one]
        _ = q * (q * z * q) * q := by simp only [mul_assoc]
    rw [h2]
    exact H.mul_mem (H.mul_mem hqH (hcp h1)) hqH
  have hqc : cent Δ q ⊆ H := by
    intro c hc
    have h1 : p * c * p ∈ cent Δ r := h.cent_conj_mem hS hpl (self_mem_cent hpl.mem_left) hc
    have h2 : c = p * (p * c * p) * p := by
      calc c = (p * p) * c * (p * p) := by rw [hpp, one_mul, mul_one]
        _ = p * (p * c * p) * p := by simp only [mul_assoc]
    rw [h2]
    exact H.mul_mem (H.mul_mem hpH (hr h1)) hpH
  rw [eq_top_iff, ← h.closure_eq_top, Subgroup.closure_le]
  intro x hx
  rw [cent_union_eq hS hpl] at hx
  rcases hx with (hx | hx) | hx
  · exact hcp hx
  · exact hqc hx
  · exact hr hx

theorem exists_conj_of_not_conn (h : IsTT Δ) {d a : Q} (hd : d ∈ Δ) (ha : a ∈ Δ)
    (hc : ¬ Conn Δ d a) : ∀ y ∈ Δ, ∃ g : Q, y = g * d * g⁻¹ := by
  let O : Set Q := {x | ∃ g : Q, x = g * d * g⁻¹}
  have hOΔ : ∀ x ∈ O, x ∈ Δ := by
    rintro x ⟨g, rfl⟩
    exact h.conj_mem' hd g
  have key : ∀ x ∈ O, ∀ y ∈ Δ, y ∉ O → x * y = y * x := by
    intro x hx y hy hyO
    by_contra hne
    have hxΔ := hOΔ x hx
    have hb := h.braid hxΔ hy hne
    obtain ⟨g, hg⟩ := hx
    apply hyO
    have hy' := h.inv_eq hy
    have hx' := h.inv_eq hxΔ
    have hxx := h.mul_self x hxΔ
    refine ⟨x * y * g, ?_⟩
    calc y = x * (x * y * x) * x := by
          calc y = (x * x) * y * (x * x) := by rw [hxx, one_mul, mul_one]
            _ = x * (x * y * x) * x := by simp only [mul_assoc]
      _ = x * (y * x * y) * x := by rw [hb]
      _ = x * y * (g * d * g⁻¹) * y * x := by rw [← hg]; simp only [mul_assoc]
      _ = (x * y * g) * d * (x * y * g)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, hx', hy']; simp only [mul_assoc]
  intro y hy
  by_contra hyO
  have hyO' : y ∉ O := hyO
  have hdO : d ∈ O := ⟨1, by simp⟩
  have haO : a ∈ O := by
    by_contra haO
    exact hc (conn_of_commute hd ha (key d hdO a ha haO))
  exact hc ((conn_of_commute hd hy (key d hdO y hy hyO')).trans
    (conn_of_commute hy ha (key a haO y hy hyO').symm))

theorem conjugatesOf_eq (h : IsTT Δ) {d a : Q} (hd : d ∈ Δ) (ha : a ∈ Δ) (hc : ¬ Conn Δ d a) :
    conjugatesOf d = Δ := by
  ext y
  constructor
  · intro hy
    obtain ⟨c, hc'⟩ := isConj_iff.mp hy
    rw [← hc']
    exact h.conj_mem' hd c
  · intro hy
    obtain ⟨g, hg⟩ := h.exists_conj_of_not_conn hd ha hc y hy
    exact isConj_iff.mpr ⟨g, hg.symm⟩

theorem ncard_eq_three_mul [Finite Q] (h : IsTT Δ) (hS : IsStar Δ) {p q r : Q}
    (hpl : IsPlane Δ p q r) : Δ.ncard = 3 * (cent Δ p).ncard := by
  have hU := cent_union_eq hS hpl
  have hdisj1 : Disjoint (cent Δ p) (cent Δ q) :=
    disjoint_cent hpl.mem_left hpl.mem_right hpl.not_conn
  have hr : r ∈ Δ := h.mem_third hpl
  have hdisj2 : Disjoint (cent Δ p) (cent Δ r) :=
    disjoint_cent hpl.mem_left hr (h.not_conn_third_left hpl)
  have hdisj3 : Disjoint (cent Δ q) (cent Δ r) :=
    disjoint_cent hpl.mem_right hr (h.not_conn_third_right hpl)
  have e1 : (cent Δ r).ncard = (cent Δ q).ncard := h.ncard_cent_eq hS hpl
  have e2 : (cent Δ r).ncard = (cent Δ p).ncard := h.ncard_cent_eq hS (h.isPlane_swap hpl)
  calc Δ.ncard = (cent Δ p ∪ cent Δ q ∪ cent Δ r).ncard := congrArg Set.ncard hU
    _ = (cent Δ p).ncard + (cent Δ q).ncard + (cent Δ r).ncard := by
        rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hdisj2, hdisj3⟩),
          Set.ncard_union_eq hdisj1]
    _ = 3 * (cent Δ p).ncard := by omega

theorem natCard_eq_three_mul [Finite Q] (h : IsTT Δ) (hS : IsStar Δ) {p q r : Q}
    (hpl : IsPlane Δ p q r) :
    Nat.card Q = 3 * (cent Δ p).ncard * Nat.card (Subgroup.centralizer ({p} : Set Q)) := by
  have h1 := Subgroup.card_mul_index (Subgroup.centralizer ({p} : Set Q))
  rw [Subgroup.index_centralizer_eq_ncard,
    h.conjugatesOf_eq hpl.mem_left hpl.mem_right hpl.not_conn, h.ncard_eq_three_mul hS hpl] at h1
  rw [← h1]
  ring

theorem cent_subset_centralizer (p : Q) : cent Δ p ⊆ Subgroup.centralizer ({p} : Set Q) := by
  intro x hx
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact hx.2

end IsTT

end CFSG.ClassicalInvolution.Asc77.Star3T
