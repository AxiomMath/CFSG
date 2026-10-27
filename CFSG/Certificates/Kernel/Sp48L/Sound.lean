module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48LocalMain
public import Certificates.Data.Kernel.Sp48L.Check

public section

namespace CFSG.KC.Sp48L

open CFSG.AGLEmbedding.KFactProofs.Sp48 CFSG.Quasithin

theorem eq_of_ceqP {p q : Pc} (h : ceqP p q = true) : p = q := by
  obtain ⟨pm, pj⟩ := p
  obtain ⟨qm, qj⟩ := q
  simp only [ceqP, Bool.and_eq_true, beq_iff_eq, Array.toList_inj] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem ne_of_ceqP {p q : Pc} (h : ceqP p q = false) : p ≠ q := by
  rintro rfl
  simp [ceqP] at h

@[expose] def mulIx (a b : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  ((a.1 + 7 ^ a.2.2 * b.1) % 9, (a.2.1 + 7 ^ a.2.2 * b.2.1) % 9, (a.2.2 + b.2.2) % 3)

@[expose] def powIx (a : ℕ × ℕ × ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | n + 1 => mulIx (powIx a n) a

@[expose] def inT (a : ℕ × ℕ × ℕ) : Prop := a.1 < 9 ∧ a.2.1 < 9 ∧ a.2.2 < 3

@[expose] def inA (a : ℕ × ℕ × ℕ) : Prop := inT a ∧ a.1 % 3 = 0 ∧ a.2.1 % 3 = 0

@[expose] def inE (a : ℕ × ℕ × ℕ) : Prop := inA a ∧ a.2.2 = 0

instance (a : ℕ × ℕ × ℕ) : Decidable (inT a) := inferInstanceAs (Decidable (_ ∧ _))

instance (a : ℕ × ℕ × ℕ) : Decidable (inA a) := inferInstanceAs (Decidable (_ ∧ _))

instance (a : ℕ × ℕ × ℕ) : Decidable (inE a) := inferInstanceAs (Decidable (_ ∧ _))

theorem inT_mulIx (a b : ℕ × ℕ × ℕ) : inT (mulIx a b) :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

@[expose] def uIx (k : ℕ) : ℕ × ℕ × ℕ :=
  if k = 0 then (0, 0, 0) else if k = 1 then (1, 0, 0) else if k = 2 then (2, 0, 0) else (0, 1, 0)

@[expose] def vIx (k : ℕ) : ℕ × ℕ × ℕ :=
  if k = 0 then (0, 0, 0) else if k = 1 then (8, 0, 0) else if k = 2 then (7, 0, 0) else (0, 8, 0)

@[expose] def cjIx (k : ℕ) (a : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := mulIx (mulIx (uIx k) a) (vIx k)

theorem ix_pow9 : ∀ i < 9, ∀ j < 9, ∀ k < 3, powIx (i, j, k) 9 = (0, 0, 0) := by decide +kernel

@[expose] def allR (n : ℕ) (f : ℕ → Bool) : Bool := (List.range n).all f

theorem allR_iff {n : ℕ} {f : ℕ → Bool} : allR n f = true ↔ ∀ i < n, f i = true := by
  simp [allR]

theorem inT_mk {i j k : ℕ} (hi : i < 9) (hj : j < 9) (hk : k < 3) : inT (i, j, k) := ⟨hi, hj, hk⟩

theorem ix_mulA : ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ a' < 3, ∀ b' < 3, ∀ c' < 3,
    inA (mulIx (3 * a, 3 * b, c) (3 * a', 3 * b', c')) ∧
      mulIx (3 * a, 3 * b, c) (3 * a', 3 * b', c') =
        mulIx (3 * a', 3 * b', c') (3 * a, 3 * b, c) := by
  have h : (allR 3 fun a => allR 3 fun b => allR 3 fun c => allR 3 fun a' => allR 3 fun b' =>
      allR 3 fun c' => decide (inA (mulIx (3 * a, 3 * b, c) (3 * a', 3 * b', c')) ∧
        mulIx (3 * a, 3 * b, c) (3 * a', 3 * b', c') =
          mulIx (3 * a', 3 * b', c') (3 * a, 3 * b, c))) = true := by decide +kernel
  simpa only [allR_iff, decide_eq_true_eq] using h

theorem ix_powA : ∀ a < 3, ∀ b < 3, ∀ c < 3,
    inA (powIx (3 * a, 3 * b, c) 2) ∧ powIx (3 * a, 3 * b, c) 3 = (0, 0, 0) := by decide +kernel

theorem ix_central : ∀ a < 3, ∀ b < 3, ∀ i < 9, ∀ j < 9, ∀ k < 3,
    mulIx (3 * a, 3 * b, 0) (i, j, k) = mulIx (i, j, k) (3 * a, 3 * b, 0) := by
  have h : (allR 3 fun a => allR 3 fun b => allR 9 fun i => allR 9 fun j => allR 3 fun k =>
      decide (mulIx (3 * a, 3 * b, 0) (i, j, k) = mulIx (i, j, k) (3 * a, 3 * b, 0))) = true := by
    decide +kernel
  simpa only [allR_iff, decide_eq_true_eq] using h

theorem ix_inE : ∀ i < 9, ∀ j < 9, ∀ k < 3,
    mulIx (i, j, k) (1, 0, 0) = mulIx (1, 0, 0) (i, j, k) →
    mulIx (i, j, k) (0, 1, 0) = mulIx (0, 1, 0) (i, j, k) →
    mulIx (i, j, k) (0, 0, 1) = mulIx (0, 0, 1) (i, j, k) → inE (i, j, k) := by
  have h : (allR 9 fun i => allR 9 fun j => allR 3 fun k =>
      decide (mulIx (i, j, k) (1, 0, 0) = mulIx (1, 0, 0) (i, j, k) →
        mulIx (i, j, k) (0, 1, 0) = mulIx (0, 1, 0) (i, j, k) →
        mulIx (i, j, k) (0, 0, 1) = mulIx (0, 0, 1) (i, j, k) → inE (i, j, k))) = true := by
    decide +kernel
  simpa only [allR_iff, decide_eq_true_eq] using h

theorem ix_ord3 : ∀ i < 9, ∀ j < 9, powIx (i, j, 0) 3 = (0, 0, 0) → inE (i, j, 0) := by
  decide +kernel

theorem ix_normE : ∀ a < 3, ∀ b < 3,
    inE (mulIx (mulIx (1, 0, 0) (3 * a, 3 * b, 0)) (8, 0, 0)) ∧
    inE (mulIx (mulIx (0, 1, 0) (3 * a, 3 * b, 0)) (0, 8, 0)) ∧
    inE (mulIx (mulIx (0, 0, 1) (3 * a, 3 * b, 0)) (0, 0, 2)) ∧
    inE ((8 * (3 * a)) % 9, 3 * b, 0) := by decide +kernel

theorem ix_orbit : ∀ a < 3, ∀ b < 3, ∀ c < 3, c = 0 ∨ ∀ k < 4, ∀ l < 4, k = l ∨
    (cjIx k (3 * a, 3 * b, c) ≠ (0, 0, 0) ∧ cjIx k (3 * a, 3 * b, c) ≠ cjIx l (3 * a, 3 * b, c)) ∧
      cjIx k (3 * a, 3 * b, c) ≠ mulIx (cjIx l (3 * a, 3 * b, c)) (cjIx l (3 * a, 3 * b, c)) := by
  have h : (allR 3 fun a => allR 3 fun b => allR 3 fun c => decide (c = 0) || allR 4 fun k =>
      allR 4 fun l => decide (k = l ∨ (cjIx k (3 * a, 3 * b, c) ≠ (0, 0, 0) ∧
        cjIx k (3 * a, 3 * b, c) ≠ cjIx l (3 * a, 3 * b, c)) ∧
        cjIx k (3 * a, 3 * b, c) ≠
          mulIx (cjIx l (3 * a, 3 * b, c)) (cjIx l (3 * a, 3 * b, c)))) = true := by
    decide +kernel
  simpa only [allR_iff, decide_eq_true_eq, Bool.or_eq_true] using h

theorem pow_mod_of {G : Type*} [Monoid G] {x : G} {n : ℕ} (h : x ^ n = 1) (m : ℕ) :
    x ^ m = x ^ (m % n) := by
  conv_lhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, h, one_pow, mul_one]

theorem semi_pow {G : Type*} [Monoid G] {f t : G} (h : f * t = t ^ 7 * f) (k i : ℕ) :
    f ^ k * t ^ i = t ^ (7 ^ k * i) * f ^ k := by
  have hk : ∀ k : ℕ, SemiconjBy (f ^ k) t (t ^ (7 ^ k)) := by
    intro k
    induction k with
    | zero => simpa using SemiconjBy.one_left t
    | succ k ih =>
      rw [pow_succ f k, pow_succ 7 k, pow_mul t]
      exact (ih.pow_right 7).mul_left h
  have := (hk k).pow_right i
  rw [SemiconjBy, ← pow_mul] at this
  exact this

section Group

variable (r : Rels)

include r in
theorem nfElt_mul (i j k i' j' k' : ℕ) :
    nfElt i j k * nfElt i' j' k' = nfElt (i + 7 ^ k * i') (j + 7 ^ k * j') (k + k') := by
  have h1 : ∀ y, gf ^ k * (gt1 ^ i' * y) = gt1 ^ (7 ^ k * i') * (gf ^ k * y) := fun y => by
    rw [← mul_assoc, semi_pow r.ft1, mul_assoc]
  have h2 : ∀ y, gf ^ k * (gt2 ^ j' * y) = gt2 ^ (7 ^ k * j') * (gf ^ k * y) := fun y => by
    rw [← mul_assoc, semi_pow r.ft2, mul_assoc]
  have hc : ∀ y, gt2 ^ j * (gt1 ^ (7 ^ k * i') * y) = gt1 ^ (7 ^ k * i') * (gt2 ^ j * y) :=
    fun y => by rw [← mul_assoc, ← ((commute_t12 r).pow_pow (7 ^ k * i') j).eq, mul_assoc]
  simp only [nfElt, pow_add, mul_assoc, h1, h2, hc]

include r in
theorem nfElt_mod (i j k : ℕ) : nfElt i j k = nfElt (i % 9) (j % 9) (k % 3) := by
  rw [nfElt, nfElt, pow_mod_of r.t1_9 i, pow_mod_of r.t2_9 j, pow_mod_of r.f_3 k]

theorem k_eq_of {i j k i' j' k' : ℕ} (hk : k < 3) (hk' : k' < 3)
    (h : nfElt i j k = nfElt i' j' k') : k = k' := by
  have := congrArg (SemidirectProduct.rightHom (N := Sp8) (G := Multiplicative (ZMod 3))
    (φ := phi)) h
  rw [rightHom_nfElt, rightHom_nfElt] at this
  have h3 : ((k : ℕ) : ZMod 3) = ((k' : ℕ) : ZMod 3) := Multiplicative.ofAdd.injective this
  rw [ZMod.natCast_eq_natCast_iff'] at h3
  omega

variable (hg : gensValid = true)
  (hom : ∀ a < 9, ∀ b < 9, powP t1c a ≠ powP t2c b ∨ a = 0)

include r hg hom in
theorem nfElt_inj {i j k i' j' k' : ℕ} (hi : i < 9) (hj : j < 9) (hk : k < 3) (hi' : i' < 9)
    (hj' : j' < 9) (hk' : k' < 3) (h : nfElt i j k = nfElt i' j' k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have hkk := k_eq_of hk hk' h
  subst hkk
  have h0 : gt1 ^ i * gt2 ^ j = gt1 ^ i' * gt2 ^ j' := mul_right_cancel h
  have hx : (gt1 ^ i')⁻¹ * gt1 ^ i = gt2 ^ j' * (gt2 ^ j)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h0, mul_assoc, mul_inv_cancel, mul_one]
  have hbot := inf_t_aux hg r hom
  have hmem : (gt1 ^ i')⁻¹ * gt1 ^ i ∈ Subgroup.zpowers gt1 ⊓ Subgroup.zpowers gt2 := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _
      (Subgroup.mem_zpowers _) _)) (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _), ?_⟩
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  rw [hbot, Subgroup.mem_bot] at hmem
  have e1 : gt1 ^ i' = gt1 ^ i := inv_mul_eq_one.1 hmem
  have e2 : gt2 ^ j' = gt2 ^ j := mul_inv_eq_one.1 (hx ▸ hmem)
  rw [pow_eq_pow_iff_modEq, order_t1 r] at e1
  rw [pow_eq_pow_iff_modEq, order_t2 r] at e2
  unfold Nat.ModEq at e1 e2
  omega

@[expose] def nfT (a : ℕ × ℕ × ℕ) : Pc := nf a.1 a.2.1 a.2.2

include r hg in
theorem nf_mulT (a b : ℕ × ℕ × ℕ) : mulP (nfT a) (nfT b) = nfT (mulIx a b) :=
  ((repP_nfElt hg _ _ _).mul (repP_nfElt hg _ _ _)).code_eq (by
    rw [nfElt_mul r, nfElt_mod r]
    exact repP_nfElt hg _ _ _)

include r hg in
theorem nf_powT (a : ℕ × ℕ × ℕ) (n : ℕ) : powP (nfT a) n = nfT (powIx a n) := by
  induction n with
  | zero =>
    refine RepP.one.code_eq ?_
    have := repP_nfElt hg 0 0 0
    simp only [nfElt, pow_zero, mul_one] at this
    exact this
  | succ n ih =>
    rw [powP, ih, nf_mulT r hg]
    rfl

include r hg hom in
theorem nfT_inj {a b : ℕ × ℕ × ℕ} (ha : inT a) (hb : inT b) (h : nfT a = nfT b) : a = b := by
  have := repP_nfElt hg b.1 b.2.1 b.2.2
  rw [← nfT, ← h] at this
  obtain ⟨e1, e2, e3⟩ := nfElt_inj r hg hom ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2
    ((repP_nfElt hg a.1 a.2.1 a.2.2).eq this)
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only at e1 e2 e3
  rw [e1, e2, e3]

theorem nfT_mem_T {a : ℕ × ℕ × ℕ} (h : inT a) : nfT a ∈ lstT :=
  mem_lstT.2 ⟨a.1, h.1, a.2.1, h.2.1, a.2.2, h.2.2, rfl⟩

theorem nfT_mem_A {a : ℕ × ℕ × ℕ} (h : inA a) : nfT a ∈ lstA := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := h
  refine mem_lstA.2 ⟨a.1 / 3, by omega, a.2.1 / 3, by omega, a.2.2, h3, ?_⟩
  have e1 : 3 * (a.1 / 3) = a.1 := by omega
  have e2 : 3 * (a.2.1 / 3) = a.2.1 := by omega
  rw [e1, e2]
  rfl

theorem nfT_mem_E {a : ℕ × ℕ × ℕ} (h : inE a) : nfT a ∈ lstE := by
  obtain ⟨⟨⟨h1, h2, h3⟩, h4, h5⟩, h6⟩ := h
  refine mem_lstE.2 ⟨a.1 / 3, by omega, a.2.1 / 3, by omega, ?_⟩
  have e1 : 3 * (a.1 / 3) = a.1 := by omega
  have e2 : 3 * (a.2.1 / 3) = a.2.1 := by omega
  rw [e1, e2, ← h6]
  rfl

theorem mem_T_iff {p : Pc} : p ∈ lstT ↔ ∃ i < 9, ∃ j < 9, ∃ k < 3, p = nfT (i, j, k) :=
  mem_lstT

theorem mem_A_iff {p : Pc} : p ∈ lstA ↔ ∃ a < 3, ∃ b < 3, ∃ c < 3, p = nfT (3 * a, 3 * b, c) :=
  mem_lstA

theorem mem_E_iff {p : Pc} : p ∈ lstE ↔ ∃ a < 3, ∃ b < 3, p = nfT (3 * a, 3 * b, 0) :=
  mem_lstE

include r hg in
theorem one_eq : oneP = nfT (0, 0, 0) := by
  have := nf_powT r hg (0, 0, 0) 0
  rw [powP] at this
  exact this

include r hg in
theorem gen_eqs : t1c = nfT (1, 0, 0) ∧ t2c = nfT (0, 1, 0) ∧ fc = nfT (0, 0, 1) := by
  have h1 := repP_nfElt hg 1 0 0
  have h2 := repP_nfElt hg 0 1 0
  have h3 := repP_nfElt hg 0 0 1
  simp only [nfElt, pow_zero, pow_one, mul_one, one_mul] at h1 h2 h3
  exact ⟨(repP_gt1 hg).code_eq h1, (repP_gt2 hg).code_eq h2, repP_gf.code_eq h3⟩

theorem nodup_box2 {α : Type*} (a b : ℕ) (g : ℕ → ℕ → α)
    (hg : ∀ i < a, ∀ j < b, ∀ i' < a, ∀ j' < b, g i j = g i' j' → i = i' ∧ j = j') :
    ((List.range a).flatMap fun i => (List.range b).map fun j => g i j).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun i hi => ?_, List.nodup_range.pairwise_of_forall_ne fun i hi i' hi' hne => ?_⟩
  · rw [List.mem_range] at hi
    refine (List.nodup_map_iff_inj_on List.nodup_range).2 fun j hj j' hj' h => ?_
    rw [List.mem_range] at hj hj'
    exact (hg i hi j hj i hi j' hj' h).2
  · rw [List.mem_range] at hi hi'
    intro x hx hx'
    simp only [List.mem_map, List.mem_range] at hx hx'
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨j', hj', h⟩ := hx'
    exact hne (hg i hi j hj i' hi' j' hj' h.symm).1

theorem nodup_box3 {α : Type*} (a b c : ℕ) (g : ℕ → ℕ → ℕ → α)
    (hg : ∀ i < a, ∀ j < b, ∀ k < c, ∀ i' < a, ∀ j' < b, ∀ k' < c, g i j k = g i' j' k' →
      i = i' ∧ j = j' ∧ k = k') :
    ((List.range a).flatMap fun i => (List.range b).flatMap fun j =>
      (List.range c).map fun k => g i j k).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun i hi => ?_, List.nodup_range.pairwise_of_forall_ne fun i hi i' hi' hne => ?_⟩
  · rw [List.mem_range] at hi
    refine nodup_box2 b c (g i) fun j hj k hk j' hj' k' hk' h => ?_
    exact (hg i hi j hj k hk i hi j' hj' k' hk' h).2
  · rw [List.mem_range] at hi hi'
    intro x hx hx'
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hx hx'
    obtain ⟨j, hj, k, hk, rfl⟩ := hx
    obtain ⟨j', hj', k', hk', h⟩ := hx'
    exact hne (hg i hi j hj k hk i' hi' j' hj' k' hk' h.symm).1

include r hg hom in
theorem normalFormOK_true : normalFormOK = true := by
  have inj := fun {a b : ℕ × ℕ × ℕ} (ha : inT a) (hb : inT b) (h : nfT a = nfT b) =>
    nfT_inj r hg hom ha hb h
  have hT : lstT.Nodup := nodup_box3 9 9 3 nf fun i hi j hj k hk i' hi' j' hj' k' hk' h => by
    have := inj (a := (i, j, k)) (b := (i', j', k')) (inT_mk hi hj hk) (inT_mk hi' hj' hk') h
    simp only [Prod.mk.injEq] at this
    exact this
  have hA : lstA.Nodup := nodup_box3 3 3 3 (fun a b c => nf (3 * a) (3 * b) c)
    fun i hi j hj k hk i' hi' j' hj' k' hk' h => by
    have := inj (a := (3 * i, 3 * j, k)) (b := (3 * i', 3 * j', k'))
      (inT_mk (by omega) (by omega) hk) (inT_mk (by omega) (by omega) hk') h
    simp only [Prod.mk.injEq] at this
    omega
  have hE : lstE.Nodup := nodup_box2 3 3 (fun a b => nf (3 * a) (3 * b) 0)
    fun i hi j hj i' hi' j' hj' h => by
    have := inj (a := (3 * i, 3 * j, 0)) (b := (3 * i', 3 * j', 0))
      (inT_mk (by omega) (by omega) (by omega)) (inT_mk (by omega) (by omega) (by omega)) h
    simp only [Prod.mk.injEq] at this
    omega
  have h1 : oneP ∈ lstT := one_eq r hg ▸ nfT_mem_T (inT_mk (by omega) (by omega) (by omega))
  have h1A : oneP ∈ lstA := one_eq r hg ▸ mem_A_iff.2 ⟨0, by omega, 0, by omega, 0, by omega, rfl⟩
  have hmulT : ∀ p ∈ lstT, ∀ q ∈ lstT, mulP p q ∈ lstT := by
    intro p hp q hq
    obtain ⟨i, -, j, -, k, -, rfl⟩ := mem_T_iff.1 hp
    obtain ⟨i', -, j', -, k', -, rfl⟩ := mem_T_iff.1 hq
    rw [nf_mulT r hg]
    exact nfT_mem_T (inT_mulIx _ _)
  have hpowT : ∀ p ∈ lstT, powP p 9 = oneP ∧ powP p 8 ∈ lstT := by
    intro p hp
    obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := mem_T_iff.1 hp
    refine ⟨?_, ?_⟩
    · rw [nf_powT r hg, ix_pow9 i hi j hj k hk, one_eq r hg]
    · rw [nf_powT r hg]
      exact nfT_mem_T (inT_mulIx _ _)
  have hmulA : ∀ p ∈ lstA, ∀ q ∈ lstA, mulP p q ∈ lstA := by
    intro p hp q hq
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := mem_A_iff.1 hp
    obtain ⟨a', ha', b', hb', c', hc', rfl⟩ := mem_A_iff.1 hq
    rw [nf_mulT r hg]
    exact nfT_mem_A (ix_mulA a ha b hb c hc a' ha' b' hb' c' hc').1
  have hsubA : ∀ p ∈ lstA, p ∈ lstT ∧ powP p 2 ∈ lstA := by
    intro p hp
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := mem_A_iff.1 hp
    refine ⟨nfT_mem_T (inT_mk (by omega) (by omega) hc), ?_⟩
    rw [nf_powT r hg]
    exact nfT_mem_A (ix_powA a ha b hb c hc).1
  have hsubE : ∀ p ∈ lstE, p ∈ lstA := by
    intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_E_iff.1 hp
    exact mem_A_iff.2 ⟨a, ha, b, hb, 0, by omega, rfl⟩
  simp [normalFormOK, and_assoc]
  exact ⟨hT, hE, hA, h1, h1A, hmulT, hpowT, hmulA, hsubA, hsubE⟩

include r hg hom in
theorem centreOK_true : centreOK = true := by
  obtain ⟨e1, e2, e3⟩ := gen_eqs r hg
  have hc : ∀ p ∈ lstE, ∀ q ∈ lstT, mulP p q = mulP q p := by
    intro p hp q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_E_iff.1 hp
    obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := mem_T_iff.1 hq
    rw [nf_mulT r hg, nf_mulT r hg, ix_central a ha b hb i hi j hj k hk]
  have hE : ∀ p ∈ lstT, mulP p t1c = mulP t1c p → mulP p t2c = mulP t2c p →
      mulP p fc = mulP fc p → p ∈ lstE := by
    intro p hp h1 h2 h3
    obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := mem_T_iff.1 hp
    rw [e1, nf_mulT r hg, nf_mulT r hg] at h1
    rw [e2, nf_mulT r hg, nf_mulT r hg] at h2
    rw [e3, nf_mulT r hg, nf_mulT r hg] at h3
    exact nfT_mem_E (ix_inE i hi j hj k hk
      (nfT_inj r hg hom (inT_mulIx _ _) (inT_mulIx _ _) h1)
      (nfT_inj r hg hom (inT_mulIx _ _) (inT_mulIx _ _) h2)
      (nfT_inj r hg hom (inT_mulIx _ _) (inT_mulIx _ _) h3))
  simp only [centreOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨hc, fun p hp => ?_⟩
  by_cases h1 : mulP p t1c = mulP t1c p <;> by_cases h2 : mulP p t2c = mulP t2c p <;>
    by_cases h3 : mulP p fc = mulP fc p <;> simp [h1, h2, h3, hE p hp]

include r hg hom in
theorem ordThreeOK_true : ordThreeOK = true := by
  have hp3 : ∀ p ∈ lstA, powP p 3 = oneP := by
    intro p hp
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := mem_A_iff.1 hp
    rw [nf_powT r hg, (ix_powA a ha b hb c hc).2, one_eq r hg]
  have hcA : ∀ p ∈ lstA, ∀ q ∈ lstA, mulP p q = mulP q p := by
    intro p hp q hq
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := mem_A_iff.1 hp
    obtain ⟨a', ha', b', hb', c', hc', rfl⟩ := mem_A_iff.1 hq
    rw [nf_mulT r hg, nf_mulT r hg, (ix_mulA a ha b hb c hc a' ha' b' hb' c' hc').2]
  have h3 : ∀ p ∈ lstT, p.j = 0 → powP p 3 = oneP → p ∈ lstE := by
    intro p hp hj h3
    obtain ⟨i, hi, j, hj', k, hk, rfl⟩ := mem_T_iff.1 hp
    have hk0 : k = 0 := by
      have := (repP_nfElt hg i j k).exp
      have hj2 : (nf i j k).j = 0 := hj
      rw [hj2] at this
      have hr := congrArg Multiplicative.toAdd (rightHom_nfElt i j k)
      simp only [SemidirectProduct.rightHom_eq_right, toAdd_ofAdd] at hr
      rw [hr, ZMod.val_natCast] at this
      omega
    subst hk0
    rw [nf_powT r hg, one_eq r hg] at h3
    exact nfT_mem_E (ix_ord3 i hi j hj' (nfT_inj r hg hom (inT_mulIx _ _)
      (inT_mk (by omega) (by omega) (by omega)) h3))
  simp only [ordThreeOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨hp3, hcA⟩, fun p hp => ?_⟩
  by_cases hj : p.j = 0 <;> by_cases h : powP p 3 = oneP <;> simp [hj, h, h3 p hp]

include r hg in
theorem normC_of {b bi : Pc} {u v : ℕ × ℕ × ℕ} (hb : b = nfT u) (hbi : bi = nfT v)
    (hinv : mulIx u v = (0, 0, 0))
    (hE : ∀ a < 3, ∀ c < 3, inE (mulIx (mulIx u (3 * a, 3 * c, 0)) v)) : NormC b bi := by
  subst hb hbi
  refine ⟨by rw [nf_mulT r hg, hinv, one_eq r hg], fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨i, -, j, -, k, -, rfl⟩ := mem_T_iff.1 hp
    rw [nf_mulT r hg, nf_mulT r hg]
    exact nfT_mem_T (inT_mulIx _ _)
  · obtain ⟨a, ha, c, hc, rfl⟩ := mem_E_iff.1 hp
    rw [nf_mulT r hg, nf_mulT r hg]
    exact nfT_mem_E (hE a ha c hc)

include r hg in
theorem normalOK_true : normalOK = true := by
  obtain ⟨e1, e2, e3⟩ := gen_eqs r hg
  have p18 : powP t1c 8 = nfT (8, 0, 0) := by rw [e1, nf_powT r hg]; rfl
  have p28 : powP t2c 8 = nfT (0, 8, 0) := by rw [e2, nf_powT r hg]; rfl
  have pf2 : powP fc 2 = nfT (0, 0, 2) := by rw [e3, nf_powT r hg]; rfl
  have hw : NormC wc wc := by
    have rw' := repP_gw hg
    have hcw : ∀ i j k, gw * nfElt i j k * gw = nfElt (8 * i) j k := fun i j k => by
      have := conj_w_nf r i j k
      rw [gw_inv r] at this
      exact this
    refine ⟨rw'.mul rw' |>.code_eq (r.ww ▸ RepP.one), fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := mem_T_iff.1 hp
      have hrep := (rw'.mul (repP_nfElt hg i j k)).mul rw'
      rw [hcw, nfElt_mod r] at hrep
      simp only [nfT]
      rw [hrep.code_eq (repP_nfElt hg _ _ _)]
      exact nfT_mem_T (a := (_, _, _)) (inT_mk (Nat.mod_lt _ (by norm_num))
        (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)))
    · obtain ⟨a, ha, c, hc, rfl⟩ := mem_E_iff.1 hp
      have hrep := (rw'.mul (repP_nfElt hg (3 * a) (3 * c) 0)).mul rw'
      rw [hcw, nfElt_mod r (8 * (3 * a))] at hrep
      simp only [nfT]
      rw [hrep.code_eq (repP_nfElt hg _ _ _)]
      have := (ix_normE a ha c hc).2.2.2
      have e : (3 * c) % 9 = 3 * c := Nat.mod_eq_of_lt (by omega)
      have e' : 0 % 3 = 0 := rfl
      rw [e, e']
      exact nfT_mem_E (a := (_, _, _)) this
  have hs : NormC sc sc := by
    have rs := repP_gs hg
    have hcs : ∀ i j k, gs * nfElt i j k * gs = nfElt j i k := fun i j k => by
      have := conj_s_nf r i j k
      rw [gs_inv r] at this
      exact this
    refine ⟨rs.mul rs |>.code_eq (r.ss ▸ RepP.one), fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := mem_T_iff.1 hp
      have hrep := (rs.mul (repP_nfElt hg i j k)).mul rs
      rw [hcs] at hrep
      simp only [nfT]
      rw [hrep.code_eq (repP_nfElt hg _ _ _)]
      exact nfT_mem_T (a := (j, i, k)) (inT_mk hj hi hk)
    · obtain ⟨a, ha, c, hc, rfl⟩ := mem_E_iff.1 hp
      have hrep := (rs.mul (repP_nfElt hg (3 * a) (3 * c) 0)).mul rs
      rw [hcs] at hrep
      simp only [nfT]
      rw [hrep.code_eq (repP_nfElt hg _ _ _)]
      exact mem_E_iff.2 ⟨c, hc, a, ha, rfl⟩
  have hall : NormAll :=
    ⟨normC_of r hg e1 p18 rfl fun a ha c hc => (ix_normE a ha c hc).1,
      normC_of r hg e2 p28 rfl fun a ha c hc => (ix_normE a ha c hc).2.1, hw, hs,
      normC_of r hg e3 pf2 rfl fun a ha c hc => (ix_normE a ha c hc).2.2.1⟩
  simp [normalOK, and_assoc]
  exact ⟨hall.t1.inv, hall.t1.normT, hall.t1.normE, hall.t2.inv, hall.t2.normT, hall.t2.normE,
    hall.w.inv, hall.w.normT, hall.w.normE, hall.s.inv, hall.s.normT, hall.s.normE,
    hall.f.inv, hall.f.normT, hall.f.normE⟩

include r hg in
theorem cj_eq (k : ℕ) (hk : k < 4) (a : ℕ × ℕ × ℕ) : cj k (nfT a) = nfT (cjIx k a) := by
  obtain ⟨e1, e2, e3⟩ := gen_eqs r hg
  have hu : (uList[k]!).1 = nfT (uIx k) ∧ (uList[k]!).2 = nfT (vIx k) := by
    interval_cases k
    · exact ⟨one_eq r hg, one_eq r hg⟩
    · refine ⟨e1, ?_⟩
      change powP t1c 8 = _
      rw [e1, nf_powT r hg]
      rfl
    · change powP t1c 2 = _ ∧ powP t1c 7 = _
      rw [e1, nf_powT r hg, nf_powT r hg]
      exact ⟨rfl, rfl⟩
    · refine ⟨e2, ?_⟩
      change powP t2c 8 = _
      rw [e2, nf_powT r hg]
      rfl
  rw [cj, hu.1, hu.2, nf_mulT r hg, nf_mulT r hg]
  rfl

include r hg hom in
theorem orbitOK_true : orbitOK = true := by
  have h : ∀ p ∈ lstA, p ∈ lstE ∨ ∀ k < 4, ∀ l < 4, k = l ∨
      (cj k p ≠ oneP ∧ cj k p ≠ cj l p) ∧ cj k p ≠ mulP (cj l p) (cj l p) := by
    intro p hp
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := mem_A_iff.1 hp
    rcases ix_orbit a ha b hb c hc with h0 | h
    · subst h0
      exact Or.inl (mem_E_iff.2 ⟨a, ha, b, hb, rfl⟩)
    refine Or.inr fun k hk l hl => ?_
    rcases h k hk l hl with h | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl h
    refine Or.inr ⟨⟨?_, ?_⟩, ?_⟩
    · rw [cj_eq r hg k hk, one_eq r hg]
      exact fun e => h1 (nfT_inj r hg hom (inT_mulIx _ _)
        (inT_mk (by omega) (by omega) (by omega)) e)
    · rw [cj_eq r hg k hk, cj_eq r hg l hl]
      exact fun e => h2 (nfT_inj r hg hom (inT_mulIx _ _) (inT_mulIx _ _) e)
    · rw [cj_eq r hg k hk, cj_eq r hg l hl, nf_mulT r hg]
      exact fun e => h3 (nfT_inj r hg hom (inT_mulIx _ _) (inT_mulIx _ _) e)
  simpa [orbitOK] using h

end Group

theorem sp48LocalCheck_of (hg : gensValid = true)
    (r1 : ceqP (powP t1c 9) oneP = true) (r2 : ceqP (powP t2c 9) oneP = true)
    (r3 : ceqP (powP fc 3) oneP = true) (r4 : ceqP (powP t1c 3) oneP = false)
    (r5 : ceqP (mulP t1c t2c) (mulP t2c t1c) = true)
    (r6 : ceqP (mulP fc t1c) (mulP (powP t1c 7) fc) = true)
    (r7 : ceqP (mulP fc t2c) (mulP (powP t2c 7) fc) = true)
    (r8 : ceqP (mulP wc wc) oneP = true) (r9 : ceqP (mulP sc sc) oneP = true)
    (r10 : ceqP (mulP (mulP wc t1c) wc) (powP t1c 8) = true)
    (r11 : ceqP (mulP wc t2c) (mulP t2c wc) = true) (r12 : ceqP (mulP wc fc) (mulP fc wc) = true)
    (r13 : ceqP (mulP (mulP sc t1c) sc) t2c = true)
    (r14 : ceqP (mulP (mulP sc t2c) sc) t1c = true)
    (r15 : ceqP (mulP sc fc) (mulP fc sc) = true) (hh : homK = true) :
    sp48LocalCheck = true := by
  have hrel : relOK = true := by
    simp only [relOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨eq_of_ceqP r1, eq_of_ceqP r2⟩, eq_of_ceqP r3⟩, ne_of_ceqP r4⟩,
      eq_of_ceqP r5⟩, eq_of_ceqP r6⟩, eq_of_ceqP r7⟩, eq_of_ceqP r8⟩, eq_of_ceqP r9⟩,
      eq_of_ceqP r10⟩, eq_of_ceqP r11⟩, eq_of_ceqP r12⟩, eq_of_ceqP r13⟩, eq_of_ceqP r14⟩,
      eq_of_ceqP r15⟩
  have hom : ∀ a < 9, ∀ b < 9, powP t1c a ≠ powP t2c b ∨ a = 0 := by
    intro a ha b hb
    simp only [homK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq] at hh
    rcases hh a ha b hb with h | h
    · exact Or.inl (ne_of_ceqP h)
    · exact Or.inr h
  have hhom : homOK = true := by simpa [homOK] using hom
  have r := rels_of_check hg hrel
  rw [sp48LocalCheck, hg, hrel, normalFormOK_true r hg hom, centreOK_true r hg hom,
    ordThreeOK_true r hg hom, normalOK_true r hg, orbitOK_true r hg hom, hhom]
  rfl

end CFSG.KC.Sp48L
