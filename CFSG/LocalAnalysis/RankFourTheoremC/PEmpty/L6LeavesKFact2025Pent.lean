module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025Step

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025

open CFSG CFSG.OddSolvableUnitary CFSG.RankThree.GroupTheory
open scoped commutatorElement

universe u v

section Facts

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem Min32.facts {R : Subgroup (Module.End k V)ˣ} {u : (Module.End k V)ˣ}
    (h : Min32 R u) :
    (-1 : (Module.End k V)ˣ) ∈ R ∧
    (∀ x ∈ R, ∀ y ∈ R, x * y = y * x ∨ x * y = -(y * x)) ∧
    (∀ x ∈ R, x * x = 1 ∨ x * x = -1) ∧
    (∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x = 1 ∨ x = -1) := by
  haveI : Finite R := Nat.finite_of_card_ne_zero (by rw [h.card_eq]; norm_num)
  obtain ⟨z, hz, hzV⟩ := h.center
  have hzn : (z : (Module.End k V)ˣ) = -1 := Units.ext (by rw [hzV]; simp)
  have horder : orderOf z = 2 := by rw [← Nat.card_zpowers, ← hz, h.isExtra.2.2.2]
  have hzz : z * z = 1 := by rw [← pow_two]; exact horder ▸ pow_orderOf_eq_one z
  have hzmem : ∀ w : R, w ∈ Subgroup.zpowers z → w = 1 ∨ w = z := by
    intro w hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hn, ← zpow_mod_orderOf, horder]
    have hn2 : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases hn2 with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  refine ⟨hzn ▸ z.2, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hc := (extraspecial_commutator_eq_one_or h.isExtra hz).2 ⟨x, hx⟩ ⟨y, hy⟩
    rcases hc with hc | hc
    · left
      have := congrArg Subtype.val hc
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
        OneMemClass.coe_one] at this
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [this, one_mul]
    · right
      have := congrArg Subtype.val hc
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hzn] at this
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = -(y * x) := by rw [this, neg_one_mul]
  · intro x hx
    have hxs : (⟨x, hx⟩ : R) ^ 2 ∈ frattini R := sq_mem_frattini_two' h.isExtra.1 ⟨x, hx⟩
    rw [h.isExtra.2.2.1, hz] at hxs
    rcases hzmem _ hxs with h1 | h1
    · left
      have := congrArg Subtype.val h1
      simpa [pow_two] using this
    · right
      have := congrArg Subtype.val h1
      simpa [pow_two, hzn] using this
  · intro x hx hxc
    have hmem : (⟨x, hx⟩ : R) ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hxc g g.2).symm
    rw [hz] at hmem
    rcases hzmem _ hmem with h1 | h1
    · left; exact congrArg Subtype.val h1
    · right; have := congrArg Subtype.val h1; simpa [hzn] using this

theorem Min32.exists_involution {R : Subgroup (Module.End k V)ˣ} {u : (Module.End k V)ˣ}
    (h : Min32 R u) : ∃ s ∈ R, s * s = 1 ∧ s ≠ 1 ∧ s ≠ -1 := by
  classical
  haveI : Finite R := Nat.finite_of_card_ne_zero (by rw [h.card_eq]; norm_num)
  obtain ⟨hm1, hcomm, hsq, hcen⟩ := h.facts
  by_contra hno
  push Not at hno
  have hnonab : ∃ a ∈ R, ¬ ∀ y ∈ R, a * y = y * a := by
    by_contra hall
    push Not at hall
    have hctop : Subgroup.center R = ⊤ := by
      rw [eq_top_iff]
      intro a _
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hall g g.2 a a.2)
    have hc : Nat.card (Subgroup.center R) = Nat.card R := by
      rw [hctop]; exact Subgroup.card_top
    rw [h.isExtra.2.2.2, h.card_eq] at hc
    omega
  obtain ⟨a, haR, ha⟩ := hnonab
  have ha1 : a ≠ 1 := fun h1 => ha fun y _ => by rw [h1, one_mul, mul_one]
  have ha1' : a ≠ -1 := fun h1 => ha fun y _ => by rw [h1, neg_one_mul, mul_neg_one]
  have ha2 : a * a = -1 := by
    rcases hsq a haR with h1 | h1
    · exact absurd (hno a haR h1 ha1) ha1'
    · exact h1
  have hainv : a⁻¹ = -a := by
    rw [inv_eq_iff_mul_eq_one, mul_neg, ha2, neg_neg]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε⟩ := nonempty_center_mulEquiv (D := R) (r := 2) h.isExtra.2.2.2
  have hZ : Subgroup.center R = commutator R := h.isExtra.2.1.symm
  let φ := commRight hZ ε (⟨a, haR⟩ : R)
  have hidx : φ.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card φ.range ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
      _ = 2 := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcardK : 16 ≤ Nat.card φ.ker := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [h.card_eq] at h1
    nlinarith
  have hkerc : ∀ b : R, b ∈ φ.ker → a * (b : (Module.End k V)ˣ) = b * a := by
    intro b hb
    rw [MonoidHom.mem_ker, commRight_apply, ← map_one ε, ε.injective.eq_iff, Subtype.ext_iff] at hb
    have := commutatorElement_eq_one_iff_mul_comm.mp (show ⁅(⟨a, haR⟩ : R), b⁆ = 1 from hb)
    exact congrArg Subtype.val this
  obtain ⟨b, hbK, hbn⟩ : ∃ b : R, b ∈ φ.ker ∧
      (b : (Module.End k V)ˣ) ∉ ({1, -1, a, -a} : Finset (Module.End k V)ˣ) := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (fun b : φ.ker =>
        (⟨((b : R) : (Module.End k V)ˣ), hcon b b.2⟩ :
          ({1, -1, a, -a} : Finset (Module.End k V)ˣ))) := by
      intro x y hxy
      have h1 : ((x : R) : (Module.End k V)ˣ) = ((y : R) : (Module.End k V)ˣ) := by
        simpa using hxy
      exact Subtype.ext (Subtype.ext h1)
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_finsetCard] at h1
    have h4 := Finset.card_le_four (a := (1 : (Module.End k V)ˣ)) (b := -1) (c := a) (d := -a)
    omega
  have hbR : (b : (Module.End k V)ˣ) ∈ R := b.2
  have hab : a * (b : (Module.End k V)ˣ) = b * a := hkerc b hbK
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbn
  obtain ⟨hb1, hb1', hba, hba'⟩ := hbn
  have hb2 : (b : (Module.End k V)ˣ) * b = -1 := by
    rcases hsq b hbR with h1 | h1
    · exact absurd (hno b hbR h1 hb1) hb1'
    · exact h1
  have habab : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, neg_one_mul, neg_neg]
  have habR : a * (b : (Module.End k V)ˣ) ∈ R := R.mul_mem haR hbR
  have hne1 : a * (b : (Module.End k V)ˣ) ≠ 1 := by
    intro h1
    apply hba'
    have : (b : (Module.End k V)ˣ) = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, hainv]
  have hne2 := hno _ habR habab hne1
  apply hba
  have h3 : (b : (Module.End k V)ˣ) = a⁻¹ * (-1) := by
    rw [← hne2]; group
  rw [h3, hainv, mul_neg_one, neg_neg]

end Facts

section Basic

variable {G : Type*} [Group G] [HasDistribNeg G]

@[expose] def conjT (u s : G) (n : ℕ) : G := u ^ n * s * (u ^ n)⁻¹

theorem conjT_zero (u s : G) : conjT u s 0 = s := by simp [conjT]

theorem conjT_succ (u s : G) (n : ℕ) : conjT u s (n + 1) = u * conjT u s n * u⁻¹ := by
  simp only [conjT, pow_succ', mul_inv_rev]
  group

theorem conjT_add_five {u : G} (hu5 : u ^ 5 = 1) (s : G) (n : ℕ) :
    conjT u s (n + 5) = conjT u s n := by
  simp [conjT, pow_add, hu5]

theorem conj_mul (u x y : G) : u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by group

theorem conj_neg (u x : G) : u * (-x) * u⁻¹ = -(u * x * u⁻¹) := by
  rw [mul_neg, neg_mul]

theorem conj_neg_one (u : G) : u * (-1 : G) * u⁻¹ = -1 := by
  rw [mul_neg_one, neg_mul, mul_inv_cancel]

theorem mem_normalizer_of_five {u : G} (hu5 : u ^ 5 = 1) {T : Subgroup G}
    (h : ∀ y ∈ T, u * y * u⁻¹ ∈ T) : u ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  have h5 : u * u * u * u * u = 1 := by
    rw [show u * u * u * u * u = u ^ 5 by simp [pow_succ], hu5]
  have := h _ (h _ (h _ (h _ hy)))
  have e : u * (u * (u * (u * (u * y * u⁻¹) * u⁻¹) * u⁻¹) * u⁻¹) * u⁻¹ =
      (u * u * u * u * u) * y * (u * u * u * u * u)⁻¹ := by group
  rw [e, h5] at this
  simpa using this

end Basic

section ListLemma

variable {G : Type*} [Group G] [HasDistribNeg G]

theorem neg_one_pow_mul_comm (n : ℕ) (g : G) : (-1 : G) ^ n * g = g * (-1 : G) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (-1 : G) ^ (n + 1) * g = (-1) ^ n * ((-1) * g) := by rw [pow_succ, mul_assoc]
      _ = -((-1) ^ n * g) := by rw [neg_one_mul, mul_neg]
      _ = -(g * (-1) ^ n) := by rw [ih]
      _ = g * ((-1) ^ n * (-1)) := by rw [mul_neg_one, mul_neg]
      _ = g * (-1) ^ (n + 1) := by rw [pow_succ]

theorem list_prod_mul_eq (x : G) (p : G → Bool) (hp : ∀ a, p a = true ↔ a * x ≠ x * a)
    (l : List G) (h : ∀ a ∈ l, a * x = x * a ∨ a * x = -(x * a)) :
    l.prod * x = (-1 : G) ^ (l.countP p) * (x * l.prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl : ∀ b ∈ l, b * x = x * b ∨ b * x = -(x * b) := fun b hb =>
      h b (List.mem_cons_of_mem a hb)
    have ha := h a (List.mem_cons_self ..)
    rw [List.prod_cons, mul_assoc, ih hl, List.countP_cons]
    by_cases hc : a * x = x * a
    · have hpa : ¬ (p a = true) := fun h' => (hp a).mp h' hc
      rw [if_neg hpa, add_zero]
      calc a * ((-1 : G) ^ List.countP p l * (x * l.prod))
          = (-1 : G) ^ List.countP p l * (a * (x * l.prod)) := by
            rw [← mul_assoc, ← neg_one_pow_mul_comm, mul_assoc]
        _ = (-1 : G) ^ List.countP p l * (x * (a * l.prod)) := by
            rw [← mul_assoc a x, hc, mul_assoc]
    · have hna : a * x = -(x * a) := ha.resolve_left hc
      have hpa : p a = true := (hp a).mpr hc
      rw [if_pos hpa, pow_succ]
      calc a * ((-1 : G) ^ List.countP p l * (x * l.prod))
          = (-1 : G) ^ List.countP p l * ((a * x) * l.prod) := by
            rw [← mul_assoc, ← neg_one_pow_mul_comm, mul_assoc, mul_assoc]
        _ = (-1 : G) ^ List.countP p l * ((-1) * (x * (a * l.prod))) := by
            rw [hna, neg_mul, neg_one_mul, mul_assoc]
        _ = (-1 : G) ^ List.countP p l * (-1) * (x * (a * l.prod)) := by rw [mul_assoc]

end ListLemma

section Shift

variable {G : Type*} [Group G] [HasDistribNeg G] {u s : G}

theorem conjT_mod_five (hu5 : u ^ 5 = 1) (s : G) (n : ℕ) : conjT u s (n % 5) = conjT u s n := by
  conv_rhs => rw [← Nat.mod_add_div n 5]
  generalize n / 5 = q
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← add_assoc, conjT_add_five hu5, ih]

theorem cm_add {n m : ℕ} (hc : conjT u s n * conjT u s m = conjT u s m * conjT u s n) (j : ℕ) :
    conjT u s (n + j) * conjT u s (m + j) = conjT u s (m + j) * conjT u s (n + j) := by
  induction j with
  | zero => simpa using hc
  | succ j ih =>
    rw [← add_assoc, ← add_assoc, conjT_succ, conjT_succ, ← conj_mul, ← conj_mul, ih]

theorem an_add {n m : ℕ} (hc : conjT u s n * conjT u s m = -(conjT u s m * conjT u s n)) (j : ℕ) :
    conjT u s (n + j) * conjT u s (m + j) = -(conjT u s (m + j) * conjT u s (n + j)) := by
  induction j with
  | zero => simpa using hc
  | succ j ih =>
    rw [← add_assoc, ← add_assoc, conjT_succ, conjT_succ, ← conj_mul, ← conj_mul, ih, conj_neg]

theorem cm_iff_succ (hu5 : u ^ 5 = 1) (n m : ℕ) :
    conjT u s n * conjT u s m = conjT u s m * conjT u s n ↔
      conjT u s (n + 1) * conjT u s (m + 1) = conjT u s (m + 1) * conjT u s (n + 1) := by
  refine ⟨fun hc => cm_add hc 1, fun hc => ?_⟩
  have := cm_add hc 4
  rw [show n + 1 + 4 = n + 5 by ring, show m + 1 + 4 = m + 5 by ring] at this
  simpa only [conjT_add_five hu5] using this

end Shift

section Seed

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {R : Subgroup (Module.End k V)ˣ} {u s : (Module.End k V)ˣ}

theorem Min32.neg_one_ne_one (h : Min32 R u) : (-1 : (Module.End k V)ˣ) ≠ 1 := by
  obtain ⟨z, hz, hzV⟩ := h.center
  have hzn : (z : (Module.End k V)ˣ) = -1 := Units.ext (by rw [hzV]; simp)
  have horder : orderOf z = 2 := by rw [← Nat.card_zpowers, ← hz, h.isExtra.2.2.2]
  intro h1
  have : z = 1 := Subtype.ext (hzn.trans h1)
  rw [this, orderOf_one] at horder
  omega

theorem Min32.fpf_elem (h : Min32 R u) {r : (Module.End k V)ˣ} (hr : r ∈ R)
    (hc : u * r = r * u ∨ u * r = -(r * u)) : r = 1 ∨ r = -1 := by
  obtain ⟨hm1, hcomm, hsq, hcen⟩ := h.facts
  obtain ⟨z, hz, hzV⟩ := h.center
  have hzn : (z : (Module.End k V)ˣ) = -1 := Units.ext (by rw [hzV]; simp)
  have hzc : (-1 : (Module.End k V)ˣ) ∈ (Subgroup.center R).map R.subtype :=
    ⟨z, by rw [hz]; exact Subgroup.mem_zpowers z, hzn⟩
  have hcm : u * r * u⁻¹ * r⁻¹ ∈ (Subgroup.center R).map R.subtype := by
    rcases hc with hc | hc
    · have : u * r * u⁻¹ * r⁻¹ = 1 := by rw [hc]; group
      rw [this]; exact one_mem _
    · have : u * r * u⁻¹ * r⁻¹ = -1 := by
        rw [hc, neg_mul, neg_mul, mul_inv_cancel_right, mul_inv_cancel]
      rw [this]; exact hzc
  obtain ⟨w, hw, hwr⟩ := h.fpf r hr hcm
  apply hcen r hr
  intro y hy
  have := Subgroup.mem_center_iff.mp hw ⟨y, hy⟩
  have h2 := congrArg Subtype.val this
  rw [← hwr]
  exact h2.symm

theorem t_mem (h : Min32 R u) (hs : s ∈ R) (n : ℕ) : conjT u s n ∈ R := by
  induction n with
  | zero => simpa [conjT_zero] using hs
  | succ n ih => rw [conjT_succ]; exact (Subgroup.mem_normalizer_iff.mp h.norm _).mp ih

theorem t_sq (hs2 : s * s = 1) (n : ℕ) : conjT u s n * conjT u s n = 1 := by
  unfold conjT
  calc u ^ n * s * (u ^ n)⁻¹ * (u ^ n * s * (u ^ n)⁻¹) = u ^ n * (s * s) * (u ^ n)⁻¹ := by group
    _ = 1 := by rw [hs2]; group

theorem t_ne (hs1 : s ≠ 1) (hs1' : s ≠ -1) (n : ℕ) :
    conjT u s n ≠ 1 ∧ conjT u s n ≠ -1 := by
  constructor
  · intro h1
    apply hs1
    unfold conjT at h1
    have : u ^ n * s = u ^ n * 1 := by
      rw [mul_one]; exact (mul_inv_eq_one.mp h1)
    exact mul_left_cancel this
  · intro h1
    apply hs1'
    unfold conjT at h1
    have h2 : u ^ n * s = -1 * u ^ n := mul_inv_eq_iff_eq_mul.mp h1
    rw [neg_one_mul, ← mul_neg_one] at h2
    exact mul_left_cancel h2

theorem t_rel (h : Min32 R u) (hs : s ∈ R) (n m : ℕ) :
    conjT u s n * conjT u s m = conjT u s m * conjT u s n ∨
      conjT u s n * conjT u s m = -(conjT u s m * conjT u s n) :=
  h.facts.2.1 _ (t_mem h hs n) _ (t_mem h hs m)

theorem gen_closure (h : Min32 R u) (hu5 : u ^ 5 = 1) (hs : s ∈ R) (hs1 : s ≠ 1)
    (hs1' : s ≠ -1) :
    ∀ y ∈ R, y ∈ Subgroup.closure
      (insert (-1 : (Module.End k V)ˣ) (Set.range fun i : Fin 5 => conjT u s i.val)) := by
  set S : Set (Module.End k V)ˣ :=
    insert (-1) (Set.range fun i : Fin 5 => conjT u s i.val) with hS
  set T := Subgroup.closure S with hT
  have hTR : T ≤ R := by
    rw [hT, Subgroup.closure_le]
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact h.facts.1
    · exact t_mem h hs _
  have hfwd : ∀ y ∈ T, u * y * u⁻¹ ∈ T := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | ⟨i, rfl⟩
      · rw [conj_neg_one]; exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [← conjT_succ, ← conjT_mod_five hu5]
        apply Subgroup.subset_closure
        refine Set.mem_insert_of_mem _ ⟨(i + 1 : Fin 5), ?_⟩
        simp [Fin.val_add]
    | one => simp
    | mul x y _ _ hx hy => rw [conj_mul]; exact T.mul_mem hx hy
    | inv x _ hx =>
      have : u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
      rw [this]; exact T.inv_mem hx
  have hnorm : u ∈ Subgroup.normalizer (T : Set (Module.End k V)ˣ) :=
    mem_normalizer_of_five hu5 hfwd
  by_cases hTeq : T = R
  · intro y hy; rw [← hTeq] at hy; exact hy
  · exfalso
    have hcomm := h.minimal T hTR hTeq hnorm
    have hs0 : s ∈ T := by
      apply Subgroup.subset_closure
      refine Set.mem_insert_of_mem _ ⟨0, ?_⟩
      simp [conjT_zero]
    rcases h.fpf_elem hs (Or.inl (hcomm s hs0)) with h1 | h1
    · exact hs1 h1
    · exact hs1' h1

section Squares

variable {G : Type*} [Group G] [HasDistribNeg G]

theorem sq2_anti (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : b * a = -(a * b)) :
    (a * b) * (a * b) = -1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (-(a * b)) * b := by rw [hab]
    _ = -((a * a) * (b * b)) := by rw [mul_neg, neg_mul]; group
    _ = -1 := by rw [ha, hb, one_mul]

theorem sq2_comm (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : b * a = a * b) :
    (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

theorem sq3_acc (a b c : G) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : b * a = -(a * b)) (hac : c * a = a * c) (hbc : c * b = -(b * c)) :
    (a * (b * c)) * (a * (b * c)) = 1 := by
  calc (a * (b * c)) * (a * (b * c)) = a * b * (c * a) * (b * c) := by group
    _ = a * b * (a * c) * (b * c) := by rw [hac]
    _ = a * (b * a) * c * (b * c) := by group
    _ = a * (-(a * b)) * c * (b * c) := by rw [hab]
    _ = -((a * a) * (b * c * (b * c))) := by rw [mul_neg, neg_mul, neg_mul]; group
    _ = -(b * (c * b) * c) := by rw [ha, one_mul]; group
    _ = -(b * (-(b * c)) * c) := by rw [hbc]
    _ = -(-((b * b) * (c * c))) := by rw [mul_neg, neg_mul, neg_inj]; group
    _ = 1 := by rw [hb, hc, one_mul, neg_neg]

theorem sq3_cac (a b c : G) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : b * a = a * b) (hac : c * a = -(a * c)) (hbc : c * b = b * c) :
    (a * (b * c)) * (a * (b * c)) = -1 := by
  calc (a * (b * c)) * (a * (b * c)) = a * b * (c * a) * (b * c) := by group
    _ = a * b * (-(a * c)) * (b * c) := by rw [hac]
    _ = -(a * (b * a) * c * (b * c)) := by rw [mul_neg, neg_mul]; group
    _ = -(a * (a * b) * c * (b * c)) := by rw [hab]
    _ = -((a * a) * (b * (c * b) * c)) := by group
    _ = -(b * (b * c) * c) := by rw [ha, one_mul, hbc]
    _ = -((b * b) * (c * c)) := by group
    _ = -1 := by rw [hb, hc, one_mul]

theorem eq_neg_symm {a b : G} (h : a = -b) : b = -a := by rw [h, neg_neg]

end Squares

open Classical in
theorem e_eq_one_or (h : Min32 R u) (hu5 : u ^ 5 = 1) (hs : s ∈ R)
    (hcnt : Even (List.countP (fun a => decide (a * conjT u s 0 ≠ conjT u s 0 * a))
      [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4])) :
    conjT u s 0 * (conjT u s 1 * (conjT u s 2 * (conjT u s 3 * conjT u s 4))) = 1 ∨
      conjT u s 0 * (conjT u s 1 * (conjT u s 2 * (conjT u s 3 * conjT u s 4))) = -1 := by
  have h5 : conjT u s 5 = conjT u s 0 := by simpa using conjT_add_five hu5 s 0
  have ha0 : u * conjT u s 0 * u⁻¹ = conjT u s 1 := (conjT_succ u s 0).symm
  have ha1 : u * conjT u s 1 * u⁻¹ = conjT u s 2 := (conjT_succ u s 1).symm
  have ha2 : u * conjT u s 2 * u⁻¹ = conjT u s 3 := (conjT_succ u s 2).symm
  have ha3 : u * conjT u s 3 * u⁻¹ = conjT u s 4 := (conjT_succ u s 3).symm
  have ha4 : u * conjT u s 4 * u⁻¹ = conjT u s 5 := (conjT_succ u s 4).symm
  have hmem : ∀ n, conjT u s n ∈ R := t_mem h hs
  have heR : conjT u s 0 * (conjT u s 1 * (conjT u s 2 * (conjT u s 3 * conjT u s 4))) ∈ R :=
    R.mul_mem (hmem 0) (R.mul_mem (hmem 1) (R.mul_mem (hmem 2) (R.mul_mem (hmem 3) (hmem 4))))
  have hue : u * (conjT u s 0 * (conjT u s 1 * (conjT u s 2 * (conjT u s 3 * conjT u s 4)))) *
      u⁻¹ = conjT u s 0 * (conjT u s 1 * (conjT u s 2 * (conjT u s 3 * conjT u s 4))) := by
    have h1 : u * (conjT u s 0 * (conjT u s 1 * (conjT u s 2 * (conjT u s 3 * conjT u s 4)))) *
        u⁻¹ = conjT u s 1 * (conjT u s 2 * (conjT u s 3 * (conjT u s 4 * conjT u s 0))) := by
      rw [conj_mul, conj_mul, conj_mul, conj_mul, ha0, ha1, ha2, ha3, ha4, h5]
    have hl : ∀ a ∈ [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4],
        a * conjT u s 0 = conjT u s 0 * a ∨ a * conjT u s 0 = -(conjT u s 0 * a) := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> exact t_rel h hs _ 0
    have h2 := list_prod_mul_eq (conjT u s 0)
      (fun a => decide (a * conjT u s 0 ≠ conjT u s 0 * a)) (fun a => by simp)
      [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4] hl
    have hc1 : (-1 : (Module.End k V)ˣ) ^ (List.countP
        (fun a => decide (a * conjT u s 0 ≠ conjT u s 0 * a))
        [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4]) = 1 := hcnt.neg_one_pow
    rw [hc1, one_mul] at h2
    simp only [List.prod_cons, List.prod_nil, mul_one] at h2
    rw [h1]
    calc conjT u s 1 * (conjT u s 2 * (conjT u s 3 * (conjT u s 4 * conjT u s 0)))
        = conjT u s 1 * (conjT u s 2 * (conjT u s 3 * conjT u s 4)) * conjT u s 0 := by group
      _ = _ := h2
  exact h.fpf_elem heR (Or.inl (by
    calc u * (conjT u s 0 * (conjT u s 1 * (conjT u s 2 * (conjT u s 3 * conjT u s 4))))
        = u * (conjT u s 0 * (conjT u s 1 * (conjT u s 2 * (conjT u s 3 * conjT u s 4)))) *
            u⁻¹ * u := by group
      _ = _ * u := by rw [hue]))

open Classical in
theorem e_contra (h : Min32 R u) (hu5 : u ^ 5 = 1) (hs : s ∈ R)
    (hcnt : Even (List.countP (fun a => decide (a * conjT u s 0 ≠ conjT u s 0 * a))
      [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4]))
    (hsq : ((conjT u s 0 * conjT u s 1) * (conjT u s 0 * conjT u s 1)) *
      ((conjT u s 2 * (conjT u s 3 * conjT u s 4)) * (conjT u s 2 * (conjT u s 3 * conjT u s 4)))
        = -1) : False := by
  have hec := e_eq_one_or h hu5 hs hcnt
  set x := conjT u s 0 * conjT u s 1 with hx
  set y := conjT u s 2 * (conjT u s 3 * conjT u s 4) with hy
  have hexy : conjT u s 0 * (conjT u s 1 * (conjT u s 2 * (conjT u s 3 * conjT u s 4))) =
      x * y := by
    rw [hx, hy]; group
  rw [hexy] at hec
  have hyx : y * x = x * y := by
    rcases hec with h1 | h1
    · calc y * x = x⁻¹ * (x * y) * x := by group
        _ = x * y := by rw [h1]; group
    · calc y * x = x⁻¹ * (x * y) * x := by group
        _ = x * y := by rw [h1, mul_neg_one, neg_mul, inv_mul_cancel]
  have hε : (x * y) * (x * y) = 1 := by
    rcases hec with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, neg_mul_neg, one_mul]
  have hxy2 : (x * x) * (y * y) = 1 := by
    calc (x * x) * (y * y) = x * (x * y) * y := by group
      _ = x * (y * x) * y := by rw [hyx]
      _ = (x * y) * (x * y) := by group
      _ = 1 := hε
  rw [hxy2] at hsq
  exact h.neg_one_ne_one hsq.symm

theorem Min32.eq_neg_self_false (h : Min32 R u) {x : (Module.End k V)ˣ} (hx : x = -x) : False := by
  apply h.neg_one_ne_one
  calc (-1 : (Module.End k V)ˣ) = -(x⁻¹ * x) := by rw [inv_mul_cancel]
    _ = x⁻¹ * (-x) := by rw [mul_neg]
    _ = x⁻¹ * x := by rw [← hx]
    _ = 1 := inv_mul_cancel x

structure Pent (R : Subgroup (Module.End k V)ˣ) (u : (Module.End k V)ˣ)
    (t : Fin 5 → (Module.End k V)ˣ) : Prop where
  mem : ∀ i, t i ∈ R
  sq : ∀ i, t i * t i = 1
  anti : ∀ i j, i ≠ j → t i * t j = -(t j * t i)
  conj : ∀ i, u * t i * u⁻¹ = t (i + 1)
  gen : ∀ y ∈ R, y ∈ Subgroup.closure (insert (-1 : (Module.End k V)ˣ) (Set.range t))
  prod : t 0 * (t 1 * (t 2 * (t 3 * t 4))) = 1 ∨ t 0 * (t 1 * (t 2 * (t 3 * t 4))) = -1
  ne : ∀ i, t i ≠ 1 ∧ t i ≠ -1

open Classical in
theorem Min32.exists_pent (h : Min32 R u) (hu5 : u ^ 5 = 1) :
    ∃ t : Fin 5 → (Module.End k V)ˣ, Pent R u t := by
  obtain ⟨s, hs, hs2, hs1, hs1'⟩ := h.exists_involution
  have hgen := gen_closure h hu5 hs hs1 hs1'
  have h5 : conjT u s 5 = conjT u s 0 := by simpa using conjT_add_five hu5 s 0
  have t0 : conjT u s 0 = s := conjT_zero u s
  have hc3 : (conjT u s 0 * conjT u s 3 = conjT u s 3 * conjT u s 0) ↔
      (conjT u s 0 * conjT u s 2 = conjT u s 2 * conjT u s 0) := by
    have e1 := cm_iff_succ hu5 (s := s) 0 3
    have e2 := cm_iff_succ hu5 (s := s) 1 4
    simp only [zero_add, Nat.reduceAdd] at e1 e2
    rw [h5] at e2
    rw [e1, e2]
    exact eq_comm
  have hc4 : (conjT u s 0 * conjT u s 4 = conjT u s 4 * conjT u s 0) ↔
      (conjT u s 0 * conjT u s 1 = conjT u s 1 * conjT u s 0) := by
    have e1 := cm_iff_succ hu5 (s := s) 0 4
    simp only [zero_add, Nat.reduceAdd] at e1
    rw [h5] at e1
    rw [e1]
    exact eq_comm
  have hrel := t_rel h hs
  by_cases hP1 : conjT u s 0 * conjT u s 1 = conjT u s 1 * conjT u s 0
  · by_cases hP2 : conjT u s 0 * conjT u s 2 = conjT u s 2 * conjT u s 0
    ·
      exfalso
      have hall : ∀ i : Fin 5, s * conjT u s i.val = conjT u s i.val * s := by
        intro i
        fin_cases i
        · simp [conjT_zero]
        · simpa [conjT_zero] using hP1
        · simpa [conjT_zero] using hP2
        · simpa [conjT_zero] using hc3.mpr hP2
        · simpa [conjT_zero] using hc4.mpr hP1
      have hcomm_all : ∀ y ∈ Subgroup.closure (insert (-1 : (Module.End k V)ˣ)
          (Set.range fun i : Fin 5 => conjT u s i.val)), s * y = y * s := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem y hy =>
          rcases hy with rfl | ⟨i, rfl⟩
          · rw [mul_neg_one, neg_one_mul]
          · exact hall i
        | one => simp
        | mul x y _ _ hx hy =>
          calc s * (x * y) = (s * x) * y := by group
            _ = (x * s) * y := by rw [hx]
            _ = x * (s * y) := by group
            _ = x * (y * s) := by rw [hy]
            _ = x * y * s := by group
        | inv x _ hx =>
          calc s * x⁻¹ = x⁻¹ * (x * s) * x⁻¹ := by group
            _ = x⁻¹ * (s * x) * x⁻¹ := by rw [hx]
            _ = x⁻¹ * s := by group
      rcases h.facts.2.2.2 s hs (fun y hy => hcomm_all y (hgen y hy)) with h1 | h1
      · exact hs1 h1
      · exact hs1' h1
    ·
      exfalso
      have hA02 : conjT u s 0 * conjT u s 2 = -(conjT u s 2 * conjT u s 0) :=
        (hrel 0 2).resolve_left hP2
      have hd1 : conjT u s 1 * conjT u s 0 = conjT u s 0 * conjT u s 1 := hP1.symm
      have hd2 : conjT u s 2 * conjT u s 0 ≠ conjT u s 0 * conjT u s 2 := fun hc =>
        hP2 hc.symm
      have hd3 : conjT u s 3 * conjT u s 0 ≠ conjT u s 0 * conjT u s 3 := fun hc =>
        hP2 (hc3.mp hc.symm)
      have hd4 : conjT u s 4 * conjT u s 0 = conjT u s 0 * conjT u s 4 := (hc4.mpr hP1).symm
      have hcnt : Even (List.countP (fun a => decide (a * conjT u s 0 ≠ conjT u s 0 * a))
          [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4]) := by
        have : List.countP (fun a => decide (a * conjT u s 0 ≠ conjT u s 0 * a))
            [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4] = 2 := by
          simp [List.countP_cons, hd1, hd2, hd3, hd4]
        rw [this]; exact ⟨1, rfl⟩
      refine e_contra h hu5 hs hcnt ?_
      have hx : (conjT u s 0 * conjT u s 1) * (conjT u s 0 * conjT u s 1) = 1 :=
        sq2_comm _ _ (t_sq hs2 0) (t_sq hs2 1) hd1
      have hab : conjT u s 3 * conjT u s 2 = conjT u s 2 * conjT u s 3 := by
        simpa using (cm_add hP1 2).symm
      have hac : conjT u s 4 * conjT u s 2 = -(conjT u s 2 * conjT u s 4) := by
        have := an_add hA02 2
        simp only [zero_add, Nat.reduceAdd] at this
        exact eq_neg_symm this
      have hbc : conjT u s 4 * conjT u s 3 = conjT u s 3 * conjT u s 4 := by
        simpa using (cm_add hP1 3).symm
      rw [hx, sq3_cac _ _ _ (t_sq hs2 2) (t_sq hs2 3) (t_sq hs2 4) hab hac hbc, one_mul]
  · have hA01 : conjT u s 0 * conjT u s 1 = -(conjT u s 1 * conjT u s 0) :=
      (hrel 0 1).resolve_left hP1
    by_cases hP2 : conjT u s 0 * conjT u s 2 = conjT u s 2 * conjT u s 0
    ·
      exfalso
      have hd1 : conjT u s 1 * conjT u s 0 ≠ conjT u s 0 * conjT u s 1 := fun hc =>
        hP1 hc.symm
      have hd2 : conjT u s 2 * conjT u s 0 = conjT u s 0 * conjT u s 2 := hP2.symm
      have hd3 : conjT u s 3 * conjT u s 0 = conjT u s 0 * conjT u s 3 := (hc3.mpr hP2).symm
      have hd4 : conjT u s 4 * conjT u s 0 ≠ conjT u s 0 * conjT u s 4 := fun hc =>
        hP1 (hc4.mp hc.symm)
      have hcnt : Even (List.countP (fun a => decide (a * conjT u s 0 ≠ conjT u s 0 * a))
          [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4]) := by
        have : List.countP (fun a => decide (a * conjT u s 0 ≠ conjT u s 0 * a))
            [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4] = 2 := by
          simp [List.countP_cons, hd1, hd2, hd3, hd4]
        rw [this]; exact ⟨1, rfl⟩
      refine e_contra h hu5 hs hcnt ?_
      have hx : (conjT u s 0 * conjT u s 1) * (conjT u s 0 * conjT u s 1) = -1 :=
        sq2_anti _ _ (t_sq hs2 0) (t_sq hs2 1) (eq_neg_symm hA01)
      have hab : conjT u s 3 * conjT u s 2 = -(conjT u s 2 * conjT u s 3) := by
        have := an_add hA01 2
        simp only [zero_add, Nat.reduceAdd] at this
        exact eq_neg_symm this
      have hac : conjT u s 4 * conjT u s 2 = conjT u s 2 * conjT u s 4 := by
        simpa using (cm_add hP2 2).symm
      have hbc : conjT u s 4 * conjT u s 3 = -(conjT u s 3 * conjT u s 4) := by
        have := an_add hA01 3
        simp only [zero_add, Nat.reduceAdd] at this
        exact eq_neg_symm this
      rw [hx, sq3_acc _ _ _ (t_sq hs2 2) (t_sq hs2 3) (t_sq hs2 4) hab hac hbc, mul_one]
    ·
      have hA02 : conjT u s 0 * conjT u s 2 = -(conjT u s 2 * conjT u s 0) :=
        (hrel 0 2).resolve_left hP2
      have hA03 : conjT u s 0 * conjT u s 3 = -(conjT u s 3 * conjT u s 0) :=
        (hrel 0 3).resolve_left (fun hc => hP2 (hc3.mp hc))
      have hA04 : conjT u s 0 * conjT u s 4 = -(conjT u s 4 * conjT u s 0) :=
        (hrel 0 4).resolve_left (fun hc => hP1 (hc4.mp hc))
      have hA : ∀ d : ℕ, 1 ≤ d → d ≤ 4 →
          conjT u s 0 * conjT u s d = -(conjT u s d * conjT u s 0) := by
        intro d h1 h4
        interval_cases d
        · exact hA01
        · exact hA02
        · exact hA03
        · exact hA04
      have han : ∀ i j : ℕ, i < j → j < 5 →
          conjT u s i * conjT u s j = -(conjT u s j * conjT u s i) := by
        intro i j hij hj
        have := an_add (hA (j - i) (by omega) (by omega)) i
        rwa [Nat.zero_add, Nat.sub_add_cancel hij.le] at this
      have hanti : ∀ i j : Fin 5, i ≠ j →
          conjT u s i.val * conjT u s j.val = -(conjT u s j.val * conjT u s i.val) := by
        intro i j hij
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
        · exact han _ _ hlt j.2
        · exact eq_neg_symm (han _ _ hgt i.2)
      have hd : ∀ d : ℕ, 1 ≤ d → d ≤ 4 →
          conjT u s d * conjT u s 0 ≠ conjT u s 0 * conjT u s d := by
        intro d h1 h4 hc
        refine h.eq_neg_self_false (x := conjT u s 0 * conjT u s d) ?_
        calc conjT u s 0 * conjT u s d = -(conjT u s d * conjT u s 0) := hA d h1 h4
          _ = -(conjT u s 0 * conjT u s d) := by rw [hc]
      have hcnt : Even (List.countP (fun a => decide (a * conjT u s 0 ≠ conjT u s 0 * a))
          [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4]) := by
        have : List.countP (fun a => decide (a * conjT u s 0 ≠ conjT u s 0 * a))
            [conjT u s 1, conjT u s 2, conjT u s 3, conjT u s 4] = 4 := by
          simp [List.countP_cons, hd 1 (by norm_num) (by norm_num),
            hd 2 (by norm_num) (by norm_num), hd 3 (by norm_num) (by norm_num),
            hd 4 (by norm_num) (by norm_num)]
        rw [this]; exact ⟨2, rfl⟩
      refine ⟨fun i => conjT u s i.val, ?_⟩
      exact
        { mem := fun i => t_mem h hs _
          sq := fun i => t_sq hs2 _
          anti := hanti
          conj := fun i => by
            show u * conjT u s i.val * u⁻¹ = conjT u s (i + 1).val
            rw [← conjT_succ, ← conjT_mod_five hu5]
            simp [Fin.val_add]
          gen := hgen
          prod := e_eq_one_or h hu5 hs hcnt
          ne := fun i => t_ne hs1 hs1' _ }

end Seed

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025
