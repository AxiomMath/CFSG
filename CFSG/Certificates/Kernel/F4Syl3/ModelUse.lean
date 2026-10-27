module

public import CFSG.Certificates.Kernel.F4Syl3.Model
public import CFSG.Certificates.Kernel.F4Syl3.E81
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.F4Syl3

variable {G : Type*} [Group G]

theorem itr_fix {f : ℕ → ℕ} {a : ℕ} (h : f a = a) (n : ℕ) : itr f n a = a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [itr, ih, h]

theorem card_le_filter {S : Type*} {s : Fin 4 → G} (Q : ℕ → Bool) (e : S → G)
    (he : Function.Injective e) (h : ∀ v, ∃ x, x < 81 ∧ Q x = true ∧ e v = fS s x) :
    Nat.card S ≤ ((List.range 81).filter Q).length := by
  classical
  choose x hx hQ hxe using h
  have hmem : ∀ v, x v ∈ ((List.range 81).filter Q).toFinset := fun v => by
    simp [List.mem_filter, hx v, hQ v]
  refine le_trans (Nat.card_le_card_of_injective
    (fun v => (⟨x v, hmem v⟩ : ((List.range 81).filter Q).toFinset)) ?_) ?_
  · intro v w hvw
    apply he
    simp only [Subtype.mk.injEq] at hvw
    rw [hxe, hxe, hvw]
  · rw [Nat.card_eq_finsetCard]
    exact List.toFinset_card_le _

theorem gQ_zero (g4 g5 : G) : gQ g4 g5 0 = 1 := by simp [gQ]

theorem phi_of_lt (s : Fin 4 → G) (g4 g5 : G) {m : ℕ} (hm : m < 81) :
    phi s g4 g5 m = fS s m := by
  simp [phi, gQ, Nat.mod_eq_of_lt hm, Nat.div_eq_of_lt hm]

theorem fS_mem_T (s : Fin 4 → G) (a : ℕ) : fS s a ∈ Subgroup.closure (Set.range s) := by
  have h : ∀ i, s i ∈ Subgroup.closure (Set.range s) := fun i =>
    Subgroup.subset_closure ⟨i, rfl⟩
  simp only [fS, sE4]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (h 0) _)
    (Subgroup.pow_mem _ (h 1) _)) (Subgroup.pow_mem _ (h 2) _)) (Subgroup.pow_mem _ (h 3) _)

section Use

variable {s : Fin 4 → G} {g4 g5 : G} (hp : Pres s g4 g5)
include hp

theorem mem_P {x : G} (hx : x ∈ Subgroup.closure (gensP s g4 g5)) :
    ∃ m, m < 729 ∧ phi s g4 g5 m = x := by
  rw [← SetLike.mem_coe, coe_P hp] at hx
  exact hx

theorem phi_mem_P {m : ℕ} (hm : m < 729) : phi s g4 g5 m ∈ Subgroup.closure (gensP s g4 g5) := by
  rw [← SetLike.mem_coe, coe_P hp]
  exact ⟨m, hm, rfl⟩

theorem mem_T {x : G} (hx : x ∈ Subgroup.closure (Set.range s)) :
    ∃ a, a < 81 ∧ fS s a = x := by
  rw [← SetLike.mem_coe, coe_T hp] at hx
  exact hx

theorem phi_mul_fS (m x : ℕ) :
    phi s g4 g5 m * fS s x = fS s (actQ (m / 81) x) * phi s g4 g5 m := by
  calc phi s g4 g5 m * fS s x
      = fS s (m % 81) * (gQ g4 g5 (m / 81) * fS s x * (gQ g4 g5 (m / 81))⁻¹) *
          gQ g4 g5 (m / 81) := by
        simp only [phi, mul_assoc, inv_mul_cancel, mul_one]
    _ = fS s (m % 81) * fS s (actQ (m / 81) x) * gQ g4 g5 (m / 81) := by rw [conjQ hp]
    _ = fS s (actQ (m / 81) x) * phi s g4 g5 m := by
        rw [fS_comm hp.comm hp.cube (m % 81), phi, mul_assoc]

theorem conj_phi_fS (m x : ℕ) :
    phi s g4 g5 m * fS s x * (phi s g4 g5 m)⁻¹ = fS s (actQ (m / 81) x) := by
  rw [phi_mul_fS hp, mul_inv_cancel_right]

theorem phi_comm_fS (hm : ModelOK) (m : ℕ) {x : ℕ} (hx : x < 81) :
    phi s g4 g5 m * fS s x = fS s x * phi s g4 g5 m ↔ actQ (m / 81) x = x := by
  rw [phi_mul_fS hp]
  constructor
  · intro h
    exact fS_injOn hp hm (actQ_lt _ hx) hx (mul_right_cancel h)
  · intro h
    rw [h]

omit hp in
theorem actQ_26 (hm : ModelOK) (q : ℕ) : actQ q 26 = 26 := by
  obtain ⟨-, -, -, -, -, -, -, h4, h5, -⟩ := hm
  rw [actQ, itr_fix h5, itr_fix h4]

theorem z_central (hm : ModelOK) {x : G} (hx : x ∈ Subgroup.closure (gensP s g4 g5)) :
    x * fS s 26 = fS s 26 * x := by
  obtain ⟨m, -, rfl⟩ := mem_P hp hx
  have e := phi_mul_fS hp m 26
  rwa [actQ_26 hm] at e

theorem phi_cube_mem (m : ℕ) : phi s g4 g5 m ^ 3 ∈ Subgroup.closure (Set.range s) := by
  have e : phi s g4 g5 m ^ 3 = phi s g4 g5 (pmul (pmul m m) m) := by
    rw [phi_pmul hp, phi_pmul hp, pow_succ, pow_two]
  have hq : qadd (qadd (m / 81) (m / 81)) (m / 81) = 0 := by
    simp only [qadd]
    omega
  rw [e, phi, pmul_div, pmul_div, hq, gQ_zero, mul_one]
  exact fS_mem_T s _

theorem phi_div_mem {n p : ℕ} (h : n / 81 = p / 81) :
    phi s g4 g5 n * (phi s g4 g5 p)⁻¹ ∈ Subgroup.closure (Set.range s) := by
  simp only [phi, h, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  exact Subgroup.mul_mem _ (fS_mem_T s _) (Subgroup.inv_mem _ (fS_mem_T s _))

theorem phi_not_mem_T {m : ℕ} (h : phi s g4 g5 m ∉ Subgroup.closure (Set.range s)) :
    m / 81 ≠ 0 := by
  intro h0
  apply h
  rw [phi, h0, gQ_zero, mul_one]
  exact fS_mem_T s _

theorem e81_unique (hm : ModelOK) {B : Subgroup G} (hBP : B ≤ Subgroup.closure (gensP s g4 g5))
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBc : Nat.card B = 81) :
    B = Subgroup.closure (Set.range s) := by
  have hTP := T_le_P s g4 g5
  have hPc : Nat.card (Subgroup.closure (gensP s g4 g5)) = 729 := card_P hp hm
  have : Finite (Subgroup.closure (gensP s g4 g5)) :=
    Nat.finite_of_card_ne_zero (by rw [hPc]; decide)
  have hP : ∀ g : Subgroup.closure (gensP s g4 g5), ∃ m, m < 729 ∧ phi s g4 g5 m = g :=
    fun g => mem_P hp g.2
  have hVn : ((Subgroup.closure (Set.range s)).subgroupOf (Subgroup.closure (gensP s g4 g5))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨x, -, hxe⟩ := mem_T hp hn
      obtain ⟨m, -, hme⟩ := hP g
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hxe, ← hme, conj_phi_fS hp m x]
      exact fS_mem_T s _⟩
  have hVc : Nat.card ((Subgroup.closure (Set.range s)).subgroupOf
      (Subgroup.closure (gensP s g4 g5))) = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv]
    exact card_T hp hm
  have hidx : ((Subgroup.closure (Set.range s)).subgroupOf
      (Subgroup.closure (gensP s g4 g5))).index ≤ 9 := by
    have := Subgroup.card_mul_index ((Subgroup.closure (Set.range s)).subgroupOf
      (Subgroup.closure (gensP s g4 g5)))
    rw [hVc, hPc] at this
    omega
  have hcube : ∀ g : Subgroup.closure (gensP s g4 g5), g ^ 3 ∈
      (Subgroup.closure (Set.range s)).subgroupOf (Subgroup.closure (gensP s g4 g5)) := by
    intro g
    rw [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow]
    obtain ⟨m, -, hme⟩ := hP g
    rw [← hme]
    exact phi_cube_mem hp m
  have h1 : ∀ g : Subgroup.closure (gensP s g4 g5), g ∉
      (Subgroup.closure (Set.range s)).subgroupOf (Subgroup.closure (gensP s g4 g5)) →
      Nat.card {v : Subgroup.closure (gensP s g4 g5) // v ∈
        (Subgroup.closure (Set.range s)).subgroupOf (Subgroup.closure (gensP s g4 g5)) ∧
          g * v = v * g} ≤ 9 := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨m, hm729, hme⟩ := hP g
    rw [← hme] at hg
    have hq := phi_not_mem_T hp hg
    rw [← hm.2.2.2.2.2.2.2.2.2.1 (m / 81) (by omega) hq]
    refine card_le_filter (s := s) _ (fun v => ((v.1 : Subgroup.closure (gensP s g4 g5)) : G))
      (fun v w h => Subtype.ext (Subtype.ext h)) fun v => ?_
    obtain ⟨x, hx, hxe⟩ := mem_T hp ((Subgroup.mem_subgroupOf).1 v.2.1)
    have hc := congrArg Subtype.val v.2.2
    simp only [Subgroup.coe_mul] at hc
    rw [← hme, ← hxe, phi_comm_fS hp hm m hx] at hc
    exact ⟨x, hx, beq_iff_eq.2 hc, hxe.symm⟩
  have h2 : ∀ g h : Subgroup.closure (gensP s g4 g5), g ∉
      (Subgroup.closure (Set.range s)).subgroupOf (Subgroup.closure (gensP s g4 g5)) →
      (∀ (k : ℕ), ∀ v ∈ (Subgroup.closure (Set.range s)).subgroupOf
        (Subgroup.closure (gensP s g4 g5)), h ≠ v * g ^ k) →
      Nat.card {v : Subgroup.closure (gensP s g4 g5) // v ∈
        (Subgroup.closure (Set.range s)).subgroupOf (Subgroup.closure (gensP s g4 g5)) ∧
          g * v = v * g ∧ h * v = v * h} ≤ 3 := by
    intro g h hg hout
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨m, hm729, hme⟩ := hP g
    obtain ⟨n, hn729, hne⟩ := hP h
    rw [← hme] at hg
    have hq := phi_not_mem_T hp hg
    have hk : ∀ (k p : ℕ), phi s g4 g5 p = (g : G) ^ k → n / 81 = p / 81 → False := by
      intro k p hpk hr
      refine hout k ⟨(h : G) * ((g : G) ^ k)⁻¹, Subgroup.mul_mem _ h.2
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ g.2 k))⟩ ?_ ?_
      · rw [Subgroup.mem_subgroupOf]
        simp only
        rw [← hpk, ← hne]
        exact phi_div_mem hp hr
      · apply Subtype.ext
        simp
    have hr0 : n / 81 ≠ 0 := fun e => hk 0 0 (by rw [phi_zero hp, pow_zero]) (by rw [e])
    have hrq : n / 81 ≠ m / 81 := fun e => hk 1 m (by rw [hme, pow_one]) e
    have hrqq : n / 81 ≠ qadd (m / 81) (m / 81) := fun e =>
      hk 2 (pmul m m) (by rw [phi_pmul hp, hme, pow_two]) (by rw [pmul_div, e])
    rw [← hm.2.2.2.2.2.2.2.2.2.2 (m / 81) (by omega) (n / 81) (by omega) hq hr0 hrq hrqq]
    refine card_le_filter (s := s) _ (fun v => ((v.1 : Subgroup.closure (gensP s g4 g5)) : G))
      (fun v w h => Subtype.ext (Subtype.ext h)) fun v => ?_
    obtain ⟨x, hx, hxe⟩ := mem_T hp ((Subgroup.mem_subgroupOf).1 v.2.1)
    have hc := congrArg Subtype.val v.2.2.1
    have hd := congrArg Subtype.val v.2.2.2
    simp only [Subgroup.coe_mul] at hc hd
    rw [← hme, ← hxe, phi_comm_fS hp hm m hx] at hc
    rw [← hne, ← hxe, phi_comm_fS hp hm n hx] at hd
    refine ⟨x, hx, ?_, hxe.symm⟩
    simp [hc, hd]
  have hB' : ∀ x ∈ B.subgroupOf (Subgroup.closure (gensP s g4 g5)),
      ∀ y ∈ B.subgroupOf (Subgroup.closure (gensP s g4 g5)), x * y = y * x := by
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf] at hx hy
    exact Subtype.ext (hB _ hx _ hy)
  have hBc' : Nat.card (B.subgroupOf (Subgroup.closure (gensP s g4 g5))) = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv]
    exact hBc
  have e := eq_of_comm_of_card _ _ hVc hidx hcube h1 h2 hB' hBc'
  have e2 := Subgroup.subgroupOf_inj.1 e
  rwa [inf_of_le_left hBP, inf_of_le_left hTP] at e2

omit hp in
theorem coverGo_spec {reps : List ℕ} :
    ∀ (rows : List (ℕ × ℕ)) (m0 : ℕ), coverGo reps m0 rows = true → ∀ i, i < rows.length →
      m0 + i ≠ 0 → pmul (pmul (m0 + i) (m0 + i)) (m0 + i) = 0 →
      (rows.getD i (0, 0)).2 < 48 ∧ pmul (rows.getD i (0, 0)).1 (m0 + i) =
        pmul (reps.getD (rows.getD i (0, 0)).2 0) (rows.getD i (0, 0)).1
  | [], _, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | (c, k) :: rows, m0, h, i, hi, h0, h3 => by
    simp only [coverGo, Bool.and_eq_true] at h
    cases i with
    | zero =>
      have h' := h.1
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true,
        decide_eq_true_eq] at h'
      simp only [Nat.add_zero] at h0 h3
      simp only [List.getD_cons_zero, Nat.add_zero]
      rcases h' with (h' | h') | h'
      · exact absurd h' h0
      · exact absurd h3 h'
      · exact h'
    | succ i =>
      have e : m0 + (i + 1) = m0 + 1 + i := by omega
      rw [e] at h0 h3 ⊢
      simp only [List.getD_cons_succ]
      exact coverGo_spec rows (m0 + 1) h.2 i (by simp at hi; omega) h0 h3

omit hp in
theorem cover_spec {reps tgt : List ℕ} {cover : List (ℕ × ℕ)} (h : coverChk reps tgt cover = true)
    {m : ℕ} (hm : m < 729) (h0 : m ≠ 0) (h3 : pmul (pmul m m) m = 0) :
    (cover.getD m (0, 0)).2 < 48 ∧ pmul (cover.getD m (0, 0)).1 m =
      pmul (reps.getD (cover.getD m (0, 0)).2 0) (cover.getD m (0, 0)).1 := by
  simp only [coverChk, Bool.and_eq_true, beq_iff_eq] at h
  have := coverGo_spec cover 0 h.2 m (by omega) (by omega) (by rwa [Nat.zero_add])
  simpa only [Nat.zero_add] using this

omit hp in
theorem tgt_lt {reps tgt : List ℕ} {cover : List (ℕ × ℕ)} (h : coverChk reps tgt cover = true)
    {k : ℕ} (hk : k < 48) : tgt.getD k 3 < 3 := by
  simp only [coverChk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hl⟩, ha⟩, -⟩, -⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact of_decide_eq_true (List.all_eq_true.1 ha _ (List.getElem_mem _))

theorem conj_rep (hm : ModelOK) {reps tgt : List ℕ} {cover : List (ℕ × ℕ)}
    (hcov : coverChk reps tgt cover = true) {x : G} (hx : x ∈ Subgroup.closure (gensP s g4 g5))
    (h1 : x ≠ 1) (h3 : x ^ 3 = 1) :
    ∃ m, m < 729 ∧ phi s g4 g5 m = x ∧ (cover.getD m (0, 0)).2 < 48 ∧
      IsConj x (phi s g4 g5 (reps.getD (cover.getD m (0, 0)).2 0)) := by
  obtain ⟨m, hm729, rfl⟩ := mem_P hp hx
  have h0 : m ≠ 0 := by
    rintro rfl
    exact h1 (phi_zero hp)
  have hc : pmul (pmul m m) m = 0 := by
    refine phi_injOn hp hm (pmul_lt _ _) (by decide : (0 : ℕ) < 729) ?_
    rw [phi_pmul hp, phi_pmul hp, phi_zero hp, ← h3, pow_succ, pow_two]
  obtain ⟨hk, he⟩ := cover_spec hcov hm729 h0 hc
  refine ⟨m, hm729, rfl, hk, isConj_iff.2 ⟨phi s g4 g5 (cover.getD m (0, 0)).1, ?_⟩⟩
  rw [← phi_pmul hp, he, phi_pmul hp, mul_inv_cancel_right]

theorem class_cover (hm : ModelOK) {reps tgt : List ℕ} {cover : List (ℕ × ℕ)}
    (hcov : coverChk reps tgt cover = true) (trg : ℕ → G)
    (hrep : ∀ k, k < 48 → IsConj (phi s g4 g5 (reps.getD k 0)) (trg (tgt.getD k 3))) {x : G}
    (hx : x ∈ Subgroup.closure (gensP s g4 g5)) (h1 : x ≠ 1) (h3 : x ^ 3 = 1) :
    IsConj x (trg 0) ∨ IsConj x (trg 1) ∨ IsConj x (trg 2) := by
  obtain ⟨m, -, -, hk, hc⟩ := conj_rep hp hm hcov hx h1 h3
  have ht := tgt_lt hcov hk
  have hc' := hc.trans (hrep _ hk)
  rcases (by omega : tgt.getD (cover.getD m (0, 0)).2 3 = 0 ∨
      tgt.getD (cover.getD m (0, 0)).2 3 = 1 ∨ tgt.getD (cover.getD m (0, 0)).2 3 = 2)
    with h | h | h <;> rw [h] at hc'
  · exact Or.inl hc'
  · exact Or.inr (Or.inl hc')
  · exact Or.inr (Or.inr hc')

theorem lines_T (hm : ModelOK) {reps tgt lineA lineB : List ℕ} {cover : List (ℕ × ℕ)}
    (hcov : coverChk reps tgt cover = true) (hline : lineChk tgt cover lineA lineB = true)
    (trg : ℕ → G)
    (hrep : ∀ k, k < 48 → IsConj (phi s g4 g5 (reps.getD k 0)) (trg (tgt.getD k 3))) :
    ∃ LA LB : Finset (Subgroup G), LA.card ≤ 12 ∧ LB.card ≤ 12 ∧
      ∀ d ∈ Subgroup.closure (Set.range s), d ≠ 1 →
        (IsConj d (trg 0) ∧ Subgroup.zpowers d ∈ LA) ∨
          (IsConj d (trg 1) ∧ Subgroup.zpowers d ∈ LB) ∨ IsConj d (trg 2) := by
  classical
  simp only [lineChk, Bool.and_eq_true, decide_eq_true_eq] at hline
  obtain ⟨⟨hA, hB⟩, hall⟩ := hline
  refine ⟨(lineA.map fun v => Subgroup.zpowers (fS s v)).toFinset,
    (lineB.map fun v => Subgroup.zpowers (fS s v)).toFinset,
    (List.toFinset_card_le _).trans (by rw [List.length_map]; exact hA),
    (List.toFinset_card_le _).trans (by rw [List.length_map]; exact hB), ?_⟩
  intro d hd h1
  obtain ⟨v, hv, rfl⟩ := mem_T hp hd
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact h1 fS_zero
  obtain ⟨m, hm729, hme, hk, hc⟩ :=
    conj_rep hp hm hcov (T_le_P s g4 g5 hd) h1 (T_cube hp hd)
  have hmv : m = v := by
    refine phi_injOn hp hm hm729 (by omega : v < 729) ?_
    rw [hme, phi_of_lt s g4 g5 hv]
  subst hmv
  have hc' := hc.trans (hrep _ hk)
  have hl := List.all_eq_true.1 hall m (List.mem_range.2 hv)
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true,
    List.contains_iff_mem, hv0, false_or, tgtOf] at hl
  have hmem : ∀ L : List ℕ, (m ∈ L ∨ vneg m ∈ L) →
      Subgroup.zpowers (fS s m) ∈ (L.map fun v => Subgroup.zpowers (fS s v)).toFinset := by
    intro L hL
    rw [List.mem_toFinset, List.mem_map]
    rcases hL with hL | hL
    · exact ⟨m, hL, rfl⟩
    · exact ⟨vneg m, hL, by rw [← fS_inv hp.comm hp.cube, Subgroup.zpowers_inv]⟩
  have ht := tgt_lt hcov hk
  rcases (by omega : tgt.getD (cover.getD m (0, 0)).2 3 = 0 ∨
      tgt.getD (cover.getD m (0, 0)).2 3 = 1 ∨ tgt.getD (cover.getD m (0, 0)).2 3 = 2)
    with h | h | h <;> rw [h] at hc' hl
  · refine Or.inl ⟨hc', hmem _ ?_⟩
    rcases hl.1 with (h' | h') | h'
    · exact absurd rfl h'
    · exact Or.inl h'
    · exact Or.inr h'
  · refine Or.inr (Or.inl ⟨hc', hmem _ ?_⟩)
    rcases hl.2 with (h' | h') | h'
    · exact absurd rfl h'
    · exact Or.inl h'
    · exact Or.inr h'
  · exact Or.inr (Or.inr hc')

end Use

end CFSG.KC.F4Syl3

end
