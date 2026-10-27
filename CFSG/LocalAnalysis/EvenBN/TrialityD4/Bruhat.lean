module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Torus
public import Mathlib.Data.Set.Card.Arithmetic

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped Pointwise

section Products

variable {G : Type*} [Group G]

theorem ncard_mul_mul_card_inf (A B : Subgroup G) :
    ((A : Set G) * (B : Set G)).ncard * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set G)
  have himg : Nat.card ↥((A : Set G).image ((↑) : G → G ⧸ B)) = B.relIndex A := by
    have horb : MulAction.orbit ↥A ((1 : G) : G ⧸ B) = (A : Set G).image ((↑) : G → G ⧸ B) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : G), a.2, by simp [Subgroup.smul_def]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    have hstab : MulAction.stabilizer ↥A ((1 : G) : G ⧸ B) = B.subgroupOf A := by
      ext a
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have : (a • ((1 : G) : G ⧸ B)) = ((a : G) : G ⧸ B) := by
        simp [Subgroup.smul_def]
      rw [this, QuotientGroup.eq]
      constructor
      · intro h
        simpa using B.inv_mem h
      · intro h
        simpa using B.inv_mem h
    have := MulAction.index_stabilizer ↥A ((1 : G) : G ⧸ B)
    rw [hstab] at this
    rw [← horb, Nat.card_coe_set_eq, ← this]
    rfl
  have h2 := Subgroup.relIndex_mul_card B A
  rw [inf_comm B A] at h2
  rw [← Nat.card_coe_set_eq, h1, himg]
  calc Nat.card ↥B * B.relIndex A * Nat.card ↥(A ⊓ B)
      = Nat.card ↥B * (B.relIndex A * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h2]; ring

end Products

@[expose] def genStep : Bool → Fin 6 → Option (Fin 6)
  | false => ![none, some 4, some 3, some 2, some 1, some 5]
  | true => ![some 2, none, some 0, some 3, some 5, some 4]

@[expose] def genAct (b : Bool) (r : Bool × Fin 6) : Bool × Fin 6 :=
  match genStep b r.2 with
  | some j => (r.1, j)
  | none => (!r.1, r.2)

@[expose] def wordAct : List Bool → Bool × Fin 6 → Bool × Fin 6
  | [], r => r
  | b :: l, r => genAct b (wordAct l r)

@[expose] def posAct : List Bool → Fin 6 → Option (Fin 6)
  | [], i => some i
  | b :: l, i => (posAct l i).bind (genStep b)

@[expose] def weylList : Fin 12 → List Bool :=
  ![[], [false], [true], [false, true], [true, false], [false, true, false],
    [true, false, true], [false, true, false, true], [true, false, true, false],
    [false, true, false, true, false], [true, false, true, false, true],
    [false, true, false, true, false, true]]

@[expose] def genMul : Bool → Fin 12 → Fin 12
  | false => ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10]
  | true => ![2, 4, 0, 6, 1, 8, 3, 10, 5, 11, 7, 9]

@[expose] def posPat (k : Fin 12) (i : Fin 6) : Bool :=
  !(wordAct (weylList k) (false, i)).1

@[expose] def posDeg (P : Fin 6 → Bool) : ℕ :=
  (bif P 0 then 3 else 0) + (bif P 1 then 1 else 0) + (bif P 2 then 3 else 0) +
    (bif P 3 then 3 else 0) + (bif P 4 then 1 else 0) + (bif P 5 then 1 else 0)

theorem posDeg_add_posDeg_not (P : Fin 6 → Bool) : posDeg P + posDeg (fun i => !P i) = 12 := by
  simp only [posDeg]
  cases P 0 <;> cases P 1 <;> cases P 2 <;> cases P 3 <;> cases P 4 <;> cases P 5 <;> rfl

theorem posDeg_not_posPat :
    (fun k => posDeg fun i => !posPat k i) = ![0, 3, 1, 4, 4, 7, 5, 8, 8, 11, 9, 12] := by
  decide

theorem posPat_eleven : posPat 11 = fun _ => false := by
  decide

@[expose] def coordSet (A : Type*) [Zero A] (b : Bool) : Set A :=
  bif b then Set.univ else {0}

theorem coordSet_inter (A : Type*) [Zero A] (b b' : Bool) :
    coordSet A b ∩ coordSet A b' = coordSet A (b && b') := by
  cases b <;> cases b' <;> simp [coordSet]

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

@[expose] def rootGroup : Fin 6 → Subgroup X :=
  ![d.U₁, d.U₂, d.U₃, d.U₄, d.U₅, d.U₆]

@[expose] def gen (b : Bool) : X :=
  bif b then d.v else d.u

@[expose] def word (l : List Bool) : X :=
  (l.map d.gen).prod

@[expose] def weylWord (k : Fin 12) : X :=
  d.word (weylList k)

@[expose] def w₀ : X :=
  d.weylWord 11

@[expose] def conjS (w : X) : Subgroup X :=
  MulAut.conj w⁻¹ • d.S

@[expose] def conjB (w : X) : Subgroup X :=
  MulAut.conj w⁻¹ • d.B

@[expose] def Uminus (w : X) : Subgroup X :=
  ⨆ (i : Fin 6) (_ : ¬ d.rootGroup i ≤ d.conjS w), d.rootGroup i

@[expose] def cell (w : X) : Set X :=
  {g | ∃ b ∈ d.B, ∃ s ∈ d.S, b * w * s = g}

theorem word_nil : d.word [] = 1 :=
  rfl

theorem word_cons (b : Bool) (l : List Bool) : d.word (b :: l) = d.gen b * d.word l := by
  simp [word]

theorem gen_mul_self (b : Bool) : d.gen b * d.gen b = 1 := by
  cases b
  · exact d.u_mul_self
  · exact d.v_mul_self

theorem gen_inv (b : Bool) : (d.gen b)⁻¹ = d.gen b :=
  inv_eq_of_mul_eq_one_right (d.gen_mul_self b)

theorem gen_mem_weyl (b : Bool) : d.gen b ∈ d.weyl := by
  cases b
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem word_mem_weyl (l : List Bool) : d.word l ∈ d.weyl := by
  induction l with
  | nil => exact one_mem _
  | cons b l ih =>
    rw [word_cons]
    exact mul_mem (d.gen_mem_weyl b) ih

theorem weylWord_mem_weyl (k : Fin 12) : d.weylWord k ∈ d.weyl :=
  d.word_mem_weyl _

theorem uvuvuv_eq : d.u * (d.v * (d.u * (d.v * (d.u * d.v)))) =
    d.v * (d.u * (d.v * (d.u * (d.v * d.u)))) := by
  have h6 : (d.u * d.v) ^ 6 = 1 := by
    rw [← d.orderOf_u_mul_v]
    exact pow_orderOf_eq_one _
  have h3 : (d.u * d.v) ^ 3 = (d.v * d.u) ^ 3 := by
    have h : (d.u * d.v) ^ 3 * (d.u * d.v) ^ 3 = 1 := by
      rw [← pow_add]
      exact h6
    rw [eq_inv_of_mul_eq_one_left h, ← inv_pow, mul_inv_rev, d.u_inv, d.v_inv]
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h3

theorem w₀_eq : d.w₀ = d.u * (d.v * (d.u * (d.v * (d.u * d.v)))) := by
  simp [w₀, weylWord, weylList, word, gen]

theorem w₀_mul_self : d.w₀ * d.w₀ = 1 := by
  have h6 : (d.u * d.v) ^ 6 = 1 := by
    rw [← d.orderOf_u_mul_v]
    exact pow_orderOf_eq_one _
  have e : d.w₀ = (d.u * d.v) ^ 3 := by
    rw [d.w₀_eq]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e, ← pow_add]
  exact h6

theorem gen_mul_w₀ (b : Bool) : d.gen b * d.w₀ = d.w₀ * d.gen b := by
  have uu (a : X) : d.u * (d.u * a) = a := by rw [← mul_assoc, d.u_mul_self, one_mul]
  have vv (a : X) : d.v * (d.v * a) = a := by rw [← mul_assoc, d.v_mul_self, one_mul]
  cases b
  · change d.u * d.w₀ = d.w₀ * d.u
    conv_rhs => rw [d.w₀_eq, d.uvuvuv_eq]
    rw [d.w₀_eq]
    simp only [mul_assoc, uu, d.u_mul_self, mul_one]
  · change d.v * d.w₀ = d.w₀ * d.v
    conv_lhs => rw [d.w₀_eq, d.uvuvuv_eq]
    rw [d.w₀_eq]
    simp only [mul_assoc, vv, d.v_mul_self, mul_one]

theorem gen_mul_weylWord (b : Bool) (k : Fin 12) :
    d.gen b * d.weylWord k = d.weylWord (genMul b k) := by
  have uu (a : X) : d.u * (d.u * a) = a := by rw [← mul_assoc, d.u_mul_self, one_mul]
  have vv (a : X) : d.v * (d.v * a) = a := by rw [← mul_assoc, d.v_mul_self, one_mul]
  have b1 := d.uvuvuv_eq
  cases b <;> fin_cases k <;>
    simp [weylWord, weylList, word, gen, genMul, uu, vv, d.u_mul_self, d.v_mul_self]
  · exact b1.symm
  · rw [b1, vv]

theorem exists_weylWord_eq {w : X} (hw : w ∈ d.weyl) : ∃ k, d.weylWord k = w := by
  refine Subgroup.closure_induction_left (p := fun w _ => ∃ k, d.weylWord k = w)
    ⟨0, rfl⟩ ?_ ?_ hw
  · rintro x hx y - ⟨k, rfl⟩
    rcases hx with rfl | rfl
    · exact ⟨genMul false k, (d.gen_mul_weylWord false k).symm⟩
    · exact ⟨genMul true k, (d.gen_mul_weylWord true k).symm⟩
  · rintro x hx y - ⟨k, rfl⟩
    rcases hx with rfl | rfl
    · rw [d.u_inv]
      exact ⟨genMul false k, (d.gen_mul_weylWord false k).symm⟩
    · rw [d.v_inv]
      exact ⟨genMul true k, (d.gen_mul_weylWord true k).symm⟩

theorem smul_rangeSubgroup {A : Type*} [AddGroup A] {x x' : A → X}
    (hx : ∀ a b, x (a + b) = x a * x b) (hx' : ∀ a b, x' (a + b) = x' a * x' b) {w : X}
    (hw : w * w = 1) (h : ∀ a, w * x a * w = x' a) :
    MulAut.conj w • rangeSubgroup hx = rangeSubgroup hx' := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  ext y
  rw [mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, by rw [MulAut.smul_def, MulAut.conj_apply, hwi, h]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨x a, ⟨a, rfl⟩, by rw [MulAut.smul_def, MulAut.conj_apply, hwi, h]⟩

theorem conj_symm_of_involution {A : Type*} {x x' : A → X} {w : X} (hw : w * w = 1)
    (h : ∀ a, w * x a * w = x' a) (a : A) : w * x' a * w = x a := by
  rw [← h a, ← mul_assoc, ← mul_assoc, hw, one_mul, mul_assoc, hw, mul_one]

theorem smul_rootGroup_of_genStep {b : Bool} {i j : Fin 6} (h : genStep b i = some j) :
    MulAut.conj (d.gen b) • d.rootGroup i = d.rootGroup j := by
  have u₄ := conj_symm_of_involution d.u_mul_self d.u_x₃
  have u₅ := conj_symm_of_involution d.u_mul_self d.u_x₂
  have v₃ := conj_symm_of_involution d.v_mul_self d.v_x₁
  have v₆ := conj_symm_of_involution d.v_mul_self d.v_x₅
  cases b <;> fin_cases i <;> simp [genStep] at h <;> subst h
  · exact smul_rangeSubgroup d.x₂_add d.x₅_add d.u_mul_self d.u_x₂
  · exact smul_rangeSubgroup d.x₃_add d.x₄_add d.u_mul_self d.u_x₃
  · exact smul_rangeSubgroup d.x₄_add d.x₃_add d.u_mul_self u₄
  · exact smul_rangeSubgroup d.x₅_add d.x₂_add d.u_mul_self u₅
  · exact smul_rangeSubgroup d.x₆_add d.x₆_add d.u_mul_self d.u_x₆
  · exact smul_rangeSubgroup d.x₁_add d.x₃_add d.v_mul_self d.v_x₁
  · exact smul_rangeSubgroup d.x₃_add d.x₁_add d.v_mul_self v₃
  · exact smul_rangeSubgroup d.x₄_add d.x₄_add d.v_mul_self d.v_x₄
  · exact smul_rangeSubgroup d.x₅_add d.x₆_add d.v_mul_self d.v_x₅
  · exact smul_rangeSubgroup d.x₆_add d.x₅_add d.v_mul_self v₆

theorem smul_rootGroup_of_posAct {l : List Bool} {i j : Fin 6} (h : posAct l i = some j) :
    MulAut.conj (d.word l) • d.rootGroup i = d.rootGroup j := by
  induction l generalizing j with
  | nil =>
    simp only [posAct, Option.some.injEq] at h
    subst h
    rw [word_nil, map_one, one_smul]
  | cons b l ih =>
    obtain ⟨k, hk, hkj⟩ := Option.bind_eq_some_iff.1 h
    rw [word_cons, map_mul, mul_smul, ih hk, d.smul_rootGroup_of_genStep hkj]

theorem smul_rootGroup_zero_u :
    MulAut.conj d.u • d.rootGroup 0 = MulAut.conj d.w₀ • d.rootGroup 0 := by
  have e : d.w₀ = d.u * d.word [true, false, true, false, true] := by
    rw [d.w₀_eq]
    simp [word, gen]
  rw [e, map_mul, mul_smul,
    d.smul_rootGroup_of_posAct (l := [true, false, true, false, true]) (i := 0) (j := 0)
      (by decide)]

theorem smul_rootGroup_one_v :
    MulAut.conj d.v • d.rootGroup 1 = MulAut.conj d.w₀ • d.rootGroup 1 := by
  have e : d.w₀ = d.v * d.word [false, true, false, true, false] := by
    rw [d.w₀_eq, d.uvuvuv_eq]
    simp [word, gen]
  rw [e, map_mul, mul_smul,
    d.smul_rootGroup_of_posAct (l := [false, true, false, true, false]) (i := 1) (j := 1)
      (by decide)]

@[expose] def signedRootGroup (r : Bool × Fin 6) : Subgroup X :=
  bif r.1 then MulAut.conj d.w₀ • d.rootGroup r.2 else d.rootGroup r.2

theorem smul_signedRootGroup_gen (b : Bool) (r : Bool × Fin 6) :
    MulAut.conj (d.gen b) • d.signedRootGroup r = d.signedRootGroup (genAct b r) := by
  obtain ⟨ε, i⟩ := r
  have hcomm : MulAut.conj (d.gen b) * MulAut.conj d.w₀ =
      MulAut.conj d.w₀ * MulAut.conj (d.gen b) := by
    rw [← map_mul, ← map_mul, d.gen_mul_w₀]
  have hw₀ : MulAut.conj d.w₀ * MulAut.conj d.w₀ = 1 := by
    rw [← map_mul, d.w₀_mul_self, map_one]
  rcases hstep : genStep b i with _ | j
  · have hneg : MulAut.conj (d.gen b) • d.rootGroup i = MulAut.conj d.w₀ • d.rootGroup i := by
      cases b <;> fin_cases i <;> simp [genStep] at hstep
      · exact d.smul_rootGroup_zero_u
      · exact d.smul_rootGroup_one_v
    cases ε
    · simp only [genAct, hstep, signedRootGroup, Bool.not_false, Bool.cond_true, Bool.cond_false]
      exact hneg
    · simp only [genAct, hstep, signedRootGroup, Bool.not_true, Bool.cond_true, Bool.cond_false]
      rw [← mul_smul, hcomm, mul_smul, hneg, ← mul_smul, hw₀, one_smul]
  · have hpos := d.smul_rootGroup_of_genStep hstep
    cases ε
    · simpa only [genAct, hstep, signedRootGroup, Bool.cond_false] using hpos
    · simp only [genAct, hstep, signedRootGroup, Bool.cond_true]
      rw [← mul_smul, hcomm, mul_smul, hpos]

theorem smul_signedRootGroup_word (l : List Bool) (r : Bool × Fin 6) :
    MulAut.conj (d.word l) • d.signedRootGroup r = d.signedRootGroup (wordAct l r) := by
  induction l with
  | nil =>
    rw [word_nil, map_one, one_smul]
    rfl
  | cons b l ih =>
    rw [word_cons, map_mul, mul_smul, ih, d.smul_signedRootGroup_gen]
    rfl

theorem smul_rootGroup_weylWord (k : Fin 12) (i : Fin 6) :
    MulAut.conj (d.weylWord k) • d.rootGroup i =
      d.signedRootGroup (wordAct (weylList k) (false, i)) :=
  d.smul_signedRootGroup_word _ (false, i)

theorem mem_conj_inv_smul {w g : X} {H : Subgroup X} :
    g ∈ MulAut.conj w⁻¹ • H ↔ w * g * w⁻¹ ∈ H := by
  rw [mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, MulAut.smul_def,
    MulAut.conj_apply]

theorem le_conjS_iff {w : X} {U : Subgroup X} : U ≤ d.conjS w ↔ MulAut.conj w • U ≤ d.S := by
  rw [conjS, subset_pointwise_smul_iff, ← map_inv, inv_inv]

theorem conjS_le_conjB (w : X) : d.conjS w ≤ d.conjB w :=
  pointwise_smul_le_pointwise_smul_iff.2 le_sup_left

theorem rootGroup_le_S (i : Fin 6) : d.rootGroup i ≤ d.S := by
  fin_cases i <;> rintro _ ⟨a, rfl⟩ <;> exact subset_closure (by simp)

theorem rootGroup_ne_bot (i : Fin 6) : d.rootGroup i ≠ ⊥ := by
  have key {A : Type} [AddGroup A] [Nontrivial A] {x : A → X}
      (hx : ∀ a b, x (a + b) = x a * x b) (hxi : Function.Injective x) :
      rangeSubgroup hx ≠ ⊥ := by
    intro h
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    have h1 : x a ∈ rangeSubgroup hx := ⟨a, rfl⟩
    rw [h, mem_bot, ← map_zero_of_add hx] at h1
    exact ha (hxi h1)
  fin_cases i
  · exact key d.x₁_add d.x₁_injective
  · exact key d.x₂_add d.x₂_injective
  · exact key d.x₃_add d.x₃_injective
  · exact key d.x₄_add d.x₄_injective
  · exact key d.x₅_add d.x₅_injective
  · exact key d.x₆_add d.x₆_injective

theorem rootGroup_le_conjS_of_posPat {k : Fin 12} {i : Fin 6} (h : posPat k i = true) :
    d.rootGroup i ≤ d.conjS (d.weylWord k) := by
  rw [le_conjS_iff, d.smul_rootGroup_weylWord]
  have h' : (wordAct (weylList k) (false, i)).1 = false := by
    simpa [posPat] using h
  rw [signedRootGroup, h', Bool.cond_false]
  exact d.rootGroup_le_S _

theorem rootGroup_le_conjS_w₀_mul_of_not_posPat {k : Fin 12} {i : Fin 6}
    (h : posPat k i = false) : d.rootGroup i ≤ d.conjS (d.w₀ * d.weylWord k) := by
  have hw₀ : MulAut.conj d.w₀ * MulAut.conj d.w₀ = 1 := by
    rw [← map_mul, d.w₀_mul_self, map_one]
  rw [le_conjS_iff, map_mul, mul_smul, d.smul_rootGroup_weylWord]
  have h' : (wordAct (weylList k) (false, i)).1 = true := by
    simpa [posPat] using h
  rw [signedRootGroup, h', Bool.cond_true, ← mul_smul, hw₀, one_smul]
  exact d.rootGroup_le_S _

@[expose] def box (P : Fin 6 → Bool) : Set (d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀) :=
  coordSet d.Γ (P 0) ×ˢ coordSet d.Γ₀ (P 1) ×ˢ coordSet d.Γ (P 2) ×ˢ coordSet d.Γ (P 3) ×ˢ
    coordSet d.Γ₀ (P 4) ×ˢ coordSet d.Γ₀ (P 5)

@[expose] def boxProd (P : Fin 6 → Bool) : Set X :=
  sixProd d.x₁ d.x₂ d.x₃ d.x₄ d.x₅ d.x₆ '' d.box P

theorem ncard_box (P : Fin 6 → Bool) : (d.box P).ncard = q ^ posDeg P := by
  have h3 (b : Bool) : (coordSet d.Γ b).ncard = q ^ (bif b then 3 else 0) := by
    cases b
    · exact Set.ncard_singleton 0
    · rw [Bool.cond_true, ← d.card_Γ]
      exact Set.ncard_univ _
  have h1 (b : Bool) : (coordSet d.Γ₀ b).ncard = q ^ (bif b then 1 else 0) := by
    cases b
    · exact Set.ncard_singleton 0
    · change (Set.univ : Set d.Γ₀).ncard = q ^ 1
      rw [Set.ncard_univ, d.card_Γ₀, pow_one]
  simp only [box, Set.ncard_prod, h3, h1, posDeg, pow_add, mul_assoc]

theorem ncard_boxProd (P : Fin 6 → Bool) : (d.boxProd P).ncard = q ^ posDeg P := by
  rw [boxProd, Set.InjOn.ncard_image (d.normal_form.injOn.mono (Set.subset_univ _)),
    d.ncard_box]

theorem map_mem_of_mem_coordSet {A : Type*} [AddGroup A] {x : A → X}
    (hx : ∀ a b, x (a + b) = x a * x b) {H : Subgroup X} {b : Bool} {a : A}
    (ha : a ∈ coordSet A b) (hH : b = true → rangeSubgroup hx ≤ H) : x a ∈ H := by
  cases b
  · rw [show a = 0 from ha, map_zero_of_add hx]
    exact H.one_mem
  · exact hH rfl ⟨a, rfl⟩

theorem sixProd_mem_of_mem_box {H : Subgroup X} {P : Fin 6 → Bool}
    (hP : ∀ i, P i = true → d.rootGroup i ≤ H) {a : d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀}
    (ha : a ∈ d.box P) : sixProd d.x₁ d.x₂ d.x₃ d.x₄ d.x₅ d.x₆ a ∈ H := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := ha
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (map_mem_of_mem_coordSet d.x₁_add h₁ (hP 0))
    (map_mem_of_mem_coordSet d.x₂_add h₂ (hP 1)))
    (map_mem_of_mem_coordSet d.x₃_add h₃ (hP 2)))
    (map_mem_of_mem_coordSet d.x₄_add h₄ (hP 3)))
    (map_mem_of_mem_coordSet d.x₅_add h₅ (hP 4)))
    (map_mem_of_mem_coordSet d.x₆_add h₆ (hP 5))

theorem boxProd_inter (P P' : Fin 6 → Bool) :
    d.boxProd P ∩ d.boxProd P' = d.boxProd (fun i => P i && P' i) := by
  rw [boxProd, boxProd, boxProd, ← Set.InjOn.image_inter d.normal_form.injOn
    (Set.subset_univ _) (Set.subset_univ _)]
  congr 1
  simp only [box, Set.prod_inter_prod, coordSet_inter]

theorem boxProd_false : d.boxProd (fun _ => false) = {1} := by
  ext g
  simp [boxProd, box, coordSet, sixProd, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero,
    d.x₅_zero, d.x₆_zero]

theorem coe_rootGroup_subset_boxProd (i : Fin 6) :
    (d.rootGroup i : Set X) ⊆ d.boxProd (fun j => decide (j = i)) := by
  fin_cases i <;> rintro _ ⟨t, rfl⟩
  · exact ⟨(t, 0, 0, 0, 0, 0), ⟨Set.mem_univ _, rfl, rfl, rfl, rfl, rfl⟩,
      by simp [sixProd, d.x₂_zero, d.x₃_zero, d.x₄_zero, d.x₅_zero, d.x₆_zero]⟩
  · exact ⟨(0, t, 0, 0, 0, 0), ⟨rfl, Set.mem_univ _, rfl, rfl, rfl, rfl⟩,
      by simp [sixProd, d.x₁_zero, d.x₃_zero, d.x₄_zero, d.x₅_zero, d.x₆_zero]⟩
  · exact ⟨(0, 0, t, 0, 0, 0), ⟨rfl, rfl, Set.mem_univ _, rfl, rfl, rfl⟩,
      by simp [sixProd, d.x₁_zero, d.x₂_zero, d.x₄_zero, d.x₅_zero, d.x₆_zero]⟩
  · exact ⟨(0, 0, 0, t, 0, 0), ⟨rfl, rfl, rfl, Set.mem_univ _, rfl, rfl⟩,
      by simp [sixProd, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₅_zero, d.x₆_zero]⟩
  · exact ⟨(0, 0, 0, 0, t, 0), ⟨rfl, rfl, rfl, rfl, Set.mem_univ _, rfl⟩,
      by simp [sixProd, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, d.x₆_zero]⟩
  · exact ⟨(0, 0, 0, 0, 0, t), ⟨rfl, rfl, rfl, rfl, rfl, Set.mem_univ _⟩,
      by simp [sixProd, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, d.x₅_zero]⟩

theorem boxProd_posPat_subset (k : Fin 12) :
    d.boxProd (posPat k) ⊆ (d.S ⊓ d.conjS (d.weylWord k) : Subgroup X) := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨d.normal_form.mapsTo (Set.mem_univ a),
    d.sixProd_mem_of_mem_box (fun _ hi => d.rootGroup_le_conjS_of_posPat hi) ha⟩

theorem cell_eq_image (w : X) :
    d.cell w = (fun z => w * z) '' ((d.conjB w : Set X) * (d.S : Set X)) := by
  ext g
  constructor
  · rintro ⟨b, hb, s, hs, rfl⟩
    refine ⟨w⁻¹ * b * w * s, ⟨w⁻¹ * b * w, ?_, s, hs, rfl⟩, by group⟩
    rw [SetLike.mem_coe, conjB, mem_conj_inv_smul]
    convert hb using 1
    group
  · rintro ⟨_, ⟨c, hc, s, hs, rfl⟩, rfl⟩
    exact ⟨w * c * w⁻¹, mem_conj_inv_smul.1 hc, s, hs, by group⟩

theorem card_conjB (w : X) : Nat.card (d.conjB w) = Nat.card d.B := by
  rw [conjB, pointwise_smul_def]
  exact card_map_of_injective (MulAction.injective (MulAut.conj w⁻¹))

theorem ncard_cell_mul_card (w : X) :
    (d.cell w).ncard * Nat.card ↥(d.conjB w ⊓ d.S) = Nat.card d.B * Nat.card d.S := by
  rw [cell_eq_image, Set.ncard_image_of_injective _ (mul_right_injective w),
    ncard_mul_mul_card_inf, card_conjB]

theorem conj_mem_J {w : X} (hw : w ∈ d.weyl) {j : X} (hj : j ∈ d.J) : w * j * w⁻¹ ∈ d.J := by
  suffices key : ∀ j ∈ d.J, w * j * w⁻¹ ∈ d.J from key j hj
  refine Subgroup.closure_induction_left (p := fun w _ => ∀ j ∈ d.J, w * j * w⁻¹ ∈ d.J)
    (fun j hj => by simpa using hj) ?_ ?_ hw
  · rintro x hx y - ih j hj
    obtain ⟨h, hh⟩ := ih j hj
    rcases hx with rfl | rfl
    · obtain ⟨h', hh'⟩ := d.u_torus h
      refine ⟨h', ?_⟩
      rw [← hh', hh, mul_inv_rev, d.u_inv]
      group
    · obtain ⟨h', hh'⟩ := d.v_torus h
      refine ⟨h', ?_⟩
      rw [← hh', hh, mul_inv_rev, d.v_inv]
      group
  · rintro x hx y - ih j hj
    obtain ⟨h, hh⟩ := ih j hj
    rcases hx with rfl | rfl
    · obtain ⟨h', hh'⟩ := d.u_torus h
      refine ⟨h', ?_⟩
      rw [← hh', hh, d.u_inv, mul_inv_rev, d.u_inv]
      group
    · obtain ⟨h', hh'⟩ := d.v_torus h
      refine ⟨h', ?_⟩
      rw [← hh', hh, d.v_inv, mul_inv_rev, d.v_inv]
      group

theorem coe_B_eq_J_mul_S : (d.B : Set X) = (d.J : Set X) * (d.S : Set X) := by
  rw [B, sup_comm]
  exact coe_mul_of_left_le_normalizer_right d.J d.S (by rw [d.normalizer_S]; exact le_sup_right)

theorem coe_B_eq_S_mul_J : (d.B : Set X) = (d.S : Set X) * (d.J : Set X) :=
  coe_mul_of_right_le_normalizer_left d.S d.J (by rw [d.normalizer_S]; exact le_sup_right)

theorem cell_eq_doubleCoset {w : X} (hw : w ∈ d.weyl) :
    d.cell w = {g | ∃ b ∈ d.B, ∃ b' ∈ d.B, b * w * b' = g} := by
  ext g
  constructor
  · rintro ⟨b, hb, s, hs, rfl⟩
    exact ⟨b, hb, s, le_sup_left (a := d.S) hs, rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    obtain ⟨j, hj, s, hs, rfl⟩ : b' ∈ (d.J : Set X) * (d.S : Set X) := d.coe_B_eq_J_mul_S ▸ hb'
    exact ⟨b * (w * j * w⁻¹), mul_mem hb (le_sup_right (a := d.S) (d.conj_mem_J hw hj)), s, hs,
      by group⟩

theorem exists_mem_cell (g : X) : ∃ k, g ∈ d.cell (d.weylWord k) := by
  obtain ⟨b₁, hb₁, w, hw, b₂, hb₂, rfl⟩ := d.bruhat g
  obtain ⟨k, rfl⟩ := d.exists_weylWord_eq hw
  refine ⟨k, ?_⟩
  rw [d.cell_eq_doubleCoset (d.weylWord_mem_weyl k)]
  exact ⟨b₁, hb₁, b₂, hb₂, rfl⟩

theorem card_le_sum_cell : Nat.card X ≤ ∑ k : Fin 12, (d.cell (d.weylWord k)).ncard := by
  have hU : (⋃ k, d.cell (d.weylWord k)) = Set.univ :=
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (d.exists_mem_cell g)
  rw [← Set.ncard_univ, ← hU]
  exact Set.ncard_iUnion_le_of_fintype _

private theorem card_J' : Nat.card d.J = (q - 1) * (q ^ 3 - 1) := by
  rw [J, ← Nat.card_congr (MonoidHom.ofInjective d.torus_injective).toEquiv, Nat.card_prod,
    d.card_units_Γ₀, d.card_units_Γ]

theorem card_B_le : Nat.card d.B ≤ Nat.card d.S * Nat.card d.J := by
  have := d.finite
  have h := ncard_mul_mul_card_inf d.S d.J
  rw [← d.coe_B_eq_S_mul_J, ← Nat.card_coe_set_eq] at h
  have hpos : 0 < Nat.card ↥(d.S ⊓ d.J) := Nat.card_pos
  calc Nat.card d.B ≤ Nat.card d.B * Nat.card ↥(d.S ⊓ d.J) := Nat.le_mul_of_pos_right _ hpos
    _ = Nat.card d.S * Nat.card d.J := h

theorem card_eq_sum : Nat.card X =
    Nat.card d.S * Nat.card d.J * ∑ k : Fin 12, q ^ posDeg (fun i => !posPat k i) := by
  have hn := posDeg_not_posPat
  have hs : ∑ k : Fin 12, q ^ posDeg (fun i => !posPat k i) =
      ∑ k : Fin 12, q ^ (![0, 3, 1, 4, 4, 7, 5, 8, 8, 11, 9, 12] : Fin 12 → ℕ) k :=
    Finset.sum_congr rfl fun k _ => by rw [← congrFun hn k]
  rw [hs, d.card_eq, d.card_S, card_J']
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  have hq := d.two_le_q
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3, h6]
  ring

theorem bruhat_count :
    (∀ k : Fin 12, (d.cell (d.weylWord k)).ncard =
      Nat.card d.B * q ^ posDeg (fun i => !posPat k i)) ∧
      Nat.card d.B = Nat.card d.S * Nat.card d.J := by
  have := d.finite
  have hq : 0 < q := by have := d.two_le_q; omega
  have hpn (k : Fin 12) := posDeg_add_posDeg_not (posPat k)
  have hmul (k : Fin 12) : (d.cell (d.weylWord k)).ncard *
      Nat.card ↥(d.conjB (d.weylWord k) ⊓ d.S) = Nat.card d.B * q ^ 12 := by
    rw [← d.card_S]
    exact d.ncard_cell_mul_card _
  have hι (k : Fin 12) : q ^ posDeg (posPat k) ≤ Nat.card ↥(d.conjB (d.weylWord k) ⊓ d.S) := by
    rw [← d.ncard_boxProd, ← Nat.card_coe_set_eq]
    refine Set.ncard_le_ncard (fun g hg => ?_) (Set.toFinite _)
    have h := d.boxProd_posPat_subset k hg
    exact ⟨d.conjS_le_conjB _ h.2, h.1⟩
  have hc (k : Fin 12) : (d.cell (d.weylWord k)).ncard ≤
      Nat.card d.B * q ^ posDeg (fun i => !posPat k i) := by
    have h1 : (d.cell (d.weylWord k)).ncard * q ^ posDeg (posPat k) ≤
        Nat.card d.B * q ^ posDeg (fun i => !posPat k i) * q ^ posDeg (posPat k) := by
      calc (d.cell (d.weylWord k)).ncard * q ^ posDeg (posPat k)
          ≤ (d.cell (d.weylWord k)).ncard * Nat.card ↥(d.conjB (d.weylWord k) ⊓ d.S) :=
            Nat.mul_le_mul_left _ (hι k)
        _ = Nat.card d.B * q ^ 12 := hmul k
        _ = Nat.card d.B * q ^ posDeg (fun i => !posPat k i) * q ^ posDeg (posPat k) := by
            rw [← hpn k, pow_add]
            ring
    exact Nat.le_of_mul_le_mul_right h1 (pow_pos hq _)
  have hsum : ∑ k : Fin 12, Nat.card d.B * q ^ posDeg (fun i => !posPat k i) ≤
      ∑ k : Fin 12, (d.cell (d.weylWord k)).ncard := by
    calc ∑ k : Fin 12, Nat.card d.B * q ^ posDeg (fun i => !posPat k i)
        = Nat.card d.B * ∑ k : Fin 12, q ^ posDeg (fun i => !posPat k i) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ Nat.card d.S * Nat.card d.J * ∑ k : Fin 12, q ^ posDeg (fun i => !posPat k i) :=
          Nat.mul_le_mul_right _ d.card_B_le
      _ = Nat.card X := d.card_eq_sum.symm
      _ ≤ ∑ k : Fin 12, (d.cell (d.weylWord k)).ncard := d.card_le_sum_cell
  have hle : ∑ k : Fin 12, (d.cell (d.weylWord k)).ncard ≤
      ∑ k : Fin 12, Nat.card d.B * q ^ posDeg (fun i => !posPat k i) :=
    Finset.sum_le_sum fun k _ => hc k
  have heq := (Finset.sum_eq_sum_iff_of_le fun k _ => hc k).1 (le_antisymm hle hsum)
  refine ⟨fun k => heq k (Finset.mem_univ k), ?_⟩
  have hpos : 0 < ∑ k : Fin 12, q ^ posDeg (fun i => !posPat k i) :=
    Finset.sum_pos (fun k _ => pow_pos hq _) Finset.univ_nonempty
  have e1 : Nat.card d.B * ∑ k : Fin 12, q ^ posDeg (fun i => !posPat k i) =
      Nat.card d.S * Nat.card d.J * ∑ k : Fin 12, q ^ posDeg (fun i => !posPat k i) := by
    refine le_antisymm (Nat.mul_le_mul_right _ d.card_B_le) ?_
    calc Nat.card d.S * Nat.card d.J * ∑ k : Fin 12, q ^ posDeg (fun i => !posPat k i)
        = Nat.card X := d.card_eq_sum.symm
      _ ≤ ∑ k : Fin 12, (d.cell (d.weylWord k)).ncard := d.card_le_sum_cell
      _ ≤ _ := hle
      _ = _ := Finset.mul_sum _ _ _ |>.symm
  exact Nat.eq_of_mul_eq_mul_right hpos e1

theorem ncard_cell (k : Fin 12) :
    (d.cell (d.weylWord k)).ncard = Nat.card d.B * q ^ posDeg (fun i => !posPat k i) :=
  d.bruhat_count.1 k

theorem card_B : Nat.card d.B = Nat.card d.S * Nat.card d.J :=
  d.bruhat_count.2

theorem S_inf_J_eq_bot : d.S ⊓ d.J = ⊥ := by
  have := d.finite
  have h := ncard_mul_mul_card_inf d.S d.J
  rw [← d.coe_B_eq_S_mul_J, ← Nat.card_coe_set_eq] at h
  change Nat.card d.B * _ = _ at h
  rw [d.card_B] at h
  have hpos : 0 < Nat.card d.S * Nat.card d.J := Nat.mul_pos Nat.card_pos Nat.card_pos
  exact card_eq_one.1 (Nat.eq_of_mul_eq_mul_left hpos (h.trans (mul_one _).symm))

theorem card_conjB_inf_S (k : Fin 12) :
    Nat.card ↥(d.conjB (d.weylWord k) ⊓ d.S) = q ^ posDeg (posPat k) := by
  have := d.finite
  have hq : 0 < q := by have := d.two_le_q; omega
  have hB : 0 < Nat.card d.B := Nat.card_pos
  have h := d.ncard_cell_mul_card (d.weylWord k)
  rw [d.ncard_cell, d.card_S, ← posDeg_add_posDeg_not (posPat k), pow_add] at h
  refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hB (pow_pos hq (posDeg fun i => !posPat k i)))
    ?_
  rw [h]
  ring

theorem coe_conjB_inf_S (k : Fin 12) :
    ((d.conjB (d.weylWord k) ⊓ d.S : Subgroup X) : Set X) = d.boxProd (posPat k) := by
  have := d.finite
  symm
  refine Set.eq_of_subset_of_ncard_le (fun g hg => ?_) ?_ (Set.toFinite _)
  · have h := d.boxProd_posPat_subset k hg
    exact ⟨d.conjS_le_conjB _ h.2, h.1⟩
  · rw [← Nat.card_coe_set_eq, d.ncard_boxProd]
    exact (d.card_conjB_inf_S k).le

theorem coe_S_inf_conjS (k : Fin 12) :
    ((d.S ⊓ d.conjS (d.weylWord k) : Subgroup X) : Set X) = d.boxProd (posPat k) := by
  refine Set.Subset.antisymm (fun g hg => ?_) (d.boxProd_posPat_subset k)
  rw [← d.coe_conjB_inf_S k]
  exact ⟨d.conjS_le_conjB _ hg.2, hg.1⟩

theorem rootGroup_inf_conjS_eq_bot {k : Fin 12} {i : Fin 6} (h : posPat k i = false) :
    d.rootGroup i ⊓ d.conjS (d.weylWord k) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have h1 : g ∈ d.boxProd (fun j => decide (j = i)) :=
    d.coe_rootGroup_subset_boxProd i hg.1
  have h2 : g ∈ d.boxProd (posPat k) := by
    rw [← coe_S_inf_conjS]
    exact ⟨d.rootGroup_le_S i hg.1, hg.2⟩
  have h3 : g ∈ d.boxProd (fun j => decide (j = i) && posPat k j) := by
    rw [← boxProd_inter]
    exact ⟨h1, h2⟩
  have hP : (fun j => decide (j = i) && posPat k j) = fun _ => false := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [h]
    · simp [hj]
  rw [hP, boxProd_false] at h3
  exact h3

theorem rootGroup_le_conjS_iff (k : Fin 12) (i : Fin 6) :
    d.rootGroup i ≤ d.conjS (d.weylWord k) ↔ posPat k i = true := by
  refine ⟨fun hle => ?_, d.rootGroup_le_conjS_of_posPat⟩
  by_contra h
  rw [Bool.not_eq_true] at h
  exact d.rootGroup_ne_bot i (by rw [← inf_of_le_left hle, d.rootGroup_inf_conjS_eq_bot h])

theorem Uminus_le_S (w : X) : d.Uminus w ≤ d.S :=
  iSup₂_le fun i _ => d.rootGroup_le_S i

theorem Uminus_le_conjS_w₀_mul (k : Fin 12) :
    d.Uminus (d.weylWord k) ≤ d.conjS (d.w₀ * d.weylWord k) := by
  refine iSup₂_le fun i hi => ?_
  have h : posPat k i = false := by
    rwa [rootGroup_le_conjS_iff, Bool.not_eq_true] at hi
  exact d.rootGroup_le_conjS_w₀_mul_of_not_posPat h

theorem conjB_w₀_inf_S_eq_bot : d.conjB d.w₀ ⊓ d.S = ⊥ := by
  have e := d.coe_conjB_inf_S 11
  rw [posPat_eleven, boxProd_false] at e
  rw [eq_bot_iff]
  intro g hg
  have hg' : g ∈ ((d.conjB (d.weylWord 11) ⊓ d.S : Subgroup X) : Set X) := hg
  rw [e] at hg'
  exact hg'

theorem Uminus_inf_conjB (k : Fin 12) :
    d.Uminus (d.weylWord k) ⊓ d.conjB (d.weylWord k) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hz₁, hz₂⟩ := Subgroup.mem_inf.1 hz
  set w := d.weylWord k
  have h1 : (d.w₀ * w) * z * (d.w₀ * w)⁻¹ ∈ d.S :=
    mem_conj_inv_smul.1 (d.Uminus_le_conjS_w₀_mul k hz₁)
  have h2 : w * z * w⁻¹ ∈ d.B := mem_conj_inv_smul.1 hz₂
  have hw₀ : d.w₀⁻¹ = d.w₀ := inv_eq_of_mul_eq_one_right d.w₀_mul_self
  have h3 : d.w₀ * (w * z * w⁻¹) * d.w₀⁻¹ ∈ d.conjB d.w₀ ⊓ d.S := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [conjB, mem_conj_inv_smul]
      convert h2 using 1
      rw [hw₀, ← mul_assoc, ← mul_assoc, d.w₀_mul_self, one_mul, mul_assoc, d.w₀_mul_self,
        mul_one]
    · rw [show d.w₀ * (w * z * w⁻¹) * d.w₀⁻¹ = (d.w₀ * w) * z * (d.w₀ * w)⁻¹ by group]
      exact h1
  rw [d.conjB_w₀_inf_S_eq_bot, mem_bot, conj_eq_one_iff, conj_eq_one_iff] at h3
  exact h3

theorem boxProd_not_posPat_subset (k : Fin 12) :
    d.boxProd (fun i => !posPat k i) ⊆ d.Uminus (d.weylWord k) := by
  rintro _ ⟨a, ha, rfl⟩
  refine d.sixProd_mem_of_mem_box (fun i hi => ?_) ha
  have h : ¬ d.rootGroup i ≤ d.conjS (d.weylWord k) := by
    rw [rootGroup_le_conjS_iff]
    simpa using hi
  exact le_iSup₂ (f := fun i (_ : ¬ d.rootGroup i ≤ d.conjS (d.weylWord k)) => d.rootGroup i)
    i h

theorem coe_S_eq_mul (k : Fin 12) :
    (d.S : Set X) = ((d.conjB (d.weylWord k) ⊓ d.S : Subgroup X) : Set X) *
      (d.Uminus (d.weylWord k) : Set X) := by
  have := d.finite
  have hHK : (d.conjB (d.weylWord k) ⊓ d.S) ⊓ d.Uminus (d.weylWord k) = ⊥ :=
    eq_bot_iff.2 fun z hz => (d.Uminus_inf_conjB k).le ⟨hz.2, hz.1.1⟩
  have hK : q ^ posDeg (fun i => !posPat k i) ≤ Nat.card (d.Uminus (d.weylWord k)) := by
    rw [← d.ncard_boxProd, ← Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (d.boxProd_not_posPat_subset k) (Set.toFinite _)
  have e := ncard_mul_mul_card_inf (d.conjB (d.weylWord k) ⊓ d.S) (d.Uminus (d.weylWord k))
  rw [hHK, card_bot, mul_one, d.card_conjB_inf_S] at e
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro _ ⟨c, hc, y, hy, rfl⟩
    exact mul_mem hc.2 (d.Uminus_le_S _ hy)
  · rw [← Nat.card_coe_set_eq, e]
    change Nat.card d.S ≤ _
    rw [d.card_S, ← posDeg_add_posDeg_not (posPat k), pow_add]
    exact Nat.mul_le_mul_left _ hK

theorem mem_B_iff {g : X} : g ∈ d.B ↔ ∃ x ∈ d.S, ∃ h ∈ d.J, x * h = g := by
  rw [← SetLike.mem_coe, d.coe_B_eq_S_mul_J]
  rfl

theorem exists_bruhat_normal_form (g : X) :
    ∃ x ∈ d.S, ∃ h ∈ d.J, ∃ w ∈ d.weyl, ∃ y ∈ d.Uminus w, g = x * h * w * y := by
  obtain ⟨k, b, hb, s, hs, rfl⟩ := d.exists_mem_cell g
  have hs' : s ∈ ((d.conjB (d.weylWord k) ⊓ d.S : Subgroup X) : Set X) *
      (d.Uminus (d.weylWord k) : Set X) := d.coe_S_eq_mul k ▸ hs
  obtain ⟨c, hc, y, hy, rfl⟩ := hs'
  have hwc : d.weylWord k * c * (d.weylWord k)⁻¹ ∈ d.B := mem_conj_inv_smul.1 hc.1
  obtain ⟨x, hx, h, hh, e⟩ := d.mem_B_iff.1 (mul_mem hb hwc)
  refine ⟨x, hx, h, hh, d.weylWord k, d.weylWord_mem_weyl k, y, hy, ?_⟩
  rw [e]
  group

theorem bruhat_normal_form_unique {x x' h h' w w' y y' : X} (hx : x ∈ d.S) (hh : h ∈ d.J)
    (hw : w ∈ d.weyl) (hy : y ∈ d.Uminus w) (hx' : x' ∈ d.S) (hh' : h' ∈ d.J)
    (hw' : w' ∈ d.weyl) (hy' : y' ∈ d.Uminus w')
    (e : x * h * w * y = x' * h' * w' * y') : x = x' ∧ h = h' ∧ w = w' ∧ y = y' := by
  have hSB : d.S ≤ d.B := le_sup_left
  have hJB : d.J ≤ d.B := le_sup_right
  have hb : (x' * h')⁻¹ * (x * h) ∈ d.B :=
    mul_mem (inv_mem (mul_mem (hSB hx') (hJB hh'))) (mul_mem (hSB hx) (hJB hh))
  have hyy : y * y'⁻¹ ∈ d.B :=
    hSB (mul_mem (d.Uminus_le_S _ hy) (inv_mem (d.Uminus_le_S _ hy')))
  have hww : w = w' := d.bruhat_disjoint w hw w' hw' _ hb _ hyy (by
    rw [show (x' * h')⁻¹ * (x * h) * w * (y * y'⁻¹) = (x' * h')⁻¹ * (x * h * w * y) * y'⁻¹ by
      group, e]
    group)
  subst hww
  obtain ⟨k, rfl⟩ := d.exists_weylWord_eq hw
  have hz : y' * y⁻¹ ∈ d.Uminus (d.weylWord k) ⊓ d.conjB (d.weylWord k) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem hy' (inv_mem hy), ?_⟩
    rw [conjB, mem_conj_inv_smul]
    convert hb using 1
    calc d.weylWord k * (y' * y⁻¹) * (d.weylWord k)⁻¹
        = (x' * h')⁻¹ * (x' * h' * d.weylWord k * y') * y⁻¹ * (d.weylWord k)⁻¹ := by group
      _ = (x' * h')⁻¹ * (x * h * d.weylWord k * y) * y⁻¹ * (d.weylWord k)⁻¹ := by rw [e]
      _ = (x' * h')⁻¹ * (x * h) := by group
  rw [d.Uminus_inf_conjB, mem_bot, mul_inv_eq_one] at hz
  subst hz
  have hxh : x * h = x' * h' := mul_right_cancel (mul_right_cancel e)
  have h1 : x'⁻¹ * x ∈ d.S ⊓ d.J := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx') hx, ?_⟩
    rw [show x'⁻¹ * x = h' * h⁻¹ by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hxh, inv_mul_cancel_left]]
    exact mul_mem hh' (inv_mem hh)
  rw [d.S_inf_J_eq_bot, mem_bot, inv_mul_eq_one] at h1
  subst h1
  exact ⟨rfl, mul_left_cancel hxh, rfl, rfl⟩

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
