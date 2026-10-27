module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTablesSp6
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.ClassicalGroups.Symplectic.Perfect

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_equiv_diagonal)
open CFSG.Quasithin (perfectCore derivedSeriesOf)
open scoped MatrixGroups commutatorElement

theorem perfectCore_eq_of_derivedSeriesOf_le {G : Type*} [Group G] {C P : Subgroup G}
    (hPC : P ≤ C) (hP : ⁅P, P⁆ = P) {k : ℕ} (hk : derivedSeriesOf C k ≤ P) : perfectCore C = P :=
  le_antisymm ((CFSG.Quasithin.perfectCore_le_derivedSeriesOf C k).trans hk)
    (CFSG.Quasithin.le_perfectCore_of_perfect hPC hP)

theorem commutator_range_eq_of_isPerfect {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (f : G →* H) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

section Rows

variable {K : Type} [Field K] {n : ℕ}

theorem mul_apply_of_row {X Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} {a : Fin n ⊕ Fin n}
    (hX : ∀ c, c ≠ a → X a c = 0) (b : Fin n ⊕ Fin n) : (X * Y) a b = X a a * Y a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hX c hc, zero_mul])
    (fun h => absurd (Finset.mem_univ a) h)]

theorem mul_apply_of_col {X Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} {a : Fin n ⊕ Fin n}
    (hY : ∀ c, c ≠ a → Y c a = 0) (b : Fin n ⊕ Fin n) : (X * Y) b a = X b a * Y a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hY c hc, mul_zero])
    (fun h => absurd (Finset.mem_univ a) h)]

theorem commutator_le_suppGroup {B : Set (Fin n ⊕ Fin n)} {H : Subgroup (StatedSp n K)}
    (hH : ∀ x ∈ H, ∀ a ∉ B, ∀ b, b ≠ a → mat n K x a b = 0 ∧ mat n K x b a = 0) :
    ⁅H, H⁆ ≤ suppGroup B := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hrow : ∀ x ∈ H, ∀ y : StatedSp n K, ∀ a ∉ B, ∀ b,
      mat n K (x * y) a b = mat n K x a a * mat n K y a b := fun x hx y a ha b => by
    rw [map_mul]
    exact mul_apply_of_row (fun c hc => (hH x hx a ha c hc).1) b
  have hcol : ∀ x : StatedSp n K, ∀ y ∈ H, ∀ a ∉ B, ∀ b,
      mat n K (x * y) b a = mat n K x b a * mat n K y a a := fun x y hy a ha b => by
    rw [map_mul]
    exact mul_apply_of_col (fun c hc => (hH y hy a ha c hc).2) b
  have hinv : ∀ x ∈ H, ∀ a ∉ B, mat n K x a a * mat n K x⁻¹ a a = 1 := fun x hx a ha => by
    rw [← hrow x hx x⁻¹ a ha a, mul_inv_cancel, map_one, Matrix.one_apply_eq]
  have hc : ⁅g, h⁆ = g * h * g⁻¹ * h⁻¹ := commutatorElement_def g h
  have hghg : g * h * g⁻¹ ∈ H := mul_mem (mul_mem hg hh) (inv_mem hg)
  have hdiag : ∀ a ∉ B, mat n K g a a * mat n K h a a * mat n K g⁻¹ a a * mat n K h⁻¹ a a = 1 :=
    fun a ha => by
    calc _ = (mat n K g a a * mat n K g⁻¹ a a) * (mat n K h a a * mat n K h⁻¹ a a) := by ring
      _ = 1 := by rw [hinv g hg a ha, hinv h hh a ha, one_mul]
  have hr : ∀ a ∉ B, ∀ b, mat n K ⁅g, h⁆ a b =
      mat n K g a a * mat n K h a a * mat n K g⁻¹ a a * mat n K h⁻¹ a b := fun a ha b => by
    rw [hc, hrow _ hghg _ a ha, hrow _ (mul_mem hg hh) _ a ha, hrow _ hg _ a ha]
  have hcl : ∀ a ∉ B, ∀ b, mat n K ⁅g, h⁆ b a =
      mat n K g b a * mat n K h a a * mat n K g⁻¹ a a * mat n K h⁻¹ a a := fun a ha b => by
    rw [hc, hcol _ _ (inv_mem hh) a ha, hcol _ _ (inv_mem hg) a ha, hcol _ _ hh a ha]
  intro r t hrt
  by_cases hrB : r ∈ B
  · have htB : t ∉ B := fun htB => hrt ⟨hrB, htB⟩
    rw [hcl t htB r]
    by_cases hrt' : r = t
    · subst hrt'
      exact absurd hrB htB
    · rw [(hH g hg t htB r hrt').2, zero_mul, zero_mul, zero_mul, Matrix.one_apply_ne hrt']
  · rw [hr r hrB t]
    by_cases hrt' : t = r
    · subst hrt'
      rw [hdiag t hrB, Matrix.one_apply_eq]
    · rw [(hH _ (inv_mem hh) r hrB t hrt').1, mul_zero, Matrix.one_apply_ne (Ne.symm hrt')]

end Rows

section Weights

variable {F : Type} [Field F]

@[expose] def sp6Weight (t : Fin 3 → Fˣ) : Fin 3 ⊕ Fin 3 → F :=
  Sum.elim (fun i => (t i : F)) (fun i => (((t i)⁻¹ : Fˣ) : F))

@[simp] theorem sp6Weight_inl (t : Fin 3 → Fˣ) (i : Fin 3) :
    sp6Weight t (Sum.inl i) = (t i : F) := rfl

@[simp] theorem sp6Weight_inr (t : Fin 3 → Fˣ) (i : Fin 3) :
    sp6Weight t (Sum.inr i) = (((t i)⁻¹ : Fˣ) : F) := rfl

theorem mat_sp6Diag (t : Fin 3 → Fˣ) : mat 3 F (sp6Diag F t) = Matrix.diagonal (sp6Weight t) :=
  mat_equiv_diagonal t

theorem commute_sp6Diag_iff (x : StatedSp 3 F) (t : Fin 3 → Fˣ) :
    Commute x (sp6Diag F t) ↔ ∀ r s, sp6Weight t r ≠ sp6Weight t s → mat 3 F x r s = 0 := by
  rw [← mul_diagonal_eq_diagonal_mul_iff, ← mat_sp6Diag, ← map_mul, ← map_mul,
    mat_injective.eq_iff]
  rfl

theorem mat_eq_zero_of_mem_centralizer {T : Subgroup (StatedSp 3 F)} {x : StatedSp 3 F}
    (hx : x ∈ centralizer (T : Set (StatedSp 3 F))) {t : Fin 3 → Fˣ} (ht : sp6Diag F t ∈ T)
    {a b : Fin 3 ⊕ Fin 3} (hab : sp6Weight t a ≠ sp6Weight t b) :
    mat 3 F x a b = 0 ∧ mat 3 F x b a = 0 := by
  have hc : Commute x (sp6Diag F t) := ((mem_centralizer_iff.1 hx) _ ht).symm
  exact ⟨(commute_sp6Diag_iff x t).1 hc a b hab, (commute_sp6Diag_iff x t).1 hc b a (Ne.symm hab)⟩

theorem suppGroup_le_centralizer {B : Set (Fin 3 ⊕ Fin 3)} {T : Subgroup (StatedSp 3 F)}
    (hT : ∀ s ∈ T, ∃ t, s = sp6Diag F t ∧ ∀ r ∈ B, ∀ r' ∈ B, sp6Weight t r = sp6Weight t r') :
    suppGroup B ≤ centralizer (T : Set (StatedSp 3 F)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro s hs
  obtain ⟨t, rfl, hw⟩ := hT s hs
  refine ((commute_sp6Diag_iff x t).2 fun r r' hrr' => ?_).eq.symm
  by_cases h : r ∈ B ∧ r' ∈ B
  · exact absurd (hw r h.1 r' h.2) hrr'
  · have hne : r ≠ r' := by
      rintro rfl
      exact hrr' rfl
    rw [hx r r' h, Matrix.one_apply_ne hne]

end Weights

section Separate

variable {F : Type} [Field F]

theorem units_ne_of_sq_ne_one {c : Fˣ} (hc : c ^ 2 ≠ 1) :
    (c : F) ≠ 1 ∧ (((c⁻¹ : Fˣ) : F)) ≠ 1 ∧ (c : F) ≠ ((c⁻¹ : Fˣ) : F) := by
  refine ⟨fun h => hc ?_, fun h => hc ?_, fun h => hc ?_⟩
  · rw [Units.val_eq_one.1 h, one_pow]
  · rw [inv_eq_one.1 (Units.val_eq_one.1 h), one_pow]
  · have h' : c = c⁻¹ := Units.val_injective h
    rw [sq, ← mul_inv_cancel c, ← h']

theorem sp6Weight_mulSingle_ne {k : Fin 3} {c : Fˣ} (hc : c ^ 2 ≠ 1) {a b : Fin 3 ⊕ Fin 3}
    (ha : a = Sum.inl k ∨ a = Sum.inr k) (hb : b ≠ a) :
    sp6Weight (Pi.mulSingle k c) a ≠ sp6Weight (Pi.mulSingle k c) b := by
  obtain ⟨h1, h2, h3⟩ := units_ne_of_sq_ne_one (F := F) hc
  rcases ha with rfl | rfl <;> rcases b with i | i
  · have hik : i ≠ k := fun h => hb (h ▸ rfl)
    simpa [sp6Weight, Pi.mulSingle_apply, hik] using h1
  · by_cases hik : i = k
    · subst hik
      simpa [sp6Weight] using h3
    · simpa [sp6Weight, Pi.mulSingle_apply, hik] using h1
  · by_cases hik : i = k
    · subst hik
      simpa [sp6Weight] using Ne.symm h3
    · simpa [sp6Weight, Pi.mulSingle_apply, hik] using h2
  · have hik : i ≠ k := fun h => hb (h ▸ rfl)
    simpa [sp6Weight, Pi.mulSingle_apply, hik] using h2

theorem sp6ParamA_eq (a : Fˣ) : sp6ParamA F a = Pi.mulSingle 0 a := rfl

theorem sp6ParamM2_eq (p : Fˣ × Fˣ) : sp6ParamM2 F p = Pi.mulSingle 0 p.1 * Pi.mulSingle 1 p.2 :=
  rfl

theorem sp6ParamM3_eq (p : Fˣ × Fˣ) :
    sp6ParamM3 F p = Pi.mulSingle 0 p.1 * (Pi.mulSingle 1 p.2 * Pi.mulSingle 2 p.2) :=
  rfl

theorem sp6Diag_mulSingle_zero_mem_sp6TorusA {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A) :
    sp6Diag F (Pi.mulSingle 0 a₀) ∈ sp6TorusA A :=
  ⟨a₀, ha₀, rfl⟩

theorem sp6Diag_mulSingle_mem_sp6TorusM2 {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A) {k : Fin 3}
    (hk : k = 0 ∨ k = 1) : sp6Diag F (Pi.mulSingle k a₀) ∈ sp6TorusM2 A := by
  rcases hk with rfl | rfl
  · refine ⟨(a₀, 1), ⟨ha₀, one_mem A⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, sp6ParamM2_eq, Pi.mulSingle_one, mul_one]
  · refine ⟨(1, a₀), ⟨one_mem A, ha₀⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, sp6ParamM2_eq, Pi.mulSingle_one, one_mul]

theorem sp6Diag_mulSingle_zero_mem_sp6TorusM3 {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A) :
    sp6Diag F (Pi.mulSingle 0 a₀) ∈ sp6TorusM3 A := by
  refine ⟨(a₀, 1), ⟨ha₀, one_mem A⟩, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, sp6ParamM3_eq, Pi.mulSingle_one, mul_one]

end Separate

section Perfect

variable {F : Type} [Field F]

theorem isPerfect_statedSp_two (hF : 4 ≤ Nat.card F) : Group.IsPerfect (StatedSp 2 F) := by
  have := CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin F 2 (Or.inl (Or.inr hF))
  exact Group.IsPerfect.ofSurjective
    (f := (CFSG.LieType.Universal.Symplectic.equivStatedSp 2 F).toMonoidHom)
    (CFSG.LieType.Universal.Symplectic.equivStatedSp 2 F).surjective

theorem isPerfect_SL2_of_sq_ne_one {c : Fˣ} (hc : c ^ 2 ≠ 1) : Group.IsPerfect SL(2, F) := by
  refine ⟨Matrix.SL2.commutator_eq_top c.ne_zero fun h => hc (Units.ext ?_)⟩
  rw [Units.val_pow_eq_pow_val, h, Units.val_one]

end Perfect

section CaseA

variable {F : Type} [Field F]

theorem eq_inl_zero_or_eq_inr_zero_of_not_mem_range {a : Fin 3 ⊕ Fin 3}
    (ha : a ∉ Set.range (Sum.map (Fin.succ : Fin 2 → Fin 3) Fin.succ)) :
    a = Sum.inl 0 ∨ a = Sum.inr 0 := by
  rcases a with i | i
  · left
    by_contra h
    have hi : i ≠ 0 := fun h0 => h (by rw [h0])
    obtain ⟨j, rfl⟩ := (Fin.exists_succ_eq (x := i)).2 hi
    exact ha ⟨Sum.inl j, rfl⟩
  · right
    by_contra h
    have hi : i ≠ 0 := fun h0 => h (by rw [h0])
    obtain ⟨j, rfl⟩ := (Fin.exists_succ_eq (x := i)).2 hi
    exact ha ⟨Sum.inr j, rfl⟩

theorem sp6Weight_mulSingle_zero_of_mem_range (a : Fˣ) {r : Fin 3 ⊕ Fin 3}
    (hr : r ∈ Set.range (Sum.map (Fin.succ : Fin 2 → Fin 3) Fin.succ)) :
    sp6Weight (Pi.mulSingle 0 a) r = 1 := by
  obtain ⟨r₀, rfl⟩ := hr
  rcases r₀ with j | j <;> simp [sp6Weight, Pi.mulSingle_apply, Fin.succ_ne_zero]

theorem suppGroup_le_centralizer_sp6TorusA (A : Subgroup Fˣ) :
    suppGroup (Set.range (Sum.map (Fin.succ : Fin 2 → Fin 3) Fin.succ)) ≤
      centralizer (sp6TorusA A : Set (StatedSp 3 F)) := by
  refine suppGroup_le_centralizer fun s hs => ?_
  obtain ⟨a, -, rfl⟩ := hs
  refine ⟨Pi.mulSingle 0 a, rfl, fun r hr r' hr' => ?_⟩
  rw [sp6Weight_mulSingle_zero_of_mem_range a hr, sp6Weight_mulSingle_zero_of_mem_range a hr']

theorem perfectCore_centralizer_sp6TorusA (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ}
    (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    perfectCore (centralizer (sp6TorusA A : Set (StatedSp 3 F))) =
      suppGroup (Set.range (Sum.map (Fin.succ : Fin 2 → Fin 3) Fin.succ)) := by
  have := isPerfect_statedSp_two hF
  refine perfectCore_eq_of_derivedSeriesOf_le (suppGroup_le_centralizer_sp6TorusA A) ?_ (k := 1) ?_
  · rw [← range_spEmbed (Fin.succ_injective 2)]
    exact commutator_range_eq_of_isPerfect _
  · rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero]
    refine commutator_le_suppGroup fun x hx a ha b hb => ?_
    exact mat_eq_zero_of_mem_centralizer hx (sp6Diag_mulSingle_zero_mem_sp6TorusA ha₀)
      (sp6Weight_mulSingle_ne hsq (eq_inl_zero_or_eq_inr_zero_of_not_mem_range ha) hb)

theorem natCard_perfectCore_centralizer_sp6TorusA [Finite F] (hF : 4 ≤ Nat.card F)
    {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    Nat.card (perfectCore (centralizer (sp6TorusA A : Set (StatedSp 3 F)))) =
      ordSp 2 (Nat.card F) := by
  rw [perfectCore_centralizer_sp6TorusA hF ha₀ hsq, ← range_spEmbed (Fin.succ_injective 2),
    ← Nat.card_congr (MonoidHom.ofInjective (spEmbed_injective (K := F)
      (Fin.succ_injective 2))).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  rfl

end CaseA

section CaseM2

variable {F : Type} [Field F]

theorem sp6Weight_paramM2_of_mem_coords (p : Fˣ × Fˣ) {r : Fin 3 ⊕ Fin 3}
    (hr : r ∈ coords (2 : Fin 3)) : sp6Weight (sp6ParamM2 F p) r = 1 := by
  rcases mem_coords.1 hr with rfl | rfl <;> simp [sp6Weight, sp6ParamM2_eq, Pi.mulSingle_apply]

theorem suppGroup_le_centralizer_sp6TorusM2 (A : Subgroup Fˣ) :
    suppGroup (coords (2 : Fin 3)) ≤ centralizer (sp6TorusM2 A : Set (StatedSp 3 F)) := by
  refine suppGroup_le_centralizer fun s hs => ?_
  obtain ⟨p, -, rfl⟩ := hs
  exact ⟨sp6ParamM2 F p, rfl, fun r hr r' hr' => by
    rw [sp6Weight_paramM2_of_mem_coords p hr, sp6Weight_paramM2_of_mem_coords p hr']⟩

theorem exists_of_not_mem_coords_two {a : Fin 3 ⊕ Fin 3} (ha : a ∉ coords (2 : Fin 3)) :
    ∃ k : Fin 3, (k = 0 ∨ k = 1) ∧ (a = Sum.inl k ∨ a = Sum.inr k) := by
  rcases a with i | i <;> fin_cases i
  · exact ⟨0, .inl rfl, .inl rfl⟩
  · exact ⟨1, .inr rfl, .inl rfl⟩
  · exact absurd (inl_mem_coords 2) ha
  · exact ⟨0, .inl rfl, .inr rfl⟩
  · exact ⟨1, .inr rfl, .inr rfl⟩
  · exact absurd (inr_mem_coords 2) ha

theorem perfectCore_centralizer_sp6TorusM2 {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A)
    (hsq : a₀ ^ 2 ≠ 1) :
    perfectCore (centralizer (sp6TorusM2 A : Set (StatedSp 3 F))) = suppGroup (coords (2 : Fin 3)) := by
  have := isPerfect_SL2_of_sq_ne_one hsq
  refine perfectCore_eq_of_derivedSeriesOf_le (suppGroup_le_centralizer_sp6TorusM2 A) ?_ (k := 1) ?_
  · rw [← range_longBlock]
    exact commutator_range_eq_of_isPerfect _
  · rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero]
    refine commutator_le_suppGroup fun x hx a ha b hb => ?_
    obtain ⟨k, hk, hak⟩ := exists_of_not_mem_coords_two ha
    exact mat_eq_zero_of_mem_centralizer hx (sp6Diag_mulSingle_mem_sp6TorusM2 ha₀ hk)
      (sp6Weight_mulSingle_ne hsq hak hb)

theorem natCard_perfectCore_centralizer_sp6TorusM2 [Finite F] {A : Subgroup Fˣ} {a₀ : Fˣ}
    (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    Nat.card (perfectCore (centralizer (sp6TorusM2 A : Set (StatedSp 3 F)))) =
      ordSL 2 (Nat.card F) := by
  rw [perfectCore_centralizer_sp6TorusM2 ha₀ hsq, ← range_longBlock,
    ← Nat.card_congr (MonoidHom.ofInjective (longBlock_injective (K := F) (n := 3) 2)).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
  rfl

end CaseM2

section CaseM3

variable {F : Type} [Field F]

theorem fin_three_one_ne_two : (1 : Fin 3) ≠ 2 := by decide

theorem sp6Weight_paramM3_inl (p : Fˣ × Fˣ) {i : Fin 3} (hi : i = 1 ∨ i = 2) :
    sp6Weight (sp6ParamM3 F p) (Sum.inl i) = (p.2 : F) := by
  rcases hi with rfl | rfl <;> simp [sp6Weight, sp6ParamM3_eq, Pi.mulSingle_apply]

theorem sp6Weight_paramM3_inr (p : Fˣ × Fˣ) {i : Fin 3} (hi : i = 1 ∨ i = 2) :
    sp6Weight (sp6ParamM3 F p) (Sum.inr i) = ((p.2⁻¹ : Fˣ) : F) := by
  rcases hi with rfl | rfl <;> simp [sp6Weight, sp6ParamM3_eq, Pi.mulSingle_apply]

theorem planeTorusElt_one_two_eq_sp6Diag (a : Fˣ) :
    planeTorusElt F (1 : Fin 3) 2 a a = sp6Diag F (sp6ParamM3 F (1, a)) := by
  apply mat_injective
  rw [mat_planeTorusElt fin_three_one_ne_two, mat_sp6Diag]
  congr 1
  funext r
  rcases r with i | i <;> fin_cases i <;>
    simp [planeTorusDiag, sp6Weight, sp6ParamM3_eq, Pi.mulSingle_apply]

theorem range_shortBlock_le_centralizer_sp6TorusM3 (A : Subgroup Fˣ) :
    (shortBlock F fin_three_one_ne_two).range ≤ centralizer (sp6TorusM3 A : Set (StatedSp 3 F)) := by
  rintro _ ⟨B, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨p, -, rfl⟩
  refine ((commute_sp6Diag_iff _ _).2 fun r r' hrr' => ?_).eq.symm
  rw [mat_shortBlock]
  rcases r with i | i <;> rcases r' with j | j
  · rw [Matrix.fromBlocks_apply₁₁]
    by_cases h : (i = 1 ∨ i = 2) ∧ (j = 1 ∨ j = 2)
    · exact absurd (by rw [sp6Weight_paramM3_inl p h.1, sp6Weight_paramM3_inl p h.2]) hrr'
    · have hij : i ≠ j := by
        rintro rfl
        exact hrr' rfl
      rw [blockMat_apply_of_not fin_three_one_ne_two _ h, Matrix.one_apply_ne hij]
  · rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]
    by_cases h : (j = 1 ∨ j = 2) ∧ (i = 1 ∨ i = 2)
    · exact absurd (by rw [sp6Weight_paramM3_inr p h.1, sp6Weight_paramM3_inr p h.2]) hrr'
    · have hij : j ≠ i := by
        rintro rfl
        exact hrr' rfl
      rw [blockMat_apply_of_not fin_three_one_ne_two _ h, Matrix.one_apply_ne hij]

theorem eq_inl_zero_or_eq_inr_zero_of_not_mem_union {a : Fin 3 ⊕ Fin 3}
    (ha : a ∉ coords (1 : Fin 3) ∪ coords 2) : a = Sum.inl 0 ∨ a = Sum.inr 0 := by
  rcases a with i | i <;> fin_cases i
  · exact .inl rfl
  · exact absurd (inl_mem_union_iff.2 (.inl rfl)) ha
  · exact absurd (inl_mem_union_iff.2 (.inr rfl)) ha
  · exact .inr rfl
  · exact absurd (inr_mem_union_iff.2 (.inl rfl)) ha
  · exact absurd (inr_mem_union_iff.2 (.inr rfl)) ha

theorem perfectCore_centralizer_sp6TorusM3 {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A)
    (hsq : a₀ ^ 2 ≠ 1) :
    perfectCore (centralizer (sp6TorusM3 A : Set (StatedSp 3 F))) =
      (shortBlock F fin_three_one_ne_two).range := by
  have := isPerfect_SL2_of_sq_ne_one hsq
  set C := centralizer (sp6TorusM3 A : Set (StatedSp 3 F)) with hCdef
  have hC1 : ⁅C, C⁆ ≤ leviCent F (1 : Fin 3) 2 a₀ := by
    refine le_inf ?_ ?_
    · refine commutator_le_suppGroup fun x hx a ha b hb => ?_
      exact mat_eq_zero_of_mem_centralizer hx (sp6Diag_mulSingle_zero_mem_sp6TorusM3 ha₀)
        (sp6Weight_mulSingle_ne hsq (eq_inl_zero_or_eq_inr_zero_of_not_mem_union ha) hb)
    · refine (CFSG.Quasithin.A3.commutator_self_le C).trans (centralizer_le ?_)
      rintro _ rfl
      rw [planeTorusElt_one_two_eq_sp6Diag]
      exact ⟨(1, a₀), ⟨one_mem A, ha₀⟩, rfl⟩
  refine perfectCore_eq_of_derivedSeriesOf_le (range_shortBlock_le_centralizer_sp6TorusM3 A)
    (commutator_range_eq_of_isPerfect _) (k := 2) ?_
  rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_succ,
    CFSG.Quasithin.derivedSeriesOf_zero,
    ← commutator_leviCent fin_three_one_ne_two (units_ne_of_sq_ne_one hsq).2.2]
  exact commutator_mono hC1 hC1

theorem natCard_perfectCore_centralizer_sp6TorusM3 [Finite F] {A : Subgroup Fˣ} {a₀ : Fˣ}
    (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    Nat.card (perfectCore (centralizer (sp6TorusM3 A : Set (StatedSp 3 F)))) =
      ordSL 2 (Nat.card F) := by
  rw [perfectCore_centralizer_sp6TorusM3 ha₀ hsq,
    ← Nat.card_congr (MonoidHom.ofInjective (shortBlock_injective (K := F)
      fin_three_one_ne_two)).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
  rfl

end CaseM3

theorem pieceCards_sp6Tori {F : Type} [Field F] [Finite F] (A : Subgroup Fˣ)
    (hF : 4 ≤ Nat.card F) (hA : ∃ a ∈ A, a ^ 2 ≠ 1) :
    pieceCards ⊤ (sp6TorusA A) (sp6TorusM2 A) (sp6TorusM3 A) =
      (ordSp 2 (Nat.card F), ordSL 2 (Nat.card F), ordSL 2 (Nat.card F)) := by
  obtain ⟨a₀, ha₀, hsq⟩ := hA
  rw [pieceCards_top, natCard_perfectCore_centralizer_sp6TorusA hF ha₀ hsq,
    natCard_perfectCore_centralizer_sp6TorusM2 ha₀ hsq,
    natCard_perfectCore_centralizer_sp6TorusM3 ha₀ hsq]

theorem sp6PieceComputation_holds : Sp6PieceComputation :=
  fun _ _ _ _ A hF hA => pieceCards_sp6Tori A hF hA

end CFSG.SeitzReduction.F4Pilot
