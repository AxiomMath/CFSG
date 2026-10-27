module

public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonBorelMatrices
public import CFSG.CGT.Timmesfeld75.NormalClosure

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Entries

variable {F : Type} [Field F]

theorem sl2_det (g : SL(2, F)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.2
  rwa [Matrix.det_fin_two] at h

theorem sl2_ext {g h : SL(2, F)} (h00 : g 0 0 = h 0 0) (h01 : g 0 1 = h 0 1)
    (h10 : g 1 0 = h 1 0) (h11 : g 1 1 = h 1 1) : g = h :=
  Matrix.SpecialLinearGroup.ext g h fun i j => by fin_cases i <;> fin_cases j <;> assumption

theorem mul_apply_00 (g h : SL(2, F)) : (g * h) 0 0 = g 0 0 * h 0 0 + g 0 1 * h 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_apply_01 (g h : SL(2, F)) : (g * h) 0 1 = g 0 0 * h 0 1 + g 0 1 * h 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_apply_10 (g h : SL(2, F)) : (g * h) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_apply_11 (g h : SL(2, F)) : (g * h) 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_apply_00 (g : SL(2, F)) : g⁻¹ 0 0 = g 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv_apply_01 (g : SL(2, F)) : g⁻¹ 0 1 = - g 0 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv_apply_10 (g : SL(2, F)) : g⁻¹ 1 0 = - g 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv_apply_11 (g : SL(2, F)) : g⁻¹ 1 1 = g 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem one_apply_00 : (1 : SL(2, F)) 0 0 = 1 := by simp

theorem one_apply_01 : (1 : SL(2, F)) 0 1 = 0 := by simp

theorem one_apply_10 : (1 : SL(2, F)) 1 0 = 0 := by simp

theorem one_apply_11 : (1 : SL(2, F)) 1 1 = 1 := by simp

@[expose] def utriElt (s : F) : SL(2, F) := CFSG.Glauberman.Dickson.unipotentSLAddChar F s

@[expose] def ltriElt (t : F) : SL(2, F) := ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def torusElt (a : Fˣ) : SL(2, F) := CFSG.Glauberman.Dickson.splitTorusSLHom F a

@[expose] def wElt : SL(2, F) := CFSG.Glauberman.Dickson.standardSplitWeylSL F

theorem utriElt_apply_00 (s : F) : utriElt s 0 0 = 1 := by simp [utriElt]

theorem utriElt_apply_01 (s : F) : utriElt s 0 1 = s := by simp [utriElt]

theorem utriElt_apply_10 (s : F) : utriElt s 1 0 = 0 := by simp [utriElt]

theorem utriElt_apply_11 (s : F) : utriElt s 1 1 = 1 := by simp [utriElt]

theorem ltriElt_apply_00 (t : F) : ltriElt t 0 0 = 1 := by simp [ltriElt]

theorem ltriElt_apply_01 (t : F) : ltriElt t 0 1 = 0 := by simp [ltriElt]

theorem ltriElt_apply_10 (t : F) : ltriElt t 1 0 = t := by simp [ltriElt]

theorem ltriElt_apply_11 (t : F) : ltriElt t 1 1 = 1 := by simp [ltriElt]

theorem torusElt_apply_00 (a : Fˣ) : torusElt a 0 0 = (a : F) := by simp [torusElt]

theorem torusElt_apply_01 (a : Fˣ) : torusElt a 0 1 = 0 := by simp [torusElt]

theorem torusElt_apply_10 (a : Fˣ) : torusElt a 1 0 = 0 := by simp [torusElt]

theorem torusElt_apply_11 (a : Fˣ) : torusElt a 1 1 = (a⁻¹ : Fˣ) := by simp [torusElt]

theorem wElt_apply_00 : (wElt : SL(2, F)) 0 0 = 0 := by
  simp [wElt, CFSG.Glauberman.Dickson.standardSplitWeylSL]

theorem wElt_apply_01 : (wElt : SL(2, F)) 0 1 = -1 := by
  simp [wElt, CFSG.Glauberman.Dickson.standardSplitWeylSL]

theorem wElt_apply_10 : (wElt : SL(2, F)) 1 0 = 1 := by
  simp [wElt, CFSG.Glauberman.Dickson.standardSplitWeylSL]

theorem wElt_apply_11 : (wElt : SL(2, F)) 1 1 = 0 := by
  simp [wElt, CFSG.Glauberman.Dickson.standardSplitWeylSL]

macro "sl2_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [mul_apply_00,
  mul_apply_01, mul_apply_10, mul_apply_11, inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11,
  one_apply_00, one_apply_01, one_apply_10, one_apply_11, utriElt_apply_00, utriElt_apply_01,
  utriElt_apply_10, utriElt_apply_11, ltriElt_apply_00, ltriElt_apply_01, ltriElt_apply_10,
  ltriElt_apply_11, torusElt_apply_00, torusElt_apply_01, torusElt_apply_10, torusElt_apply_11,
  wElt_apply_00, wElt_apply_01, wElt_apply_10, wElt_apply_11] $[$loc]?)

end Entries

section Subgroups

variable (F : Type) [Field F]

@[expose] def borel : Subgroup SL(2, F) where
  carrier := {g | g 1 0 = 0}
  one_mem' := one_apply_10
  mul_mem' := by
    intro g h hg hh
    have hg' : g 1 0 = 0 := hg
    have hh' : h 1 0 = 0 := hh
    show (g * h) 1 0 = 0
    rw [mul_apply_10, hg', hh']
    ring
  inv_mem' := by
    intro g hg
    have hg' : g 1 0 = 0 := hg
    show g⁻¹ 1 0 = 0
    rw [inv_apply_10, hg', neg_zero]

@[expose] def utri : Subgroup SL(2, F) where
  carrier := {g | g 1 0 = 0 ∧ g 0 0 = 1}
  one_mem' := ⟨one_apply_10, one_apply_00⟩
  mul_mem' := by
    rintro g h ⟨hg10, hg00⟩ ⟨hh10, hh00⟩
    refine ⟨?_, ?_⟩
    · show (g * h) 1 0 = 0
      rw [mul_apply_10, hg10, hh10]
      ring
    · show (g * h) 0 0 = 1
      rw [mul_apply_00, hg00, hh00, hh10]
      ring
  inv_mem' := by
    rintro g ⟨hg10, hg00⟩
    have hd := sl2_det g
    rw [hg00, hg10] at hd
    refine ⟨?_, ?_⟩
    · show g⁻¹ 1 0 = 0
      rw [inv_apply_10, hg10, neg_zero]
    · show g⁻¹ 0 0 = 1
      rw [inv_apply_00]
      linear_combination hd

@[expose] def ltri : Subgroup SL(2, F) where
  carrier := {g | g 0 1 = 0 ∧ g 0 0 = 1}
  one_mem' := ⟨one_apply_01, one_apply_00⟩
  mul_mem' := by
    rintro g h ⟨hg01, hg00⟩ ⟨hh01, hh00⟩
    refine ⟨?_, ?_⟩
    · show (g * h) 0 1 = 0
      rw [mul_apply_01, hg01, hh01]
      ring
    · show (g * h) 0 0 = 1
      rw [mul_apply_00, hg00, hh00, hg01]
      ring
  inv_mem' := by
    rintro g ⟨hg01, hg00⟩
    have hd := sl2_det g
    rw [hg00, hg01] at hd
    refine ⟨?_, ?_⟩
    · show g⁻¹ 0 1 = 0
      rw [inv_apply_01, hg01, neg_zero]
    · show g⁻¹ 0 0 = 1
      rw [inv_apply_00]
      linear_combination hd

@[expose] def torus : Subgroup SL(2, F) where
  carrier := {g | g 0 1 = 0 ∧ g 1 0 = 0}
  one_mem' := ⟨one_apply_01, one_apply_10⟩
  mul_mem' := by
    rintro g h ⟨hg01, hg10⟩ ⟨hh01, hh10⟩
    refine ⟨?_, ?_⟩
    · show (g * h) 0 1 = 0
      rw [mul_apply_01, hg01, hh01]
      ring
    · show (g * h) 1 0 = 0
      rw [mul_apply_10, hg10, hh10]
      ring
  inv_mem' := by
    rintro g ⟨hg01, hg10⟩
    refine ⟨?_, ?_⟩
    · show g⁻¹ 0 1 = 0
      rw [inv_apply_01, hg01, neg_zero]
    · show g⁻¹ 1 0 = 0
      rw [inv_apply_10, hg10, neg_zero]

end Subgroups

section Membership

variable {F : Type} [Field F]

theorem mem_borel_iff {g : SL(2, F)} : g ∈ borel F ↔ g 1 0 = 0 := Iff.rfl

theorem mem_utri_entries {g : SL(2, F)} : g ∈ utri F ↔ g 1 0 = 0 ∧ g 0 0 = 1 := Iff.rfl

theorem mem_ltri_entries {g : SL(2, F)} : g ∈ ltri F ↔ g 0 1 = 0 ∧ g 0 0 = 1 := Iff.rfl

theorem mem_torus_entries {g : SL(2, F)} : g ∈ torus F ↔ g 0 1 = 0 ∧ g 1 0 = 0 := Iff.rfl

theorem utriElt_injective : Function.Injective (utriElt : F → SL(2, F)) := fun s t h => by
  have h01 := congrArg (fun g : SL(2, F) => g 0 1) h
  simpa only [utriElt_apply_01] using h01

theorem utriElt_zero : (utriElt 0 : SL(2, F)) = 1 :=
  (CFSG.Glauberman.Dickson.unipotentSLAddChar F).map_zero_eq_one

theorem utriElt_add (s t : F) : (utriElt (s + t) : SL(2, F)) = utriElt s * utriElt t :=
  (CFSG.Glauberman.Dickson.unipotentSLAddChar F).map_add_eq_mul s t

theorem utriElt_inv (s : F) : (utriElt s : SL(2, F))⁻¹ = utriElt (-s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← utriElt_add, add_neg_cancel, utriElt_zero]

theorem utriElt_mem_utri (s : F) : (utriElt s : SL(2, F)) ∈ utri F :=
  ⟨utriElt_apply_10 s, utriElt_apply_00 s⟩

theorem ltriElt_mem_ltri (t : F) : (ltriElt t : SL(2, F)) ∈ ltri F :=
  ⟨ltriElt_apply_01 t, ltriElt_apply_00 t⟩

theorem torusElt_mem_torus (a : Fˣ) : (torusElt a : SL(2, F)) ∈ torus F :=
  ⟨torusElt_apply_01 a, torusElt_apply_10 a⟩

theorem eq_utriElt_of_mem_utri {g : SL(2, F)} (hg : g ∈ utri F) : g = utriElt (g 0 1) := by
  obtain ⟨h10, h00⟩ := hg
  have hd := sl2_det g
  rw [h00, h10] at hd
  refine sl2_ext ?_ ?_ ?_ ?_
  · rw [utriElt_apply_00, h00]
  · rw [utriElt_apply_01]
  · rw [utriElt_apply_10, h10]
  · rw [utriElt_apply_11]
    linear_combination hd

theorem mem_utri_iff {g : SL(2, F)} : g ∈ utri F ↔ ∃ s, g = utriElt s :=
  ⟨fun hg => ⟨_, eq_utriElt_of_mem_utri hg⟩, fun ⟨s, hs⟩ => hs ▸ utriElt_mem_utri s⟩

theorem eq_ltriElt_of_mem_ltri {g : SL(2, F)} (hg : g ∈ ltri F) : g = ltriElt (g 1 0) := by
  obtain ⟨h01, h00⟩ := hg
  have hd := sl2_det g
  rw [h00, h01] at hd
  refine sl2_ext ?_ ?_ ?_ ?_
  · rw [ltriElt_apply_00, h00]
  · rw [ltriElt_apply_01, h01]
  · rw [ltriElt_apply_10]
  · rw [ltriElt_apply_11]
    linear_combination hd

theorem mem_ltri_iff {g : SL(2, F)} : g ∈ ltri F ↔ ∃ t, g = ltriElt t :=
  ⟨fun hg => ⟨_, eq_ltriElt_of_mem_ltri hg⟩, fun ⟨t, ht⟩ => ht ▸ ltriElt_mem_ltri t⟩

theorem eq_torusElt_of_mem_torus {g : SL(2, F)} (hg : g ∈ torus F) :
    ∃ a : Fˣ, g = torusElt a := by
  obtain ⟨h01, h10⟩ := hg
  have hd := sl2_det g
  rw [h01, h10] at hd
  have hd' : g 0 0 * g 1 1 = 1 := by linear_combination hd
  refine ⟨Units.mk0 (g 0 0) (left_ne_zero_of_mul_eq_one hd'), sl2_ext ?_ ?_ ?_ ?_⟩
  · rw [torusElt_apply_00]
    rfl
  · rw [torusElt_apply_01, h01]
  · rw [torusElt_apply_10, h10]
  · rw [torusElt_apply_11]
    exact eq_inv_of_mul_eq_one_right hd'

theorem mem_torus_iff {g : SL(2, F)} : g ∈ torus F ↔ ∃ a : Fˣ, g = torusElt a :=
  ⟨eq_torusElt_of_mem_torus, fun ⟨a, ha⟩ => ha ▸ torusElt_mem_torus a⟩

theorem torusElt_mul (a b : Fˣ) : (torusElt (a * b) : SL(2, F)) = torusElt a * torusElt b :=
  map_mul (CFSG.Glauberman.Dickson.splitTorusSLHom F) a b

theorem torusElt_one : (torusElt 1 : SL(2, F)) = 1 :=
  map_one (CFSG.Glauberman.Dickson.splitTorusSLHom F)

theorem torusElt_injective : Function.Injective (torusElt : Fˣ → SL(2, F)) := fun a b h => by
  have h00 := congrArg (fun g : SL(2, F) => g 0 0) h
  exact Units.ext (by simpa only [torusElt_apply_00] using h00)

theorem utri_le_borel : utri F ≤ borel F := fun _ hg => hg.1

theorem torus_le_borel : torus F ≤ borel F := fun _ hg => hg.2

theorem torusElt_mem_borel (a : Fˣ) : (torusElt a : SL(2, F)) ∈ borel F :=
  torus_le_borel (torusElt_mem_torus a)

theorem inf_utri_torus : utri F ⊓ torus F = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hu, ht⟩
  rw [Subgroup.mem_bot, eq_utriElt_of_mem_utri hu, ht.1, utriElt_zero]

end Membership

section Utri

variable {F : Type} [Field F]

theorem isElemAbelian_utri [CharP F 2] : IsElemAbelian 2 (utri F) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    obtain ⟨s, hs⟩ := mem_utri_iff.1 a.2
    obtain ⟨t, ht⟩ := mem_utri_iff.1 b.2
    change (a : SL(2, F)) * b = b * a
    rw [hs, ht, ← utriElt_add, ← utriElt_add, add_comm]
  · obtain ⟨s, rfl⟩ := mem_utri_iff.1 hx
    rw [pow_two, ← utriElt_add, CharTwo.add_self_eq_zero, utriElt_zero]

theorem card_utri : Nat.card (utri F) = Nat.card F := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun s : F => (⟨utriElt s, utriElt_mem_utri s⟩ : utri F)) ⟨?_, ?_⟩)
  · intro s t h
    exact utriElt_injective (congrArg Subtype.val h)
  · rintro ⟨g, hg⟩
    obtain ⟨s, rfl⟩ := mem_utri_iff.1 hg
    exact ⟨s, rfl⟩

end Utri

section Conjugation

variable {F : Type} [Field F]

theorem conj_utriElt_apply_10 (g : SL(2, F)) (s : F) :
    (g * utriElt s * g⁻¹) 1 0 = - g 1 0 ^ 2 * s := by
  sl2_simp
  ring

theorem conj_utriElt_apply_00 (g : SL(2, F)) (s : F) :
    (g * utriElt s * g⁻¹) 0 0 = 1 - g 0 0 * g 1 0 * s := by
  sl2_simp
  linear_combination sl2_det g

theorem conj_utriElt_apply_01 (g : SL(2, F)) (s : F) :
    (g * utriElt s * g⁻¹) 0 1 = g 0 0 ^ 2 * s := by
  sl2_simp
  ring

theorem conj_utriElt_apply_11 (g : SL(2, F)) (s : F) :
    (g * utriElt s * g⁻¹) 1 1 = 1 + g 0 0 * g 1 0 * s := by
  sl2_simp
  linear_combination sl2_det g

theorem conj_mem_utri_of_mem_borel {g : SL(2, F)} (hg : g ∈ borel F) {h : SL(2, F)}
    (hh : h ∈ utri F) : g * h * g⁻¹ ∈ utri F := by
  obtain ⟨s, rfl⟩ := mem_utri_iff.1 hh
  have hg' : g 1 0 = 0 := hg
  refine ⟨?_, ?_⟩
  · show (g * utriElt s * g⁻¹) 1 0 = 0
    rw [conj_utriElt_apply_10, hg']
    ring
  · show (g * utriElt s * g⁻¹) 0 0 = 1
    rw [conj_utriElt_apply_00, hg']
    ring

theorem torusElt_mul_utriElt_mul_inv (a : Fˣ) (s : F) :
    torusElt a * utriElt s * (torusElt a)⁻¹ = utriElt ((a : F) ^ 2 * s) := by
  apply sl2_ext
  · rw [conj_utriElt_apply_00, utriElt_apply_00, torusElt_apply_10]
    ring
  · rw [conj_utriElt_apply_01, utriElt_apply_01, torusElt_apply_00]
  · rw [conj_utriElt_apply_10, utriElt_apply_10, torusElt_apply_10]
    ring
  · rw [conj_utriElt_apply_11, utriElt_apply_11, torusElt_apply_10]
    ring

theorem centralizer_utriElt [CharP F 2] {s : F} (hs : s ≠ 0) :
    Subgroup.centralizer ({utriElt s} : Set SL(2, F)) = utri F := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h00 := congrArg (fun x : SL(2, F) => x 0 0) h
    have h01 := congrArg (fun x : SL(2, F) => x 0 1) h
    sl2_simp at h00 h01
    have h10 : g 1 0 = 0 := by
      have h1 : s * g 1 0 = 0 := by linear_combination (-1) * h00
      exact (mul_eq_zero.1 h1).resolve_left hs
    have h11 : g 0 0 = g 1 1 := by
      have h1 : s * (g 0 0 - g 1 1) = 0 := by linear_combination h01
      exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hs)
    have hd := sl2_det g
    rw [h10, ← h11] at hd
    have hsq : g 0 0 ^ 2 = 1 := by linear_combination hd
    exact ⟨h10, CharTwo.sq_injective (by simpa using hsq)⟩
  · intro hg
    obtain ⟨t, rfl⟩ := mem_utri_iff.1 hg
    rw [← utriElt_add, ← utriElt_add, add_comm]

theorem normalizer_utri : Subgroup.normalizer (utri F : Set SL(2, F)) = borel F := by
  ext g
  constructor
  · intro hg
    have h := (Subgroup.mem_normalizer_iff.1 hg (utriElt (1 : F))).1 (utriElt_mem_utri 1)
    have h10 : (g * utriElt (1 : F) * g⁻¹) 1 0 = 0 := h.1
    rw [conj_utriElt_apply_10] at h10
    have h2 : g 1 0 ^ 2 = 0 := by linear_combination (-1) * h10
    exact pow_eq_zero_iff two_ne_zero |>.1 h2
  · intro hg
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => conj_mem_utri_of_mem_borel hg hx,
      fun hx => ?_⟩
    have h := conj_mem_utri_of_mem_borel (inv_mem hg) hx
    simpa [mul_assoc] using h

end Conjugation

section Borel

variable {F : Type} [Field F]

theorem card_borel : Nat.card (borel F) = Nat.card F * (Nat.card F - 1) := by
  have key : Nat.card (borel F) = Nat.card (F × Fˣ) := by
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun p : F × Fˣ => (⟨utriElt p.1 * torusElt p.2,
        Subgroup.mul_mem _ (utri_le_borel (utriElt_mem_utri p.1)) (torusElt_mem_borel p.2)⟩ :
          borel F)) ⟨?_, ?_⟩)
    · rintro ⟨x, a⟩ ⟨y, b⟩ h
      have h00 := congrArg (fun g : borel F => (g : SL(2, F)) 0 0) h
      have h01 := congrArg (fun g : borel F => (g : SL(2, F)) 0 1) h
      sl2_simp at h00 h01
      have hab : a = b := Units.ext (by linear_combination h00)
      subst hab
      have hxy : x = y := mul_right_cancel₀ (a⁻¹).ne_zero (by linear_combination h01)
      rw [hxy]
    · rintro ⟨g, hg⟩
      obtain ⟨a, ha⟩ :=
        CFSG.Glauberman.Dickson.eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero g hg
      exact ⟨(g 0 1 * g 0 0, a), Subtype.ext ha.symm⟩
  rw [key, Nat.card_prod, Nat.card_units]

theorem borel_eq_sup : borel F = utri F ⊔ torus F := by
  apply le_antisymm
  · intro g hg
    obtain ⟨a, ha⟩ :=
      CFSG.Glauberman.Dickson.eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero g hg
    rw [ha]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (utriElt_mem_utri _))
      (Subgroup.mem_sup_right (torusElt_mem_torus a))
  · exact sup_le utri_le_borel torus_le_borel

theorem card_torus : Nat.card (torus F) = Nat.card F - 1 := by
  rw [← Nat.card_units F]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun a : Fˣ => (⟨torusElt a, torusElt_mem_torus a⟩ : torus F)) ⟨?_, ?_⟩)
  · intro a b h
    exact torusElt_injective (congrArg Subtype.val h)
  · rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := mem_torus_iff.1 hg
    exact ⟨a, rfl⟩

theorem isCyclic_torus [Finite F] : IsCyclic (torus F) := by
  let f : Fˣ →* torus F := (CFSG.Glauberman.Dickson.splitTorusSLHom F).codRestrict (torus F)
    fun a => torusElt_mem_torus a
  refine isCyclic_of_surjective f ?_
  rintro ⟨g, hg⟩
  obtain ⟨a, rfl⟩ := mem_torus_iff.1 hg
  exact ⟨a, rfl⟩

theorem exists_torusElt_conj_utriElt [Finite F] [CharP F 2] {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ a : Fˣ, torusElt a * utriElt s * (torusElt a)⁻¹ = utriElt t := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (t / s)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact div_ne_zero ht hs (by simpa using hr)
  refine ⟨Units.mk0 r hr0, ?_⟩
  rw [torusElt_mul_utriElt_mul_inv]
  congr 1
  rw [Units.val_mk0, sq]
  have h2 : t = r * r * s := by rw [← hr]; field_simp
  exact h2.symm

theorem exists_mem_borel_conj_utriElt [Finite F] [CharP F 2] {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ b ∈ borel F, b * utriElt s * b⁻¹ = utriElt t := by
  obtain ⟨a, ha⟩ := exists_torusElt_conj_utriElt hs ht
  exact ⟨torusElt a, torusElt_mem_borel a, ha⟩

theorem eq_of_torusElt_conj_eq [CharP F 2] {s : F} (hs : s ≠ 0) {a b : Fˣ}
    (h : torusElt a * utriElt s * (torusElt a)⁻¹ = torusElt b * utriElt s * (torusElt b)⁻¹) :
    a = b := by
  rw [torusElt_mul_utriElt_mul_inv, torusElt_mul_utriElt_mul_inv] at h
  have h1 := utriElt_injective h
  have h2 : (a : F) ^ 2 = (b : F) ^ 2 := mul_right_cancel₀ hs h1
  exact Units.ext (CharTwo.sq_injective h2)

end Borel

end CFSG.CGT.Timmesfeld75
