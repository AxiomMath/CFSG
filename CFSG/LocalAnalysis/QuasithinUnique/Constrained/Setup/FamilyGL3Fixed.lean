module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Irred
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyDisplacement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

@[expose] def tinvols : List Mat3 :=
  [unitri 0 1 0, unitri 1 0 0, unitri 1 1 0, unitri 0 0 1, unitri 0 1 1]

theorem mem_tinvols : ∀ a b c : ZMod 2, unitri a b c * unitri a b c = 1 → unitri a b c ≠ 1 →
    unitri a b c ∈ tinvols := by
  decide

theorem rank_two_T : ∀ M₁ ∈ tinvols, ∀ M₂ ∈ tinvols, ∀ M₃ ∈ tinvols,
    (M₁ ≠ M₂ ∧ M₁ * M₂ = M₂ * M₁ ∧ M₁ * M₃ = M₃ * M₁ ∧ M₂ * M₃ = M₃ * M₂) →
      (M₃ = M₁ ∨ M₃ = M₂ ∨ M₃ = M₁ * M₂) := by
  decide +kernel

abbrev Tup8 : Type := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2

@[expose] def tzp (p : Tup8) : Mat3 :=
  traceZeroMat p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1
    p.2.2.2.2.2.2.2

@[expose] def cntV (M₁ M₂ : Mat3) : ℕ :=
  (Finset.univ.filter fun v : Fin 3 → ZMod 2 => M₁ *ᵥ v = v ∧ M₂ *ᵥ v = v).card

@[expose] def cntD (M₁ M₂ : Mat3) : ℕ :=
  (Finset.univ.filter fun v : Fin 3 → ZMod 2 => M₁ᵀ *ᵥ v = v ∧ M₂ᵀ *ᵥ v = v).card

@[expose] def cntT (M₁ M₂ : Mat3) : ℕ :=
  (Finset.univ.filter fun p : Tup8 => M₁ * tzp p * M₁ = tzp p ∧ M₂ * tzp p * M₂ = tzp p).card

theorem cnt_single_T : ∀ M ∈ tinvols, cntV M M = 4 ∧ cntD M M = 4 ∧ cntT M M = 16 := by
  decide +kernel

theorem cnt_pair_T : ∀ M₁ ∈ tinvols, ∀ M₂ ∈ tinvols, M₁ ≠ M₂ → M₁ * M₂ = M₂ * M₁ →
    ((cntV M₁ M₂ = 2 ∧ cntD M₁ M₂ = 4) ∨ (cntV M₁ M₂ = 4 ∧ cntD M₁ M₂ = 2)) ∧
      cntT M₁ M₂ = 4 := by
  decide +kernel

@[expose] def fixVec3 (B : Subgroup GL32) : Set (Fin 3 → ZMod 2) :=
  {v | ∀ g ∈ B, (g : Mat3) *ᵥ v = v}

@[expose] def fixDual3 (B : Subgroup GL32) : Set (Fin 3 → ZMod 2) :=
  {v | ∀ g ∈ B, ((g⁻¹ : GL32) : Mat3)ᵀ *ᵥ v = v}

@[expose] def fixTrace3 (B : Subgroup GL32) : Set Mat3 :=
  {X | X ∈ traceZero ∧ ∀ g ∈ B, (g : Mat3) * X * ((g⁻¹ : GL32) : Mat3) = X}

theorem natCard_setOf_eq_card_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {x | p x} = (Finset.univ.filter p).card := by
  rw [← Fintype.card_subtype, Nat.card_eq_fintype_card]
  rfl

theorem mem_traceZero_iff {X : Mat3} : X ∈ traceZero ↔ X.trace = 0 := by
  simp [traceZero]

theorem tzp_mem (p : Tup8) : tzp p ∈ traceZero := by
  rw [mem_traceZero_iff, Matrix.trace_fin_three]
  have h : ∀ a b : ZMod 2, a + b + (a + b) = 0 := by decide
  exact h _ _

@[expose] def tzEquiv : Tup8 ≃ traceZero where
  toFun p := ⟨tzp p, tzp_mem p⟩
  invFun X := ((X : Mat3) 0 0, (X : Mat3) 0 1, (X : Mat3) 0 2, (X : Mat3) 1 0, (X : Mat3) 1 1,
    (X : Mat3) 1 2, (X : Mat3) 2 0, (X : Mat3) 2 1)
  left_inv _ := rfl
  right_inv X := Subtype.ext (eq_traceZeroMat X.2).symm

theorem natCard_traceZero_setOf (P : Mat3 → Prop) [DecidablePred P] :
    Nat.card {X : Mat3 | X ∈ traceZero ∧ P X} =
      (Finset.univ.filter fun p : Tup8 => P (tzp p)).card := by
  have e : {X : Mat3 | X ∈ traceZero ∧ P X} ≃ {p : Tup8 // P (tzp p)} :=
    { toFun := fun X => ⟨tzEquiv.symm ⟨X.1, X.2.1⟩, by
        have := tzEquiv.apply_symm_apply ⟨X.1, X.2.1⟩
        have h2 : tzp (tzEquiv.symm ⟨X.1, X.2.1⟩) = X.1 := congrArg Subtype.val this
        rw [h2]
        exact X.2.2⟩
      invFun := fun p => ⟨tzp p.1, tzp_mem p.1, p.2⟩
      left_inv := fun X => by
        apply Subtype.ext
        show tzp (tzEquiv.symm ⟨X.1, X.2.1⟩) = X.1
        have := tzEquiv.apply_symm_apply ⟨X.1, X.2.1⟩
        exact congrArg Subtype.val this
      right_inv := fun p => by
        apply Subtype.ext
        show tzEquiv.symm ⟨tzp p.1, tzp_mem p.1⟩ = p.1
        exact tzEquiv.symm_apply_apply p.1 }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem val_mem_tinvols {g : GL32} (hT : g ∈ sylowT) (hg : g ^ 2 = 1) (hg1 : g ≠ 1) :
    (g : Mat3) ∈ tinvols := by
  obtain ⟨a, b, c, rfl⟩ := hT
  have h1 : unitri a b c * unitri a b c = 1 := by
    have := congrArg Units.val hg
    rwa [pow_two, Units.val_mul, Units.val_one] at this
  have h2 : unitri a b c ≠ 1 := fun h => hg1 (Units.ext h)
  exact mem_tinvols a b c h1 h2

theorem inv_eq_self_of_sq {g : GL32} (hg : g ^ 2 = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, hg])

theorem elemAbelian_cases_T {B : Subgroup GL32} (hle : B ≤ sylowT) (hB : B ≠ ⊥)
    (hsq : ∀ a ∈ B, a ^ 2 = 1) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    (∃ b ∈ B, b ≠ 1 ∧ ∀ g ∈ B, g = 1 ∨ g = b) ∨
      (∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ 1 ∧ b₂ ≠ 1 ∧ b₁ ≠ b₂ ∧
        ∀ g ∈ B, g = 1 ∨ g = b₁ ∨ g = b₂ ∨ g = b₁ * b₂) := by
  obtain ⟨⟨b₁, hb₁⟩, hb₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB
  have hb₁1' : b₁ ≠ 1 := fun h => hb₁1 (Subtype.ext h)
  by_cases h : ∀ g ∈ B, g = 1 ∨ g = b₁
  · exact Or.inl ⟨b₁, hb₁, hb₁1', h⟩
  · have h' : ∃ g ∈ B, g ≠ 1 ∧ g ≠ b₁ := by
      by_contra hcon
      apply h
      intro g hg
      by_contra hne
      exact hcon ⟨g, hg, fun h1 => hne (Or.inl h1), fun h2 => hne (Or.inr h2)⟩
    obtain ⟨b₂, hb₂, hb₂1, hb₂ne⟩ := h'
    refine Or.inr ⟨b₁, hb₁, b₂, hb₂, hb₁1', hb₂1, fun h => hb₂ne h.symm, fun g hg => ?_⟩
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    · right
      have hmat : ∀ x y : GL32, x ∈ B → y ∈ B →
          (x : Mat3) * (y : Mat3) = (y : Mat3) * (x : Mat3) :=
        fun x y hx hy => by rw [← Units.val_mul, ← Units.val_mul, hcomm x hx y hy]
      rcases rank_two_T (b₁ : Mat3) (val_mem_tinvols (hle hb₁) (hsq _ hb₁) hb₁1') (b₂ : Mat3)
        (val_mem_tinvols (hle hb₂) (hsq _ hb₂) hb₂1) (g : Mat3)
        (val_mem_tinvols (hle hg) (hsq _ hg) hg1)
        ⟨fun h => hb₂ne (Units.ext h).symm, hmat _ _ hb₁ hb₂, hmat _ _ hb₁ hg, hmat _ _ hb₂ hg⟩
        with h | h | h
      · exact Or.inl (Units.ext h)
      · exact Or.inr (Or.inl (Units.ext h))
      · exact Or.inr (Or.inr (Units.ext (by rw [h, Units.val_mul])))

theorem fixed_eq_of_gen {B : Subgroup GL32} {b₁ b₂ : GL32} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hs₁ : b₁ ^ 2 = 1) (hs₂ : b₂ ^ 2 = 1) (hgen : ∀ g ∈ B, g = 1 ∨ g = b₁ ∨ g = b₂ ∨ g = b₁ * b₂) :
    fixVec3 B = {v | (b₁ : Mat3) *ᵥ v = v ∧ (b₂ : Mat3) *ᵥ v = v} ∧
    fixDual3 B = {v | (b₁ : Mat3)ᵀ *ᵥ v = v ∧ (b₂ : Mat3)ᵀ *ᵥ v = v} ∧
    fixTrace3 B = {X | X ∈ traceZero ∧ (b₁ : Mat3) * X * (b₁ : Mat3) = X ∧
      (b₂ : Mat3) * X * (b₂ : Mat3) = X} := by
  have i₁ := inv_eq_self_of_sq hs₁
  have i₂ := inv_eq_self_of_sq hs₂
  refine ⟨?_, ?_, ?_⟩
  · ext v
    constructor
    · intro hv
      exact ⟨hv b₁ hb₁, hv b₂ hb₂⟩
    · rintro ⟨h1, h2⟩ g hg
      rcases hgen g hg with rfl | rfl | rfl | rfl
      · rw [Units.val_one, Matrix.one_mulVec]
      · exact h1
      · exact h2
      · rw [Units.val_mul, ← Matrix.mulVec_mulVec, h2, h1]
  · ext v
    constructor
    · intro hv
      have e1 := hv b₁ hb₁
      have e2 := hv b₂ hb₂
      rw [i₁] at e1
      rw [i₂] at e2
      exact ⟨e1, e2⟩
    · rintro ⟨h1, h2⟩ g hg
      rcases hgen g hg with rfl | rfl | rfl | rfl
      · rw [inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]
      · rw [i₁]; exact h1
      · rw [i₂]; exact h2
      · rw [_root_.mul_inv_rev, i₁, i₂, Units.val_mul, Matrix.transpose_mul,
          ← Matrix.mulVec_mulVec, h2, h1]
  · ext X
    constructor
    · rintro ⟨hX, hg⟩
      refine ⟨hX, ?_, ?_⟩
      · have := hg b₁ hb₁; rw [i₁] at this; exact this
      · have := hg b₂ hb₂; rw [i₂] at this; exact this
    · rintro ⟨hX, h1, h2⟩
      refine ⟨hX, fun g hg => ?_⟩
      rcases hgen g hg with rfl | rfl | rfl | rfl
      · simp
      · rw [i₁]; exact h1
      · rw [i₂]; exact h2
      · rw [_root_.mul_inv_rev, i₁, i₂]
        calc ((b₁ * b₂ : GL32) : Mat3) * X * ((b₂ * b₁ : GL32) : Mat3)
            = (b₁ : Mat3) * ((b₂ : Mat3) * X * (b₂ : Mat3)) * (b₁ : Mat3) := by
              simp only [Units.val_mul, Matrix.mul_assoc]
          _ = X := by rw [h2, h1]

theorem card_two {B : Subgroup GL32} {b : GL32} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hgen : ∀ g ∈ B, g = 1 ∨ g = b) : Nat.card B = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨b, hb⟩, fun h => hb1 (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨g, hg⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases hgen g hg with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem card_four {B : Subgroup GL32} {b₁ b₂ : GL32} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (h1 : b₁ ≠ 1) (h2 : b₂ ≠ 1) (hne : b₁ ≠ b₂) (hs₂ : b₂ ^ 2 = 1)
    (hgen : ∀ g ∈ B, g = 1 ∨ g = b₁ ∨ g = b₂ ∨ g = b₁ * b₂) : Nat.card B = 4 := by
  have h12 : b₁ * b₂ ≠ 1 := by
    intro h
    exact hne ((mul_eq_one_iff_eq_inv.1 h).trans (inv_eq_self_of_sq hs₂))
  have h13 : b₁ * b₂ ≠ b₁ := by
    intro h
    exact h2 (by simpa using h)
  have h23 : b₁ * b₂ ≠ b₂ := by
    intro h
    exact h1 (by simpa using h)
  have hS : (B : Set GL32) = ↑({1, b₁, b₂, b₁ * b₂} : Finset GL32) := by
    ext g
    constructor
    · intro hg
      simpa using hgen g hg
    · intro hg
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact B.one_mem
      · exact hb₁
      · exact hb₂
      · exact B.mul_mem hb₁ hb₂
  rw [show Nat.card B = Nat.card (B : Set GL32) from Nat.card_congr (Equiv.refl _), hS,
    Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have n1 : (1 : GL32) ∉ ({b₁, b₂, b₁ * b₂} : Finset GL32) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.symm, h2.symm, h12.symm⟩
  have n2 : b₁ ∉ ({b₂, b₁ * b₂} : Finset GL32) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne, h13.symm⟩
  have n3 : b₂ ∉ ({b₁ * b₂} : Finset GL32) := by
    simp only [Finset.mem_singleton]
    exact h23.symm
  rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
    Finset.card_insert_of_notMem n3, Finset.card_singleton]

@[expose] def FixedCodimData (B : Subgroup GL32) : Prop :=
  (Nat.card B = 2 ∧ Nat.card (fixVec3 B) = 4 ∧ Nat.card (fixDual3 B) = 4 ∧
      Nat.card (fixTrace3 B) = 16) ∨
    (Nat.card B = 4 ∧ ((Nat.card (fixVec3 B) = 2 ∧ Nat.card (fixDual3 B) = 4) ∨
      (Nat.card (fixVec3 B) = 4 ∧ Nat.card (fixDual3 B) = 2)) ∧ Nat.card (fixTrace3 B) = 4)

theorem fixedCodimData_of_le_T {B : Subgroup GL32} (hle : B ≤ sylowT) (hB : B ≠ ⊥)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hsq : ∀ a ∈ B, a ^ 2 = 1) : FixedCodimData B := by
  classical
  rcases elemAbelian_cases_T hle hB hsq hcomm with
    ⟨b, hb, hb1, hgen⟩ | ⟨b₁, hb₁, b₂, hb₂, h1, h2, hne, hgen⟩
  · left
    obtain ⟨hV, hD, hT⟩ := fixed_eq_of_gen hb hb (hsq b hb) (hsq b hb)
      (fun g hg => by
        rcases hgen g hg with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
    obtain ⟨c1, c2, c3⟩ := cnt_single_T _ (val_mem_tinvols (hle hb) (hsq b hb) hb1)
    refine ⟨card_two hb hb1 hgen, ?_, ?_, ?_⟩
    · rw [hV, natCard_setOf_eq_card_filter]; exact c1
    · rw [hD, natCard_setOf_eq_card_filter]; exact c2
    · rw [hT, natCard_traceZero_setOf]; exact c3
  · right
    have hc : b₁ * b₂ = b₂ * b₁ := hcomm b₁ hb₁ b₂ hb₂
    obtain ⟨hV, hD, hT⟩ := fixed_eq_of_gen hb₁ hb₂ (hsq b₁ hb₁) (hsq b₂ hb₂) hgen
    have hm : (b₁ : Mat3) * (b₂ : Mat3) = (b₂ : Mat3) * (b₁ : Mat3) := by
      rw [← Units.val_mul, ← Units.val_mul, hc]
    obtain ⟨hVD, c3⟩ := cnt_pair_T _ (val_mem_tinvols (hle hb₁) (hsq b₁ hb₁) h1) _
      (val_mem_tinvols (hle hb₂) (hsq b₂ hb₂) h2) (fun h => hne (Units.ext h)) hm
    refine ⟨card_four hb₁ hb₂ h1 h2 hne (hsq b₂ hb₂) hgen, ?_, ?_⟩
    · rw [hV, hD, natCard_setOf_eq_card_filter, natCard_setOf_eq_card_filter]
      exact hVD
    · rw [hT, natCard_traceZero_setOf]; exact c3

@[expose] def conjSub (B : Subgroup GL32) (g : GL32) : Subgroup GL32 :=
  B.comap (MulAut.conj g).toMonoidHom

theorem mem_conjSub {B : Subgroup GL32} {g x : GL32} : x ∈ conjSub B g ↔ g * x * g⁻¹ ∈ B :=
  Iff.rfl

theorem natCard_conjSub (B : Subgroup GL32) (g : GL32) : Nat.card (conjSub B g) = Nat.card B := by
  refine Nat.card_congr
    { toFun := fun x => ⟨g * x.1 * g⁻¹, x.2⟩
      invFun := fun y => ⟨g⁻¹ * y.1 * g, by
        rw [mem_conjSub]
        have : g * (g⁻¹ * y.1 * g) * g⁻¹ = y.1 := by group
        rw [this]
        exact y.2⟩
      left_inv := fun x => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group) }

theorem natCard_fix_conj {X : Type*} (act : GL32 → X → X)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x)) (hone : ∀ x, act 1 x = x)
    (S : X → Prop) (hS : ∀ g x, S x → S (act g x)) (B : Subgroup GL32) (g : GL32) :
    Nat.card {x | S x ∧ ∀ b ∈ conjSub B g, act b x = x} =
      Nat.card {x | S x ∧ ∀ b ∈ B, act b x = x} := by
  have hinv : ∀ x, act g⁻¹ (act g x) = x := fun x => by rw [← hmul, inv_mul_cancel, hone]
  have hinv' : ∀ x, act g (act g⁻¹ x) = x := fun x => by rw [← hmul, mul_inv_cancel, hone]
  refine Nat.card_congr ((Equiv.mk (act g) (act g⁻¹) hinv hinv').subtypeEquiv fun x => ?_)
  have hSx : S x ↔ S (act g x) := ⟨hS g x, fun h => by simpa [hinv] using hS g⁻¹ _ h⟩
  refine and_congr hSx ⟨fun hx a ha => ?_, fun hx b hb => ?_⟩
  · have hb : g⁻¹ * a * g ∈ conjSub B g := by
      rw [mem_conjSub]
      have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [this]
      exact ha
    have h1 : act (g⁻¹ * a * g) x = x := hx _ hb
    have h2 : act (g * (g⁻¹ * a * g)) x = act g x := by rw [hmul, h1]
    have h3 : g * (g⁻¹ * a * g) = a * g := by group
    rw [h3, hmul] at h2
    exact h2
  · have ha : g * b * g⁻¹ ∈ B := hb
    have h1 : act (g * b * g⁻¹) (act g x) = act g x := hx _ ha
    have h2 : act (g * b * g⁻¹ * g) x = act g x := by rw [hmul, h1]
    have h3 : g * b * g⁻¹ * g = g * b := by group
    rw [h3, hmul] at h2
    have h4 := congrArg (act g⁻¹) h2
    rwa [hinv, hinv] at h4

theorem natCard_fixVec3_conj (B : Subgroup GL32) (g : GL32) :
    Nat.card (fixVec3 (conjSub B g)) = Nat.card (fixVec3 B) := by
  have key := natCard_fix_conj (X := Fin 3 → ZMod 2) (fun g v => (g : Mat3) *ᵥ v)
    (fun g h x => by simp only [Units.val_mul, Matrix.mulVec_mulVec])
    (fun x => by simp) (fun _ => True) (fun _ _ _ => trivial) B g
  simpa [fixVec3] using key

theorem natCard_fixDual3_conj (B : Subgroup GL32) (g : GL32) :
    Nat.card (fixDual3 (conjSub B g)) = Nat.card (fixDual3 B) := by
  have key := natCard_fix_conj (X := Fin 3 → ZMod 2)
    (fun g v => ((g⁻¹ : GL32) : Mat3)ᵀ *ᵥ v)
    (fun g h x => by
      simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec])
    (fun x => by simp) (fun _ => True) (fun _ _ _ => trivial) B g
  simpa [fixDual3] using key

theorem natCard_fixTrace3_conj (B : Subgroup GL32) (g : GL32) :
    Nat.card (fixTrace3 (conjSub B g)) = Nat.card (fixTrace3 B) := by
  have key := natCard_fix_conj (X := Mat3) (fun g X => (g : Mat3) * X * ((g⁻¹ : GL32) : Mat3))
    (fun g h x => by
      simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc])
    (fun x => by simp) (fun X => X ∈ traceZero) (fun g X hX => by
      rw [mem_traceZero_iff] at hX ⊢
      rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
      exact hX) B g
  exact key

theorem exists_sylow_T : ∃ U : Sylow 2 GL32, (U : Subgroup GL32) = sylowT := by
  have h := Subgroup.card_mul_index sylowT
  rw [card_sylowT, Nat.card_eq_fintype_card (α := GL32)] at h
  have hc : Fintype.card GL32 = 168 := by
    rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field]
    simp [Fin.prod_univ_three, ZMod.card]
  rw [hc] at h
  have hidx : sylowT.index = 21 := by omega
  exact ⟨isPGroup_sylowT.toSylow (by rw [hidx]; norm_num), rfl⟩

theorem GL3_elementary_abelian_fixed_codimensions {B : Subgroup GL32} (hB : B ≠ ⊥)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hsq : ∀ a ∈ B, a ^ 2 = 1) : FixedCodimData B := by
  obtain ⟨U, hU⟩ := exists_sylow_T
  obtain ⟨g, hg⟩ := exists_conj_le_sylow_two U B (fun a ha => by rw [← pow_two]; exact hsq a ha)
  have hle : conjSub B g ≤ sylowT := by
    intro x hx
    have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ (U : Subgroup GL32) := hg _ hx
    rw [← hU]
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e] at h1
    exact h1
  have hne : conjSub B g ≠ ⊥ := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    intro h
    have hx : g⁻¹ * a * g ∈ conjSub B g := by
      rw [mem_conjSub]
      have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [e]
      exact ha
    rw [h, Subgroup.mem_bot] at hx
    apply ha1'
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hcomm' : ∀ x ∈ conjSub B g, ∀ y ∈ conjSub B g, x * y = y * x := by
    intro x hx y hy
    have h1 := hcomm _ hx _ hy
    have h2 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := h1
        _ = g * (y * x) * g⁻¹ := by group
    simpa using h2
  have hsq' : ∀ x ∈ conjSub B g, x ^ 2 = 1 := by
    intro x hx
    have h1 : (g * x * g⁻¹) ^ 2 = 1 := hsq _ hx
    have h2 : g * x ^ 2 * g⁻¹ = 1 := by rw [← conj_pow]; exact h1
    calc x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  have hdata := fixedCodimData_of_le_T hle hne hcomm' hsq'
  unfold FixedCodimData at hdata ⊢
  rwa [natCard_conjSub, natCard_fixVec3_conj, natCard_fixDual3_conj,
    natCard_fixTrace3_conj] at hdata

end CFSG.QuasithinUnique.Setup.Family
