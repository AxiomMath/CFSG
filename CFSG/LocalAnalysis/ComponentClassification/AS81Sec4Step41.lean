module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cent
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4S
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16FourProof
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Normal

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace Six

open Equiv

@[expose] def InK (a b x : Perm (Fin 6)) : Prop := x = 1 ∨ x = a ∨ x = b ∨ x = a * b

@[expose] def CondA (a : Perm (Fin 6)) : Prop := a 0 = 0 ∧ a 1 = 1 ∧ a * a = 1 ∧ a ≠ 1

@[expose] def CondB (a b : Perm (Fin 6)) : Prop :=
  b 0 = 0 ∧ b 1 = 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a

@[expose] def CondC (a b c : Perm (Fin 6)) : Prop :=
  c 0 = 0 ∧ c 1 = 1 ∧ InK a b (c * a * c⁻¹) ∧ InK a b (c * b * c⁻¹) ∧
    c * a * c⁻¹ ≠ a ∧ c * b * c⁻¹ ≠ b ∧ c * (a * b) * c⁻¹ ≠ a * b

@[expose] def CondS (a b c s : Perm (Fin 6)) : Prop :=
  s 0 = 1 ∧ s 1 = 0 ∧ InK a b (s * a * s⁻¹) ∧ InK a b (s * b * s⁻¹) ∧
    InK a b (s * c * s⁻¹ * c⁻¹)

@[expose] def SwapN (a b s : Perm (Fin 6)) : Prop :=
  Perm.sign s = 1 ∧ s 0 = 1 ∧ s 1 = 0 ∧ InK a b (s * a * s⁻¹) ∧ InK a b (s * b * s⁻¹)

instance (a b x : Perm (Fin 6)) : Decidable (InK a b x) := by unfold InK; infer_instance
instance (a : Perm (Fin 6)) : Decidable (CondA a) := by unfold CondA; infer_instance
instance (a b : Perm (Fin 6)) : Decidable (CondB a b) := by unfold CondB; infer_instance
instance (a b c : Perm (Fin 6)) : Decidable (CondC a b c) := by unfold CondC; infer_instance
instance (a b c s : Perm (Fin 6)) : Decidable (CondS a b c s) := by unfold CondS; infer_instance
instance (a b s : Perm (Fin 6)) : Decidable (SwapN a b s) := by unfold SwapN; infer_instance

theorem sign_check : ∀ a, CondA a → ∀ b, CondB a b → ∀ c, CondC a b c → ∀ s, CondS a b c s →
    Perm.sign s = -1 := by
  decide +kernel

theorem swap_check : ∀ a, CondA a → ∀ b, CondB a b → ∃ s, SwapN a b s := by
  decide +kernel

@[expose] def v₁ : Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 4 5

@[expose] def v₂ : Perm (Fin 6) := Equiv.swap 2 4 * Equiv.swap 3 5

@[expose] def v₃ : Perm (Fin 6) := Equiv.swap 2 5 * Equiv.swap 3 4

@[expose] def InV (x : Perm (Fin 6)) : Prop := x = v₁ ∨ x = v₂ ∨ x = v₃

@[expose] def NormK (a b s : Perm (Fin 6)) : Prop := InK a b (s * a * s⁻¹) ∧ InK a b (s * b * s⁻¹)

@[expose] def SqK (a b s : Perm (Fin 6)) : Prop := NormK a b s → s ^ 16 = 1 → InK a b (s * s)

instance (x : Perm (Fin 6)) : Decidable (InV x) := by unfold InV; infer_instance
instance (a b s : Perm (Fin 6)) : Decidable (NormK a b s) := by unfold NormK; infer_instance
instance (a b s : Perm (Fin 6)) : Decidable (SqK a b s) := by unfold SqK; infer_instance

theorem klein_check : ∀ a, CondA a → ∀ b, CondB a b → ∀ c, CondC a b c → InV a ∧ InV b := by
  decide +kernel

theorem card_check : ∀ a, InV a → ∀ b, InV b → a ≠ b →
    (Finset.univ.filter fun s => NormK a b s).card = 48 := by
  decide +kernel

theorem sq_check : ∀ a, InV a → ∀ b, InV b → a ≠ b → ∀ s, SqK a b s := by
  decide +kernel

end Six

section SixPoints

open Equiv

variable {P : Type*} [Finite P]

theorem exists_equiv_fin_six (h6 : Nat.card P = 6) {p₀ p₁ : P} (h01 : p₀ ≠ p₁) :
    ∃ e : P ≃ Fin 6, e p₀ = 0 ∧ e p₁ = 1 := by
  obtain ⟨e₀⟩ : Nonempty (P ≃ Fin 6) := Finite.card_eq.mp (by rw [h6, Nat.card_eq_fintype_card,
    Fintype.card_fin])
  set e₁ := e₀.trans (Equiv.swap (e₀ p₀) 0) with he₁
  have h0 : e₁ p₀ = 0 := by rw [he₁, Equiv.trans_apply, Equiv.swap_apply_left]
  have h1 : e₁ p₁ ≠ 0 := fun h => h01 (e₁.injective (h0.trans h.symm))
  refine ⟨e₁.trans (Equiv.swap (e₁ p₁) 1), ?_, ?_⟩
  · rw [Equiv.trans_apply, h0, Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (by decide)]
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

variable [DecidableEq P] [Fintype P]

theorem sign_eq_neg_one_of_six (h6 : Nat.card P = 6) {p₀ p₁ : P} (h01 : p₀ ≠ p₁)
    {a b c s : Perm P}
    (ha : a p₀ = p₀ ∧ a p₁ = p₁ ∧ a * a = 1 ∧ a ≠ 1)
    (hb : b p₀ = p₀ ∧ b p₁ = p₁ ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a)
    (hc : c p₀ = p₀ ∧ c p₁ = p₁ ∧
      (c * a * c⁻¹ = 1 ∨ c * a * c⁻¹ = a ∨ c * a * c⁻¹ = b ∨ c * a * c⁻¹ = a * b) ∧
      (c * b * c⁻¹ = 1 ∨ c * b * c⁻¹ = a ∨ c * b * c⁻¹ = b ∨ c * b * c⁻¹ = a * b) ∧
      c * a * c⁻¹ ≠ a ∧ c * b * c⁻¹ ≠ b ∧ c * (a * b) * c⁻¹ ≠ a * b)
    (hs : s p₀ = p₁ ∧ s p₁ = p₀ ∧
      (s * a * s⁻¹ = 1 ∨ s * a * s⁻¹ = a ∨ s * a * s⁻¹ = b ∨ s * a * s⁻¹ = a * b) ∧
      (s * b * s⁻¹ = 1 ∨ s * b * s⁻¹ = a ∨ s * b * s⁻¹ = b ∨ s * b * s⁻¹ = a * b) ∧
      (s * c * s⁻¹ * c⁻¹ = 1 ∨ s * c * s⁻¹ * c⁻¹ = a ∨ s * c * s⁻¹ * c⁻¹ = b ∨
        s * c * s⁻¹ * c⁻¹ = a * b)) :
    Perm.sign s = -1 := by
  obtain ⟨e, he0, he1⟩ := exists_equiv_fin_six h6 h01
  set φ := e.permCongrHom with hφ
  have hs0 : e.symm 0 = p₀ := by rw [← he0, Equiv.symm_apply_apply]
  have hs1 : e.symm 1 = p₁ := by rw [← he1, Equiv.symm_apply_apply]
  have happ : ∀ (x : Perm P) (i : Fin 6), φ x i = e (x (e.symm i)) := fun x i => rfl
  have hfix : ∀ (x : Perm P) {i j : Fin 6} {p q : P}, e.symm i = p → e.symm j = q →
      (x p = q ↔ φ x i = j) := by
    intro x i j p q hi hj
    rw [happ, ← hi, ← hj]
    exact e.eq_symm_apply
  have hinj : ∀ {x y : Perm P}, φ x = φ y ↔ x = y := fun {x y} => φ.injective.eq_iff
  have hne : ∀ {x y : Perm P}, x ≠ y → φ x ≠ φ y := fun {x y} h h' => h (hinj.mp h')
  have e2 : ∀ x y : Perm P, φ x * φ y = φ (x * y) := fun x y => (map_mul φ x y).symm
  have e3 : ∀ x y : Perm P, φ x * φ y * (φ x)⁻¹ = φ (x * y * x⁻¹) := fun x y => by
    rw [map_mul, map_mul, map_inv]
  have e4 : ∀ x y : Perm P, φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹ = φ (x * y * x⁻¹ * y⁻¹) :=
    fun x y => by rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  have hK' : ∀ x : Perm P, (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) →
      Six.InK (φ a) (φ b) (φ x) := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact Or.inl (map_one φ)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (map_mul φ a b)))
  obtain ⟨ha0, ha1, haa, ha1'⟩ := ha
  obtain ⟨hb0, hb1, hbb, hb1', hab, habc⟩ := hb
  obtain ⟨hc0, hc1, hca, hcb, hca', hcb', hcab'⟩ := hc
  obtain ⟨hs0', hs1', hsa, hsb, hsc⟩ := hs
  have hA : Six.CondA (φ a) := ⟨(hfix a hs0 hs0).mp ha0, (hfix a hs1 hs1).mp ha1,
    by rw [e2, haa, map_one], by rw [← map_one φ]; exact hne ha1'⟩
  have hB : Six.CondB (φ a) (φ b) := ⟨(hfix b hs0 hs0).mp hb0, (hfix b hs1 hs1).mp hb1,
    by rw [e2, hbb, map_one], by rw [← map_one φ]; exact hne hb1', hne hab,
    by rw [e2, e2, habc]⟩
  have hC : Six.CondC (φ a) (φ b) (φ c) := by
    refine ⟨(hfix c hs0 hs0).mp hc0, (hfix c hs1 hs1).mp hc1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e3]; exact hK' _ hca
    · rw [e3]; exact hK' _ hcb
    · rw [e3]; exact hne hca'
    · rw [e3]; exact hne hcb'
    · rw [e2, e3]; exact hne hcab'
  have hS : Six.CondS (φ a) (φ b) (φ c) (φ s) := by
    refine ⟨(hfix s hs0 hs1).mp hs0', (hfix s hs1 hs0).mp hs1', ?_, ?_, ?_⟩
    · rw [e3]; exact hK' _ hsa
    · rw [e3]; exact hK' _ hsb
    · rw [e4]; exact hK' _ hsc
  have h := Six.sign_check _ hA _ hB _ hC _ hS
  have hφs : φ s = e.permCongr s := rfl
  rwa [hφs, Equiv.Perm.sign_permCongr] at h

theorem exists_swap_of_six (h6 : Nat.card P = 6) {p₀ p₁ : P} (h01 : p₀ ≠ p₁) {a b : Perm P}
    (ha : a p₀ = p₀ ∧ a p₁ = p₁ ∧ a * a = 1 ∧ a ≠ 1)
    (hb : b p₀ = p₀ ∧ b p₁ = p₁ ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) :
    ∃ s : Perm P, Perm.sign s = 1 ∧ s p₀ = p₁ ∧ s p₁ = p₀ ∧
      (s * a * s⁻¹ = 1 ∨ s * a * s⁻¹ = a ∨ s * a * s⁻¹ = b ∨ s * a * s⁻¹ = a * b) ∧
      (s * b * s⁻¹ = 1 ∨ s * b * s⁻¹ = a ∨ s * b * s⁻¹ = b ∨ s * b * s⁻¹ = a * b) := by
  obtain ⟨e, he0, he1⟩ := exists_equiv_fin_six h6 h01
  set φ := e.permCongrHom with hφ
  have hs0 : e.symm 0 = p₀ := by rw [← he0, Equiv.symm_apply_apply]
  have hs1 : e.symm 1 = p₁ := by rw [← he1, Equiv.symm_apply_apply]
  have happ : ∀ (x : Perm P) (i : Fin 6), φ x i = e (x (e.symm i)) := fun x i => rfl
  have hfix : ∀ (x : Perm P) {i j : Fin 6} {p q : P}, e.symm i = p → e.symm j = q →
      (x p = q ↔ φ x i = j) := by
    intro x i j p q hi hj
    rw [happ, ← hi, ← hj]
    exact e.eq_symm_apply
  have hinj : ∀ {x y : Perm P}, φ x = φ y ↔ x = y := fun {x y} => φ.injective.eq_iff
  have hne : ∀ {x y : Perm P}, x ≠ y → φ x ≠ φ y := fun {x y} h h' => h (hinj.mp h')
  have e2 : ∀ x y : Perm P, φ x * φ y = φ (x * y) := fun x y => (map_mul φ x y).symm
  obtain ⟨ha0, ha1, haa, ha1'⟩ := ha
  obtain ⟨hb0, hb1, hbb, hb1', hab, habc⟩ := hb
  have hA : Six.CondA (φ a) := ⟨(hfix a hs0 hs0).mp ha0, (hfix a hs1 hs1).mp ha1,
    by rw [e2, haa, map_one], by rw [← map_one φ]; exact hne ha1'⟩
  have hB : Six.CondB (φ a) (φ b) := ⟨(hfix b hs0 hs0).mp hb0, (hfix b hs1 hs1).mp hb1,
    by rw [e2, hbb, map_one], by rw [← map_one φ]; exact hne hb1', hne hab,
    by rw [e2, e2, habc]⟩
  obtain ⟨σ, hσ1, hσ0, hσ1', hσa, hσb⟩ := Six.swap_check _ hA _ hB
  obtain ⟨s, rfl⟩ := φ.surjective σ
  have hback : ∀ x : Perm P, Six.InK (φ a) (φ b) (φ x) →
      (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) := by
    intro x hx
    rcases hx with h | h | h | h
    · exact Or.inl (hinj.mp (h.trans (map_one φ).symm))
    · exact Or.inr (Or.inl (hinj.mp h))
    · exact Or.inr (Or.inr (Or.inl (hinj.mp h)))
    · exact Or.inr (Or.inr (Or.inr (hinj.mp (h.trans (e2 a b)))))
  have e3 : ∀ x y : Perm P, φ x * φ y * (φ x)⁻¹ = φ (x * y * x⁻¹) := fun x y => by
    rw [map_mul, map_mul, map_inv]
  have hφs : φ s = e.permCongr s := rfl
  refine ⟨s, by rwa [hφs, Equiv.Perm.sign_permCongr] at hσ1, (hfix s hs0 hs1).mpr hσ0,
    (hfix s hs1 hs0).mpr hσ1', hback _ (by rw [← e3]; exact hσa),
    hback _ (by rw [← e3]; exact hσb)⟩

@[expose] def InFour {M : Type*} [Mul M] [One M] (a b x : M) : Prop :=
  x = 1 ∨ x = a ∨ x = b ∨ x = a * b

structure FourData {P : Type*} (p₀ p₁ : P) (a b c : Perm P) : Prop where
  ha : a p₀ = p₀ ∧ a p₁ = p₁ ∧ a * a = 1 ∧ a ≠ 1
  hb : b p₀ = p₀ ∧ b p₁ = p₁ ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a
  hc : c p₀ = p₀ ∧ c p₁ = p₁ ∧ InFour a b (c * a * c⁻¹) ∧ InFour a b (c * b * c⁻¹) ∧
    c * a * c⁻¹ ≠ a ∧ c * b * c⁻¹ ≠ b ∧ c * (a * b) * c⁻¹ ≠ a * b

omit [DecidableEq P] [Fintype P] in
theorem normalizer_four_of_six (h6 : Nat.card P = 6) {p₀ p₁ : P} (h01 : p₀ ≠ p₁)
    {a b c : Perm P} (ha : a p₀ = p₀ ∧ a p₁ = p₁ ∧ a * a = 1 ∧ a ≠ 1)
    (hb : b p₀ = p₀ ∧ b p₁ = p₁ ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a)
    (hc : c p₀ = p₀ ∧ c p₁ = p₁ ∧
      (c * a * c⁻¹ = 1 ∨ c * a * c⁻¹ = a ∨ c * a * c⁻¹ = b ∨ c * a * c⁻¹ = a * b) ∧
      (c * b * c⁻¹ = 1 ∨ c * b * c⁻¹ = a ∨ c * b * c⁻¹ = b ∨ c * b * c⁻¹ = a * b) ∧
      c * a * c⁻¹ ≠ a ∧ c * b * c⁻¹ ≠ b ∧ c * (a * b) * c⁻¹ ≠ a * b) :
    Nat.card {s : Perm P // InFour a b (s * a * s⁻¹) ∧ InFour a b (s * b * s⁻¹)} = 48 ∧
      ∀ s : Perm P, InFour a b (s * a * s⁻¹) → InFour a b (s * b * s⁻¹) → s ^ 16 = 1 →
        InFour a b (s * s) := by
  obtain ⟨e, he0, he1⟩ := exists_equiv_fin_six h6 h01
  set φ := e.permCongrHom with hφ
  have hs0 : e.symm 0 = p₀ := by rw [← he0, Equiv.symm_apply_apply]
  have hs1 : e.symm 1 = p₁ := by rw [← he1, Equiv.symm_apply_apply]
  have happ : ∀ (x : Perm P) (i : Fin 6), φ x i = e (x (e.symm i)) := fun x i => rfl
  have hfix : ∀ (x : Perm P) {i j : Fin 6} {p q : P}, e.symm i = p → e.symm j = q →
      (x p = q ↔ φ x i = j) := by
    intro x i j p q hi hj
    rw [happ, ← hi, ← hj]
    exact e.eq_symm_apply
  have hinj : ∀ {x y : Perm P}, φ x = φ y ↔ x = y := fun {x y} => φ.injective.eq_iff
  have hne : ∀ {x y : Perm P}, x ≠ y → φ x ≠ φ y := fun {x y} h h' => h (hinj.mp h')
  have e2 : ∀ x y : Perm P, φ x * φ y = φ (x * y) := fun x y => (map_mul φ x y).symm
  have e3 : ∀ x y : Perm P, φ x * φ y * (φ x)⁻¹ = φ (x * y * x⁻¹) := fun x y => by
    rw [map_mul, map_mul, map_inv]
  have hK : ∀ x : Perm P, InFour a b x ↔ Six.InK (φ a) (φ b) (φ x) := by
    intro x
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl (map_one φ)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (map_mul φ a b)))
    · rintro (h | h | h | h)
      · exact Or.inl (hinj.mp (h.trans (map_one φ).symm))
      · exact Or.inr (Or.inl (hinj.mp h))
      · exact Or.inr (Or.inr (Or.inl (hinj.mp h)))
      · exact Or.inr (Or.inr (Or.inr (hinj.mp (h.trans (e2 a b)))))
  have hK4 : ∀ x : Perm P, (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) →
      Six.InK (φ a) (φ b) (φ x) := fun x hx => (hK x).mp hx
  obtain ⟨ha0, ha1, haa, ha1'⟩ := ha
  obtain ⟨hb0, hb1, hbb, hb1', hab, habc⟩ := hb
  obtain ⟨hc0, hc1, hca, hcb, hca', hcb', hcab'⟩ := hc
  have hA : Six.CondA (φ a) := ⟨(hfix a hs0 hs0).mp ha0, (hfix a hs1 hs1).mp ha1,
    by rw [e2, haa, map_one], by rw [← map_one φ]; exact hne ha1'⟩
  have hB : Six.CondB (φ a) (φ b) := ⟨(hfix b hs0 hs0).mp hb0, (hfix b hs1 hs1).mp hb1,
    by rw [e2, hbb, map_one], by rw [← map_one φ]; exact hne hb1', hne hab,
    by rw [e2, e2, habc]⟩
  have hC : Six.CondC (φ a) (φ b) (φ c) := by
    refine ⟨(hfix c hs0 hs0).mp hc0, (hfix c hs1 hs1).mp hc1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e3]; exact hK4 _ hca
    · rw [e3]; exact hK4 _ hcb
    · rw [e3]; exact hne hca'
    · rw [e3]; exact hne hcb'
    · rw [e2, e3]; exact hne hcab'
  obtain ⟨hVa, hVb⟩ := Six.klein_check _ hA _ hB _ hC
  have hN : ∀ s : Perm P, (InFour a b (s * a * s⁻¹) ∧ InFour a b (s * b * s⁻¹)) ↔
      Six.NormK (φ a) (φ b) (φ s) := by
    intro s
    rw [hK, hK, Six.NormK, e3, e3]
  refine ⟨?_, fun s h1 h2 h16 => ?_⟩
  · have h48 := Six.card_check _ hVa _ hVb (hne hab)
    rw [← h48, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (φ.toEquiv.subtypeEquiv hN)
  · rw [hK, ← e2]
    exact Six.sq_check _ hVa _ hVb (hne hab) (φ s) ((hN s).mp ⟨h1, h2⟩)
      (by rw [← map_pow, h16, map_one])

end SixPoints

section Frame

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}

theorem Frame.swap (hF : Frame G A A₁ R g E F) : Frame G A A₁ R g F E where
  base := hF.base
  le := hF.le
  quasisimple := hF.quasisimple
  typeA₁ := hF.typeA₁
  sylowR := hF.sylowR
  elemR := hF.elemR
  cardR := hF.cardR
  not_mem := hF.not_mem
  comm := hF.comm
  conj_le := hF.conj_le
  E_le := hF.F_le
  F_le := hF.E_le
  R_le_E := hF.R_le_F
  R_le_F := hF.R_le_E
  elemE := hF.elemF
  elemF := hF.elemE
  cardE := hF.cardF
  cardF := hF.cardE
  ne := hF.ne.symm
  inf_eq := by rw [inf_comm]; exact hF.inf_eq
  inf_eq_center := by rw [inf_comm, sup_comm]; exact hF.inf_eq_center
  sylow := by rw [sup_comm]; exact hF.sylow

end Frame

section Odd

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_sup_odd {S O : Subgroup G} (hS : IsPGroup 2 S) (hO : Odd (Nat.card O))
    (hOS : O ≤ centralizer (S : Set G)) {x : G} (hx : x ∈ S ⊔ O) (hx2 : x * x = 1) : x ∈ S := by
  have hN : S ≤ normalizer (O : Set G) := fun s hs =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun o ho =>
      (mem_centralizer_iff.mp (hOS ho) s hs).symm)
  have hx' : x ∈ ((S ⊔ O : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right S O hN] at hx'
  obtain ⟨s, hs, o, ho, rfl⟩ := hx'
  have hso : s * o = o * s := mem_centralizer_iff.mp (hOS ho) s hs
  have hSO : S ⊓ O = ⊥ := two_subgroup_of_odd_eq_bot (S ⊓ O) O (hS.to_le inf_le_left) hO
    inf_le_right
  have hoo : o * o = 1 := by
    have h1 : s * s * (o * o) = 1 := by
      calc s * s * (o * o) = s * (s * o) * o := by group
        _ = s * (o * s) * o := by rw [hso]
        _ = s * o * (s * o) := by group
        _ = 1 := hx2
    have h2 : o * o = (s * s)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : o * o ∈ S ⊓ O := ⟨h2 ▸ S.inv_mem (S.mul_mem hs hs), O.mul_mem ho ho⟩
    rwa [hSO, mem_bot] at h3
  have ho1 : o = 1 := by
    have hdvd : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe] at hdvd
    have h2 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hoo])
    have h1 : orderOf o = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact h
      · exfalso
        rw [h] at hdvd
        exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hdvd)
    exact orderOf_eq_one_iff.mp h1
  rw [ho1]
  simpa using hs

end Odd

section Plane

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

structure PlaneData (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G)
    (E F : Subgroup G) : Prop where
  frame : Frame G A A R g E F
  type : TypeL34 (rankTwoQuot A)
  le : R ≤ A
  two : Nat.card (pointsIn R (E ⊓ F)) = 2
  six : Nat.card (pointsIn R E) = 6
  fix : ∀ k : G, (∀ Q ∈ pointsIn R E, k ∈ normalizer (Q : Set G)) → ∀ r ∈ R, r ≠ 1 →
    k * r * k⁻¹ = r → k ∈ centralizer (E : Set G)
  perfect : ∃ L : Subgroup G, centralizer (E : Set G) ≤ L ∧ L ≤ normalizer (E : Set G) ∧
    normalizer (E : Set G) ≤ normalizer (L : Set G) ∧
    ⁅L, L⁆ ⊔ centralizer (E : Set G) = L ∧ (centralizer (E : Set G)).relIndex L = 1080
  radical : A ⊓ normalizer (E : Set G) ≤
    ⁅A ⊓ normalizer (E : Set G), A ⊓ normalizer (E : Set G)⁆ ⊔ centralizer (E : Set G)
  sep : ∀ P ∈ pointsIn R E, P ≠ R → P ≠ rightConjugate R g →
    P ⊓ (R ⊔ rightConjugate R g) = ⊥

theorem planeData_of {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (heven : Even (Nat.card (center ↥A))) :
    PlaneData G A R g E F := by
  have hL : TypeL34 (rankTwoQuot A) := hF.typeA₁
  have h2 : Nat.card (pointsIn R (E ⊓ F)) = 2 := by
    rcases card_pointsIn_inf hE16 h11 hF hL with h | h
    · exact h
    · exact absurd h (step16NotFourPoints hE16 h11 G A R g E F hF heven)
  have hRA := le_of_card_pointsIn_inf_eq_two hE16 h11 hF hL heven h2
  obtain ⟨hP, -, hPR⟩ := rightConjugate_mem_pointsIn_frame hF
  refine ⟨hF, hL, hRA, h2, card_pointsIn_eq_six hE16 h11 hF hL h2,
    fun k hk r hr hr1 hkr => mem_centralizer_of_fix_points hE16 h11 hF hL h2 hk hr hr1 hkr,
    exists_normal_perfect hE16 h11 hF hL heven h2, ?_, ?_⟩
  · have h := (radical_at_point hE16 h11 hF hL hRA
      (by rw [rightConjugate_one]; exact hF.R_le_E : rightConjugate R 1 ≤ E)).1
    rwa [rightConjugate_one] at h
  · intro P hP' hPR' hPg
    exact inf_sup_eq_bot_of_card_two hE16 h11 hF hL h2 hP' hP hPR' hPR hPg

namespace PlaneData

variable (hD : PlaneData G A R g E F)
include hD

theorem commE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (hD.frame.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem commF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (hD.frame.elemF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem sqE : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hD.frame.elemE.2 x hx

theorem sqF : ∀ x ∈ F, x * x = 1 := fun x hx => by rw [← sq]; exact hD.frame.elemF.2 x hx

theorem R_mem : R ∈ pointsIn R E := self_mem_pointsIn hD.frame.R_le_E

theorem Rg_mem : rightConjugate R g ∈ pointsIn R E := (rightConjugate_mem_pointsIn_frame hD.frame).1

theorem Rg_ne : rightConjugate R g ≠ R := (rightConjugate_mem_pointsIn_frame hD.frame).2.2

theorem Rg_le : rightConjugate R g ≤ E ⊓ F := (rightConjugate_mem_pointsIn_frame hD.frame).2.1

theorem E_le_A : E ≤ A := by
  have h := hD.frame.E_le
  rwa [sup_eq_left.mpr hD.le] at h

theorem F_le_A : F ≤ A := by
  have h := hD.frame.F_le
  rwa [sup_eq_left.mpr hD.le] at h

theorem R_le_centralizer : R ≤ centralizer (A : Set G) := hD.frame.sylowR.le

theorem comm_R {a r : G} (ha : a ∈ A) (hr : r ∈ R) : a * r = r * a :=
  (mem_centralizer_iff.mp (hD.R_le_centralizer hr) a ha)

theorem F_le_normalizer : F ≤ normalizer (E : Set G) := by
  have hc := hD.frame.commutator_eq hD.le hD.type
  have hconj : ∀ f ∈ F, ∀ e ∈ E, f * e * f⁻¹ ∈ E := by
    intro f hf e he
    have h1 : f * e * f⁻¹ * e⁻¹ ∈ E ⊓ F := by
      rw [← hc]
      exact commutator_mem_commutator (mem_sup_right hf) (mem_sup_left he)
    have h2 : f * e * f⁻¹ = f * e * f⁻¹ * e⁻¹ * e := by group
    rw [h2]
    exact E.mul_mem h1.1 he
  intro f hf
  rw [mem_normalizer_iff]
  intro e
  constructor
  · exact hconj f hf e
  · intro he
    have h := hconj f⁻¹ (F.inv_mem hf) _ he
    rwa [inv_inv, show f⁻¹ * (f * e * f⁻¹) * f = e by group] at h

theorem centralizer_eq :
    centralizer (E : Set G) = E ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) :=
  centralizer_eq_sup_of_le hD.frame hD.type hD.le (Or.inl rfl)

theorem centralizer_eq' :
    centralizer (F : Set G) = F ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) :=
  centralizer_eq_sup_of_le hD.frame hD.type hD.le (Or.inr rfl)

theorem oddCore_le_centralizer :
    AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer ((E ⊔ F : Subgroup G) : Set G) := by
  have hE : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (E : Set G) :=
    hD.centralizer_eq ▸ le_sup_right
  have hF : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (F : Set G) :=
    hD.centralizer_eq' ▸ le_sup_right
  exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hE) (le_centralizer_iff.mp hF))

end PlaneData

end Plane

section Kernel

variable {G : Type} [Group G] {R E : Subgroup G}

@[expose] noncomputable def ptsKer (R E : Subgroup G) : Subgroup G :=
  (pointsAction R E).ker.map (normalizer (E : Set G)).subtype

theorem mem_ptsKer {x : G} :
    x ∈ ptsKer R E ↔ ∃ hx : x ∈ normalizer (E : Set G), pointsAction R E ⟨x, hx⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem ptsKer_le_normalizer : ptsKer R E ≤ normalizer (E : Set G) := fun _ hx =>
  (mem_ptsKer.mp hx).1

theorem centralizer_le_ptsKer : centralizer (E : Set G) ≤ ptsKer R E := fun _ hc =>
  mem_ptsKer.mpr ⟨Subgroup.centralizer_le_normalizer _ hc,
    pointsAction_eq_one_of_mem_centralizer hc⟩

theorem mem_normalizer_of_mem_ptsKer {κ : G} (hκ : κ ∈ ptsKer R E) {Q : Subgroup G}
    (hQ : Q ∈ pointsIn R E) : κ ∈ normalizer (Q : Set G) := by
  obtain ⟨hκN, h⟩ := mem_ptsKer.mp hκ
  exact mem_normalizer_of_pointsAction_eq_one h Q hQ

theorem conj_mem_ptsKer {n κ : G} (hn : n ∈ normalizer (E : Set G)) (hκ : κ ∈ ptsKer R E) :
    n * κ * n⁻¹ ∈ ptsKer R E := by
  obtain ⟨hκN, h⟩ := mem_ptsKer.mp hκ
  refine mem_ptsKer.mpr ⟨mul_mem (mul_mem hn hκN) (inv_mem hn), ?_⟩
  have e : (⟨n * κ * n⁻¹, mul_mem (mul_mem hn hκN) (inv_mem hn)⟩ :
      ↥(normalizer (E : Set G))) = ⟨n, hn⟩ * ⟨κ, hκN⟩ * (⟨n, hn⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, h, mul_one, map_inv, mul_inv_cancel]

theorem pointsAction_apply_eq {n : G} (hn : n ∈ normalizer (E : Set G)) {Q P : Subgroup G}
    (hQ : Q ∈ pointsIn R E) (hP : P ∈ pointsIn R E) :
    pointsAction R E ⟨n, hn⟩ ⟨Q, hQ⟩ = ⟨P, hP⟩ ↔ rightConjugate Q n⁻¹ = P := by
  rw [← Subtype.coe_inj, coe_pointsAction_apply]

theorem pointsAction_apply_self {n : G} (hn : n ∈ normalizer (E : Set G)) {Q : Subgroup G}
    (hQ : Q ∈ pointsIn R E) (hnQ : n ∈ normalizer (Q : Set G)) :
    pointsAction R E ⟨n, hn⟩ ⟨Q, hQ⟩ = ⟨Q, hQ⟩ :=
  (pointsAction_apply_eq hn hQ hQ).mpr ((rightConjugate_eq_self_iff Q _).mpr (inv_mem hnQ))

end Kernel

section Even

variable {G : Type} [Group G] [Finite G]

theorem centralizes_of_relIndex_three {N C K L : Subgroup G} (hCK : C ≤ K) (hKN : K ≤ N)
    (hCn : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) (hKn : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K)
    (hK3 : C.relIndex K = 3) (hLN : L ≤ N) (hperf : ⁅L, L⁆ ⊔ C = L) :
    (∀ κ ∈ K, κ ^ 3 ∈ C) ∧ ∀ n ∈ L, ∀ κ ∈ K, n * κ * n⁻¹ * κ⁻¹ ∈ C := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCN : C ≤ N := hCK.trans hKN
  have hnC : (C.subgroupOf N).Normal := ⟨fun c hc n => by
    rw [mem_subgroupOf] at hc ⊢
    exact hCn n n.2 c hc⟩
  set π := QuotientGroup.mk' (C.subgroupOf N) with hπ
  set Kb := (K.subgroupOf N).map π with hKbdef
  have hπC : ∀ x : ↥N, π x = 1 ↔ (x : G) ∈ C := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hcardK : Nat.card Kb = 3 := by
    have h := card_eq_card_inf_ker_mul_card_map π (K.subgroupOf N)
    rw [QuotientGroup.ker_mk', inf_eq_right.mpr (fun x hx => hCK hx :
      C.subgroupOf N ≤ K.subgroupOf N)] at h
    have hK' : Nat.card (K.subgroupOf N) = Nat.card K :=
      Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv
    have hC' : Nat.card (C.subgroupOf N) = Nat.card C :=
      Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv
    have hrel := Subgroup.relIndex_mul_card (H := C) (K := K)
    rw [inf_eq_left.mpr hCK, hK3] at hrel
    rw [hK', hC', ← hrel, mul_comm] at h
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h).symm
  have hmemKb : ∀ κ (hκ : κ ∈ K), π ⟨κ, hKN hκ⟩ ∈ Kb := fun κ hκ => ⟨⟨κ, hKN hκ⟩, hκ, rfl⟩
  have hpow : ∀ κ ∈ K, κ ^ 3 ∈ C := by
    intro κ hκ
    have h1 : (⟨π ⟨κ, hKN hκ⟩, hmemKb κ hκ⟩ : Kb) ^ 3 = 1 := by
      rw [← hcardK]
      exact pow_card_eq_one'
    have h2 : π (⟨κ, hKN hκ⟩ ^ 3) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val h1
    exact (hπC _).mp h2
  refine ⟨hpow, fun n hn κ hκ => ?_⟩
  by_cases hκC : κ ∈ C
  · exact mul_mem (hCn n (hLN hn) κ hκC) (inv_mem hκC)
  set y := π ⟨κ, hKN hκ⟩ with hy
  have hy1 : y ≠ 1 := fun h => hκC ((hπC _).mp h)
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← map_pow]
    exact (hπC _).mpr (hpow κ hκ)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyinv : y ≠ y⁻¹ := by
    intro h
    have h2 : y ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h]
      exact mul_inv_cancel y
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hyo] at this
    omega
  have hzp : zpowers y = Kb := Subgroup.eq_of_le_of_card_ge
    (zpowers_le.mpr (hmemKb κ hκ)) (by rw [hcardK, Nat.card_zpowers, hyo])
  have hKb3 : ∀ x ∈ Kb, x = 1 ∨ x = y ∨ x = y⁻¹ := by
    intro x hx
    rw [← hzp, mem_zpowers_iff_mem_range_orderOf, hyo, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Finset.mem_range] at hk
    interval_cases k
    · exact Or.inl (pow_zero y)
    · exact Or.inr (Or.inl (pow_one y))
    · right; right
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hy3
  have hconj : ∀ a, a * y * a⁻¹ = y ∨ a * y * a⁻¹ = y⁻¹ := by
    intro a
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf N) a
    have hmem : π m * y * (π m)⁻¹ ∈ Kb := by
      rw [hy, ← map_inv, ← map_mul, ← map_mul]
      exact ⟨m * ⟨κ, hKN hκ⟩ * m⁻¹, hKn m m.2 κ hκ, rfl⟩
    rcases hKb3 _ hmem with h | h | h
    · exfalso
      apply hy1
      calc y = (π m)⁻¹ * (π m * y * (π m)⁻¹) * π m := by group
        _ = (π m)⁻¹ * 1 * π m := by rw [h]
        _ = 1 := by group
    · exact Or.inl h
    · exact Or.inr h
  set Z := Subgroup.centralizer ({y} : Set (↥N ⧸ C.subgroupOf N)) with hZdef
  have hZ : ∀ a, a ∈ Z ↔ a * y * a⁻¹ = y := fun a => by
    rw [hZdef, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have key : ∀ a b, a * b ∈ Z ↔ (a ∈ Z ↔ b ∈ Z) := by
    intro a b
    rw [hZ, hZ, hZ]
    have e : (a * b) * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
    rw [e]
    rcases hconj b with hb | hb
    · rw [hb]
      exact ⟨fun h => ⟨fun _ => rfl, fun _ => h⟩, fun h => h.mpr rfl⟩
    · rw [hb, show a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ by group]
      rcases hconj a with ha | ha
      · rw [ha]
        exact ⟨fun h => ⟨fun _ => h, fun _ => rfl⟩, fun h => h.mp rfl⟩
      · rw [ha, inv_inv]
        exact ⟨fun _ => Iff.rfl, fun _ => rfl⟩
  have hcomm : ∀ a b, a * b * a⁻¹ * b⁻¹ ∈ Z := by
    intro a b
    rw [key, key, key, inv_mem_iff, inv_mem_iff]
    tauto
  have hcommL : ⁅L, L⁆ ≤ L := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
  have hLZ : L.subgroupOf N ≤ Z.comap π := by
    rw [← hperf, Subgroup.subgroupOf_sup (hcommL.trans hLN) hCN, commutator_subgroupOf hLN]
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro x _ w _
      rw [Subgroup.mem_comap, map_commutatorElement, commutatorElement_def]
      exact hcomm _ _
    · intro c hc
      rw [Subgroup.mem_comap, (hπC c).mpr hc]
      exact Z.one_mem
  have hnZ : π ⟨n, hLN hn⟩ ∈ Z := hLZ hn
  rw [hZ] at hnZ
  have h1 : π (⟨n, hLN hn⟩ * ⟨κ, hKN hκ⟩ * (⟨n, hLN hn⟩)⁻¹ * (⟨κ, hKN hκ⟩)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hy, hnZ, mul_inv_cancel]
  exact (hπC _).mp h1

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}
variable [Fintype ↥(pointsIn R E)] [DecidableEq ↥(pointsIn R E)]

omit [Finite G] in
theorem pointsAction_mem_alternatingGroup {M : Subgroup G} (hMN : M ≤ normalizer (E : Set G))
    (hM : M ≤ ⁅M, M⁆ ⊔ centralizer (E : Set G)) {x : G} (hx : x ∈ M) :
    pointsAction R E ⟨x, hMN hx⟩ ∈ alternatingGroup ↥(pointsIn R E) := by
  set ψ : ↥(normalizer (E : Set G)) →* ℤˣ := Equiv.Perm.sign.comp (pointsAction R E)
  have hCN : centralizer (E : Set G) ≤ normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hcommM : ⁅M, M⁆ ≤ M := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  have hM' : M.subgroupOf (normalizer (E : Set G)) ≤ ψ.ker := by
    have hle : M.subgroupOf (normalizer (E : Set G)) ≤
        ⁅M.subgroupOf (normalizer (E : Set G)), M.subgroupOf (normalizer (E : Set G))⁆ ⊔
          (centralizer (E : Set G)).subgroupOf (normalizer (E : Set G)) := by
      rw [← commutator_subgroupOf hMN, ← Subgroup.subgroupOf_sup (hcommM.trans hMN) hCN]
      exact fun y hy => hM hy
    refine hle.trans (sup_le ((Subgroup.commutator_mono le_top le_top).trans
      (Abelianization.commutator_subset_ker ψ)) fun c hc => ?_)
    rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      pointsAction_eq_one_of_mem_centralizer hc, map_one]
  have h := hM' (show (⟨x, hMN hx⟩ : ↥(normalizer (E : Set G))) ∈
    M.subgroupOf (normalizer (E : Set G)) from hx)
  rw [MonoidHom.mem_ker] at h
  exact Equiv.Perm.mem_alternatingGroup.mpr h

theorem PlaneData.exists_even (hD : PlaneData G A R g E F) :
    ∃ L : Subgroup G, centralizer (E : Set G) ≤ L ∧ L ≤ normalizer (E : Set G) ∧
      ⁅L, L⁆ ⊔ centralizer (E : Set G) = L ∧ ptsKer R E ≤ L ∧
      (centralizer (E : Set G)).relIndex (ptsKer R E) = 3 ∧
      (∀ n (hn : n ∈ normalizer (E : Set G)),
        n ∈ L ↔ pointsAction R E ⟨n, hn⟩ ∈ alternatingGroup ↥(pointsIn R E)) ∧
      alternatingGroup ↥(pointsIn R E) ≤ (pointsAction R E).range := by
  obtain ⟨L, hCL, hLN, -, hperf, hidx⟩ := hD.perfect
  have hCK : centralizer (E : Set G) ≤ ptsKer R E := centralizer_le_ptsKer
  have hLalt : ∀ x (hx : x ∈ L),
      pointsAction R E ⟨x, hLN hx⟩ ∈ alternatingGroup ↥(pointsIn R E) :=
    fun x hx => pointsAction_mem_alternatingGroup hLN hperf.ge hx
  have hthree : ∀ H : Subgroup G, H ≤ ptsKer R E →
      (centralizer (E : Set G)).relIndex H = 1 ∨ (centralizer (E : Set G)).relIndex H = 3 := by
    intro H hHK
    refine relIndex_eq_one_or_three hD.frame.elemR hD.frame.cardR
      (fun h hh => mem_normalizer_of_mem_ptsKer (hHK hh) hD.R_mem) ?_ ?_
    · intro c hc
      exact mem_centralizer_iff.mpr fun r hr => mem_centralizer_iff.mp hc.1 r (hD.frame.R_le_E hr)
    · intro h hh r hr hr1 hhr
      exact hD.fix h (fun Q hQ => mem_normalizer_of_mem_ptsKer (hHK hh) hQ) r hr hr1 hhr
  have hKL : (ptsKer R E).relIndex L =
      Nat.card ((L.subgroupOf (normalizer (E : Set G))).map (pointsAction R E)) := by
    rw [← relIndex_subgroupOf hLN]
    have hK' : (ptsKer R E).subgroupOf (normalizer (E : Set G)) = (pointsAction R E).ker :=
      comap_map_eq_self_of_injective (normalizer (E : Set G)).subtype_injective _
    rw [hK', Subgroup.relIndex_ker]
  have hmul := Subgroup.relIndex_mul_relIndex (centralizer (E : Set G)) (L ⊓ ptsKer R E) L
    (le_inf hCL hCK) inf_le_left
  rw [inf_relIndex_left, hidx, hKL] at hmul
  have hρL : (L.subgroupOf (normalizer (E : Set G))).map (pointsAction R E) ≤
      alternatingGroup ↥(pointsIn R E) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hLalt x hx
  have h6 : Nat.card ↥(pointsIn R E) = 6 := hD.six
  have : Nontrivial ↥(pointsIn R E) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hAlt : Nat.card (alternatingGroup ↥(pointsIn R E)) = 360 := by
    rw [nat_card_alternatingGroup, h6]
    rfl
  have hle360 := Subgroup.card_le_of_le hρL
  rw [hAlt] at hle360
  have h3 : (centralizer (E : Set G)).relIndex (L ⊓ ptsKer R E) = 3 := by
    rcases hthree (L ⊓ ptsKer R E) inf_le_right with h | h
    · rw [h] at hmul
      omega
    · exact h
  have hρLeq : (L.subgroupOf (normalizer (E : Set G))).map (pointsAction R E) =
      alternatingGroup ↥(pointsIn R E) :=
    Subgroup.eq_of_le_of_card_ge hρL (by rw [hAlt]; rw [h3] at hmul; omega)
  have hmul' := Subgroup.relIndex_mul_relIndex (centralizer (E : Set G)) (L ⊓ ptsKer R E)
    (ptsKer R E) (le_inf hCL hCK) inf_le_right
  rw [h3] at hmul'
  have hK3 : (centralizer (E : Set G)).relIndex (ptsKer R E) = 3 := by
    rcases hthree (ptsKer R E) le_rfl with h | h <;> omega
  have hKle : ptsKer R E ≤ L := by
    have h1 : (L ⊓ ptsKer R E).relIndex (ptsKer R E) = 1 := by omega
    exact (Subgroup.relIndex_eq_one.mp h1).trans inf_le_left
  refine ⟨L, hCL, hLN, hperf, hKle, hK3, fun n hn => ⟨fun h => hLalt n h, fun h => ?_⟩, ?_⟩
  · rw [← hρLeq] at h
    obtain ⟨⟨l, hlN⟩, hl, hle⟩ := h
    have hk : l⁻¹ * n ∈ ptsKer R E := by
      refine mem_ptsKer.mpr ⟨mul_mem (inv_mem hlN) hn, ?_⟩
      have e : (⟨l⁻¹ * n, mul_mem (inv_mem hlN) hn⟩ : ↥(normalizer (E : Set G))) =
          (⟨l, hlN⟩)⁻¹ * ⟨n, hn⟩ := rfl
      rw [e, map_mul, map_inv, hle, inv_mul_cancel]
    have h' : l * (l⁻¹ * n) ∈ L := L.mul_mem hl (hKle hk)
    rwa [mul_inv_cancel_left] at h'
  · rw [← hρLeq]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩

end Even

section Cross

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

namespace PlaneData

variable (hD : PlaneData G A R g E F)
include hD

theorem exists_conj {Q : Subgroup G} (hQ : Q ∈ pointsIn R E) :
    ∃ n ∈ normalizer (E : Set G), rightConjugate R n = Q := by
  classical
  have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
  obtain ⟨L, -, -, -, -, -, -, halt⟩ := hD.exists_even
  have h3 : 3 ≤ Nat.card ↥(pointsIn R E) := by rw [hD.six]; norm_num
  have := alternatingGroup.isPretransitive_of_three_le_card ↥(pointsIn R E) h3
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup ↥(pointsIn R E))
    (⟨R, hD.R_mem⟩ : ↥(pointsIn R E)) ⟨Q, hQ⟩
  obtain ⟨m, hm⟩ := halt σ.2
  refine ⟨(m : G)⁻¹, inv_mem m.2, ?_⟩
  have h1 : pointsAction R E m ⟨R, hD.R_mem⟩ = ⟨Q, hQ⟩ := by
    rw [hm]
    exact hσ
  have h2 := congrArg Subtype.val h1
  rwa [coe_pointsAction_apply] at h2

theorem conj_ne_of_mem_ptsKer {κ : G} (hκ : κ ∈ ptsKer R E) (hκC : κ ∉ centralizer (E : Set G))
    {Q : Subgroup G} (hQ : Q ∈ pointsIn R E) {q : G} (hq : q ∈ Q) (hq1 : q ≠ 1) :
    κ * q * κ⁻¹ ≠ q := by
  intro hfix
  obtain ⟨n, hn, rfl⟩ := hD.exists_conj hQ
  have hr : n * q * n⁻¹ ∈ R := (mem_rightConjugate_iff R n q).mp hq
  have hr1 : n * q * n⁻¹ ≠ 1 := fun h => hq1 (conj_eq_one_iff.mp h)
  have hκ' := conj_mem_ptsKer hn hκ
  have hfix' : (n * κ * n⁻¹) * (n * q * n⁻¹) * (n * κ * n⁻¹)⁻¹ = n * q * n⁻¹ := by
    calc (n * κ * n⁻¹) * (n * q * n⁻¹) * (n * κ * n⁻¹)⁻¹ = n * (κ * q * κ⁻¹) * n⁻¹ := by
          group
      _ = n * q * n⁻¹ := by rw [hfix]
  have hC := hD.fix _ (fun Q' hQ' => mem_normalizer_of_mem_ptsKer hκ' hQ') _ hr hr1 hfix'
  apply hκC
  have h := conj_mem_centralizer (inv_mem hn) hC
  rwa [show n⁻¹ * (n * κ * n⁻¹) * n⁻¹⁻¹ = κ by group] at h

theorem isPGroup_sup : IsPGroup 2 (E ⊔ F : Subgroup G) := hD.frame.sylow.isPGroup

theorem mem_sup_of_mem {x : G} (hx : x ∈ centralizer (E : Set G) ⊔ F) (hx2 : x * x = 1) :
    x ∈ E ⊔ F := by
  have hle : centralizer (E : Set G) ⊔ F ≤
      (E ⊔ F) ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) := by
    rw [hD.centralizer_eq]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (le_sup_right.trans le_sup_left)
  exact mem_of_mem_sup_odd hD.isPGroup_sup (AS76b.odd_card_oddCoreIn _)
    hD.oddCore_le_centralizer (hle hx) hx2

theorem ptsKer_le_normalizer_other : ptsKer R E ≤ normalizer (F : Set G) := by
  classical
  have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
  obtain ⟨L, hCL, hLN, hperf, hKL, hK3, heven, -⟩ := hD.exists_even
  have hCN : centralizer (E : Set G) ≤ normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  obtain ⟨-, hcent⟩ := centralizes_of_relIndex_three centralizer_le_ptsKer ptsKer_le_normalizer
    (fun n hn c hc => conj_mem_centralizer hn hc) (fun n hn k hk => conj_mem_ptsKer hn hk) hK3
    hLN hperf
  have hFL : F ≤ L := fun f hf => (heven f (hD.F_le_normalizer hf)).mpr
    (pointsAction_mem_alternatingGroup (M := A ⊓ normalizer (E : Set G)) inf_le_right hD.radical
      ⟨hD.F_le_A hf, hD.F_le_normalizer hf⟩)
  intro κ hκ
  have hle : rightConjugate F κ⁻¹ ≤ E ⊔ F := by
    intro x hx
    have hx' : κ⁻¹ * x * κ ∈ F := by
      have h := (mem_rightConjugate_iff F κ⁻¹ x).mp hx
      rwa [inv_inv] at h
    set f := κ⁻¹ * x * κ with hf
    have hc := hcent f (hFL hx') κ hκ
    have hxf : x = (f * κ * f⁻¹ * κ⁻¹)⁻¹ * f := by rw [hf]; group
    have hx2 : x * x = 1 := by
      have := (AS76b.isElemAbelian_rightConjugate hD.frame.elemF κ⁻¹).2 x hx
      rwa [sq] at this
    refine hD.mem_sup_of_mem ?_ hx2
    rw [hxf]
    exact mul_mem (mem_sup_left (inv_mem hc)) (mem_sup_right hx')
  rcases hD.frame.eq_or_eq_of_isElemAbelian hD.le hD.type hle
      (AS76b.isElemAbelian_rightConjugate hD.frame.elemF κ⁻¹)
      (by rw [rightConjugate_card, hD.frame.cardF]) with h | h
  · exfalso
    apply hD.frame.ne
    have h' := congrArg (fun X => rightConjugate X κ) h
    simp only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h'
    rw [h', (rightConjugate_eq_self_iff E κ).mpr (ptsKer_le_normalizer hκ)]
  · exact (normalizer (F : Set G)).inv_mem_iff.mp ((rightConjugate_eq_self_iff F _).mp h)

theorem exists_ne_one_R : ∃ r ∈ R, r ≠ 1 := by
  by_contra h
  push Not at h
  have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).mpr h
  have h4 := hD.frame.cardR
  rw [this, Subgroup.card_bot] at h4
  omega

theorem pointsAction_ne_one {u : G} (hu : u ∈ F) (huV : u ∉ E ⊓ F) :
    pointsAction R E ⟨u, hD.F_le_normalizer hu⟩ ≠ 1 := by
  intro h1
  obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one_R
  have hC := hD.fix u (mem_normalizer_of_pointsAction_eq_one h1) r hr hr1
    (by rw [hD.comm_R (hD.F_le_A hu) hr, mul_inv_cancel_right])
  rw [hD.centralizer_eq] at hC
  have hE2 : IsPGroup 2 E := hD.isPGroup_sup.to_le le_sup_left
  have hOE : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (E : Set G) :=
    hD.centralizer_eq ▸ le_sup_right
  exact huV ⟨mem_of_mem_sup_odd hE2 (AS76b.odd_card_oddCoreIn _) hOE hC (hD.sqF u hu), hu⟩

theorem exists_point : ∃ Q ∈ pointsIn R E, Q ⊓ (R ⊔ rightConjugate R g) = ⊥ ∧
    (R ⊔ rightConjugate R g) ⊔ Q = E ∧
    ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ ≠ 1 ∧ q₂ ≠ 1 ∧ q₁ ≠ q₂ ∧
      ∀ q ∈ Q, q = 1 ∨ q = q₁ ∨ q = q₂ ∨ q = q₁ * q₂ := by
  classical
  obtain ⟨Q, hQ, hQR, hQg⟩ : ∃ Q ∈ pointsIn R E, Q ≠ R ∧ Q ≠ rightConjugate R g := by
    by_contra h
    push Not at h
    have hsub : pointsIn R E ⊆ {R, rightConjugate R g} := fun Q hQ => by
      by_cases hQR : Q = R
      · exact Or.inl hQR
      · exact Or.inr (h Q hQ hQR)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, hD.six] at h1
    have h2 : ({R, rightConjugate R g} : Set (Subgroup G)).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    omega
  have hsep := hD.sep Q hQ hQR hQg
  have hV : R ⊔ rightConjugate R g = E ⊓ F := hD.frame.inf_eq.symm
  have hV16 : Nat.card ↥(R ⊔ rightConjugate R g) = 16 := by
    rw [hV]
    exact card_inf_of_frame hD.frame
  have hQ4 : Nat.card Q = 4 := by
    obtain ⟨-, x, rfl⟩ := hQ
    rw [rightConjugate_card, hD.frame.cardR]
  have hVE : R ⊔ rightConjugate R g ≤ E := hV ▸ inf_le_left
  have hdec : (R ⊔ rightConjugate R g) ⊔ Q = E :=
    sup_eq_of_inf_eq_bot hD.commE hVE hQ.1 (by rw [inf_comm]; exact hsep)
      (by rw [hD.frame.cardE, hV16, hQ4])
  have hsq : ∀ q ∈ Q, q * q = 1 := fun q hq => hD.sqE q (hQ.1 hq)
  obtain ⟨q₁, hq₁, hq₁1⟩ : ∃ q ∈ Q, q ≠ 1 := by
    by_contra h
    push Not at h
    have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).mpr h
    rw [this, Subgroup.card_bot] at hQ4
    omega
  have hQset : (Q : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hQ4
  obtain ⟨q₂, hq₂, hq₂1, hq₂q₁⟩ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ q₁ := by
    by_contra h
    push Not at h
    have hsub : (Q : Set G) ⊆ {1, q₁} := fun q hq => by
      by_cases hq1 : q = 1
      · exact Or.inl hq1
      · exact Or.inr (h q hq hq1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, q₁} : Set G).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    omega
  have h12a : q₁ * q₂ ≠ 1 := fun h => hq₂q₁ (by
    have h' := eq_inv_of_mul_eq_one_right h
    rwa [inv_eq_of_mul_eq_one_right (hsq q₁ hq₁)] at h')
  have h12b : q₁ * q₂ ≠ q₁ := fun h => hq₂1 (by simpa using h)
  have h12c : q₁ * q₂ ≠ q₂ := fun h => hq₁1 (by simpa using h)
  refine ⟨Q, hQ, hsep, hdec, q₁, hq₁, q₂, hq₂, hq₁1, hq₂1, Ne.symm hq₂q₁, fun q hq => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨hq1, hqa, hqb, hqab⟩ := h
  have hsub : ({1, q₁, q₂, q₁ * q₂, q} : Set G) ⊆ Q := by
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · exact Q.one_mem
    · exact hq₁
    · exact hq₂
    · exact Q.mul_mem hq₁ hq₂
    · exact hq
  have h5 : ({1, q₁, q₂, q₁ * q₂, q} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair (Ne.symm hqab)]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm h12c, Ne.symm hqb⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hq₂q₁, Ne.symm h12b, Ne.symm hqa⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hq₁1, Ne.symm hq₂1, Ne.symm h12a, Ne.symm hq1⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem pointsAction_mem_four (hD' : PlaneData G A R g F E) {Q : Subgroup G}
    (hdec : (R ⊔ rightConjugate R g) ⊔ Q = E) (hQE : Q ≤ E) {q₁ q₂ : G}
    (hQ : ∀ q ∈ Q, q = 1 ∨ q = q₁ ∨ q = q₂ ∨ q = q₁ * q₂) (hq₁ : q₁ ∈ E) (hq₂ : q₂ ∈ E)
    {e : G} (he : e ∈ E) :
    pointsAction R F ⟨e, hD'.F_le_normalizer he⟩ = 1 ∨
      pointsAction R F ⟨e, hD'.F_le_normalizer he⟩ =
        pointsAction R F ⟨q₁, hD'.F_le_normalizer hq₁⟩ ∨
      pointsAction R F ⟨e, hD'.F_le_normalizer he⟩ =
        pointsAction R F ⟨q₂, hD'.F_le_normalizer hq₂⟩ ∨
      pointsAction R F ⟨e, hD'.F_le_normalizer he⟩ =
        pointsAction R F ⟨q₁, hD'.F_le_normalizer hq₁⟩ *
          pointsAction R F ⟨q₂, hD'.F_le_normalizer hq₂⟩ := by
  have hVE : R ⊔ rightConjugate R g ≤ E := hdec ▸ le_sup_left
  have he' : e ∈ (R ⊔ rightConjugate R g) ⊔ Q := hdec.symm ▸ he
  obtain ⟨v, hv, u, hu, rfl⟩ := exists_mul_of_mem_sup hD.commE hVE hQE he'
  have hvF : v ∈ F := by
    have h := hD.frame.inf_eq
    exact (h ▸ hv : v ∈ E ⊓ F).2
  have hv1 : pointsAction R F ⟨v, hD'.F_le_normalizer (hVE hv)⟩ = 1 :=
    pointsAction_eq_one_of_mem_centralizer (mem_centralizer_iff.mpr fun f hf =>
      hD.commF f hf v hvF)
  have e1 : pointsAction R F ⟨v * u, hD'.F_le_normalizer he⟩ =
      pointsAction R F ⟨v, hD'.F_le_normalizer (hVE hv)⟩ *
        pointsAction R F ⟨u, hD'.F_le_normalizer (hQE hu)⟩ := by
    rw [← map_mul]
    rfl
  rw [e1, hv1, one_mul]
  rcases hQ u hu with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · right; right; right
    rw [← map_mul]
    rfl

end PlaneData

theorem mem_four_mul {M : Type*} [Group M] {a b x y : M} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (hx : x = 1 ∨ x = a ∨ x = b ∨ x = a * b)
    (hy : y = 1 ∨ y = a ∨ y = b ∨ y = a * b) :
    x * y = 1 ∨ x * y = a ∨ x * y = b ∨ x * y = a * b := by
  have ha' : ∀ z, a * (a * z) = z := fun z => by rw [← mul_assoc, ha, one_mul]
  have hba : b * a = a * b := hab.symm
  have hba' : ∀ z, b * (a * z) = a * (b * z) := fun z => by rw [← mul_assoc, hba, mul_assoc]
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [mul_assoc, ha, hb, ha', hba, hba', mul_one, one_mul, true_or, or_true]

end Cross

section Odd

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem PlaneData.mem_normalizer_other (hD : PlaneData G A R g E F) {n : G}
    (hn : n ∈ normalizer (E : Set G))
    (h : ∀ f (hf : f ∈ F), ∃ u, ∃ hu : u ∈ F, pointsAction R E ⟨u, hD.F_le_normalizer hu⟩ =
      pointsAction R E ⟨n * f * n⁻¹, mul_mem (mul_mem hn (hD.F_le_normalizer hf)) (inv_mem hn)⟩) :
    n ∈ normalizer (F : Set G) := by
  classical
  have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
  obtain ⟨L, hCL, hLN, hperf, hKL, hK3, heven, -⟩ := hD.exists_even
  obtain ⟨hpow, hcent⟩ := centralizes_of_relIndex_three centralizer_le_ptsKer
    ptsKer_le_normalizer (fun n hn c hc => conj_mem_centralizer hn hc)
    (fun n hn k hk => conj_mem_ptsKer hn hk) hK3 hLN hperf
  have hFL : F ≤ L := fun f hf => (heven f (hD.F_le_normalizer hf)).mpr
    (pointsAction_mem_alternatingGroup (M := A ⊓ normalizer (E : Set G)) inf_le_right hD.radical
      ⟨hD.F_le_A hf, hD.F_le_normalizer hf⟩)
  have hle : rightConjugate F n⁻¹ ≤ E ⊔ F := by
    intro x hx
    have hx' : n⁻¹ * x * n ∈ F := by
      have h := (mem_rightConjugate_iff F n⁻¹ x).mp hx
      rwa [inv_inv] at h
    have hxe : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    have hxN : x ∈ normalizer (E : Set G) := by
      have h' := mul_mem (mul_mem hn (hD.F_le_normalizer hx')) (inv_mem hn)
      rwa [hxe] at h'
    have hx2 : x * x = 1 := by
      have := (AS76b.isElemAbelian_rightConjugate hD.frame.elemF n⁻¹).2 x hx
      rwa [sq] at this
    obtain ⟨u, hu, hρu⟩ := h _ hx'
    have hρu' : pointsAction R E ⟨u, hD.F_le_normalizer hu⟩ = pointsAction R E ⟨x, hxN⟩ := by
      rw [hρu]
      congr 1
      exact Subtype.ext hxe
    have hκ : u⁻¹ * x ∈ ptsKer R E := by
      refine mem_ptsKer.mpr ⟨mul_mem (inv_mem (hD.F_le_normalizer hu)) hxN, ?_⟩
      have e : (⟨u⁻¹ * x, mul_mem (inv_mem (hD.F_le_normalizer hu)) hxN⟩ :
          ↥(normalizer (E : Set G))) = (⟨u, hD.F_le_normalizer hu⟩)⁻¹ * ⟨x, hxN⟩ := rfl
      rw [e, map_mul, map_inv, hρu', inv_mul_cancel]
    have hc := hcent u (hFL hu) (u⁻¹ * x) hκ
    have hu2 : u * u = 1 := hD.sqF u hu
    have hprod : (u * (u⁻¹ * x) * u⁻¹ * (u⁻¹ * x)⁻¹) * ((u⁻¹ * x) * (u⁻¹ * x)) = 1 := by
      calc _ = x * (u * u)⁻¹ * x := by group
        _ = 1 := by rw [hu2, inv_one, mul_one, hx2]
    have hκ2 : (u⁻¹ * x) * (u⁻¹ * x) ∈ centralizer (E : Set G) := by
      rw [eq_inv_of_mul_eq_one_right hprod]
      exact inv_mem hc
    have hκC : u⁻¹ * x ∈ centralizer (E : Set G) := by
      have h3 := hpow _ hκ
      generalize u⁻¹ * x = y at h3 hκ2 ⊢
      have e : y = y ^ 3 * (y * y)⁻¹ := by group
      rw [e]
      exact mul_mem h3 (inv_mem hκ2)
    refine hD.mem_sup_of_mem ?_ hx2
    rw [show x = u * (u⁻¹ * x) by group]
    exact mul_mem (mem_sup_right hu) (mem_sup_left hκC)
  rcases hD.frame.eq_or_eq_of_isElemAbelian hD.le hD.type hle
      (AS76b.isElemAbelian_rightConjugate hD.frame.elemF n⁻¹)
      (by rw [rightConjugate_card, hD.frame.cardF]) with h | h
  · exfalso
    apply hD.frame.ne
    have h' := congrArg (fun X => rightConjugate X n) h
    simp only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h'
    rw [h', (rightConjugate_eq_self_iff E n).mpr hn]
  · exact (normalizer (F : Set G)).inv_mem_iff.mp ((rightConjugate_eq_self_iff F _).mp h)

theorem PlaneData.mem_normalizer_of_four (hD : PlaneData G A R g E F) {f₁ f₂ : G}
    (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F)
    (hFfour : ∀ f (hf : f ∈ F), InFour (pointsAction R E ⟨f₁, hD.F_le_normalizer hf₁⟩)
      (pointsAction R E ⟨f₂, hD.F_le_normalizer hf₂⟩)
      (pointsAction R E ⟨f, hD.F_le_normalizer hf⟩))
    {n : G} (hn : n ∈ normalizer (E : Set G))
    (h₁ : InFour (pointsAction R E ⟨f₁, hD.F_le_normalizer hf₁⟩)
      (pointsAction R E ⟨f₂, hD.F_le_normalizer hf₂⟩)
      (pointsAction R E ⟨n, hn⟩ * pointsAction R E ⟨f₁, hD.F_le_normalizer hf₁⟩ *
        (pointsAction R E ⟨n, hn⟩)⁻¹))
    (h₂ : InFour (pointsAction R E ⟨f₁, hD.F_le_normalizer hf₁⟩)
      (pointsAction R E ⟨f₂, hD.F_le_normalizer hf₂⟩)
      (pointsAction R E ⟨n, hn⟩ * pointsAction R E ⟨f₂, hD.F_le_normalizer hf₂⟩ *
        (pointsAction R E ⟨n, hn⟩)⁻¹)) :
    n ∈ normalizer (F : Set G) := by
  set ρ := pointsAction R E with hρ
  set a := ρ ⟨f₁, hD.F_le_normalizer hf₁⟩ with ha
  set b := ρ ⟨f₂, hD.F_le_normalizer hf₂⟩ with hb
  set σ := ρ ⟨n, hn⟩ with hσ
  have hsq : ∀ f (hf : f ∈ F), ρ ⟨f, hD.F_le_normalizer hf⟩ * ρ ⟨f, hD.F_le_normalizer hf⟩ = 1 :=
    fun f hf => by
      have e1 : (⟨f, hD.F_le_normalizer hf⟩ : ↥(normalizer (E : Set G))) *
          ⟨f, hD.F_le_normalizer hf⟩ = 1 := Subtype.ext (hD.sqF f hf)
      rw [← map_mul, e1, map_one]
  have hcomm : a * b = b * a := by
    rw [ha, hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hD.commF f₁ hf₁ f₂ hf₂)
  have hσK : ∀ y, InFour a b y → InFour a b (σ * y * σ⁻¹) := by
    rintro y (rfl | rfl | rfl | rfl)
    · left; group
    · exact h₁
    · exact h₂
    · rw [show σ * (a * b) * σ⁻¹ = (σ * a * σ⁻¹) * (σ * b * σ⁻¹) by group]
      exact mem_four_mul (hsq f₁ hf₁) (hsq f₂ hf₂) hcomm h₁ h₂
  refine hD.mem_normalizer_other hn fun f hf => ?_
  have hρx : ρ ⟨n * f * n⁻¹, mul_mem (mul_mem hn (hD.F_le_normalizer hf)) (inv_mem hn)⟩ =
      σ * ρ ⟨f, hD.F_le_normalizer hf⟩ * σ⁻¹ := by
    rw [hσ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hxK := hσK _ (hFfour f hf)
  rw [← hρx] at hxK
  rcases hxK with h | h | h | h
  · exact ⟨1, F.one_mem, by rw [h]; exact map_one ρ⟩
  · exact ⟨f₁, hf₁, h.symm⟩
  · exact ⟨f₂, hf₂, h.symm⟩
  · refine ⟨f₁ * f₂, F.mul_mem hf₁ hf₂, ?_⟩
    rw [h, ha, hb, ← map_mul]
    rfl

theorem PlaneData.exists_four (hD : PlaneData G A R g E F) (hD' : PlaneData G A R g F E) :
    ∃ (q₁ q₂ κ : G) (hq₁ : q₁ ∈ E) (hq₂ : q₂ ∈ E) (hκ : κ ∈ ptsKer R E),
      κ ∉ centralizer (E : Set G) ∧
      FourData (⟨R, hD'.R_mem⟩ : ↥(pointsIn R F)) ⟨rightConjugate R g, hD'.Rg_mem⟩
        (pointsAction R F ⟨q₁, hD'.F_le_normalizer hq₁⟩)
        (pointsAction R F ⟨q₂, hD'.F_le_normalizer hq₂⟩)
        (pointsAction R F ⟨κ, hD.ptsKer_le_normalizer_other hκ⟩) ∧
      ∀ e (he : e ∈ E), InFour (pointsAction R F ⟨q₁, hD'.F_le_normalizer hq₁⟩)
        (pointsAction R F ⟨q₂, hD'.F_le_normalizer hq₂⟩)
        (pointsAction R F ⟨e, hD'.F_le_normalizer he⟩) := by
  classical
  have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
  obtain ⟨L, -, -, -, -, hK3, -, -⟩ := hD.exists_even
  obtain ⟨κ, hκ, hκC⟩ : ∃ κ ∈ ptsKer R E, κ ∉ centralizer (E : Set G) := by
    by_contra h
    push Not at h
    have h1 := Subgroup.relIndex_eq_one.mpr (show ptsKer R E ≤ centralizer (E : Set G) from h)
    omega
  have hκF := hD.ptsKer_le_normalizer_other hκ
  have hκE := ptsKer_le_normalizer hκ
  obtain ⟨Q, hQ, hsep, hdec, q₁, hq₁, q₂, hq₂, hq₁1, hq₂1, hq12, hQ4⟩ := hD.exists_point
  have hQE : Q ≤ E := hQ.1
  have hV : R ⊔ rightConjugate R g = E ⊓ F := hD.frame.inf_eq.symm
  set ρ := pointsAction R F with hρ
  have hEN : ∀ {e : G}, e ∈ E → e ∈ normalizer (F : Set G) := fun he => hD'.F_le_normalizer he
  have hne1 : ∀ u (hu : u ∈ Q), u ≠ 1 → ρ ⟨u, hEN (hQE hu)⟩ ≠ 1 := by
    intro u hu hu1
    refine hD'.pointsAction_ne_one (hQE hu) fun huV => hu1 ?_
    have h : u ∈ Q ⊓ (R ⊔ rightConjugate R g) := ⟨hu, by rw [hV, inf_comm]; exact huV⟩
    rwa [hsep, mem_bot] at h
  have hq₁N := hEN (hQE hq₁)
  have hq₂N := hEN (hQE hq₂)
  set a := ρ ⟨q₁, hq₁N⟩ with ha
  set b := ρ ⟨q₂, hq₂N⟩ with hb
  set c := ρ ⟨κ, hκF⟩ with hc
  set p₀ : ↥(pointsIn R F) := ⟨R, hD'.R_mem⟩
  set p₁ : ↥(pointsIn R F) := ⟨rightConjugate R g, hD'.Rg_mem⟩
  have hmul : ∀ {x y : G} (hx : x ∈ normalizer (F : Set G)) (hy : y ∈ normalizer (F : Set G)),
      ρ ⟨x * y, mul_mem hx hy⟩ = ρ ⟨x, hx⟩ * ρ ⟨y, hy⟩ := fun hx hy => by
    rw [← map_mul]
    rfl
  have hconj : ∀ {x y : G} (hx : x ∈ normalizer (F : Set G)) (hy : y ∈ normalizer (F : Set G)),
      ρ ⟨x, hx⟩ * ρ ⟨y, hy⟩ * (ρ ⟨x, hx⟩)⁻¹ =
        ρ ⟨x * y * x⁻¹, mul_mem (mul_mem hx hy) (inv_mem hx)⟩ := fun hx hy => by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hEfour : ∀ e (he : e ∈ E), InFour a b (ρ ⟨e, hEN he⟩) := fun e he =>
    hD.pointsAction_mem_four hD' hdec hQE hQ4 (hQE hq₁) (hQE hq₂) he
  have hfixR : ∀ e (he : e ∈ E), ρ ⟨e, hEN he⟩ p₀ = p₀ := fun e he =>
    pointsAction_apply_self _ hD'.R_mem (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun r hr => (hD.comm_R (hD.E_le_A he) hr).symm))
  have hfixRg : ∀ e (he : e ∈ E), ρ ⟨e, hEN he⟩ p₁ = p₁ := fun e he =>
    pointsAction_apply_self _ hD'.Rg_mem (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun r hr => hD.commE r (hD.Rg_le hr).1 e he))
  have hsq : ∀ e (he : e ∈ E), ρ ⟨e, hEN he⟩ * ρ ⟨e, hEN he⟩ = 1 := fun e he => by
    have e1 : (⟨e, hEN he⟩ : ↥(normalizer (F : Set G))) * ⟨e, hEN he⟩ = 1 :=
      Subtype.ext (hD.sqE e he)
    rw [← map_mul, e1, map_one]
  have hab : a ≠ b := by
    intro h
    have hu : q₁ * q₂⁻¹ ∈ Q := Q.mul_mem hq₁ (Q.inv_mem hq₂)
    refine hne1 _ hu (fun h' => hq12 (mul_inv_eq_one.mp h')) ?_
    have e : (⟨q₁ * q₂⁻¹, hEN (hQE hu)⟩ : ↥(normalizer (F : Set G))) =
        ⟨q₁, hq₁N⟩ * (⟨q₂, hq₂N⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, ← ha, ← hb, h, mul_inv_cancel]
  have hcomm : a * b = b * a := by
    rw [ha, hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hD.commE q₁ (hQE hq₁) q₂ (hQE hq₂))
  have hcfix : ∀ {u : G} (hu : u ∈ Q), u ≠ 1 →
      c * ρ ⟨u, hEN (hQE hu)⟩ * c⁻¹ ≠ ρ ⟨u, hEN (hQE hu)⟩ := by
    intro u hu hu1 h
    have hκu : κ * u * κ⁻¹ ∈ Q :=
      (mem_normalizer_iff.mp (mem_normalizer_of_mem_ptsKer hκ hQ) u).mp hu
    have hv : κ * u * κ⁻¹ * u⁻¹ ∈ Q := Q.mul_mem hκu (Q.inv_mem hu)
    refine hne1 _ hv (fun h' => hD.conj_ne_of_mem_ptsKer hκ hκC hQ hu hu1
      (mul_inv_eq_one.mp h')) ?_
    have e : (⟨κ * u * κ⁻¹ * u⁻¹, hEN (hQE hv)⟩ : ↥(normalizer (F : Set G))) =
        ⟨κ, hκF⟩ * ⟨u, hEN (hQE hu)⟩ * (⟨κ, hκF⟩)⁻¹ * (⟨u, hEN (hQE hu)⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc, h, mul_inv_cancel]
  have hc4 : ∀ {u : G} (hu : u ∈ E), InFour a b (c * ρ ⟨u, hEN hu⟩ * c⁻¹) := fun {u} hu => by
    rw [hc, hconj]
    exact hEfour _ ((mem_normalizer_iff.mp hκE u).mp hu)
  have hab' : a * b = ρ ⟨q₁ * q₂, hEN (hQE (Q.mul_mem hq₁ hq₂))⟩ := (hmul hq₁N hq₂N).symm
  refine ⟨q₁, q₂, κ, hQE hq₁, hQE hq₂, hκ, hκC, ⟨⟨hfixR q₁ (hQE hq₁), hfixRg q₁ (hQE hq₁),
    hsq q₁ (hQE hq₁), hne1 q₁ hq₁ hq₁1⟩, ⟨hfixR q₂ (hQE hq₂), hfixRg q₂ (hQE hq₂),
    hsq q₂ (hQE hq₂), hne1 q₂ hq₂ hq₂1, hab, hcomm⟩,
    ⟨pointsAction_apply_self _ hD'.R_mem (mem_normalizer_of_mem_ptsKer hκ hD.R_mem),
      pointsAction_apply_self _ hD'.Rg_mem (mem_normalizer_of_mem_ptsKer hκ hD.Rg_mem),
      hc4 (hQE hq₁), hc4 (hQE hq₂), hcfix hq₁ hq₁1, hcfix hq₂ hq₂1, by
        rw [hab']
        refine hcfix (Q.mul_mem hq₁ hq₂) fun h => hq12 ?_
        have h' := eq_inv_of_mul_eq_one_right h
        rwa [inv_eq_of_mul_eq_one_right (hD.sqE q₁ (hQE hq₁)), eq_comm] at h'⟩⟩, hEfour⟩

theorem PlaneData.exists_swap [Fintype ↥(pointsIn R E)] [DecidableEq ↥(pointsIn R E)]
    (hD : PlaneData G A R g E F) (hD' : PlaneData G A R g F E) :
    ∃ t, ∃ htE : t ∈ normalizer (E : Set G), t ∈ normalizer (F : Set G) ∧
      Equiv.Perm.sign (pointsAction R E ⟨t, htE⟩) = 1 ∧
      rightConjugate R t⁻¹ = rightConjugate R g ∧ rightConjugate (rightConjugate R g) t⁻¹ = R ∧
      ∀ κ ∈ ptsKer R E, t * κ * t⁻¹ * κ⁻¹ ∈ centralizer (E : Set G) := by
  classical
  obtain ⟨L, hCL, hLN, hperf, hKL, hK3, heven, halt⟩ := hD.exists_even
  obtain ⟨-, hcent⟩ := centralizes_of_relIndex_three centralizer_le_ptsKer
    ptsKer_le_normalizer (fun n hn c hc => conj_mem_centralizer hn hc)
    (fun n hn k hk => conj_mem_ptsKer hn hk) hK3 hLN hperf
  obtain ⟨f₁, f₂, κ', hf₁, hf₂, hκ', -, hF4, hFfour⟩ := hD'.exists_four hD
  set ρ := pointsAction R E with hρ
  set a := ρ ⟨f₁, hD.F_le_normalizer hf₁⟩ with ha
  set b := ρ ⟨f₂, hD.F_le_normalizer hf₂⟩ with hb
  set p₀ : ↥(pointsIn R E) := ⟨R, hD.R_mem⟩
  set p₁ : ↥(pointsIn R E) := ⟨rightConjugate R g, hD.Rg_mem⟩
  have hp01 : p₀ ≠ p₁ := fun h => hD.Rg_ne (congrArg Subtype.val h).symm
  obtain ⟨σ, hσ1, hσ0, hσ1', hσa, hσb⟩ := exists_swap_of_six hD.six hp01 hF4.ha hF4.hb
  obtain ⟨m, hm⟩ := halt (Equiv.Perm.mem_alternatingGroup.mpr hσ1)
  set t : G := (m : G) with ht
  have htE : t ∈ normalizer (E : Set G) := m.2
  have hρt : ρ ⟨t, htE⟩ = σ := hm
  have htL : t ∈ L := (heven t htE).mpr (by rw [hρt]; exact Equiv.Perm.mem_alternatingGroup.mpr hσ1)
  have htF : t ∈ normalizer (F : Set G) :=
    hD.mem_normalizer_of_four hf₁ hf₂ hFfour htE (by rw [hρt]; exact hσa) (by rw [hρt]; exact hσb)
  refine ⟨t, htE, htF, by rw [hρt]; exact hσ1, ?_, ?_, fun κ hκ => hcent t htL κ hκ⟩
  · exact (pointsAction_apply_eq htE hD.R_mem hD.Rg_mem).mp (by rw [hρt]; exact hσ0)
  · exact (pointsAction_apply_eq htE hD.Rg_mem hD.R_mem).mp (by rw [hρt]; exact hσ1')

variable [Fintype ↥(pointsIn R F)] [DecidableEq ↥(pointsIn R F)]

theorem PlaneData.exists_odd [Fintype ↥(pointsIn R E)] [DecidableEq ↥(pointsIn R E)]
    (hD : PlaneData G A R g E F) (hD' : PlaneData G A R g F E) :
    ∃ t, ∃ (htE : t ∈ normalizer (E : Set G)) (htF : t ∈ normalizer (F : Set G)),
      Equiv.Perm.sign (pointsAction R E ⟨t, htE⟩) = 1 ∧
        Equiv.Perm.sign (pointsAction R F ⟨t, htF⟩) = -1 := by
  classical
  obtain ⟨t, htE, htF, htev, htR, htRg, htcomm⟩ := hD.exists_swap hD'
  obtain ⟨q₁, q₂, κ, hq₁, hq₂, hκ, -, hF4, hEfour⟩ := hD.exists_four hD'
  set ρ := pointsAction R F with hρ
  have hEN : ∀ {e : G}, e ∈ E → e ∈ normalizer (F : Set G) := fun he => hD'.F_le_normalizer he
  have hκF := hD.ptsKer_le_normalizer_other hκ
  set a := ρ ⟨q₁, hEN hq₁⟩ with ha
  set b := ρ ⟨q₂, hEN hq₂⟩ with hb
  set c := ρ ⟨κ, hκF⟩ with hc
  set s := ρ ⟨t, htF⟩ with hs
  set p₀ : ↥(pointsIn R F) := ⟨R, hD'.R_mem⟩
  set p₁ : ↥(pointsIn R F) := ⟨rightConjugate R g, hD'.Rg_mem⟩
  have hp01 : p₀ ≠ p₁ := fun h => hD.Rg_ne (congrArg Subtype.val h).symm
  have hmul : ∀ {x y : G} (hx : x ∈ normalizer (F : Set G)) (hy : y ∈ normalizer (F : Set G)),
      ρ ⟨x * y, mul_mem hx hy⟩ = ρ ⟨x, hx⟩ * ρ ⟨y, hy⟩ := fun hx hy => by
    rw [← map_mul]
    rfl
  have hinv : ∀ {x : G} (hx : x ∈ normalizer (F : Set G)),
      ρ ⟨x⁻¹, inv_mem hx⟩ = (ρ ⟨x, hx⟩)⁻¹ := fun hx => by
    rw [← map_inv]
    rfl
  have hconj : ∀ {x y : G} (hx : x ∈ normalizer (F : Set G)) (hy : y ∈ normalizer (F : Set G)),
      ρ ⟨x, hx⟩ * ρ ⟨y, hy⟩ * (ρ ⟨x, hx⟩)⁻¹ =
        ρ ⟨x * y * x⁻¹, mul_mem (mul_mem hx hy) (inv_mem hx)⟩ := fun hx hy => by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hs4 : ∀ {u : G} (hu : u ∈ E), InFour a b (s * ρ ⟨u, hEN hu⟩ * s⁻¹) := fun {u} hu => by
    rw [hs, hconj]
    exact hEfour _ ((mem_normalizer_iff.mp htE u).mp hu)
  have hsc : InFour a b (s * c * s⁻¹ * c⁻¹) := by
    have hk := htcomm κ hκ
    rw [hD.centralizer_eq] at hk
    have hON : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ normalizer (E : Set G) := fun o ho =>
      Subgroup.centralizer_le_normalizer _ ((hD.centralizer_eq ▸ le_sup_right :
        AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (E : Set G)) ho)
    have hk' : t * κ * t⁻¹ * κ⁻¹ ∈ ((E ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) :
        Subgroup G) : Set G) := hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left E _ hON] at hk'
    obtain ⟨e, he, o, ho, heo⟩ := hk'
    have hoF : o ∈ centralizer (F : Set G) := (hD.centralizer_eq' ▸ le_sup_right :
      AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (F : Set G)) ho
    have hoN : o ∈ normalizer (F : Set G) := Subgroup.centralizer_le_normalizer _ hoF
    have h1 : s * c * s⁻¹ * c⁻¹ = ρ ⟨e, hEN he⟩ * ρ ⟨o, hoN⟩ := by
      rw [hs, hc, ← hinv, ← hinv, ← hmul, ← hmul, ← hmul, ← hmul]
      congr 1
      exact Subtype.ext heo.symm
    rw [h1, pointsAction_eq_one_of_mem_centralizer (c := ⟨o, hoN⟩) hoF, mul_one]
    exact hEfour e he
  have hsign := sign_eq_neg_one_of_six hD'.six hp01 hF4.ha hF4.hb hF4.hc
    ⟨(pointsAction_apply_eq htF hD'.R_mem hD'.Rg_mem).mpr htR,
      (pointsAction_apply_eq htF hD'.Rg_mem hD'.R_mem).mpr htRg, hs4 hq₁, hs4 hq₂, hsc⟩
  exact ⟨t, htE, htF, htev, hsign⟩

end Odd

section Main

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem PlaneData.surjective_pointsAction (hD : PlaneData G A R g E F)
    (hD' : PlaneData G A R g F E) : Function.Surjective (pointsAction R F) := by
  classical
  have : Fintype ↥(pointsIn R F) := Fintype.ofFinite _
  have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
  obtain ⟨t, -, ht, -, hsign⟩ := hD.exists_odd hD'
  obtain ⟨-, -, -, -, -, -, -, halt⟩ := hD'.exists_even
  intro σ
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact halt (Equiv.Perm.mem_alternatingGroup.mpr h)
  · have h' : σ * (pointsAction R F ⟨t, ht⟩)⁻¹ ∈ alternatingGroup ↥(pointsIn R F) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, h, hsign]
      rfl
    obtain ⟨m, hm⟩ := halt h'
    refine ⟨m * ⟨t, ht⟩, ?_⟩
    rw [map_mul, hm, inv_mul_cancel_right]

theorem PlaneData.inducesSym (hD : PlaneData G A R g E F) (hD' : PlaneData G A R g F E) :
    InducesSym (normalizer (F : Set G)) (pointsIn R F) := by
  intro σ
  obtain ⟨m, hm⟩ := hD.surjective_pointsAction hD' σ
  refine ⟨(m : G)⁻¹, inv_mem m.2, fun Q => ?_⟩
  rw [← hm, coe_pointsAction_apply]

end Main

end CFSG.ComponentClassification.AS81
