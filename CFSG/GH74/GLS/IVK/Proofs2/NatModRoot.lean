module

public import CFSG.GH74.GLS.IVK.Proofs2.NatModRootSL
public import CFSG.GH74.GLS.IVK.Proofs2.NatModGrp
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Matrix
open scoped commutatorElement

section Basic

variable {F : Type} [Field F] {V : Type} [AddCommGroup V]

private theorem End_inv_apply_self (ρ : SpecialLinearGroup (Fin 2) F →* AddMonoid.End V)
    (g : SpecialLinearGroup (Fin 2) F) (x : V) : ρ g⁻¹ (ρ g x) = x := by
  have h : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  simpa using congrArg (fun f : AddMonoid.End V => f x) h

end Basic

section Coordinates

variable {F : Type} [Field F] {V : Type} [AddCommGroup V]

private theorem upperSL_mulVec_zero (c : F) (v : Fin 2 → F) :
    ((upperSL c : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v 0 =
      v 0 + c * v 1 := by
  simp [coe_upperSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem upperSL_mulVec_one (c : F) (v : Fin 2 → F) :
    ((upperSL c : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v 1 = v 1 := by
  simp [coe_upperSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem lowerSL_mulVec_zero (c : F) (v : Fin 2 → F) :
    ((lowerSL c : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v 0 = v 0 := by
  simp [coe_lowerSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem lowerSL_mulVec_one (c : F) (v : Fin 2 → F) :
    ((lowerSL c : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v 1 =
      v 1 + c * v 0 := by
  simp [coe_lowerSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm]

private def coordMap (Φ₁ Φ₂ : F →+ V) : (Fin 2 → F) →+ V where
  toFun v := Φ₁ (v 0) + Φ₂ (v 1)
  map_zero' := by simp
  map_add' v w := by
    simp only [Pi.add_apply, map_add]
    abel

private theorem coordMap_apply (Φ₁ Φ₂ : F →+ V) (v : Fin 2 → F) :
    coordMap Φ₁ Φ₂ v = Φ₁ (v 0) + Φ₂ (v 1) := rfl

private def equivSubgroup (ρ : SpecialLinearGroup (Fin 2) F →* AddMonoid.End V)
    (Φ : (Fin 2 → F) →+ V) : Subgroup (SpecialLinearGroup (Fin 2) F) where
  carrier := {g | ∀ v, Φ ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) = ρ g (Φ v)}
  mul_mem' := by
    intro a b ha hb v
    have ha' : ∀ v, Φ ((a : Matrix (Fin 2) (Fin 2) F).mulVec v) = ρ a (Φ v) := ha
    have hb' : ∀ v, Φ ((b : Matrix (Fin 2) (Fin 2) F).mulVec v) = ρ b (Φ v) := hb
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ha', hb', map_mul]
    rfl
  one_mem' := by
    intro v
    simp
  inv_mem' := by
    intro g hg v
    have hg' : ∀ v, Φ ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) = ρ g (Φ v) := hg
    have h := hg' (((g⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v)
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h
    calc Φ (((g⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v)
        = ρ g⁻¹ (ρ g (Φ (((g⁻¹ : SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F).mulVec v))) :=
          (End_inv_apply_self ρ g _).symm
      _ = ρ g⁻¹ (Φ v) := by rw [← h]

private theorem mem_equivSubgroup {ρ : SpecialLinearGroup (Fin 2) F →* AddMonoid.End V}
    {Φ : (Fin 2 → F) →+ V} {g : SpecialLinearGroup (Fin 2) F} :
    g ∈ equivSubgroup ρ Φ ↔ ∀ v, Φ ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) = ρ g (Φ v) :=
  Iff.rfl

private theorem exists_equivariant_of_coordinates
    (ρ : SpecialLinearGroup (Fin 2) F →* AddMonoid.End V)
    (A A' : AddSubgroup V) (hinf : A ⊓ A' = ⊥) (Φ₁ Φ₂ : F →+ V)
    (hinj₁ : Function.Injective Φ₁) (hinj₂ : Function.Injective Φ₂)
    (hmem₁ : ∀ s, Φ₁ s ∈ A) (hmem₂ : ∀ t, Φ₂ t ∈ A')
    (hsurj₁ : ∀ a ∈ A, ∃ s, Φ₁ s = a) (hsurj₂ : ∀ a ∈ A', ∃ t, Φ₂ t = a)
    (hup₁ : ∀ c s, ρ (upperSL c) (Φ₁ s) = Φ₁ s)
    (hup₂ : ∀ c t, ρ (upperSL c) (Φ₂ t) = Φ₂ t + Φ₁ (c * t))
    (hlow₁ : ∀ d s, ρ (lowerSL d) (Φ₁ s) = Φ₁ s + Φ₂ (d * s))
    (hlow₂ : ∀ d t, ρ (lowerSL d) (Φ₂ t) = Φ₂ t) :
    ∃ Φ : (Fin 2 → F) →+ V, Function.Injective Φ ∧
      (∀ (g : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
        Φ ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) = ρ g (Φ v)) ∧
      Φ.range = A ⊔ A' := by
  refine ⟨coordMap Φ₁ Φ₂, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    rw [coordMap_apply] at hv
    have h1 : Φ₁ (v 0) = 0 := by
      have hmem : Φ₁ (v 0) ∈ A ⊓ A' := by
        refine ⟨hmem₁ _, ?_⟩
        have : Φ₁ (v 0) = -Φ₂ (v 1) := eq_neg_of_add_eq_zero_left hv
        rw [this]
        exact A'.neg_mem (hmem₂ _)
      rw [hinf] at hmem
      exact AddSubgroup.mem_bot.mp hmem
    have h2 : Φ₂ (v 1) = 0 := by
      rw [h1, zero_add] at hv
      exact hv
    ext i
    fin_cases i
    · exact hinj₁ (h1.trans (map_zero Φ₁).symm)
    · exact hinj₂ (h2.trans (map_zero Φ₂).symm)
  · have hup : Qup F ≤ equivSubgroup ρ (coordMap Φ₁ Φ₂) := by
      intro g hg
      obtain ⟨c, rfl⟩ := mem_Qup.1 hg
      intro v
      rw [coordMap_apply, coordMap_apply, upperSL_mulVec_zero, upperSL_mulVec_one, map_add,
        map_add, hup₁, hup₂]
      abel
    have hlow : Qlow F ≤ equivSubgroup ρ (coordMap Φ₁ Φ₂) := by
      intro g hg
      obtain ⟨d, rfl⟩ := mem_Qlow.1 hg
      intro v
      rw [coordMap_apply, coordMap_apply, lowerSL_mulVec_zero, lowerSL_mulVec_one, map_add,
        map_add, hlow₁, hlow₂]
      abel
    have htop : equivSubgroup ρ (coordMap Φ₁ Φ₂) = ⊤ := by
      rw [eq_top_iff, ← Qup_sup_Qlow (F := F)]
      exact sup_le hup hlow
    intro g v
    exact mem_equivSubgroup.1 (htop ▸ Subgroup.mem_top g) v
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [coordMap_apply]
      exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (hmem₁ _))
        (AddSubgroup.mem_sup_right (hmem₂ _))
    · intro x hx
      obtain ⟨a, ha, a', ha', rfl⟩ := AddSubgroup.mem_sup.mp hx
      obtain ⟨s, rfl⟩ := hsurj₁ a ha
      obtain ⟨t, rfl⟩ := hsurj₂ a' ha'
      exact ⟨![s, t], by simp [coordMap_apply]⟩

end Coordinates

section Semidirect

variable {F : Type} [Field F] {V : Type} [AddCommGroup V]

private def actMulAut (ρ : SpecialLinearGroup (Fin 2) F →* AddMonoid.End V) :
    SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative V) where
  toFun g :=
    { toFun := fun x => Multiplicative.ofAdd (ρ g (Multiplicative.toAdd x))
      invFun := fun x => Multiplicative.ofAdd (ρ g⁻¹ (Multiplicative.toAdd x))
      left_inv := fun x => by
        simp [End_inv_apply_self]
      right_inv := fun x => by
        have h := End_inv_apply_self ρ g⁻¹ (Multiplicative.toAdd x)
        rw [inv_inv] at h
        show Multiplicative.ofAdd (ρ g (ρ g⁻¹ (Multiplicative.toAdd x))) = x
        rw [h]
        rfl
      map_mul' := fun x y => by simp }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

variable (ρ : SpecialLinearGroup (Fin 2) F →* AddMonoid.End V)

private abbrev SemiG : Type :=
  SemidirectProduct (Multiplicative V) (SpecialLinearGroup (Fin 2) F) (actMulAut ρ)

private def ιV (a : V) : SemiG ρ := SemidirectProduct.inl (Multiplicative.ofAdd a)

private def πG : SpecialLinearGroup (Fin 2) F →* SemiG ρ := SemidirectProduct.inr

private theorem ιV_add (a b : V) : ιV ρ (a + b) = ιV ρ a * ιV ρ b := by
  unfold ιV
  rw [ofAdd_add, map_mul]

private theorem ιV_zero : ιV ρ 0 = 1 := by
  unfold ιV
  rw [ofAdd_zero, map_one]

private theorem ιV_neg (a : V) : ιV ρ (-a) = (ιV ρ a)⁻¹ := by
  unfold ιV
  rw [ofAdd_neg, map_inv]

private theorem ιV_injective : Function.Injective (ιV ρ) := by
  intro a b h
  exact Multiplicative.ofAdd.injective (SemidirectProduct.inl_injective h)

private theorem conj_ιV (g : SpecialLinearGroup (Fin 2) F) (a : V) :
    πG ρ g * ιV ρ a * (πG ρ g)⁻¹ = ιV ρ (ρ g a) := by
  unfold πG ιV
  rw [← map_inv]
  exact (SemidirectProduct.inl_aut (φ := actMulAut ρ) g (Multiplicative.ofAdd a)).symm

private theorem comm_ιV (g : SpecialLinearGroup (Fin 2) F) (a : V) :
    ⁅πG ρ g, ιV ρ a⁆ = ιV ρ (ρ g a - a) := by
  rw [commutatorElement_def, conj_ιV, sub_eq_add_neg, ιV_add, ιV_neg]

private def subgroupOf (B : AddSubgroup V) : Subgroup (SemiG ρ) where
  carrier := {x | ∃ a ∈ B, ιV ρ a = x}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, B.add_mem ha hb, ιV_add ρ a b⟩
  one_mem' := ⟨0, B.zero_mem, ιV_zero ρ⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, B.neg_mem ha, ιV_neg ρ a⟩

private theorem card_subgroupOf (B : AddSubgroup V) :
    Nat.card (subgroupOf ρ B) = Nat.card B := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun a : B => (⟨ιV ρ a, a, a.2, rfl⟩ : subgroupOf ρ B))
    ⟨fun a b h => Subtype.ext (ιV_injective ρ (congrArg Subtype.val h)), fun x => ?_⟩)
  obtain ⟨a, ha, h⟩ := x.2
  exact ⟨⟨a, ha⟩, Subtype.ext h⟩

private theorem isRootModuleSL_subgroupOf (A A' : AddSubgroup V)
    (hA : ∀ v, v ∈ A ↔ ∀ c : F, ρ (upperSL c) v = v)
    (hA' : ∀ v, v ∈ A' ↔ ∀ d : F, ρ (lowerSL d) v = v)
    (hcardA : Nat.card A = Nat.card F) (hcardA' : Nat.card A' = Nat.card F)
    (hinf : A ⊓ A' = ⊥)
    (hxA : ∀ (c : F), ∀ v ∈ A', ρ (upperSL c) v - v ∈ A)
    (hyA' : ∀ (d : F), ∀ v ∈ A, ρ (lowerSL d) v - v ∈ A') :
    IsRootModuleSL (πG ρ) (subgroupOf ρ A) (subgroupOf ρ A') where
  comm₁ := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    rw [← ιV_add, ← ιV_add, add_comm]
  comm₂ := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    rw [← ιV_add, ← ιV_add, add_comm]
  comm₁₂ := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    rw [← ιV_add, ← ιV_add, add_comm]
  inter := by
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    have hb' : b = a := ιV_injective ρ hba
    subst hb'
    have hmem : b ∈ A ⊓ A' := ⟨ha, hb⟩
    rw [hinf, AddSubgroup.mem_bot] at hmem
    rw [hmem, ιV_zero]
  card₁ := (card_subgroupOf ρ A).trans hcardA
  card₂ := (card_subgroupOf ρ A').trans hcardA'
  up₁ := by
    rintro c _ ⟨a, ha, rfl⟩
    have h := conj_ιV ρ (upperSL c) a
    rw [(hA a).1 ha c] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  up₂ := by
    rintro c _ ⟨a, ha, rfl⟩
    rw [comm_ιV]
    exact ⟨_, hxA c a ha, rfl⟩
  low₂ := by
    rintro c _ ⟨a, ha, rfl⟩
    have h := conj_ιV ρ (lowerSL c) a
    rw [(hA' a).1 ha c] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  low₁ := by
    rintro c _ ⟨a, ha, rfl⟩
    rw [comm_ιV]
    exact ⟨_, hyA' c a ha, rfl⟩
  nondeg := by
    rintro _ ⟨a, ha, rfl⟩ h
    have haA : a ∈ A := by
      rw [hA]
      intro c
      have h1 := conj_ιV ρ (upperSL c) a
      rw [mul_inv_eq_iff_eq_mul.2 (h c)] at h1
      exact (ιV_injective ρ h1).symm
    have hmem : a ∈ A ⊓ A' := ⟨haA, ha⟩
    rw [hinf, AddSubgroup.mem_bot] at hmem
    rw [hmem, ιV_zero]

private def valV (x : SemiG ρ) : V := Multiplicative.toAdd x.left

private theorem valV_mem {B : AddSubgroup V} {x : SemiG ρ} (hx : x ∈ subgroupOf ρ B) :
    valV ρ x ∈ B ∧ ιV ρ (valV ρ x) = x := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨ha, rfl⟩

private theorem valV_mul {B C : AddSubgroup V} {x y : SemiG ρ} (hx : x ∈ subgroupOf ρ B)
    (hy : y ∈ subgroupOf ρ C) : valV ρ (x * y) = valV ρ x + valV ρ y := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [← ιV_add]
  rfl

private theorem exists_coordinates [Finite F] (A A' : AddSubgroup V)
    (hA : ∀ v, v ∈ A ↔ ∀ c : F, ρ (upperSL c) v = v)
    (hA' : ∀ v, v ∈ A' ↔ ∀ d : F, ρ (lowerSL d) v = v)
    (hcardA : Nat.card A = Nat.card F) (hcardA' : Nat.card A' = Nat.card F)
    (hinf : A ⊓ A' = ⊥)
    (hxA : ∀ (c : F), ∀ v ∈ A', ρ (upperSL c) v - v ∈ A)
    (hyA' : ∀ (d : F), ∀ v ∈ A, ρ (lowerSL d) v - v ∈ A') :
    ∃ Φ₁ Φ₂ : F →+ V, Function.Injective Φ₁ ∧ Function.Injective Φ₂ ∧
      (∀ s, Φ₁ s ∈ A) ∧ (∀ t, Φ₂ t ∈ A') ∧
      (∀ a ∈ A, ∃ s, Φ₁ s = a) ∧ (∀ a ∈ A', ∃ t, Φ₂ t = a) ∧
      (∀ c t, ρ (upperSL c) (Φ₂ t) = Φ₂ t + Φ₁ (c * t)) ∧
      (∀ d s, ρ (lowerSL d) (Φ₁ s) = Φ₁ s + Φ₂ (d * s)) := by
  have hV := isRootModuleSL_subgroupOf ρ A A' hA hA' hcardA hcardA' hinf hxA hyA'
  have hF : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨a₀, ha₀, ha₀ne⟩ : ∃ a ∈ A, a ≠ 0 := by
    by_contra hcon
    have hbot : A = ⊥ := (AddSubgroup.eq_bot_iff_forall A).2 fun a ha => by
      by_contra hne
      exact hcon ⟨a, ha, hne⟩
    have := (AddSubgroup.eq_bot_iff_card A).1 hbot
    omega
  let e : subgroupOf ρ A := ⟨ιV ρ a₀, a₀, ha₀, rfl⟩
  have he : e ≠ 1 := by
    intro h
    apply ha₀ne
    apply ιV_injective ρ
    rw [ιV_zero]
    exact congrArg Subtype.val h
  obtain ⟨Φ₁, hΦ₁⟩ : ∃ Φ₁ : F →+ V, ∀ s, Φ₁ s = valV ρ (hV.xi₁ e s : SemiG ρ) :=
    ⟨AddMonoidHom.mk' (fun s => valV ρ (hV.xi₁ e s : SemiG ρ)) (fun s t => by
      rw [hV.xi₁_add, Subgroup.coe_mul]
      exact valV_mul ρ (hV.xi₁ e s).2 (hV.xi₁ e t).2), fun s => rfl⟩
  obtain ⟨Φ₂, hΦ₂⟩ : ∃ Φ₂ : F →+ V, ∀ t, Φ₂ t = valV ρ (hV.xi₂ e t : SemiG ρ) :=
    ⟨AddMonoidHom.mk' (fun t => valV ρ (hV.xi₂ e t : SemiG ρ)) (fun s t => by
      rw [hV.xi₂_add, Subgroup.coe_mul]
      exact valV_mul ρ (hV.xi₂ e s).2 (hV.xi₂ e t).2), fun s => rfl⟩
  have hmem₁ : ∀ s, Φ₁ s ∈ A := fun s => by
    rw [hΦ₁]
    exact (valV_mem ρ (hV.xi₁ e s).2).1
  have hmem₂ : ∀ t, Φ₂ t ∈ A' := fun t => by
    rw [hΦ₂]
    exact (valV_mem ρ (hV.xi₂ e t).2).1
  have hι₁ : ∀ s, ιV ρ (Φ₁ s) = (hV.xi₁ e s : SemiG ρ) := fun s => by
    rw [hΦ₁]
    exact (valV_mem ρ (hV.xi₁ e s).2).2
  have hι₂ : ∀ t, ιV ρ (Φ₂ t) = (hV.xi₂ e t : SemiG ρ) := fun t => by
    rw [hΦ₂]
    exact (valV_mem ρ (hV.xi₂ e t).2).2
  refine ⟨Φ₁, Φ₂, ?_, ?_, hmem₁, hmem₂, ?_, ?_, ?_, ?_⟩
  · intro s t h
    apply hV.xi₁_injective e he
    apply Subtype.ext
    rw [← hι₁, ← hι₁, h]
  · intro s t h
    apply (hV.xi₂_bijective e he).1
    apply Subtype.ext
    rw [← hι₂, ← hι₂, h]
  · intro a ha
    obtain ⟨s, hs⟩ := (hV.xi₁_bijective e he).2 ⟨ιV ρ a, a, ha, rfl⟩
    refine ⟨s, ?_⟩
    rw [hΦ₁, hs]
    rfl
  · intro a ha
    obtain ⟨t, ht⟩ := (hV.xi₂_bijective e he).2 ⟨ιV ρ a, a, ha, rfl⟩
    refine ⟨t, ?_⟩
    rw [hΦ₂, ht]
    rfl
  · intro c t
    have h := hV.comm_up e c t
    rw [← hι₂, comm_ιV, ← hι₁] at h
    have h2 := ιV_injective ρ h
    rw [sub_eq_iff_eq_add'] at h2
    exact h2
  · intro d s
    have h := hV.comm_low e s d
    rw [← hι₁, comm_ιV, ← hι₂] at h
    have h2 := ιV_injective ρ h
    rw [sub_eq_iff_eq_add'] at h2
    exact h2

end Semidirect

theorem exists_equivariant_injection_of_quadratic
    {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) F →* AddMonoid.End V)
    (A A' : AddSubgroup V)
    (hA : ∀ v, v ∈ A ↔ ∀ c : F, ρ (upperSL c) v = v)
    (hA' : ∀ v, v ∈ A' ↔ ∀ d : F, ρ (lowerSL d) v = v)
    (hcardA : Nat.card A = Nat.card F) (hcardA' : Nat.card A' = Nat.card F)
    (hinf : A ⊓ A' = ⊥)
    (hxA : ∀ (c : F), ∀ v ∈ A', ρ (upperSL c) v - v ∈ A)
    (hyA' : ∀ (d : F), ∀ v ∈ A, ρ (lowerSL d) v - v ∈ A') :
    ∃ Φ : (Fin 2 → F) →+ V, Function.Injective Φ ∧
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
        Φ ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) = ρ g (Φ v)) ∧
      Φ.range = A ⊔ A' := by
  obtain ⟨Φ₁, Φ₂, hinj₁, hinj₂, hmem₁, hmem₂, hsurj₁, hsurj₂, hup₂, hlow₁⟩ :=
    exists_coordinates ρ A A' hA hA' hcardA hcardA' hinf hxA hyA'
  exact exists_equivariant_of_coordinates ρ A A' hinf Φ₁ Φ₂ hinj₁ hinj₂ hmem₁ hmem₂ hsurj₁ hsurj₂
    (fun c s => (hA _).1 (hmem₁ s) c) hup₂ hlow₁ (fun d t => (hA' _).1 (hmem₂ t) d)

theorem exists_equivariant_injection_of_quadratic_representation
    {F : Type} [Field F] [Finite F] {k : Type*} [CommSemiring k] {V : Type} [AddCommGroup V]
    [Module k V] (ρ : Representation k (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (A A' : AddSubgroup V)
    (hA : ∀ v, v ∈ A ↔ ∀ c : F, ρ (upperSL c) v = v)
    (hA' : ∀ v, v ∈ A' ↔ ∀ d : F, ρ (lowerSL d) v = v)
    (hcardA : Nat.card A = Nat.card F) (hcardA' : Nat.card A' = Nat.card F)
    (hinf : A ⊓ A' = ⊥)
    (hxA : ∀ (c : F), ∀ v ∈ A', ρ (upperSL c) v - v ∈ A)
    (hyA' : ∀ (d : F), ∀ v ∈ A, ρ (lowerSL d) v - v ∈ A') :
    ∃ Φ : (Fin 2 → F) →+ V, Function.Injective Φ ∧
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
        Φ ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) = ρ g (Φ v)) ∧
      Φ.range = A ⊔ A' := by
  let ρ' : Matrix.SpecialLinearGroup (Fin 2) F →* AddMonoid.End V :=
    { toFun := fun g => (ρ g).toAddMonoidHom
      map_one' := by
        ext x
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        ext x
        rw [map_mul]
        rfl }
  exact exists_equivariant_injection_of_quadratic ρ' A A' hA hA' hcardA hcardA' hinf hxA hyA'

end CFSG.GH74.GLS.IVK.Proofs2
