module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup

section Quot

variable {V : Type*} [CommGroup V] (Z : Subgroup V)

@[expose] def cls (v : V) : Additive (V ⧸ Z) := Additive.ofMul (QuotientGroup.mk v)

theorem cls_mul (a b : V) : cls Z (a * b) = cls Z a + cls Z b := rfl
theorem cls_one : cls Z (1 : V) = 0 := rfl
theorem cls_inv (a : V) : cls Z a⁻¹ = - cls Z a := rfl
theorem cls_surjective : Function.Surjective (cls Z) := fun q =>
  by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    exact ⟨v, by simp [cls, hv]⟩
theorem cls_eq_zero_iff (v : V) : cls Z v = 0 ↔ v ∈ Z := QuotientGroup.eq_one_iff v

theorem cls_eq_iff (a b : V) : cls Z a = cls Z b ↔ a⁻¹ * b ∈ Z := by
  unfold cls
  rw [Additive.ofMul.apply_eq_iff_eq]
  exact QuotientGroup.eq

instance quotModule [h : Fact (∀ a : V, a * a = 1)] : Module (ZMod 2) (Additive (V ⧸ Z)) :=
  AddCommGroup.zmodModule (fun q => by
    obtain ⟨v, rfl⟩ := cls_surjective Z q
    rw [two_nsmul, ← cls_mul, cls_eq_zero_iff, h.out v]
    exact one_mem _)

@[expose] def liftAdd (U : AddSubgroup (Additive (V ⧸ Z))) : Subgroup V where
  carrier := {v | cls Z v ∈ U}
  mul_mem' := fun {a b} ha hb => by
    show cls Z (a * b) ∈ U
    rw [cls_mul]; exact U.add_mem ha hb
  one_mem' := by
    show cls Z 1 ∈ U
    rw [cls_one]; exact U.zero_mem
  inv_mem' := fun {a} ha => by
    show cls Z a⁻¹ ∈ U
    rw [cls_inv]; exact U.neg_mem ha

theorem mem_liftAdd {U : AddSubgroup (Additive (V ⧸ Z))} {v : V} :
    v ∈ liftAdd Z U ↔ cls Z v ∈ U := Iff.rfl

theorem le_liftAdd (U : AddSubgroup (Additive (V ⧸ Z))) : Z ≤ liftAdd Z U := fun z hz => by
  rw [mem_liftAdd, (cls_eq_zero_iff Z z).2 hz]; exact U.zero_mem

theorem liftAdd_le_iff {U U' : AddSubgroup (Additive (V ⧸ Z))} :
    liftAdd Z U ≤ liftAdd Z U' ↔ U ≤ U' := by
  constructor
  · intro h q hq
    obtain ⟨v, rfl⟩ := cls_surjective Z q
    exact h hq
  · intro h v hv
    exact h hv

theorem liftAdd_bot : liftAdd Z (⊥ : AddSubgroup (Additive (V ⧸ Z))) = Z := by
  ext v
  rw [mem_liftAdd, AddSubgroup.mem_bot, cls_eq_zero_iff]

theorem liftAdd_top : liftAdd Z (⊤ : AddSubgroup (Additive (V ⧸ Z))) = ⊤ := by
  ext v
  simp [mem_liftAdd]

theorem liftAdd_inf (U U' : AddSubgroup (Additive (V ⧸ Z))) :
    liftAdd Z (U ⊓ U') = liftAdd Z U ⊓ liftAdd Z U' := by
  ext v
  simp [mem_liftAdd]

theorem liftAdd_sup (U U' : AddSubgroup (Additive (V ⧸ Z))) :
    liftAdd Z (U ⊔ U') = liftAdd Z U ⊔ liftAdd Z U' := by
  apply le_antisymm
  · intro v hv
    rw [mem_liftAdd, AddSubgroup.mem_sup] at hv
    obtain ⟨a, ha, b, hb, hab⟩ := hv
    obtain ⟨a', rfl⟩ := cls_surjective Z a
    obtain ⟨b', rfl⟩ := cls_surjective Z b
    have h1 : cls Z (a' * b') = cls Z v := by rw [cls_mul, hab]
    rw [cls_eq_iff] at h1
    have h2 : v = a' * b' * ((a' * b')⁻¹ * v) := by group
    rw [h2]
    exact mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right hb))
      (mem_sup_left (le_liftAdd Z U h1))
  · exact sup_le (liftAdd_le_iff Z |>.2 le_sup_left) (liftAdd_le_iff Z |>.2 le_sup_right)

theorem exists_eq_liftAdd (A : Subgroup V) (hA : Z ≤ A) :
    ∃ U : AddSubgroup (Additive (V ⧸ Z)), liftAdd Z U = A := by
  refine ⟨{ carrier := {q | ∃ v ∈ A, cls Z v = q}
            add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, ?_⟩
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, cls_mul Z a b⟩
  · exact ⟨1, one_mem _, cls_one Z⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, inv_mem ha, cls_inv Z a⟩
  · ext v
    simp only [mem_liftAdd, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, ha, hav⟩
      rw [cls_eq_iff] at hav
      have : v = a * (a⁻¹ * v) := by group
      rw [this]
      exact mul_mem ha (hA hav)
    · intro hv
      exact ⟨v, hv, rfl⟩

theorem card_quot_mul_card [Finite V] :
    Nat.card (Additive (V ⧸ Z)) * Nat.card Z = Nat.card V := by
  have h := Subgroup.card_mul_index Z
  rw [mul_comm, Subgroup.index] at h
  rw [← h]
  congr 1

theorem card_liftAdd [Finite V] (U : AddSubgroup (Additive (V ⧸ Z))) :
    Nat.card (liftAdd Z U) = Nat.card Z * Nat.card U := by
  let K := liftAdd Z U
  let ψ : K →* V ⧸ Z := (QuotientGroup.mk' Z).comp K.subtype
  have hker : ψ.ker = Z.subgroupOf K := by
    ext k
    simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      Subgroup.coe_subtype, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have h1 : Nat.card ψ.ker = Nat.card Z := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_liftAdd Z U)).toEquiv
  have h2 : Nat.card ψ.range = Nat.card U := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun q => ⟨Additive.ofMul q.1, ?_⟩
        invFun := fun u => ⟨Additive.toMul u.1, ?_⟩
        left_inv := fun q => rfl
        right_inv := fun u => rfl }
    · obtain ⟨⟨k, hk⟩, hq⟩ := q.2
      have : cls Z k = Additive.ofMul q.1 := by
        rw [← hq]; rfl
      rw [← this]; exact hk
    · obtain ⟨v, hv⟩ := cls_surjective Z u.1
      refine ⟨⟨v, ?_⟩, ?_⟩
      · show cls Z v ∈ U
        rw [hv]; exact u.2
      · show QuotientGroup.mk v = Additive.toMul u.1
        have : Additive.ofMul (QuotientGroup.mk v : V ⧸ Z) = u.1 := hv
        rw [← this]; rfl
  have h3 := Subgroup.card_ker_mul_card_range ψ
  rw [h1, h2] at h3
  exact h3.symm

end Quot

section Action

variable {V : Type*} [CommGroup V] (Z : Subgroup V)

@[expose] def addEquivLin {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (e : M ≃+ M) :
    M ≃ₗ[ZMod 2] M :=
  { e with map_smul' := fun c x => ZMod.map_smul e c x }

@[simp] theorem addEquivLin_apply {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (e : M ≃+ M)
    (x : M) : addEquivLin e x = e x := rfl

@[expose] def quotAut (σ : MulAut V) (hσ : Z.map (σ : V →* V) = Z) :
    Additive (V ⧸ Z) ≃+ Additive (V ⧸ Z) :=
  MulEquiv.toAdditive (QuotientGroup.congr Z Z σ hσ)

theorem quotAut_cls (σ : MulAut V) (hσ : Z.map (σ : V →* V) = Z) (v : V) :
    quotAut Z σ hσ (cls Z v) = cls Z (σ v) := by
  unfold quotAut cls
  exact congrArg Additive.ofMul (QuotientGroup.congr_mk Z Z σ hσ v)

@[expose] noncomputable def quotRep [Fact (∀ a : V, a * a = 1)] (B : Subgroup (MulAut V))
    (hB : ∀ σ ∈ B, Z.map (σ : V →* V) = Z) :
    ↥B →* (Additive (V ⧸ Z) ≃ₗ[ZMod 2] Additive (V ⧸ Z)) where
  toFun σ := addEquivLin (quotAut Z σ (hB σ σ.2))
  map_one' := by
    refine LinearEquiv.ext fun q => ?_
    obtain ⟨v, rfl⟩ := cls_surjective Z q
    exact quotAut_cls Z ((1 : ↥B) : MulAut V) (hB _ (1 : ↥B).2) v
  map_mul' σ τ := by
    refine LinearEquiv.ext fun q => ?_
    obtain ⟨v, rfl⟩ := cls_surjective Z q
    have h1 := quotAut_cls Z ((σ * τ : ↥B) : MulAut V) (hB _ (σ * τ : ↥B).2) v
    have h2 := quotAut_cls Z (τ : MulAut V) (hB _ τ.2) v
    have h3 := quotAut_cls Z (σ : MulAut V) (hB _ σ.2) ((τ : MulAut V) v)
    have e : cls Z (((σ * τ : ↥B) : MulAut V) v) =
        cls Z ((σ : MulAut V) ((τ : MulAut V) v)) := rfl
    refine h1.trans (e.trans (h3.symm.trans ?_))
    change quotAut Z (σ : MulAut V) (hB _ σ.2) (cls Z ((τ : MulAut V) v)) =
      quotAut Z (σ : MulAut V) (hB _ σ.2) (quotAut Z (τ : MulAut V) (hB _ τ.2) (cls Z v))
    rw [h2]

theorem quotRep_cls [Fact (∀ a : V, a * a = 1)] (B : Subgroup (MulAut V))
    (hB : ∀ σ ∈ B, Z.map (σ : V →* V) = Z) (σ : ↥B) (v : V) :
    quotRep Z B hB σ (cls Z v) = cls Z ((σ : MulAut V) v) :=
  quotAut_cls Z (σ : MulAut V) (hB σ σ.2) v

end Action

section Bridge

theorem toAddSubgroup_sup {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (U U' : Submodule (ZMod 2) M) :
    (U ⊔ U').toAddSubgroup = U.toAddSubgroup ⊔ U'.toAddSubgroup :=
  (AddSubgroup.toZModSubmodule 2).symm.map_sup U U'

theorem toAddSubgroup_inf {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (U U' : Submodule (ZMod 2) M) :
    (U ⊓ U').toAddSubgroup = U.toAddSubgroup ⊓ U'.toAddSubgroup :=
  (AddSubgroup.toZModSubmodule 2).symm.map_inf U U'

theorem relIndex_liftAdd {V : Type*} [CommGroup V] [Finite V] (Z : Subgroup V)
    (U : AddSubgroup (Additive (V ⧸ Z))) : Z.relIndex (liftAdd Z U) = Nat.card U := by
  have h := Subgroup.relIndex_mul_card (H := Z) (K := liftAdd Z U)
  rw [inf_eq_left.2 (le_liftAdd Z U), card_liftAdd Z U] at h
  have hpos : 0 < Nat.card Z := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])

end Bridge

section GenericSup

theorem exists_mul_of_mem_sup_of_commute {Γ : Type*} [Group Γ] (K₁ K₂ : Subgroup Γ)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) {x : Γ} (hx : x ∈ K₁ ⊔ K₂) :
    ∃ a ∈ K₁, ∃ b ∈ K₂, a * b = x := by
  let P : Subgroup Γ :=
    { carrier := {g | ∃ a ∈ K₁, ∃ b ∈ K₂, a * b = g}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, mul_mem ha₁ ha₂, b₁ * b₂, mul_mem hb₁ hb₂, ?_⟩
        have := hc a₂ ha₂ b₁ hb₁
        calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [this]
          _ = a₁ * b₁ * (a₂ * b₂) := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        have := hc a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
        calc a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := this
          _ = (a * b)⁻¹ := by group }
  have h1 : K₁ ≤ P := fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩
  have h2 : K₂ ≤ P := fun b hb => ⟨1, one_mem _, b, hb, by simp⟩
  exact sup_le h1 h2 hx

end GenericSup

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
