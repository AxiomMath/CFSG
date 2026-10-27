module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

abbrev ppQuot (p : ℕ) (H : Type) [Group H] : Type := H ⧸ GLAPPrimeCore p H

abbrev psimpleOf (p : ℕ) (H : Type) [Group H] : Type :=
  ppQuot p H ⧸ Subgroup.center (ppQuot p H)

@[expose] noncomputable def piOf (p : ℕ) (H : Type) [Group H] : H →* psimpleOf p H :=
  (QuotientGroup.mk' (Subgroup.center (ppQuot p H))).comp (QuotientGroup.mk' (GLAPPrimeCore p H))

@[expose] def fixSub {H : Type} [Group H] (δ : MulAut H) : Subgroup H where
  carrier := {x | δ x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

@[expose] def relOfAut (p : ℕ) {H : Type} [Group H] (δ : MulAut H) :
    ppQuot p H → ppQuot p H → Prop :=
  fun q q' => ∃ l l' : H, (QuotientGroup.mk l : H ⧸ GLAPPrimeCore p H) = q ∧
    (QuotientGroup.mk l' : H ⧸ GLAPPrimeCore p H) = q' ∧ δ l = l'

@[expose] def InnerAutGrp (p : ℕ) (H : Type) [Group H] (δ : MulAut H) : Prop :=
  ∃ l : H, ∀ y : H, (l⁻¹ * y * l)⁻¹ * δ y ∈ GLAPPrimeCore p H

@[expose] def IsTD4Grp (p : ℕ) (H : Type) [Group H] : Prop :=
  catalogIs (psimpleOf p H) (onLie fun | .trialityD4 _ => True | _ => False)

@[expose] def FieldAutOn (p : ℕ) (H : Type) [Group H] (δ : MulAut H) : Prop :=
  GLAMarking (ppQuot p H)
      (fun lab _ _ I F θ => GLAPrimeField p lab I F (GLAInduces θ (relOfAut p δ))) ∨
    (p = 3 ∧ IsTD4Grp 3 H ∧ ¬ InnerAutGrp 3 H δ)

@[expose] def I2015OddCentreFact : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (δ : MulAut H), p.Prime → p ≠ 2 → δ ^ p = 1 →
    commutator (ppQuot p H) = ⊤ → IsChevSimple 2 (psimpleOf p H) → FieldAutOn p H δ →
    Odd (Nat.card (Subgroup.center (ppQuot p H)))

@[expose] def I2015LieModelFact : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (δ : MulAut H), p.Prime → p ≠ 2 → δ ^ p = 1 →
    commutator (ppQuot p H) = ⊤ → IsChevSimple 2 (psimpleOf p H) → FieldAutOn p H δ →
    ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel (psimpleOf p H) t n 2 f

@[expose] def I2015NoParabolicFact : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (δ : MulAut H) (I I₀ : Subgroup H), p.Prime → p ≠ 2 →
    δ ^ p = 1 → commutator (ppQuot p H) = ⊤ → IsChevSimple 2 (psimpleOf p H) → FieldAutOn p H δ →
    GLAPComponent p (fixSub δ) I → I₀ ≤ I → I₀ ⊔ GLAPPrimeCoreOf p I = I →
    ∀ U : Subgroup (psimpleOf p H), U ≠ ⊥ → IsPGroup 2 U →
      ¬ (I₀.map (piOf p H) ≤ Subgroup.normalizer (U : Set (psimpleOf p H)))

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
