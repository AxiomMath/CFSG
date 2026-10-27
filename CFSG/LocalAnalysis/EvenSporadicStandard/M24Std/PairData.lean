module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PinnedB

public section

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

@[expose] def pairGenW : List (List ℤ) :=
  [
    [-2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1,
     -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, -2, -1, -2, -1, -2, -1, -2,
     -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -1, -2, -1, 2, -1, 2,
     -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1,
     -2, -1, -2, -1, 2, -1, 2, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1,
     2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2],
    [1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2,
     1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1,
     -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, -2,
     -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2,
     -2, 1, -2, 1, -2, 1, 2, 1, 2, 2, -1, -2, -1]]

@[expose] def pairGens : List S24 := pairGenW.map m24Cj

@[expose] def pairN (w : List ℤ) : S24 := evalN NativeSporadic.M24 pairGens w

@[expose] def pairX0 : S24 := m24Elt4 m24B0B 1

@[expose] def pairTransW : List (List ℤ) :=
  [[], [1], [2], [-1], [-2], [1, 1], [2, 1], [-2, 1], [1, 2], [2, 2], [2, -1], [1, 1, 1],
    [-2, 1, 1], [2, 1, 2], [-2, 1, 2]]

@[expose] def pairTransL : List S24 := pairTransW.map pairN

@[expose] def pairFixL : List S24 := [pairN [2, -1, 2]]

@[expose] def pairOrd3 : S24 :=
  pairN [-1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1]

@[expose] def pairOrd5 : S24 := pairN [1, 2, 1, 2, 1, 2]

@[expose] def pairOrd7 : S24 := pairN [-1, 1, 1, -2, -1, 1, 1, -2]

@[expose] def pairC1 : S24 := m24Elt4 m24B0B 4

@[expose] def pairC2 : S24 := m24Elt4 m24B0B 8

@[expose] def pairL256 : List S24 :=
  m24E1l.flatMap fun a =>
    [a, a * pairC1, a * pairC2, a * (pairC1 * pairC2)].map (normH NativeSporadic.M24)

@[expose] def pairCW : List ℤ :=
  [1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2,
   1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, -2,
   1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1,
   2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, -1, 2,
   -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, 1, 2, 1, -2, 1, 2,
   1, -2, 1, -2, 1, 2, 2]

@[expose] def pairC : S24 := m24Cj pairCW

@[expose] def OctadCentData : Prop :=
  (∀ i : Fin 24, (∀ b ∈ m24B0l, (b : Equiv.Perm (Fin 24)) i = i) ∨
      ∃ b ∈ m24B0l, (b : Equiv.Perm (Fin 24)) 0 = i) ∧
    (∃ b ∈ m24B0l, (b : Equiv.Perm (Fin 24)) 0 ≠ 0) ∧
    ∀ j : Fin 24, j.val < 7 →
      ∃ b ∈ m24B0l, (pairC : Equiv.Perm (Fin 24)) j = (b : Equiv.Perm (Fin 24)) 0

instance : Decidable OctadCentData := by unfold OctadCentData; infer_instance

@[expose] def OctadTransData : Prop :=
  pairX0 ∈ m24B0l ∧ pairX0 ≠ 1 ∧
    (∀ g ∈ pairTransL, ∀ b ∈ m24B0l, g * b * g⁻¹ ∈ m24B0l) ∧
    ∀ b ∈ m24B0l, b = 1 ∨ ∃ g ∈ pairTransL, g * pairX0 * g⁻¹ = b

instance : Decidable OctadTransData := by unfold OctadTransData; infer_instance

@[expose] def OctadFixData : Prop :=
  (∀ s ∈ pairFixL, ∀ b ∈ m24B0l, s * b * s⁻¹ ∈ m24B0l) ∧
    (∀ s ∈ pairFixL, s * pairX0 * s⁻¹ = pairX0) ∧
    ∀ w ∈ m24B0l, (∀ s ∈ pairFixL, s * w * s⁻¹ = w) → w = 1 ∨ w = pairX0

instance : Decidable OctadFixData := by unfold OctadFixData; infer_instance

@[expose] def OrdNormB0 (p : S24) (r : ℕ) : Prop :=
  p ^ r = 1 ∧ p ≠ 1 ∧ ∀ b ∈ m24B0l, p * b * p⁻¹ ∈ m24B0l

instance (p : S24) (r : ℕ) : Decidable (OrdNormB0 p r) := by unfold OrdNormB0; infer_instance

@[expose] def OctadBigData : Prop :=
  pairL256.length = 256 ∧ pairL256.Nodup ∧ (1 : S24) ∈ pairL256 ∧
    (∀ x ∈ pairL256, ∀ y ∈ pairL256, x * y ∈ pairL256) ∧
    (∀ x ∈ pairL256, ∀ b ∈ m24B0l, x * b * x⁻¹ ∈ m24B0l) ∧
    OrdNormB0 pairOrd3 3 ∧ OrdNormB0 pairOrd5 5 ∧ OrdNormB0 pairOrd7 7

instance : Decidable OctadBigData := by unfold OctadBigData; infer_instance

@[expose] def pairYW : List ℤ :=
  [-1, 2, -1, 2, -1, 2, -1, -2, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1,
   2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2,
   1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2,
   1, -2, 1, -2, 1, 2, 1, 2, 1, 2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1,
   2, -1, -2]

@[expose] def pairY : S24 := m24Cj pairYW

@[expose] def pairZB : List S24 := [8, 4, 14, 9].map (m24Elt m24E1B)

@[expose] def pairZl : List S24 := (List.range 16).map (m24Elt4 pairZB)

@[expose] def CompatPairData : Prop :=
  (∀ a ∈ m24E1l, ∀ b ∈ m24B0l, a * b * a⁻¹ ∈ m24B0l) ∧
    (∀ b ∈ m24B0l, ∀ a ∈ m24E1l, b * a * b⁻¹ ∈ m24E1l) ∧
    (m24E1l.filter fun a => decide (a ∈ m24B0l)).length = 4 ∧
    ∀ x ∈ m24B0l, x ∉ m24E1l → (∀ a ∈ m24E1l, a * (x * a⁻¹ * x⁻¹) ∈ m24B0l) ∧
      ∀ b ∈ m24B0l, b ∈ m24E1l → ∃ a ∈ m24E1l, b = a * (x * a⁻¹ * x⁻¹)

instance : Decidable CompatPairData := by unfold CompatPairData; infer_instance

@[expose] def CompatZData : Prop :=
  pairZl.length = 16 ∧ pairZl.Nodup ∧ (1 : S24) ∈ pairZl ∧
    (∀ x ∈ pairZl, ∀ y ∈ pairZl, x * y ∈ pairZl) ∧ (∀ x ∈ pairZl, x ∈ m24E1l) ∧
    (∀ x ∈ pairZl, x ∈ m24B0l → x = 1) ∧ (∀ z ∈ pairZB, z ∈ pairZl) ∧
    ∀ z ∈ pairZB, (∀ b ∈ m24B0l, b * (z * b⁻¹ * z⁻¹) ∈ m24E1l ∧ b * (z * b⁻¹ * z⁻¹) ∈ m24B0l) ∧
      ∀ c ∈ m24B0l, c ∈ m24E1l → ∃ b ∈ m24B0l, c = b * (z * b⁻¹ * z⁻¹)

instance : Decidable CompatZData := by unfold CompatZData; infer_instance

@[expose] def CompatYData : Prop :=
  (∀ b ∈ m24B0l, pairY * b * pairY⁻¹ ∈ m24B0l) ∧ (∀ z ∈ pairZl, pairY * z * pairY⁻¹ ∈ pairZl) ∧
    pairY * pairY * pairY = 1 ∧ (∀ b ∈ m24B0l, (pairY * b * pairY⁻¹ = b ↔ b ∈ m24E1l)) ∧
    (∀ x ∈ pairZl, x * (pairY * x⁻¹ * pairY⁻¹) ∈ pairZl) ∧
    ∀ z ∈ pairZB, ∃ x ∈ pairZl, z = x * (pairY * x⁻¹ * pairY⁻¹)

instance : Decidable CompatYData := by unfold CompatYData; infer_instance

end CFSG.EvenSporadicStandard.M24Std
