module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

structure Sec12F4 where
  a : Bool
  b : Bool
  deriving DecidableEq, Fintype

namespace Sec12F4

instance : Zero Sec12F4 := ⟨⟨false, false⟩⟩

instance : One Sec12F4 := ⟨⟨true, false⟩⟩

instance : Add Sec12F4 := ⟨fun x y => ⟨xor x.a y.a, xor x.b y.b⟩⟩

instance : Neg Sec12F4 := ⟨fun x => x⟩

instance : Mul Sec12F4 :=
  ⟨fun x y => ⟨xor (x.a && y.a) (x.b && y.b),
    xor (xor (x.a && y.b) (x.b && y.a)) (x.b && y.b)⟩⟩

instance : Inv Sec12F4 := ⟨fun x => ⟨xor x.a x.b, x.b⟩⟩

instance : Field Sec12F4 :=
  Field.ofMinimalAxioms Sec12F4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ⟨0, 1, by decide⟩

def w : Sec12F4 := ⟨false, true⟩

def w2 : Sec12F4 := ⟨true, true⟩

end Sec12F4

theorem sec12F4_card : Nat.card Sec12F4 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

noncomputable def sec12GF4Equiv : GaloisField 2 2 ≃+* Sec12F4 :=
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, sec12F4_card,
      GaloisField.card 2 2 (by norm_num)]
    norm_num)

abbrev Sec12M : Type := Matrix (Fin 2) (Fin 2) Sec12F4

def sec12Reps : List Sec12M :=
  [!![1, 0; 0, 1], !![1, 1; 0, 1], !![Sec12F4.w, 0; 0, Sec12F4.w2], !![0, 1; 1, Sec12F4.w],
    !![0, 1; 1, Sec12F4.w2]]

theorem sec12_conj_fin : ∀ A : Sec12M, A.det = 1 →
    ∃ g : Sec12M, g.det = 1 ∧ ∃ R ∈ sec12Reps, g * A = R * g := by
  decide +kernel

theorem sec12_fix_fin : ∀ R ∈ sec12Reps, ∀ R' ∈ sec12Reps, (R ≠ 1 ∨ R' ≠ 1) →
    (Finset.univ.filter (fun M : Sec12M => R * M * R'ᵀ = M)).card ≤ 16 := by
  decide +kernel

theorem sec12_fix2_fin : ∀ R ∈ sec12Reps, ∀ R' ∈ sec12Reps, R ≠ 1 → R' ≠ 1 →
    (Finset.univ.filter (fun M : Sec12M => R * M = M ∧ M * R'ᵀ = M)).card ≤ 4 := by
  decide +kernel

theorem sec12_cent_fin : ∀ A : Sec12M, A.det = 1 → A * A = 1 →
    (Finset.univ.filter (fun B : Sec12M => B.det = 1 ∧ B * A = A * B)).card = 60 ∨
    (Finset.univ.filter (fun B : Sec12M => B.det = 1 ∧ B * A = A * B)).card = 4 := by
  decide +kernel

theorem sec12_sl_fin :
    (Finset.univ.filter (fun M : Sec12M => M.det = 1)).card = 60 := by
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
