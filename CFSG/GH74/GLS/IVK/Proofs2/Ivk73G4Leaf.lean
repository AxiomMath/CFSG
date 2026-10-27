module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

@[expose] def OddClassicalSix (X : Type) [Group X] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    (LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f ∨ LieModel X .PSp 2 p f ∨
      (p ^ f % 8 ≠ 1 ∧ LieModel X .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel X .PSU 4 p f))) ∨
  (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧
    ((p ^ f % 4 = 3 ∧ LieModel X .PSL 5 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel X .PSU 5 p f)))

structure Ivk73Rest : Prop where
  alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → Ivk73Fam (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n)))
  m11 : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : Ivk73Fam (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : Ivk73Fam (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .PSL 2 p f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .G2 0 p f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .trialityD4 0 p f)
  ree : ∀ f : ℕ, Ivk73Empty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : Ivk73Empty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : Ivk73Empty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : Ivk73Empty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : Ivk73Empty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : Ivk73Empty (fun X _ => LieModel X .twistedB2 0 2 3)

end CFSG.GH74.GLS.IVK
