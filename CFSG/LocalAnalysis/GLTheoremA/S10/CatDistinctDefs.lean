module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10

structure CatDistinctAt : Prop where
  td4_ys09 : ∀ (S : Type) [Group S] [Finite S],
    catalogIs S (onLie fun | .trialityD4 _ => True | _ => False) → catalogIs S isYs09Type → False
  u42_a6 : ∀ (S : Type) [Group S], catalogIs S S9.isU4two → catalogIs S S10.isA6 → False
  u45_l2 : ∀ (S : Type) [Group S] [Finite S] (k : ℕ),
    catalogIs S (fun i => S9.isU4two i ∨ S9.isU5two i) → catalogIs S (isL2n k) → False
  td4_u6 : ∀ (S : Type) [Group S] [Finite S] (m : ℕ), Odd m →
    catalogIs S (onLie fun | .trialityD4 _ => True | _ => False) → catalogIs S (isU6n m) → False
  td4_l2 : ∀ (S : Type) [Group S] [Finite S] (k : ℕ),
    catalogIs S (isL2n k) → catalogIs S (onLie fun | .trialityD4 _ => True | _ => False) → False
  g2_inj : ∀ (S : Type) [Group S] [Finite S] (n n' : ℕ),
    catalogIs S (isG2n n) → catalogIs S (isG2n n') → n = n'
  g2_u6 : ∀ (S : Type) [Group S] [Finite S] (n m : ℕ), (n = m ∨ Odd m) →
    catalogIs S (isG2n n) → catalogIs S (isU6n m) → False
  urn_l2 : ∀ (S : Type) [Group S] [Finite S] (n k : ℕ), Odd n → 1 < n →
    catalogIs S (isUrn n) → catalogIs S (isL2n k) → False
  u33_u6 : ∀ (S : Type) [Group S] [Finite S] (m : ℕ), catalogIs S isU33 → catalogIs S (isU6n m) → False
  td4_exc : ∀ (S : Type) [Group S] [Finite S], IsChevSimple 2 S →
    catalogIs S (onLie fun | .trialityD4 _ => True | _ => False) → catalogIs S excIndex → False
  g2_chev2 : ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid),
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) → IsChevSimple 2 S → q.p = 2
  u33_center : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid), q.card = 3 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) → Subgroup.center S = ⊥

end CFSG.LocalAnalysis.GLTheoremA
