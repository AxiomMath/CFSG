module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def I262 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsChevSimple 2 K →
    p ∣ Nat.card K → ∀ A : Subgroup (MulAut K), IsElemAbelian p A → p ^ 2 ≤ Nat.card A →
      (∀ a ∈ A, a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥) →
      (p = 3 ∧ (catalogIs K S265.tyA ∨ catalogIs K S265.tyUn ∨ catalogIs K S265.tyC ∨
          catalogIs K S265.tyD)) ∨
        (p = 5 ∧ catalogIs K S265.tyE) ∨ catalogIs K (S265.tyF p)

@[expose] def I262GF2 : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    d.1.characteristic = 2 → KD264Lie.ov2Idx d.1 →
    ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group), IsElemAbelian 3 A → 9 ≤ Nat.card A →
      (∀ a ∈ A, a ≠ 1 → GLAPLayer 3 (fixSubgroup a) = ⊥) →
      S265.tyA (.lie d) ∨ S265.tyUn (.lie d) ∨ S265.tyC (.lie d)

@[expose] def I262Alt8 : Prop :=
  ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.alternating 8 (by norm_num)).Group), IsElemAbelian 3 A →
    9 ≤ Nat.card A → ∃ a ∈ A, a ≠ 1 ∧ GLAPLayer 3 (fixSubgroup a) ≠ ⊥

end CFSG.LocalAnalysis.GLTheoremA.S262

end
