module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def U9Gf8Absurd : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (K J : Subgroup Γ) (x a : Γ), x ^ 3 = 1 → a ^ 3 = 1 → x * a = a * x →
    ∀ (hI1 : S10.InnDiagOn 3 (Subgroup.zpowers x) K) (_ : S10.InnDiagOn 3 (Subgroup.zpowers a) K),
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J →
    catalogIs (PSimple 3 J) S9.isU3eight → S10.FieldOn 3 a J →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    d.1.characteristic = 2 → KD264Lie.fieldSize d.1 = 8 →
    KD264Lie.CompAlgAt (TauCeti.CFSGIndex.lie d).Group →
    chevAut 3 K ⟨x, hI1.1 (Subgroup.mem_zpowers x)⟩ ≠ 1 → False

end CFSG.LocalAnalysis.GLTheoremA.I141F
