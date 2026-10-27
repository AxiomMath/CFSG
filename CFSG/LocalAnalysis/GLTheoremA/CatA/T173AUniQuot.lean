module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniIv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly
open scoped MatrixGroups commutatorElement

theorem uni_quot_iv {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : UniArith p n d F)
    {Q : Type} [Group Q] (θ : Q ≃* UniPSU n d F) {Bbar Kbar : Subgroup Q}
    (hB : IsElemAbelian p Bbar)
    (hhb : ∃ T : Subgroup Q, IsPGroup 2 T ∧ Bbar ≤ Subgroup.normalizer (T : Set Q) ∧
      (⁅T, Bbar⁆ : Subgroup Q) ≠ ⊥)
    {y : Q} (hy : y ∈ Bbar) (hy1 : y ≠ 1)
    (hK : CFSG.Open.IsComponentOf Kbar (Subgroup.centralizer ({y} : Set Q))) :
    ∃ B' U : Subgroup Q, IsElemAbelian p B' ∧ Bbar ≤ B' ∧ Bbar ≠ B' ∧
      B' ≤ Subgroup.normalizer (Kbar : Set Q) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ Kbar ∧
      B' = (B' ⊓ Kbar) ⊔ (B' ⊓ Subgroup.normalizer (U : Set Q)) := by
  obtain ⟨ψ, A, hfr⟩ := uni_exists_frame h θ hB
  have hrep := uni_repeated_weight h hfr hhb
  obtain ⟨I, hI, hKI⟩ := uni_component_support h hfr hy hy1 hK
  exact uni_iv_frame h hfr hrep hI hKI

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
