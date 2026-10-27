module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G]

theorem chevAut_notMem_range_conj_of_fieldOn {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup G} {g : G} (hF : FieldOn p g L) :
    chevAut p L ⟨g, hF.1⟩ ∉ (MulAut.conj : PSimple p L →* MulAut (PSimple p L)).range := by
  rintro ⟨s, hs⟩
  obtain ⟨-, lab, hlam, hraw⟩ := FP.canon_marking_and_labelAll_simple' (P' := FP.DataFacts p)
    (fun lab hlab => FP.canonDataFacts hp hp2 hlab) hF.2
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, f, hf, u, hu, hord, hind⟩, ⟨hmul, hinv, hconj, hfI⟩, -, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have e1 : u * f * u⁻¹ = MulAut.congr θ (indAut p L g hF.1) := (induces_indRel_iff hF.1 θ).1 hind
  rw [OutCyc.indAut_eq_inv_chevAut, ← hs, ← map_inv MulAut.conj s] at e1
  have e2 : MulAut.congr θ (MulAut.conj s⁻¹) = MulAut.conj (θ s⁻¹) := by
    ext r
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.conj_apply,
      MulAut.conj_apply, map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv θ s⁻¹]
  have h1 : u * f * u⁻¹ ∈ I := by
    rw [e1, e2]
    exact hconj _
  apply hfI f hf hord
  have e3 : f = u⁻¹ * (u * f * u⁻¹) * u := by group
  rw [e3]
  exact hmul _ (hmul _ (hinv u hu) _ h1) _ hu

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
