module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIsoAssembly
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.StandardType (GGInndiagCommEq ggInndiag ggInndiagComm GGInndiagCommExclLabel
  GGInndiagCommProvedLabel GGInndiagCommRestInput LargeEvenSimpleGuard)


theorem centerQuotAut_conjAut_ne_one {Γ : Type} [Group Γ] {L : Subgroup Γ} {y : Γ}
    (hy : y ∈ Subgroup.normalizer (L : Set Γ)) (hyL : y ∉ Subgroup.centralizer (L : Set Γ))
    (hperf : commutator ↥L = ⊤) : centerQuotAut ↥L (conjAut L y hy) ≠ 1 := by
  intro h
  haveI : Group.IsPerfect ↥L := ⟨hperf⟩
  have hc : ∀ l : ↥L, l⁻¹ * (conjAut L y hy).toMonoidHom l ∈ Subgroup.center ↥L := fun l => by
    have h1 : (QuotientGroup.mk (conjAut L y hy l) : ↥L ⧸ Subgroup.center ↥L) =
        QuotientGroup.mk l := by
      rw [← centerQuotAut_mk ↥L (conjAut L y hy) l, h]
      rfl
    exact QuotientGroup.eq.mp h1.symm
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    (conjAut L y hy).toMonoidHom hc
  apply hyL
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h2 := congrArg Subtype.val (DFunLike.congr_fun hid ⟨g, hg⟩)
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.id_apply] at h2
  rw [coe_conjAut] at h2
  calc g * y = y * (y⁻¹ * g * y) := by group
    _ = y * g := by rw [h2]

theorem n_eq_one_of_derived {lab : GLALabel} (hlam : LargeEvenInLambda2 lab)
    (h : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) : lab.n = 1 := by
  obtain ⟨t, r, n⟩ := lab
  rcases h with h | h | h <;>
    (simp only at h; subst h; obtain ⟨-, -, h1⟩ := hlam; exact h1)

section Certs


theorem mem_innAutDerived_of_innDiagKind (hRest : GGInndiagCommRestInput) {S : Type} [Group S]
    [Finite S] {lab : GLALabel} {α : MulAut S} (hcen : Subgroup.center S = ⊥) (hn : 2 ≤ lab.n)
    (hin : InnDiagKind S lab α) : α ∈ innAutDerived S := by
  by_cases hF : FamOrth lab
  · obtain ⟨-, a, ha⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthMark.innDiagKind_orth_data hcen hF hin
    exact inner_le_innAutDerived S ⟨a, ha⟩
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, -, -, -, hlab, -⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst lab'
  have hnd : ¬ CFSG.LocalAnalysis.GLTheoremA.MI.DerivedLab lab := fun h => by
    have := n_eq_one_of_derived hlam (h.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)))
    omega
  have hne : ¬ GGInndiagCommExclLabel lab := by
    rintro (⟨ht, hr⟩ | h)
    · exact hF (Or.inl ⟨ht, by omega⟩)
    · have := n_eq_one_of_derived hlam (Or.inl h)
      omega
  have hall : CFSG.StandardType.LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
    by_cases hp : GGInndiagCommProvedLabel lab
    · exact CFSG.StandardType.largeEvenLabelAll_inndiagComm_proved hlam hp
    · exact hRest lab hlam hne hp
  have h2 := (CFSG.LocalAnalysis.GLTheoremA.MI.canonAll_iff_legacyAll hlam hnd _).2 hall _ hraw
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, u, hu, hind⟩, hEq⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists h2
  have hu' : u ∈ ggInndiagComm R := by
    rw [← hEq hs hna]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure hu)
  let e : S ≃* R := (CanonInn.quotCenterEquivOfBot hcen).symm.trans θ
  have he : ∀ s, e s = θ (QuotientGroup.mk s) := fun s => by
    show θ ((CanonInn.quotCenterEquivOfBot hcen).symm s) = _
    congr 1
    rw [MulEquiv.symm_apply_eq, CanonInn.quotCenterEquivOfBot_mk]
  have hconj : MulAut.congr e α = u := by
    ext r
    obtain ⟨s, rfl⟩ := e.surjective r
    show e (α (e.symm (e s))) = u (e s)
    rw [MulEquiv.symm_apply_apply, he, he]
    exact (hind s (α s) rfl).symm
  rw [← mem_innAutDerived_congr e, hconj]
  exact hu'

end Certs

end CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp

end
