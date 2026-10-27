module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CosetDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Reduce

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section CaseB

set_option linter.unusedSectionVars false


theorem d4t2c_torus_le_toralRootGroup {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (a : Fin Tag.E6.rank → Lˣ) :
    S.D.torus ≤ toralRootGroup .E6 L a :=
  fun _ hx => Subgroup.mem_sup_left (Subgroup.mem_inf.1 hx).1

theorem d4t2c_caseB (hC : D4T2CentralTorus) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) (hAlg : S.IsAlgebraic)
    {l f : ℕ} (hl : l.Prime) (hf : 0 < f) (hq : S.D.q = l ^ f) (hl3 : l ≠ 3)
    (h3 : ((3 : ℕ) : L) ≠ 0) (h3q : 3 ∣ l ^ f + 1)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (hall : (kernelRoots (rootCharHom a)).ncard = 24)
    {Eh : Subgroup (ModGL Tag.E6 L)} (hEhM : Eh ≤ S.D.model) (hab : IsElemAbelian 3 Eh)
    (hcard : Nat.card Eh = 3 ^ 3) (hdE : rootDiagUnit .E6 a ∈ Eh)
    (hEM : ¬ Eh ≤ toralRootGroup .E6 L a) :
    ∃ F : Subgroup (ModGL Tag.E6 L), F ≤ Eh ∧ F.relIndex Eh = 3 ∧ rootDiagUnit .E6 a ∈ F ∧
      ∃ y ∈ S.Γ ⊓ Subgroup.centralizer (F : Set (ModGL Tag.E6 L)),
        y ∉ toralRootGroup .E6 L a := by
  have hd1 : rootDiagUnit .E6 a ≠ 1 := d4t2_rootDiagUnit_ne_one hall
  have hdT : rootDiagUnit .E6 a ∈ torusGroup .E6 L := (Subgroup.mem_inf.1 hT).1
  have hEhC : Eh ≤ toralCentralizer .E6 L a := by
    intro x hx
    refine mem_toralCentralizer.2 ⟨(S.D.mem_model.1 (hEhM hx)).1, ?_⟩
    rw [hab.comm hdE hx, mul_inv_cancel_right]
  obtain ⟨F₀, hF₀E, hF₀idx, hdF₀, hF₀M⟩ := d4t2_exists_plane a hap hdT hEhC hab hcard hdE hd1
  obtain ⟨e, heE, heM⟩ := SetLike.not_le_iff_exists.1 hEM
  obtain ⟨t, htT, htc, htΓ⟩ := hC S hS hAlg hl hf hq hl3 h3 h3q hT hap hall e (hEhM heE)
  refine ⟨F₀, hF₀E, hF₀idx, hdF₀, t * e, ⟨htΓ, ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    have h1 : t * h = h * t := htc h (hF₀M hh)
    have h2 : h * e = e * h := hab.comm (hF₀E hh) heE
    calc h * (t * e) = t * (h * e) := by rw [← mul_assoc, ← h1, mul_assoc]
      _ = t * e * h := by rw [h2, mul_assoc]
  · intro hy
    apply heM
    have htM : t ∈ toralRootGroup .E6 L a := d4t2c_torus_le_toralRootGroup S a htT
    have e' : e = t⁻¹ * (t * e) := by group
    rw [e']
    exact mul_mem (inv_mem htM) hy

end CaseB

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
