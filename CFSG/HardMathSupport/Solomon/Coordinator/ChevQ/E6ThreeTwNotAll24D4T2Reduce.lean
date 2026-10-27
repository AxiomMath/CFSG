module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Cent
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2ModelDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Defs


@[expose] def D4T2TorusPart : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀),
    (∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) → S.IsAlgebraic →
    ∀ {l f : ℕ}, l.Prime → 0 < f → S.D.q = l ^ f → l ≠ 3 → ((3 : ℕ) : L) ≠ 0 →
      3 ∣ l ^ f + 1 →
    ∀ {a : Fin Tag.E6.rank → Lˣ}, rootDiagUnit .E6 a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
      (kernelRoots (rootCharHom a)).ncard = 24 →
    ∀ F₀ : Subgroup (ModGL Tag.E6 L), F₀ ≤ S.D.model → F₀ ≤ toralRootGroup .E6 L a →
      IsElemAbelian 3 F₀ → Nat.card F₀ = 3 ^ 2 → rootDiagUnit .E6 a ∈ F₀ →
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 a} ⊓ toralRootGroup .E6 L a ≤
        sSup {J | CFSG.Open.IsComponentOf J
            (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 a})} ⊔
          (S.Γ ⊓ Subgroup.centralizer (F₀ : Set (ModGL Tag.E6 L)))

@[expose] def D4T2CosetPart : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀),
    (∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) → S.IsAlgebraic →
    ∀ {l f : ℕ}, l.Prime → 0 < f → S.D.q = l ^ f → l ≠ 3 → ((3 : ℕ) : L) ≠ 0 →
      3 ∣ l ^ f + 1 →
    ∀ {a : Fin Tag.E6.rank → Lˣ}, rootDiagUnit .E6 a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
      (kernelRoots (rootCharHom a)).ncard = 24 →
    ∀ Eh : Subgroup (ModGL Tag.E6 L), Eh ≤ S.D.model → IsElemAbelian 3 Eh →
      Nat.card Eh = 3 ^ 3 → rootDiagUnit .E6 a ∈ Eh → ¬ Eh ≤ S.Γ →
      (∀ R : Subgroup (ModGL Tag.E6 L), R ≤ S.Γ → R ≠ ⊥ → IsPGroup l R →
        ∃ ε ∈ Eh, R.map (MulAut.conj ε).toMonoidHom ≠ R) →
      Eh ⊓ S.Γ ≤ toralRootGroup .E6 L a →
      (∃ x ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 a}, x ∉ toralRootGroup .E6 L a) →
      ∃ F : Subgroup (ModGL Tag.E6 L), F ≤ Eh ∧ F.relIndex Eh = 3 ∧ rootDiagUnit .E6 a ∈ F ∧
        ∃ y ∈ S.Γ ⊓ Subgroup.centralizer (F : Set (ModGL Tag.E6 L)),
          y ∉ toralRootGroup .E6 L a

end Defs

section Reduce

set_option linter.unusedSectionVars false


theorem d4t2_rootDiagUnit_ne_one {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (hall : (kernelRoots (rootCharHom a)).ncard = 24) : rootDiagUnit .E6 a ≠ 1 := by
  intro h
  have ha : a = 1 :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
  subst ha
  have hset : kernelRoots (rootCharHom (1 : Fin Tag.E6.rank → Lˣ)) =
      ↑(rootFinset Tag.E6) := by
    ext α
    simp [kernelRoots, rootCharHom, rootChar, mem_rootFinset]
  rw [hset, Set.ncard_coe_finset, card_rootFinset] at hall
  exact absurd hall (by decide)

theorem d4t2ModelGen_of_parts (hA : D4T2TorusPart) (hB : D4T2CosetPart) : D4T2ModelGen := by
  intro L _ _ p₀ S hS hAlg l f hl hf hq hl3 h3 h3q a hT hap hall Eh hEhM hab hcard hdE hnin hr
  have hd1 : rootDiagUnit .E6 a ≠ 1 := d4t2_rootDiagUnit_ne_one hall
  have hdT : rootDiagUnit .E6 a ∈ torusGroup .E6 L := (Subgroup.mem_inf.1 hT).1
  have hEhC : Eh ≤ toralCentralizer .E6 L a := by
    intro x hx
    refine mem_toralCentralizer.2 ⟨(S.D.mem_model.1 (hEhM hx)).1, ?_⟩
    rw [hab.comm hdE hx, mul_inv_cancel_right]
  have hXC : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 a} ≤ toralCentralizer .E6 L a := by
    intro x hx
    exact mem_toralCentralizer.2 ⟨(S.D.mem_model.1 (S.Γ_le_model hx.1)).1,
      conj_eq_iff_mem_centralizer.2 hx.2⟩
  obtain ⟨F₀, hF₀E, hF₀idx, hdF₀, hF₀M⟩ := d4t2_exists_plane a hap hdT hEhC hab hcard hdE hd1
  have hF₀card : Nat.card F₀ = 3 ^ 2 := by
    have h := Subgroup.relIndex_mul_card (H := F₀) (K := Eh)
    rw [hF₀idx, inf_eq_left.2 hF₀E, hcard] at h
    omega
  have h0 := hA S hS hAlg hl hf hq hl3 h3 h3q hT hap hall F₀ (hF₀E.trans hEhM) hF₀M
    (hab.mono hF₀E) hF₀card hdF₀
  set X : Subgroup (ModGL Tag.E6 L) :=
    S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 a} with hX
  set N : Subgroup (ModGL Tag.E6 L) := sSup {J | CFSG.Open.IsComponentOf J X} ⊔
    ⨆ (F : Subgroup (ModGL Tag.E6 L)) (_ : F ≤ Eh ∧ F.relIndex Eh = 3 ∧ rootDiagUnit .E6 a ∈ F),
      S.Γ ⊓ Subgroup.centralizer (F : Set (ModGL Tag.E6 L)) with hN
  have hFN : ∀ F : Subgroup (ModGL Tag.E6 L),
      (F ≤ Eh ∧ F.relIndex Eh = 3 ∧ rootDiagUnit .E6 a ∈ F) →
      S.Γ ⊓ Subgroup.centralizer (F : Set (ModGL Tag.E6 L)) ≤ N :=
    fun F hF => le_sup_of_le_right (le_iSup₂_of_le F hF le_rfl)
  have hXM : X ⊓ toralRootGroup .E6 L a ≤ N :=
    h0.trans (sup_le le_sup_left (hFN F₀ ⟨hF₀E, hF₀idx, hdF₀⟩))
  have hNX : N ≤ X := by
    refine sup_le (sSup_le fun J hJ => hJ.1) (iSup₂_le fun F hF => ?_)
    exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hF.2.2))
  by_cases hXM' : X ≤ toralRootGroup .E6 L a
  · exact (le_inf le_rfl hXM').trans hXM
  · have hy : ∃ y ∈ N, y ∉ toralRootGroup .E6 L a := by
      by_cases hEΓM : Eh ⊓ S.Γ ≤ toralRootGroup .E6 L a
      · obtain ⟨x, hxX, hxM⟩ := SetLike.not_le_iff_exists.1 hXM'
        obtain ⟨F, hFE, hFidx, hdF, y, hy, hyM⟩ := hB S hS hAlg hl hf hq hl3 h3 h3q hT hap hall
          Eh hEhM hab hcard hdE hnin hr hEΓM ⟨x, hxX, hxM⟩
        exact ⟨y, hFN F ⟨hFE, hFidx, hdF⟩ hy, hyM⟩
      · obtain ⟨c, hcEΓ, hcM⟩ := SetLike.not_le_iff_exists.1 hEΓM
        have hcE : c ∈ Eh := hcEΓ.1
        have hdM : rootDiagUnit .E6 a ∈ toralRootGroup .E6 L a := hF₀M hdF₀
        have hcz : c ∉ Subgroup.zpowers (rootDiagUnit .E6 a) := fun h =>
          hcM ((Subgroup.zpowers_le.2 hdM) h)
        have hFE : Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers c ≤ Eh :=
          sup_le (Subgroup.zpowers_le.2 hdE) (Subgroup.zpowers_le.2 hcE)
        have hFidx : (Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers c).relIndex Eh = 3 :=
          KSNotAll24.relIndex_eq_three hFE hcard
            (KSNotAll24.card_zpowers_sup_zpowers (hab.comm hdE hcE) hd1 (hab.2 _ hdE)
              (hab.2 c hcE) hcz)
        have hdF : rootDiagUnit .E6 a ∈ Subgroup.zpowers (rootDiagUnit .E6 a) ⊔
            Subgroup.zpowers c := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
        have hcF : c ∈ Subgroup.centralizer ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔
            Subgroup.zpowers c : Subgroup (ModGL Tag.E6 L)) : Set (ModGL Tag.E6 L)) :=
          Subgroup.mem_centralizer_iff.2 fun h hh => hab.comm (hFE hh) hcE
        exact ⟨c, hFN _ ⟨hFE, hFidx, hdF⟩ ⟨hcEΓ.2, hcF⟩, hcM⟩
    obtain ⟨y, hyN, hyM⟩ := hy
    exact d4t2_le_of_not_mem a hap hXC hNX hXM hyN hyM

end Reduce

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
