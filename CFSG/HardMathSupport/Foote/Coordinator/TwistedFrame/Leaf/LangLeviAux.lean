module

public import CFSG.LieType.AlgebraicGroups.SupportedNativeLang
public import CFSG.LieType.AlgebraicGroups.RootWordBruhatCover
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.LangLeviAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups WithConv

open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false


variable {τ : Tag} {k : Type} [Field k]

theorem isDomainImage_torusGroup [IsAlgClosed k] :
    SeminaireExp3.IsDomainImage k
      (transportPoints (modGLPoint τ k) (torusGroup τ k : Set (ModGL τ k))) := by
  refine ⟨TorusAffine k τ.rank (0 + 0), inferInstance, inferInstance, inferInstance,
    inferInstance, bruhatCo τ k 1 (N := 0) (m := 0) Fin.elim0 Fin.elim0, ?_⟩
  have hpt : ∀ (t : Fin τ.rank → kˣ) (c : Fin (0 + 0) → k),
      (modGLPoint τ k).symm (toConv ((torusAffinePoint t c).comp
        (bruhatCo τ k 1 (N := 0) (m := 0) Fin.elim0 Fin.elim0))) = torusProdHom τ k t := by
    intro t c
    rw [point_bruhatCo, torusProdHom_apply, canonicalRep_one]
    simp
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, ← range_torusProdHom] at hg
    obtain ⟨t, rfl⟩ := hg
    refine ⟨torusAffinePoint t (fun i => i.elim0), ?_⟩
    have h := hpt t (fun i => i.elim0)
    rw [← h]
    beta_reduce
    rw [MulEquiv.apply_symm_apply, ofConv_toConv]
  · rintro ⟨z, rfl⟩
    obtain ⟨⟨t, c⟩, rfl⟩ := torusAffinePointEquiv.surjective z
    refine ⟨torusProdHom τ k t, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← range_torusProdHom]
      exact ⟨t, rfl⟩
    · rw [← hpt t c]
      beta_reduce
      rw [MulEquiv.apply_symm_apply, ofConv_toConv]
      rfl

theorem isConnectedAlgebraicSubgroup_parabolicLevi [IsAlgClosed k] (J : Set (Fin τ.rank)) :
    IsConnectedAlgebraicSubgroup k
      ((parabolicLevi τ k J).map (modGLPoint τ k).toMonoidHom) := by
  classical
  obtain ⟨W, hW0, hWs⟩ : ∃ W : Option {l : Letter τ // l.1 ∈ J} →
      Set (SeminaireExp3.ZariskiGL (Label τ) k),
      W none = modGLZariski τ k '' (torusGroup τ k : Set (ModGL τ k)) ∧
        ∀ l, W (some l) = supportedCurve τ k J l :=
    ⟨fun i => Option.elim i (modGLZariski τ k '' (torusGroup τ k : Set (ModGL τ k)))
      (supportedCurve τ k J), rfl, fun _ => rfl⟩
  have hW : ∀ i, SeminaireExp3.IsDomainImage k (SeminaireExp3.ZariskiGL.pt '' W i) := by
    intro i
    cases i with
    | none =>
      rw [hW0, ← transportPoints_eq_image_modGLZariski]
      exact isDomainImage_torusGroup
    | some l =>
      rw [hWs]
      exact isDomainImage_letterCurve l.1
  have h1 : ∀ i, (1 : SeminaireExp3.ZariskiGL (Label τ) k) ∈ W i := by
    intro i
    cases i with
    | none =>
      rw [hW0]
      exact ⟨1, one_mem _, map_one _⟩
    | some l =>
      rw [hWs]
      exact ⟨1, ⟨0, letterUnit_zero l.1⟩, map_one _⟩
  obtain ⟨-, -, a, ha⟩ := SeminaireExp3.ZariskiGL.closure_eq_wordSet W hW h1
  have hclos : Subgroup.closure (⋃ i, W i) =
      (parabolicLevi τ k J).map (modGLZariski τ k).toMonoidHom := by
    have h2 : Subgroup.closure (modGLZariski τ k '' (torusGroup τ k : Set (ModGL τ k))) =
        (torusGroup τ k).map (modGLZariski τ k).toMonoidHom := by
      have h := MonoidHom.map_closure (modGLZariski τ k).toMonoidHom
        (torusGroup τ k : Set (ModGL τ k))
      rw [Subgroup.closure_eq] at h
      exact h.symm
    have h3 : Subgroup.closure (⋃ l : {l : Letter τ // l.1 ∈ J}, supportedCurve τ k J l) =
        (subsystemGroup τ k J).map (modGLZariski τ k).toMonoidHom :=
      (map_subsystemGroup_eq_closure J).symm
    have h4 : (⋃ l : {l : Letter τ // l.1 ∈ J}, W (some l)) =
        ⋃ l : {l : Letter τ // l.1 ∈ J}, supportedCurve τ k J l := by
      simp only [hWs]
    rw [Set.iUnion_option, hW0, h4, Subgroup.closure_union, h2, h3, ← Subgroup.map_sup]
    rfl
  have hdom : SeminaireExp3.IsDomainImage k
      (transportPoints (modGLPoint τ k) (parabolicLevi τ k J : Set (ModGL τ k))) := by
    have himg : modGLZariski τ k '' (parabolicLevi τ k J : Set (ModGL τ k)) =
        SeminaireExp3.ZariskiGL.wordSet W a := by
      rw [← ha, hclos, Subgroup.coe_map]
      rfl
    rw [transportPoints_eq_image_modGLZariski, himg]
    exact SeminaireExp3.ZariskiGL.isDomainImage_wordSet W hW a
  exact (isConnectedAlgebraicSubgroup_map (modGLPoint τ k) (parabolicLevi τ k J)
    hdom.isPointConstructible hdom.isPointIrreducible).2.1

theorem frobTwistGL_one_mem_parabolicLevi [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (e : ℕ) (J : Set (Fin τ.rank)) {g : ModGL τ k} (hg : g ∈ parabolicLevi τ k J) :
    frobTwistGL τ k p e 1 g ∈ parabolicLevi τ k J := by
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hle : (parabolicLevi τ k J).map (entrywiseFrobGL τ k p e) ≤ parabolicLevi τ k J := by
    change (torusGroup τ k ⊔ subsystemGroup τ k J).map (entrywiseFrobGL τ k p e) ≤
      torusGroup τ k ⊔ subsystemGroup τ k J
    rw [Subgroup.map_sup, map_entrywiseFrobGL_subsystemGroup p e J]
    refine sup_le_sup_right ?_ _
    rintro _ ⟨h, hh, rfl⟩
    exact entrywise_mem_torusGroup (σ := iterateFrobeniusEquiv k p e) hh
  exact hle ⟨g, hg, rfl⟩

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.LangLeviAux
