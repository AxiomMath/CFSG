module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang.Family
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LocalAnalysis.ComponentInitial.SylowLocalTransfer

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

theorem commutator_eq_bot_of_isComponentOf_ne_of_finite {G : Type*} [Group G]
    {A B K : Subgroup G} [Finite K] (hA : IsComponentOf A K) (hB : IsComponentOf B K)
    (hne : A ≠ B) : ⁅A, B⁆ = ⊥ := by
  have hA' := (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hA.1).mp hA
  have hB' := (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hB.1).mp hB
  have hne' : A.subgroupOf K ≠ B.subgroupOf K := by
    intro h
    have h' := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hA.1, inf_eq_left.mpr hB.1] at h'
    exact hne h'
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA' hB' hne'
  have hmap := congrArg (Subgroup.map K.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA.1,
    Subgroup.map_subgroupOf_eq_of_le hB.1, Subgroup.map_bot] at hmap


theorem exists_eq_rationalComponent_of_isComponentOf
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {J : Subgroup (ModGL τ L)}
    (hJ : IsComponentOf J (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})) :
    ∃ i : KernelComponent (rootCharHom a),
      J = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hP : J ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := hJ.1
  have hperf : ⁅J, J⁆ = J := commutator_self_eq_of_commutator_top hJ.2.2.1
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  have hform := S.frob.iform_eq
  have hΓ : S.Γ ≤ adjointGroup τ L :=
    (Subgroup.commutator_le_self S.D.model).trans inf_le_left
  have hΓfix : ∀ x ∈ S.Γ, S.D.step x = x := fun x hx =>
    ((Subgroup.commutator_le_self S.D.model) hx).2
  have hPX : J ≤ toralCentralizer τ L a := fun x hx =>
    Subgroup.mem_inf.2 ⟨hΓ (Subgroup.mem_inf.1 (hP hx)).1, (Subgroup.mem_inf.1 (hP hx)).2⟩
  have hPU : J ≤ rootSpan τ L (rootCharKernel a) :=
    perfect_le_rootSpan_kernel hp a hap hPX hperf
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ L (rootCharHom a)).2.1
  haveI : Finite (Set.range (rationalRoots S.ρ (rootCharHom a))) :=
    (Set.finite_range _).to_subtype
  let A : Set.range (rationalRoots S.ρ (rootCharHom a)) → Subgroup (ModGL τ L) :=
    fun O => rootSpan τ L O.1
  have hc : ∀ O O', O ≠ O' → ∀ x ∈ A O, ∀ y ∈ A O', Commute x y := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
    exact commute_rootSpan_rationalRoots hker hform (fun h => hne (Subtype.ext h))
  have hF : ∀ O, ∀ x ∈ A O, S.D.step x ∈ A O := by
    rintro ⟨_, i, rfl⟩ x hx
    exact step_mem_rootSpan S (fun γ hγ => (rationalRoots_subset_kernelRoots hker i hγ).1)
      (rationalRoots_mapsTo i) hx
  have hU : ⨆ O, A O = rootSpan τ L (rootCharKernel a) := by
    refine le_antisymm (iSup_le fun O => ?_) ?_
    · obtain ⟨_, i, rfl⟩ := O
      exact rootSpan_mono (rationalRoots_subset_kernelRoots hker i)
    · refine le_trans (iSup_componentRootSpan L (χ := rootCharHom a)).ge (iSup_le fun i => ?_)
      have h : componentRootSpan L (rootCharHom a) i ≤ A ⟨_, i, rfl⟩ :=
        rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩
      exact h.trans (le_iSup A ⟨_, i, rfl⟩)
  have hAadj : ∀ O, A O ≤ adjointGroup τ L := fun O => rootSpan_le_adjointGroup L O.1
  have h1' := perfect_le_iSup_inf_fixed S.D.step A hc hF hperf (hPU.trans hU.ge)
    fun x hx => hΓfix x (Subgroup.mem_inf.1 (hP hx)).1
  have hc2 : ∀ O O', O ≠ O' → ∀ x ∈ A O ⊓ S.D.step.eqLocus (MonoidHom.id _),
      ∀ y ∈ A O' ⊓ S.D.step.eqLocus (MonoidHom.id _), Commute x y :=
    fun O O' hne x hx y hy => hc O O' hne x hx.1 y hy.1
  have h2 : J ≤ ⨆ O, A O ⊓ S.Γ := by
    refine (perfect_le_iSup_commutator (fun O => A O ⊓ S.D.step.eqLocus (MonoidHom.id _)) hc2
      hperf h1').trans (iSup_mono fun O => le_inf ?_ ?_)
    · exact (Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (Subgroup.commutator_le_self _)
    · exact Subgroup.commutator_mono (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
        (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
  have hc3 : ∀ O O', O ≠ O' → ∀ x ∈ A O ⊓ S.Γ, ∀ y ∈ A O' ⊓ S.Γ, Commute x y :=
    fun O O' hne x hx y hy => hc O O' hne x hx.1 y hy.1
  have h3 := perfect_le_iSup_commutator (fun O => A O ⊓ S.Γ) hc3 hperf h2
  have hc4 : ∀ O O', O ≠ O' → ∀ x ∈ ⁅A O ⊓ S.Γ, A O ⊓ S.Γ⁆, ∀ y ∈ ⁅A O' ⊓ S.Γ, A O' ⊓ S.Γ⁆,
      Commute x y := fun O O' hne x hx y hy =>
    hc3 O O' hne x (Subgroup.commutator_le_self _ hx) y (Subgroup.commutator_le_self _ hy)
  have h4 := perfect_le_iSup_of_solvable (fun O => ⁅A O ⊓ S.Γ, A O ⊓ S.Γ⁆) hc4
    (fun O => CFSG.IsQuasisimple ↥⁅A O ⊓ S.Γ, A O ⊓ S.Γ⁆)
    (fun O hO => Subgroup.isPerfect_iff.mp hO.1)
    (by
      rintro ⟨_, i, rfl⟩ hO
      exact (hTame i).resolve_left hO)
    hperf h3
  haveI : Finite ↥(S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
    have := S.finite
    have hle : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ≤ S.D.model :=
      inf_le_left.trans (Subgroup.commutator_le_self S.D.model)
    exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  by_contra hne
  push Not at hne
  have hcent : (⨆ O, ⨆ (_ : CFSG.IsQuasisimple ↥⁅A O ⊓ S.Γ, A O ⊓ S.Γ⁆),
      ⁅A O ⊓ S.Γ, A O ⊓ S.Γ⁆) ≤ Subgroup.centralizer (J : Set (ModGL τ L)) := by
    refine iSup_le fun O => iSup_le fun hO => ?_
    obtain ⟨_, i, rfl⟩ := O
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
    obtain ⟨hperfO, hsimpO, hncO⟩ := hO
    have hcomp : IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) :=
      ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub,
        ⟨hperfO.commutator_eq_top, hsimpO⟩⟩
    by_cases h : J = rationalComponent S.ρ S.Γ (rootCharHom a) i
    · exact absurd ⟨hperfO, hsimpO, hncO⟩ (hne i h)
    · have h' := commutator_eq_bot_of_isComponentOf_ne_of_finite hJ hcomp h
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h'
      exact (Subgroup.le_centralizer_iff).1 h'
  exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hJ.2.2
    (h4.trans hcent)

theorem eq_rationalComponent_of_isComponentOf_of_le_rationalSpan
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {J : Subgroup (ModGL τ L)}
    (hJ : IsComponentOf J (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}))
    (hle : J ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i)
    (hRi : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    J = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hperf : ⁅J, J⁆ = J := commutator_self_eq_of_commutator_top hJ.2.2.1
  have hJR : J ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [← hperf]
    exact Subgroup.commutator_mono hle hle
  have hRq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    hRi.resolve_right fun hs =>
      CFSG.LocalAnalysis.ComponentInitial.not_le_of_isQuasisimple_of_isSolvable hJ.2.2 hs hJR
  obtain ⟨hRle, hRsub⟩ := langSubnormal_of_mem_torus S hT i
  have hRcomp : IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) :=
    ⟨hRle, (CFSG.Open.IsSubnormal.iff_subgroupOf hRle).2 hRsub,
      ⟨hRq.1.commutator_eq_top, hRq.2.1⟩⟩
  haveI : Finite ↥(S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
    have := S.finite
    have hmodel : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ≤ S.D.model :=
      inf_le_left.trans (Subgroup.commutator_le_self S.D.model)
    exact Finite.of_injective (Subgroup.inclusion hmodel) (Subgroup.inclusion_injective hmodel)
  refine ⟨?_, hRq⟩
  by_contra hne
  have hc := commutator_eq_bot_of_isComponentOf_ne_of_finite hJ hRcomp hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  have hRcent := (Subgroup.le_centralizer_iff).1 hc
  exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple
    hJ.2.2 (hJR.trans hRcent)

end CFSG.HardMathSupport.Timmesfeld.LangTorus
