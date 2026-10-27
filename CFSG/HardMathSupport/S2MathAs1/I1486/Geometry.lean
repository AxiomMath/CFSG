module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharCentralizer
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.GroupActions.SubgroupStabilizerOuterBound

public section

namespace CFSG.HardMathSupport.S2MathAs1.I1486

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.GroupActions

theorem f4_toral_centralizer_le_rootGroup
    {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin Tag.F4.rank → Lˣ}
    (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit Tag.F4 a ≠ 1) :
    toralCentralizer Tag.F4 L a ≤
      torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (kernelRoots (rootCharHom a)) := by
  have ha1 : a ≠ 1 := fun h => h1 (by rw [h, rootDiagUnit_one])
  have h3le : 3 ≤ p := by have := hp.two_le; omega
  by_cases hp3 : p = 3
  · subst hp3
    rw [CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_F4_three
      L a hap]
    exact le_of_eq rfl
  · have h3p : 3 < p := by omega
    have hker : rootCharKernel a ⊆ kernelRoots (rootCharHom a) := fun α hα => hα
    have hneg : ∀ α ∈ kernelRoots (rootCharHom a), -α ∈ kernelRoots (rootCharHom a) := by
      intro α hα
      refine ⟨IsRoot.neg hα.1, ?_⟩
      have hα2 : rootChar a α = 1 := hα.2
      show rootChar a (-α) = 1
      rw [show (-α : Fin Tag.F4.rank → ℤ) = 0 - α by simp, rootChar_sub, rootChar_zero,
        one_mul, hα2, inv_one]
    exact CFSG.RankThree.PartOne.KE.toralCentralizer_le_sup_rootSpan_of_stab
      (CFSG.RankThree.PartOne.KE.rootCharStabilizer_subset_closure hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp h3p) hap ha1)
      (fun α hα => hα.1) hneg hker

theorem conj_mem_rationalComponent_of_mem_sup_rootSpan
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y) (r : ModGL τ L)
    (hr : r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    y * r * y⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hker : ∀ γ ∈ kernelRoots (rootCharHom a), S.ρ γ ∈ kernelRoots (rootCharHom a) := by
    rintro γ ⟨hγ, h⟩
    refine ⟨(S.frob.isRoot_iff γ).2 hγ, ?_⟩
    have h' : rootChar a γ = 1 := h
    show rootChar a (S.ρ γ) = 1
    rw [S.frob.rootChar_eq a hT γ hγ, h', one_pow]
  have hΨ : rationalRoots S.ρ (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) :=
    rationalRoots_subset_kernelRoots hker i
  have hcl : ∀ γ (hγ : γ ∈ rationalRoots S.ρ (rootCharHom a) i) β
      (hβ : β ∈ kernelRoots (rootCharHom a)),
      (⟦⟨β, hβ⟩⟧ : KernelComponent (rootCharHom a)) = ⟦⟨γ, hΨ hγ⟩⟧ →
        β ∈ rationalRoots S.ρ (rootCharHom a) i :=
    fun γ hγ β hβ h => rationalRoots_closed hker S.frob.iform_eq i hγ hβ h
  have hroot : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, IsRoot τ γ :=
    fun γ hγ => (hΨ hγ).1
  have hN : torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) ≤
      Subgroup.normalizer (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) :
        Set (ModGL τ L)) :=
    sup_le (CFSG.Quasithin.SmithCurtis.Chev.torusGroup_le_normalizer_rootSpan _ hroot)
      (rootSpan_le_normalizer_of_closed hΨ hcl)
  have hyAdj : y ∈ adjointGroup τ L :=
    (sup_le ((Subgroup.closure_le _).2 (by
        rintro _ ⟨⟨j, t⟩, rfl⟩
        exact torusElt_mem_adjointGroup j t))
      (rootSpan_le_adjointGroup L (kernelRoots (rootCharHom a)))) hyZ
  have hyM : y ∈ S.D.model := ⟨hyAdj, hyF⟩
  let φ : ModGL τ L →* ModGL τ L := (MulAut.conj y).toMonoidHom
  have hφ : ∀ g, φ g = y * g * y⁻¹ := fun g => rfl
  have hM : S.D.model.map φ ≤ S.D.model := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hφ]
    exact mul_mem (mul_mem hyM hg) (inv_mem hyM)
  have hΓ : S.Γ.map φ ≤ S.Γ := by
    have h1 : (⁅S.D.model, S.D.model⁆).map φ ≤ ⁅S.D.model, S.D.model⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hM hM
    exact h1
  have hS : (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i)).map φ ≤
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hφ]
    exact (Subgroup.mem_normalizer_iff.1 (hN hyZ) g).1 hg
  have hrs : (rationalSpan S.ρ S.Γ (rootCharHom a) i).map φ ≤
      rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    (Subgroup.map_inf_le _ _ _).trans (inf_le_inf hS hΓ)
  have hcomp : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map φ ≤
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    unfold rationalComponent
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hrs hrs
  exact hcomp ⟨r, hr, rfl⟩

theorem conj_mem_subgroupStabAut_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y) :
    MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hyZ' : y⁻¹ ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) := inv_mem hyZ
  have hyF' : S.D.step y⁻¹ = y⁻¹ := by rw [map_inv, hyF]
  have h1 : ∀ r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      y * r * y⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    fun r hr => conj_mem_rationalComponent_of_mem_sup_rootSpan S hT i hyZ hyF r hr
  have h2 : ∀ r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      y⁻¹ * r * y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    fun r hr => conj_mem_rationalComponent_of_mem_sup_rootSpan S hT i hyZ' hyF' r hr
  change (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj y).toMonoidHom =
    rationalComponent S.ρ S.Γ (rootCharHom a) i
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    simpa using h1 r hr
  · intro r hr
    exact ⟨y⁻¹ * r * y, h2 r hr, by change y * (y⁻¹ * r * y) * y⁻¹ = r; group⟩

end CFSG.HardMathSupport.S2MathAs1.I1486

end
