module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

open scoped Matrix


theorem exc3core_rho_inv {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (SL : LangSetup τ L 5)
    {a : Fin τ.rank → Lˣ} {e : ℕ} (hq : SL.D.q = 2 ^ e) (h3 : 3 ∣ 2 ^ e + 1)
    (hT : rootDiagUnit τ a ∈ SL.D.torus) (hap : ∀ m, a m ^ 3 = 1) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    rootCharHom a (Multiplicative.ofAdd (SL.ρ γ)) = (rootCharHom a (Multiplicative.ofAdd γ))⁻¹ := by
  have hxq : rootChar a (SL.ρ γ) = (rootChar a γ)⁻¹ := by
    rw [SL.frob.rootChar_eq a hT γ hγ, hq]
    have hx3 : rootChar a γ ^ 3 = 1 :=
      CFSG.RankThree.PartOne.KE.CTTorus.rootChar_pow_eq_one hap γ
    obtain ⟨k, hk⟩ := h3
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_succ', hk, pow_mul, hx3, one_pow]
  simpa [rootCharHom] using hxq

private lemma exc3core_orbit_one_aux1 {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {F : kernelRoots χ → kernelRoots χ}
    (hF : ∀ x y : kernelRoots χ,
      x.1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ y.1) ≠ 0 →
      (F x).1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ (F y).1) ≠ 0)
    {x y : kernelRoots χ} :
    Relation.EqvGen (fun a b : kernelRoots χ =>
      a.1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ b.1) ≠ 0) x y →
    Relation.EqvGen (fun a b : kernelRoots χ =>
      a.1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ b.1) ≠ 0) (F x) (F y) := by
  intro h
  induction h with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (hF a b hab)
  | refl => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private lemma exc3core_orbit_one_aux2 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ}
    (h1 : ∀ γ, IsRoot τ γ →
      rootCharHom a (Multiplicative.ofAdd (SL.ρ γ)) =
        (rootCharHom a (Multiplicative.ofAdd γ))⁻¹) :
    ∃ (f0 g0 : kernelRoots (rootCharHom a) → kernelRoots (rootCharHom a)),
      (∀ x, (f0 x).1 = SL.ρ x.1) ∧ (∀ x, (g0 x).1 = SL.ρ.symm x.1) ∧
      (∀ x, (g0 (f0 x)).1 = x.1) ∧
      (∀ x y, x.1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ y.1) ≠ 0 →
        (f0 x).1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ (f0 y).1) ≠ 0) ∧
      (∀ x y, x.1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ y.1) ≠ 0 →
        (g0 x).1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ (g0 y).1) ≠ 0) := by
  let f0 : kernelRoots (rootCharHom a) → kernelRoots (rootCharHom a) := fun x =>
    ⟨SL.ρ x.1, (SL.frob.isRoot_iff x.1).mpr x.2.1,
      by rw [h1 x.1 x.2.1, x.2.2, inv_one]⟩
  let g0 : kernelRoots (rootCharHom a) → kernelRoots (rootCharHom a) := fun x =>
    let hx : IsRoot τ (SL.ρ.symm x.1) :=
      (SL.frob.isRoot_iff (SL.ρ.symm x.1)).mp (by rw [Equiv.apply_symm_apply]; exact x.2.1)
    ⟨SL.ρ.symm x.1, hx, by
      have h := h1 (SL.ρ.symm x.1) hx
      rw [Equiv.apply_symm_apply, x.2.2] at h
      exact inv_eq_one.mp h.symm⟩
  have hf0 : ∀ x, (f0 x).1 = SL.ρ x.1 := fun x => rfl
  have hg0 : ∀ x, (g0 x).1 = SL.ρ.symm x.1 := fun x => rfl
  have hgf : ∀ x, (g0 (f0 x)).1 = x.1 := fun x => Equiv.symm_apply_apply SL.ρ x.1
  have hrel_f : ∀ x y, x.1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ y.1) ≠ 0 →
      (f0 x).1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ (f0 y).1) ≠ 0 := by
    intro x y hxy
    rw [dotProduct_mulVec_eq_iform] at hxy
    rw [dotProduct_mulVec_eq_iform]
    rwa [SL.frob.iform_eq]
  have hrel_g : ∀ x y, x.1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ y.1) ≠ 0 →
      (g0 x).1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ (g0 y).1) ≠ 0 := by
    intro x y hxy
    rw [dotProduct_mulVec_eq_iform] at hxy
    rw [dotProduct_mulVec_eq_iform]
    have h := SL.frob.iform_eq (SL.ρ.symm x.1) (SL.ρ.symm y.1)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rwa [← h]
  exact ⟨f0, g0, hf0, hg0, hgf, hrel_f, hrel_g⟩

private lemma exc3core_orbit_one_aux3 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ}
    {f0 g0 : kernelRoots (rootCharHom a) → kernelRoots (rootCharHom a)}
    (hf0 : ∀ x, (f0 x).1 = SL.ρ x.1) (hg0 : ∀ x, (g0 x).1 = SL.ρ.symm x.1)
    (hgf : ∀ x, (g0 (f0 x)).1 = x.1)
    (hrel_f : ∀ x y, x.1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ y.1) ≠ 0 →
      (f0 x).1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ (f0 y).1) ≠ 0)
    (hrel_g : ∀ x y, x.1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ y.1) ≠ 0 →
      (g0 x).1 ⬝ᵥ (τ.symmetrizedCartan *ᵥ (g0 y).1) ≠ 0)
    (i : KernelComponent (rootCharHom a)) :
    ∃ j : KernelComponent (rootCharHom a),
      (SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) j := by
  let x0 : kernelRoots (rootCharHom a) := Quotient.out i
  have hx0 : (⟦x0⟧ : KernelComponent (rootCharHom a)) = i := Quotient.out_eq i
  refine ⟨⟦f0 x0⟧, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨hxK, hxi⟩ := hx
    have hxx0 := Quotient.exact (hxi.trans hx0.symm)
    have hstep := exc3core_orbit_one_aux1 (F := f0) hrel_f hxx0
    refine ⟨hf0 ⟨x, hxK⟩ ▸ (f0 ⟨x, hxK⟩).2, ?_⟩
    have hsub : (⟨SL.ρ x, hf0 ⟨x, hxK⟩ ▸ (f0 ⟨x, hxK⟩).2⟩ :
        kernelRoots (rootCharHom a)) = f0 ⟨x, hxK⟩ := Subtype.ext (hf0 ⟨x, hxK⟩).symm
    rw [hsub]
    exact Quotient.sound hstep
  · intro y hy
    obtain ⟨hyK, hyi⟩ := hy
    have hy0 := Quotient.exact hyi
    have hstep := exc3core_orbit_one_aux1 (F := g0) hrel_g hy0
    have hgx0 : g0 (f0 x0) = x0 := Subtype.ext (hgf x0)
    rw [hgx0] at hstep
    have hg : (⟦g0 ⟨y, hyK⟩⟧ : KernelComponent (rootCharHom a)) = i :=
      (Quotient.sound hstep).trans hx0
    refine ⟨SL.ρ.symm y, ?_, Equiv.apply_symm_apply SL.ρ y⟩
    refine ⟨hg0 ⟨y, hyK⟩ ▸ (g0 ⟨y, hyK⟩).2, ?_⟩
    have hsub : (⟨SL.ρ.symm y, hg0 ⟨y, hyK⟩ ▸ (g0 ⟨y, hyK⟩).2⟩ :
        kernelRoots (rootCharHom a)) = g0 ⟨y, hyK⟩ := Subtype.ext (hg0 ⟨y, hyK⟩).symm
    rw [hsub]
    exact hg

theorem exc3core_orbit_one {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (SL : LangSetup τ L 5)
    {a : Fin τ.rank → Lˣ} {e : ℕ} (hq : SL.D.q = 2 ^ e) (h3 : 3 ∣ 2 ^ e + 1)
    (hT : rootDiagUnit τ a ∈ SL.D.torus) (hap : ∀ m, a m ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (huniq : ∀ i' : KernelComponent (rootCharHom a),
      (componentRoots (rootCharHom a) i').ncard = (componentRoots (rootCharHom a) i).ncard → i' = i) :
    ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i) ∧
      componentOrbitLength SL.ρ (componentRoots (rootCharHom a) i) = 1 := by
  classical
  obtain ⟨f0, g0, hf0, hg0, hgf, hrel_f, hrel_g⟩ :=
    exc3core_orbit_one_aux2 SL (fun γ hγ => exc3core_rho_inv SL hq h3 hT hap hγ)
  obtain ⟨j, hj⟩ := exc3core_orbit_one_aux3 SL hf0 hg0 hgf hrel_f hrel_g i
  have hcard : (componentRoots (rootCharHom a) j).ncard =
      (componentRoots (rootCharHom a) i).ncard := by
    rw [← hj, Set.ncard_image_of_injective _ SL.ρ.injective]
  have hji : j = i := huniq j hcard
  have hstable : (SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) ''
      componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    rw [hj, hji]
  refine ⟨hstable, ?_⟩
  let Ψ : Set (Fin τ.rank → ℤ) := componentRoots (rootCharHom a) i
  change componentOrbitLength SL.ρ Ψ = 1
  have h1S : (1 : ℕ) ∈
      {s : ℕ | 0 < s ∧ (SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' Ψ = Ψ} := by
    refine ⟨Nat.zero_lt_one, ?_⟩
    simpa [Ψ] using hstable
  have hne : {s : ℕ | 0 < s ∧
      (SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' Ψ = Ψ}.Nonempty := ⟨1, h1S⟩
  have hmem := Nat.sInf_mem hne
  have hle : componentOrbitLength SL.ρ Ψ ≤ 1 := Nat.sInf_le h1S
  have hge : 1 ≤ componentOrbitLength SL.ρ Ψ := Nat.succ_le_of_lt hmem.1
  exact le_antisymm hle hge

private theorem exc3core_weight_match_aux1 {τ : Tag} {L : Type} [Field L]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : Ψ ⊆ kernelRoots χ) :
    ∀ β ∈ Ψ, ∀ x : Fin τ.rank → ℤ,
      χ (Multiplicative.ofAdd (rootReflection β • x)) = χ (Multiplicative.ofAdd x) := by
  intro β hβ x
  have hβroot : IsRoot τ β := (hΨ hβ).1
  have hker : χ (Multiplicative.ofAdd β) = 1 := (hΨ hβ).2
  rw [rootReflection_smul hβroot, sub_eq_add_neg, ofAdd_add, map_mul, ofAdd_neg, map_inv,
    ofAdd_zsmul, map_zpow, hker, one_zpow, inv_one, mul_one]

theorem exc3core_weight_match {τ : Tag} {L : Type} [Field L]
    (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ)
    (hroot : ∀ γ, IsRoot τ γ → IsRoot τ (σ γ))
    (hform : ∀ γ δ, CFSG.LieType.Steinberg.Adjoint.iform (σ γ) (σ δ) =
      CFSG.LieType.Steinberg.Adjoint.iform γ δ)
    (hinv : ∀ γ, IsRoot τ γ →
      χ (Multiplicative.ofAdd (σ γ)) = (χ (Multiplicative.ofAdd γ))⁻¹)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : Ψ ⊆ kernelRoots χ) (hin : twistInner Ψ σ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ γ' : Fin τ.rank → ℤ, IsRoot τ γ' ∧
      χ (Multiplicative.ofAdd γ') = (χ (Multiplicative.ofAdd γ))⁻¹ ∧
      ∀ β ∈ Ψ, CFSG.LieType.Steinberg.Adjoint.iform γ' β =
        CFSG.LieType.Steinberg.Adjoint.iform γ β := by
  rcases hin with ⟨w, hw, hσ⟩
  refine ⟨w⁻¹ • σ γ, IsRoot.smul (hroot γ hγ) w⁻¹, ?_, ?_⟩
  · have hχw : ∀ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ δ ∈ Ψ, s = rootReflection δ},
        ∀ x : Fin τ.rank → ℤ,
          χ (Multiplicative.ofAdd (u • x)) = χ (Multiplicative.ofAdd x) := by
      intro u hu
      refine Subgroup.closure_induction
        (p := fun u _ => ∀ x, χ (Multiplicative.ofAdd (u • x)) =
          χ (Multiplicative.ofAdd x)) ?_ ?_ ?_ ?_ hu
      · rintro s ⟨δ, hδ, rfl⟩ x
        exact exc3core_weight_match_aux1 χ hΨ δ hδ x
      · intro x; rw [one_smul]
      · intro u v _ _ ihu ihv x; rw [mul_smul, ihu (v • x), ihv x]
      · intro u _ ihu x
        have h := ihu (u⁻¹ • x)
        rw [smul_inv_smul] at h
        exact h.symm
    rw [hχw w⁻¹ (inv_mem hw) (σ γ)]
    exact hinv γ hγ
  · intro β hβ
    have h1 : CFSG.LieType.Steinberg.Adjoint.iform (σ γ) (σ β) =
        CFSG.LieType.Steinberg.Adjoint.iform (w⁻¹ • σ γ) β := by
      rw [← iform_smul w (w⁻¹ • σ γ) β, smul_inv_smul, (hσ β hβ).symm]
    exact h1.symm.trans (hform γ β)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
