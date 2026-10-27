module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MICore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Assembly (LargeEvenInduces LargeEvenMarking)
open CFSG.StandardType (GGOutdiagPrime)
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.PerfectAutomorphisms (hom_eq_id_of_central_displacement)

section Real

@[expose] def L154RealizedMarking {M : Type} [Group M] (R : Subgroup M) : Prop :=
  LargeEvenMarking ↥R fun _ _ _ I _ θ => ∀ φ ∈ I, ∃ w ∈ Subgroup.normalizer (R : Set M),
    LargeEvenInduces θ (fun r r' : ↥R => w * (r : M) * w⁻¹ = (r' : M)) φ

theorem l154_eq_conj_of_induces {M : Type} [Group M] {X : Subgroup M} (hX : commutator ↥X = ⊤)
    (σ : M →* M) (hσ : ∀ x ∈ X, σ x ∈ X) {R : Type} [Group R] (θ : ↥X ⧸ Subgroup.center ↥X ≃* R)
    {φ : MulAut R} (hind : LargeEvenInduces θ (fun x x' : ↥X => σ (x : M) = (x' : M)) φ) {w : M}
    (hw : w ∈ Subgroup.normalizer (X : Set M))
    (hwind : LargeEvenInduces θ (fun r r' : ↥X => w * (r : M) * w⁻¹ = (r' : M)) φ) :
    ∀ x ∈ X, σ x = w * x * w⁻¹ := by
  haveI : Group.IsPerfect ↥X := ⟨hX⟩
  have hw' : ∀ x ∈ X, w⁻¹ * x * w ∈ X := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hw) x).1 hx
    simpa using this
  have hwX : ∀ x ∈ X, w * x * w⁻¹ ∈ X := fun x hx => (Subgroup.mem_normalizer_iff.1 hw x).1 hx
  let f : ↥X →* ↥X :=
    { toFun := fun x => ⟨w⁻¹ * σ x * w, hw' _ (hσ x x.2)⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have hf : f = MonoidHom.id _ := by
    refine hom_eq_id_of_central_displacement f fun x => ?_
    have h1 : φ (θ (QuotientGroup.mk x)) = θ (QuotientGroup.mk ⟨σ x, hσ x x.2⟩) :=
      hind x ⟨σ x, hσ x x.2⟩ rfl
    have h2 : φ (θ (QuotientGroup.mk x)) = θ (QuotientGroup.mk ⟨w * x * w⁻¹, hwX x x.2⟩) :=
      hwind x ⟨w * x * w⁻¹, hwX x x.2⟩ rfl
    have h3 : (QuotientGroup.mk ⟨σ x, hσ x x.2⟩ : ↥X ⧸ Subgroup.center ↥X) =
        QuotientGroup.mk ⟨w * x * w⁻¹, hwX x x.2⟩ := θ.injective (h1.symm.trans h2)
    have hc := QuotientGroup.eq.1 h3
    set c : ↥X := (⟨σ x, hσ x x.2⟩ : ↥X)⁻¹ * ⟨w * x * w⁻¹, hwX x x.2⟩ with hcdef
    have hcent : ∀ g : ↥X, g * c⁻¹ = c⁻¹ * g := fun g =>
      (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hc)) g
    rw [Subgroup.mem_center_iff]
    intro g
    have hg' := hcent ⟨w * g * w⁻¹, hwX g g.2⟩
    apply Subtype.ext
    have e1 : ((c⁻¹ : ↥X) : M) = w * (x : M)⁻¹ * w⁻¹ * σ x := by
      simp [hcdef, mul_assoc]
    have e2 := congrArg Subtype.val hg'
    simp only [Subgroup.coe_mul] at e2
    rw [e1] at e2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.coe_mk, OneHom.coe_mk, f]
    have e3 : (g : M) * ((x : M)⁻¹ * (w⁻¹ * σ x * w)) =
        w⁻¹ * ((w * g * w⁻¹) * (w * (x : M)⁻¹ * w⁻¹ * σ x)) * w := by group
    have e4 : (x : M)⁻¹ * (w⁻¹ * σ x * w) * g =
        w⁻¹ * ((w * (x : M)⁻¹ * w⁻¹ * σ x) * (w * g * w⁻¹)) * w := by group
    rw [e3, e4, e2]
  intro x hx
  have h0 := congrArg Subtype.val (DFunLike.congr_fun hf ⟨x, hx⟩)
  have h' : w⁻¹ * σ x * w = x := h0
  calc σ x = w * (w⁻¹ * σ x * w) * w⁻¹ := by group
    _ = w * x * w⁻¹ := by rw [h']

end Real

section Classes


abbrev L154TypeAClass {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) : Prop :=
  2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
    (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)

abbrev L154E6Class {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) : Prop :=
  compRank (componentRoots (rootCharHom a) i) = 6 ∧ (componentRoots (rootCharHom a) i).ncard = 72

@[expose] def L154RealTypeA : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (p : ℕ) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    p.Prime → p ≠ 2 → rootDiagUnit τ a ∈ S.D.torus → (∀ k, a k ^ p = 1) →
    rootDiagUnit τ a ≠ 1 → CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    L154TypeAClass a i → L154RealizedMarking (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def L154RealE6 : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (p : ℕ) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    p.Prime → p ≠ 2 → rootDiagUnit τ a ∈ S.D.torus → (∀ k, a k ^ p = 1) →
    rootDiagUnit τ a ≠ 1 → CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    L154E6Class a i → L154RealizedMarking (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def L154NonCfgOutdiag : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (p : ℕ) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    p.Prime → p ≠ 2 → rootDiagUnit τ a ∈ S.D.torus → (∀ k, a k ^ p = 1) →
    rootDiagUnit τ a ≠ 1 → CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    ¬ L154TypeAClass a i → ¬ L154E6Class a i →
    LargeEvenMarking ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (fun _ R' _ I _ _ => GGOutdiagPrime p R' I)

end Classes

section Assembly


theorem l154_conj_of_realized {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (R : FrobRoot S.D p) {a : Fin τ.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)}
    (hstab : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hM : LargeEvenMarking ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (fun x x' => R.step0 (x : ModGL τ L) = (x' : ModGL τ L)) φ)
    (hreal : L154RealizedMarking (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ z : ModGL τ L, ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 x = z * x * z⁻¹ := by
  have h := MI.marking_transport _ hM hreal
  obtain ⟨hperf, lab, -, hraw⟩ := h
  obtain ⟨R', _, I, F, -, -, θ, hall, φ, hφ, hind⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨w, hw, hwind⟩ := hall φ hφ
  exact ⟨w, l154_eq_conj_of_induces hperf R.step0 hstab θ hind hw hwind⟩

theorem l154_conj_of_outdiagMarking {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (R : FrobRoot S.D p) {a : Fin τ.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)}
    (hstab : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hM : LargeEvenMarking ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (fun x x' => R.step0 (x : ModGL τ L) = (x' : ModGL τ L)) φ)
    (hout : LargeEvenMarking ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (fun _ R' _ I _ _ => GGOutdiagPrime p R' I)) :
    ∃ z : ModGL τ L, ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 x = z * x * z⁻¹ := by
  obtain ⟨z, -, hz⟩ := l154_lang_exists_conj S R hstab (MI.marking_transport _ hM hout)
  exact ⟨z, hz⟩

theorem l154LangInnRes_of_real (hA : L154RealTypeA) (hE : L154RealE6)
    (hN : L154NonCfgOutdiag) : L154LangInnRes := by
  intro τ L _ _ _ p₀ S p R a i hp hp2 hT hap ha1 _ hqi hstab hM
  have hM' := CFSG.StandardType.Canonical.largeEvenMarking_mono
    (P' := fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ
      (fun x x' : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) =>
        R.step0 (x : ModGL τ L) = (x' : ModGL τ L)) φ)
    (by
      intro _ _ _ _ _ _ h
      exact h.2) hM
  by_cases hAc : L154TypeAClass a i
  · exact l154_conj_of_realized S R hstab hM' (hA τ L p₀ S p a i hp hp2 hT hap ha1 hqi hAc)
  by_cases hEc : L154E6Class a i
  · exact l154_conj_of_realized S R hstab hM' (hE τ L p₀ S p a i hp hp2 hT hap ha1 hqi hEc)
  exact l154_conj_of_outdiagMarking S R hstab hM'
    (hN τ L p₀ S p a i hp hp2 hT hap ha1 hqi hAc hEc)

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
