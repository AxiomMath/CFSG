module

public import CFSG.LargeExtraspecial.S9Mod
public import CFSG.LargeExtraspecial.S9RACover
public import CFSG.LargeExtraspecial.S2SpC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))

theorem exists_cover_of_finrank_two (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hdim : finrank (ZMod 2) V = 4) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hD : SpRadDecomp ρ ⊥ ⊤ p p₁) {U : Submodule (ZMod 2) M}
    (hUfix : U ≤ fixOf ρ (spPointRadical f p : Set (V ≃ₗ[ZMod 2] V)))
    (hU2 : finrank (ZMod 2) U = 2)
    (hUinv : ∀ e : TauCeti.BilinForm.isometryGroup f, (e : V ≃ₗ[ZMod 2] V) p = p →
      ∀ u ∈ U, ρ e u ∈ U) :
    ∃ Z : Submodule (ZMod 2) M, U ≤ Z ∧ (∀ e, ∀ z ∈ Z, ρ e z ∈ Z) ∧
      ∀ z ∈ Z, ∃ e : TauCeti.BilinForm.isometryGroup f, z ∈ U.map (ρ e : M →ₗ[ZMod 2] M) := by
  have hbot : (⊥ : Submodule (ZMod 2) V) ⊓ spPerp f ⊥ = ⊥ := bot_inf_eq _
  have hperp : ∀ c : V, c ∈ spPerp f ⊥ := fun c => by rw [spPerp_bot]; exact Submodule.mem_top
  have hdim' : finrank (ZMod 2) (spPerp f (⊥ : Submodule (ZMod 2) V)) = 2 * 2 := by
    rw [spPerp_bot, finrank_top, hdim]
  have hdim'' : finrank (ZMod 2) V = 2 * 2 := by rw [hdim]
  obtain ⟨hp0, hp₁0, -⟩ :=
    linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  have hN : SpInvariant ρ ⊥ (⊤ : Submodule (ZMod 2) M) := fun _ _ _ _ => Submodule.mem_top
  have hg' := exists_mem_spRadGen_apply_eq hf hnd hbot (hperp p) (hperp p₁) hp0 hp₁0
  obtain ⟨g₀, hg₀, hg₀p⟩ := hg'
  have hg₀S := spRadGen_le_spFix (⊥ : Submodule (ZMod 2) V) hg₀
  set g : TauCeti.BilinForm.isometryGroup f := ⟨g₀, hg₀S.1⟩ with hgdef
  set Z := U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M) with hZdef
  have hUW : U ≤ ⊤ ⊓ fixOf ρ (spRadFix f ⊥ p : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [spRadFix_bot]
    exact le_inf le_top hUfix
  have hZinv : ∀ e : TauCeti.BilinForm.isometryGroup f, ∀ z ∈ Z, ρ e z ∈ Z := fun e =>
    sp_timmesfeld_2_1_c ρ hf hnd hbot hdim' hN (hperp p) (hperp p₁) hpp₁ hD hUW
      (fun e' _ he' u hu => hUinv e' he' u hu) g hg₀S.2 hg₀p e (by rw [fixGroup_bot]; trivial)
  refine ⟨Z, le_sup_left, hZinv, ?_⟩
  have hZD := spRadDecomp_of_invariant ρ hf hnd hdim'' hpp₁ hD hZinv
  have hZsp : SpInvariant ρ ⊥ Z := fun e _ z hz => hZinv e z hz
  have hZ4 : finrank (ZMod 2) Z = 4 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (U.map (ρ g : M →ₗ[ZMod 2] M))
    have h2 : U ⊓ U.map (ρ g : M →ₗ[ZMod 2] M) = ⊥ := by
      have hmapg := map_inf_fixOf_spRadFix ρ hf hnd
        (fun _ _ _ _ => Submodule.mem_top : SpInvariant ρ ⊥ (⊤ : Submodule (ZMod 2) M))
        g hg₀S.2 (hperp p) hp0
      have hD2 := hD.2
      rw [eq_bot_iff]
      rintro m ⟨hmU, hmUg⟩
      have h3 : m ∈ (⊤ ⊓ fixOf ρ (spRadFix f ⊥ p : Set (V ≃ₗ[ZMod 2] V))) ⊓
          (⊤ ⊓ fixOf ρ (spRadFix f ⊥ p₁ : Set (V ≃ₗ[ZMod 2] V))) := by
        refine ⟨hUW hmU, ?_⟩
        have : (g : V ≃ₗ[ZMod 2] V) p = p₁ := hg₀p
        rw [← this, ← hmapg]
        exact Submodule.map_mono hUW hmUg
      rwa [hD2] at h3
    rw [h2, finrank_bot, add_zero, LinearEquiv.finrank_map_eq, hU2] at h1
    exact h1
  have hp2 := (sp_finrank_eq_two_mul ρ hf hnd hbot hZsp (hperp p) (hperp p₁) hpp₁ hZD).2
  have hUeq : U = Z ⊓ fixOf ρ (spRadFix f ⊥ p : Set (V ≃ₗ[ZMod 2] V)) := by
    refine Submodule.eq_of_le_of_finrank_eq (le_inf le_sup_left ?_) ?_
    · rw [spRadFix_bot]; exact hUfix
    · omega
  have hDc : ∀ c : V, c ≠ 0 → ∃ e : TauCeti.BilinForm.isometryGroup f,
      Z ⊓ fixOf ρ (spRadFix f ⊥ c : Set (V ≃ₗ[ZMod 2] V)) = U.map (ρ e : M →ₗ[ZMod 2] M) := by
    intro c hc
    have he' := exists_mem_spRadGen_apply_eq hf hnd hbot (hperp p) (hperp c) hp0 hc
    obtain ⟨e₀, he₀, he₀p⟩ := he'
    have he₀S := spRadGen_le_spFix (⊥ : Submodule (ZMod 2) V) he₀
    refine ⟨⟨e₀, he₀S.1⟩, ?_⟩
    have hmap := map_inf_fixOf_spRadFix ρ hf hnd hZsp ⟨e₀, he₀S.1⟩ he₀S.2 (hperp p) hp0
    rw [hUeq, hmap, he₀p]
  have hcov := exists_mem_of_cover hnd hdim (Z := ↥Z) hZ4
    (fun c => (Z ⊓ fixOf ρ (spRadFix f ⊥ c : Set (V ≃ₗ[ZMod 2] V))).comap Z.subtype)
    (fun c hc => by
      obtain ⟨e, he⟩ := hDc c hc
      rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left), he,
        LinearEquiv.finrank_map_eq, hU2])
    (fun c c' hcc' => by
      obtain ⟨hc0, hc'0, -⟩ :=
        linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hcc')
      have hD' := spRadDecomp_of_pair ρ hf hnd hbot hZsp (hperp p) (hperp p₁) (hperp c)
        (hperp c') hpp₁ hcc' hZD
      rw [← Submodule.comap_inf, hD'.2, Submodule.comap_bot, Submodule.ker_subtype])
  intro z hz
  obtain ⟨c, hc0, hcz⟩ := hcov ⟨z, hz⟩
  obtain ⟨e, he⟩ := hDc c hc0
  refine ⟨e, ?_⟩
  rw [← he]
  exact hcz

end CFSG.LargeExtraspecial.S9
