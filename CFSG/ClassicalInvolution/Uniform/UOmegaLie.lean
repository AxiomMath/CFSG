module

public import CFSG.ClassicalInvolution.Uniform.ULieSystemIff
public import CFSG.ClassicalInvolution.Uniform.UStand

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ComponentClassification
open scoped MatrixGroups

section InClass

variable {t : MemberType} {G : Type} [Group G]

theorem inClassU_of_isClassicalMemberU_in {H : Subgroup G} {𝒮 : Set (Subgroup G)}
    (hne : 𝒮.Nonempty) (hle : ∀ L ∈ 𝒮, L ≤ H) (hconj : ∀ n ∈ H, ∀ L ∈ 𝒮, conjSub n L ∈ 𝒮)
    (hgen : (⨆ L ∈ 𝒮, L) = H)
    (hcl : ∀ L ∈ 𝒮, ∃ z, ∃ hz : z ∈ H, IsClassicalMemberU t (L.subgroupOf H) (⟨z, hz⟩ : H)) :
    InClassU t (restrictFamily 𝒮 H) where
  nonempty := by
    obtain ⟨L, hL⟩ := hne
    exact ⟨L.subgroupOf H, L, hL, hle L hL, rfl⟩
  conjInvariant := by
    rintro n _ ⟨L, hL, hLH, rfl⟩
    exact ⟨conjSub (n : G) L, hconj n n.2 L hL, hle _ (hconj n n.2 L hL),
      conjSub_subgroupOf _ n L⟩
  generated := by
    have key := iSup_subgroupOf_self (G := G) (fun i : 𝒮 => (i : Subgroup G))
    have hsup : (⨆ i : 𝒮, (i : Subgroup G)) = H := by
      rw [← hgen, iSup_subtype']
    rw [hsup] at key
    refine eq_top_iff.mpr (key.symm.le.trans ?_)
    refine iSup_le fun i => ?_
    exact le_iSup₂ (f := fun (L' : Subgroup H) (_ : L' ∈ restrictFamily 𝒮 H) => L')
      ((i : Subgroup G).subgroupOf H) ⟨i, i.2, hle i i.2, rfl⟩
  classical := by
    rintro _ ⟨L, hL, hLH, rfl⟩
    obtain ⟨z, hz, hcl'⟩ := hcl L hL
    exact ⟨⟨z, hz⟩, hcl'⟩

theorem inClassU_restrict_omegaGen {Ω : Set (Subgroup G)} (hΩ : HypOmegaModU t Ω)
    (hne : Ω.Nonempty) : InClassU t (restrictFamily Ω (omegaGen Ω)) := by
  refine inClassU_of_isClassicalMemberU_in hne (fun L hL => le_omegaGen hL)
    (fun n _ L hL => hΩ.conjInvariant n L hL) rfl ?_
  intro L hL
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  exact ⟨z, le_omegaGen hL hz.mem, hz.subgroupOf (le_omegaGen hL)⟩

end InClass

section OmegaLie

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

variable (p f) in
structure OmegaLieU (Ω : Set (Subgroup G)) where
  card : ℕ
  kind : Fin card → Q3.CompData
  valid : ∀ i, CompValid p f (kind i)
  hom : ∀ i, (kind i).G →* G
  ker_le_center : ∀ i, (hom i).ker ≤ Subgroup.center _
  commute : ∀ i j, i ≠ j → ∀ x y, hom i x * hom j y = hom j y * hom i x
  generate : ⨆ i, (hom i).range = omegaGen Ω
  fundamental : ∀ L ∈ Ω, ∃ i, ∃ R ∈ (kind i).fund, L = R.map (hom i)
  meets : ∀ i, ∃ R ∈ (kind i).fund, R.map (hom i) ∈ Ω
  card_eq : p ^ f = 3 → ∀ L ∈ Ω, Nat.card L = 24

theorem exists_omegaLieU [Finite G] {n : ℕ} (hn : CITBelowT (.sl2 p f) n)
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaModU (.sl2 p f) Ω) (hne : Ω.Nonempty)
    (hO : classicalInvolutionOddCore G = ⊥) (hlt : Nat.card G < n) :
    Nonempty (OmegaLieU p f Ω) := by
  set Y := omegaGen Ω with hY
  have : Y.Normal := omegaGen_normal hΩ.conjInvariant
  have hYO : classicalInvolutionOddCore ↥Y = ⊥ := oddCore_normal_eq_bot Y hO
  have hcard : Nat.card ↥Y < n := lt_of_le_of_lt (Subgroup.card_le_card_group Y) hlt
  have hLS : LieSystemModU (.sl2 p f) (restrictFamily Ω Y) :=
    hn ↥Y hcard _ (inClassU_restrict_omegaGen hΩ hne)
  obtain ⟨ι, hι, ⟨D₀⟩⟩ := hLS.toLieSystemU
  have := hι
  let D := D₀.reindex (Finite.equivFin ι).symm
  let ε : (↥Y ⧸ classicalInvolutionOddCore ↥Y) ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hYO).trans QuotientGroup.quotientBot
  let g : (↥Y ⧸ classicalInvolutionOddCore ↥Y) →* G := Y.subtype.comp ε.toMonoidHom
  have hginj : Function.Injective g := Y.subtype_injective.comp ε.injective
  have hgmk : ∀ L ∈ Ω, ((L.subgroupOf Y).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))).map g = L := by
    intro L hL
    rw [Subgroup.map_map]
    have : g.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) = Y.subtype := by
      ext y
      rfl
    rw [this]
    exact Subgroup.map_subgroupOf_eq_of_le (le_omegaGen hL)
  have hrange : g.range = Y := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact (ε q).2
    · intro hx
      obtain ⟨q, hq⟩ := ε.surjective ⟨x, hx⟩
      exact ⟨q, by simp [g, hq]⟩
  have hfund : ∀ L' ∈ oddQuotientFamily (restrictFamily Ω Y), ∃ L ∈ Ω, L'.map g = L := by
    rintro _ ⟨_, ⟨L, hL, -, rfl⟩, rfl⟩
    exact ⟨L, hL, hgmk L hL⟩
  refine ⟨{ card := Nat.card ι
            kind := D.kind
            valid := D.valid
            hom := fun i => g.comp (D.hom i)
            ker_le_center := ?_
            commute := ?_
            generate := ?_
            fundamental := ?_
            meets := ?_
            card_eq := ?_ }⟩
  · intro i x hx
    have : D.hom i x = 1 := hginj (by simpa using hx)
    exact D.ker_le_center i this
  · intro i j hij x y
    simp only [MonoidHom.comp_apply, ← map_mul]
    rw [D.commute i j hij x y]
  · simp only [MonoidHom.range_comp]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top, hrange]
  · intro L hL
    obtain ⟨i, R, hR, hLR⟩ := D.fundamental _ ⟨_, ⟨L, hL, le_omegaGen hL, rfl⟩, rfl⟩
    refine ⟨i, R, hR, ?_⟩
    rw [← Subgroup.map_map, ← hLR]
    exact (hgmk L hL).symm
  · intro i
    obtain ⟨R, hR, hmem⟩ := D.meets i
    obtain ⟨L, hL, hLR⟩ := hfund _ hmem
    refine ⟨R, hR, ?_⟩
    rw [Subgroup.map_map] at hLR
    simpa [Subgroup.map_map, hLR] using hL
  · intro h3 L hL
    have h1 := D.card_eq h3 _ ⟨_, ⟨L, hL, le_omegaGen hL, rfl⟩, rfl⟩
    have h2 := Subgroup.card_map_of_injective hginj
      (K := (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)))
    rw [hgmk L hL] at h2
    omega

namespace OmegaLieU

variable {Ω : Set (Subgroup G)}

variable (D : OmegaLieU p f Ω)

@[expose] noncomputable def comp (i : Fin D.card) : Subgroup G := (D.hom i).range

theorem comp_commute {i j : Fin D.card} (h : i ≠ j) : Commutes (D.comp i) (D.comp j) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact D.commute i j h a b

theorem iSup_comp : ⨆ i, D.comp i = omegaGen Ω := D.generate

theorem comp_le_omegaGen (i : Fin D.card) : D.comp i ≤ omegaGen Ω :=
  D.generate ▸ le_iSup (fun i => D.comp i) i

theorem exists_comp_of_mem {L : Subgroup G} (hL : L ∈ Ω) : ∃ i, L ≤ D.comp i := by
  obtain ⟨i, R, -, rfl⟩ := D.fundamental L hL
  exact ⟨i, Subgroup.map_le_range _ _⟩

theorem mem_comp_conj {i : Fin D.card} {g : G} (hg : g ∈ omegaGen Ω) {x : G}
    (hx : x ∈ D.comp i) : g * x * g⁻¹ ∈ D.comp i := by
  rw [← D.iSup_comp] at hg
  induction hg using Subgroup.iSup_induction' generalizing x with
  | hp k y hy =>
    by_cases hki : k = i
    · subst hki
      exact (D.comp k).mul_mem ((D.comp k).mul_mem hy hx) ((D.comp k).inv_mem hy)
    · have := D.comp_commute hki y hy x hx
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
  | h1 => simpa using hx
  | hmul a b _ _ ha hb =>
    have e : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact ha (hb hx)

end OmegaLieU

end OmegaLie

end CFSG.ClassicalInvolution.Uniform
