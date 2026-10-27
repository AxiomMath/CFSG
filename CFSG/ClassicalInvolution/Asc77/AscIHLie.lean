module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzy
public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ComponentClassification

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def omegaGen (Ω : Set (Subgroup G)) : Subgroup G := ⨆ L ∈ Ω, L

theorem le_omegaGen {Ω : Set (Subgroup G)} {L : Subgroup G} (hL : L ∈ Ω) : L ≤ omegaGen Ω :=
  le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ Ω) => L) L hL

theorem omegaGen_normal {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) :
    (omegaGen Ω).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have h1 : conjSub g (omegaGen Ω) ≤ omegaGen Ω := by
    unfold omegaGen conjSub
    rw [Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    exact le_omegaGen (hΩ g L hL)
  exact h1 (conj_mem_conjSub hx)

theorem oddCore_normal_eq_bot [Finite G] (N : Subgroup G) [N.Normal]
    (hO : classicalInvolutionOddCore G = ⊥) : classicalInvolutionOddCore N = ⊥ := by
  have h := OddCore.normal_intersection G N
  have h2 : (classicalInvolutionOddCore N).map N.subtype = ⊥ := by
    rw [show classicalInvolutionOddCore N = componentClassificationOddCore N from rfl, h,
      show componentClassificationOddCore G = classicalInvolutionOddCore G from rfl, hO]
    simp
  exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h2

theorem inClass_restrict_omegaGen {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω)
    (hne : Ω.Nonempty) : InClass p f (restrictFamily Ω (omegaGen Ω)) := by
  refine inClass_of_isClassicalMemberIn hne (fun L hL => le_omegaGen hL)
    (fun n _ L hL => hΩ.conjInvariant n L hL) rfl ?_
  intro L hL
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  have hsec : IsSectionMember p f (omegaGen Ω) L z :=
    { le := le_omegaGen hL
      orderOf_eq_two := hz.orderOf_eq_two
      mem := hz.mem
      perfect := hz.perfect
      subnormal := by
        have := isSubnormal_inf hz.subnormal (omegaGen Ω)
        rwa [inf_eq_left.mpr (le_omegaGen hL)] at this
      nonempty_equiv := hz.nonempty_equiv }
  exact ⟨z, hsec.toIn⟩

variable (p f) in
structure OmegaLie (Ω : Set (Subgroup G)) where
  card : ℕ
  tag : Fin card → CFSG.Assembly.LowTwoRank.StatedLieTag
  rank : Fin card → ℕ
  exp : Fin card → ℕ
  hom : ∀ i, (modelUniv (tag i) (rank i) p (exp i) Fact.out).K →* G
  isFundTag : ∀ i, IsFundTag (tag i)
  admissible : ∀ i, CFSG.Assembly.LowTwoRank.StatedLieAdmissible (tag i) (rank i) p (exp i)
  exp_eq : ∀ i, exp i = f ∨ (tag i = .trialityD4 ∧ 3 * exp i = f)
  ker_le_center : ∀ i, (hom i).ker ≤ Subgroup.center _
  commute : ∀ i j, i ≠ j → ∀ x y, hom i x * hom j y = hom j y * hom i x
  generate : ⨆ i, (hom i).range = omegaGen Ω
  fundamental : ∀ L ∈ Ω, ∃ i, ∃ R ∈ fundamentalSubgroups (tag i)
    (modelUniv (tag i) (rank i) p (exp i) Fact.out).D, L = R.map (hom i)
  meets : ∀ i, ∃ R ∈ fundamentalSubgroups (tag i)
    (modelUniv (tag i) (rank i) p (exp i) Fact.out).D, R.map (hom i) ∈ Ω

theorem exists_omegaLie [Finite G] {n : ℕ} (hn : CITBelowU p f n) {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaMod p f Ω) (hne : Ω.Nonempty) (hO : classicalInvolutionOddCore G = ⊥)
    (hlt : Nat.card G < n) : Nonempty (OmegaLie p f Ω) := by
  set Y := omegaGen Ω with hY
  have : Y.Normal := omegaGen_normal hΩ.conjInvariant
  have hYO : classicalInvolutionOddCore ↥Y = ⊥ := oddCore_normal_eq_bot Y hO
  have hcard : Nat.card ↥Y < n := lt_of_le_of_lt (Subgroup.card_le_card_group Y) hlt
  have hLS : LieSystemMod p f (restrictFamily Ω Y) :=
    hn ↥Y hcard _ (inClass_restrict_omegaGen hΩ hne)
  obtain ⟨D⟩ := hLS
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
  refine ⟨{ card := D.card
            tag := D.tag
            rank := D.rank
            exp := D.exp
            hom := fun i => g.comp (D.hom i)
            isFundTag := D.isFundTag
            admissible := D.admissible
            exp_eq := D.exp_eq
            ker_le_center := ?_
            commute := ?_
            generate := ?_
            fundamental := ?_
            meets := ?_ }⟩
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

namespace OmegaLie

variable {Ω : Set (Subgroup G)} (D : OmegaLie p f Ω)

noncomputable abbrev model (i : Fin D.card) : CFSG.LieType.Universal.LieUniversal :=
  modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out

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

end OmegaLie

end CFSG.ClassicalInvolution.Asc77
