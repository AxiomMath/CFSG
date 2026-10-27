module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutDefs
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestClassical
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestE6
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestExc
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIsoAssembly
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)


theorem largeEvenLabelAll_inndiagComm_charTwo {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hc : markChar lab = 2)
    (htits : lab.tag ≠ .twF4der) (hD4 : ¬ (lab.tag = .D ∧ lab.rank = 4)) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  obtain ⟨tag, r, m⟩ := lab
  cases tag
  case A =>
    dsimp only [LargeEvenInLambda2] at hlab
    have hr : 1 ≤ r := hlab.2.1
    by_cases h1 : r = 1
    · subst h1
      exact largeEvenLabelAll_inndiagComm_linearTwo hlab (Or.inl ⟨rfl, rfl⟩)
    · exact largeEvenLabelAll_inndiagComm_linear (Or.inl ⟨rfl, show 2 ≤ r from by omega⟩)
  case twA =>
    dsimp only [LargeEvenInLambda2] at hlab
    exact largeEvenLabelAll_inndiagComm_unitary hlab (Or.inl rfl)
  case B =>
    dsimp only [LargeEvenInLambda2] at hlab
    have hr : 2 ≤ r := hlab.2.1
    by_cases h2 : r = 2
    · subst h2
      exact largeEvenLabelAll_inndiagComm_symplecticTwo hlab ⟨Or.inl rfl, rfl⟩
    · exact largeEvenLabelAll_inndiagComm_symplectic ⟨Or.inl rfl, show 3 ≤ r from by omega⟩
  case C =>
    dsimp only [LargeEvenInLambda2] at hlab
    have hr : 2 ≤ r := hlab.2.1
    by_cases h2 : r = 2
    · subst h2
      exact largeEvenLabelAll_inndiagComm_symplecticTwo hlab ⟨Or.inr rfl, rfl⟩
    · exact largeEvenLabelAll_inndiagComm_symplectic ⟨Or.inr rfl, show 3 ≤ r from by omega⟩
  case D =>
    dsimp only [LargeEvenInLambda2] at hlab
    have hr : 3 ≤ r := hlab.2
    have hD4' : ¬ (r = 4) := by
      rintro rfl
      exact hD4 ⟨rfl, rfl⟩
    by_cases h3 : r = 3
    · subst h3
      exact largeEvenLabelAll_inndiagComm_linear (Or.inr ⟨rfl, rfl⟩)
    · exact largeEvenLabelAll_inndiagComm_omegaPlus hlab rfl (show 5 ≤ r from by omega)
  case twD =>
    dsimp only [LargeEvenInLambda2] at hlab
    have hr : 2 ≤ r := hlab.2
    by_cases h2 : r = 2
    · subst h2
      exact largeEvenLabelAll_inndiagComm_linearTwo hlab (Or.inr ⟨rfl, rfl⟩)
    · by_cases h3 : r = 3
      · subst h3
        exact largeEvenLabelAll_inndiagComm_unitary hlab (Or.inr ⟨rfl, rfl⟩)
      · exact largeEvenLabelAll_inndiagComm_omegaMinus hlab rfl (show 4 ≤ r from by omega)
  case E6 => exact largeEvenLabelAll_inndiagComm_E6 rfl
  case E7 => exact largeEvenLabelAll_inndiagComm_excOut hlab (Or.inr (Or.inr (Or.inl rfl)))
  case E8 => exact largeEvenLabelAll_inndiagComm_excOut hlab (Or.inr (Or.inr (Or.inr rfl)))
  case F4 => exact largeEvenLabelAll_inndiagComm_excOut hlab (Or.inr (Or.inl rfl))
  case G2 => exact largeEvenLabelAll_inndiagComm_excOut hlab (Or.inl rfl)
  case twE6 => exact largeEvenLabelAll_inndiagComm_twE6 hlab rfl
  case triD4 => exact largeEvenLabelAll_inndiagComm_triD4 hlab rfl
  case twB2 => exact largeEvenLabelAll_inndiagComm_twB2 hlab rfl
  case twF4 => exact largeEvenLabelAll_inndiagComm_twF4 hlab rfl
  case B2der => simp [markChar] at hc
  case G2der => simp [markChar] at hc
  case twF4der => exact absurd rfl htits

theorem largeEvenLabelAll_innSubgroup {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGRawInnSubgroup) :=
  ggRawInnSubgroupInput_of_rawInnField ggRawInnFieldInput_holds lab hlab

private theorem tag_ne_twF4der_of_markTag {lab : LargeEvenLabel} {t : StatedLieTag}
    (htag : markTag lab = t) (htits : t ≠ .Tits) : lab.tag ≠ .twF4der := by
  obtain ⟨tag, r, m⟩ := lab
  rintro rfl
  exact htits (by rw [← htag]; rfl)

private theorem not_D4_of_model {lab : LargeEvenLabel} {t : StatedLieTag} {n : ℕ}
    (htag : markTag lab = t) (hrank : markRank lab = n)
    (hnotD4 : ¬ (t = .POmegaPlus ∧ n = 4)) : ¬ (lab.tag = .D ∧ lab.rank = 4) := by
  obtain ⟨tag, r, m⟩ := lab
  rintro ⟨rfl, rfl⟩
  exact hnotD4 ⟨by rw [← htag]; rfl, by rw [← hrank]; rfl⟩

private theorem not_derivedLab_of_markChar {lab : LargeEvenLabel} (hc : markChar lab = 2)
    (htits : lab.tag ≠ .twF4der) : ¬ MI.DerivedLab lab := by
  obtain ⟨tag, r, m⟩ := lab
  rintro (h | h)
  · have h' : tag = .G2der := h
    rw [h'] at hc
    simp [markChar] at hc
  · exact htits h

private theorem mem_of_mem_ggInndiag {R : Type} [Group R] {I : Set (MulAut R)}
    (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I)
    (hinn : ∀ r : R, MulAut.conj r ∈ I) {φ : MulAut R}
    (h : φ ∈ CFSG.StandardType.ggInndiag R I) : φ ∈ I := by
  let Isub : Subgroup (MulAut R) :=
    { carrier := I
      mul_mem' := fun {φ ψ} hφ hψ => hmul φ hφ ψ hψ
      one_mem' := by simpa using hinn 1
      inv_mem' := fun {φ} hφ => hinv φ hφ }
  have : CFSG.StandardType.ggInndiag R I ≤ Isub := by
    refine sup_le ?_ ?_
    · rintro _ ⟨r, rfl⟩
      exact hinn r
    · exact (Subgroup.closure_le Isub).2 fun φ hφ => hφ
  exact this h

theorem innDiagOn_of_lieModel
    {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} {J : Subgroup Γ} {a : Γ}
    (haJ : a ∈ Subgroup.normalizer (J : Set Γ))
    (hq : CFSG.IsQuasisimple (PQuot p J))
    {t : StatedLieTag} {n f : ℕ}
    (hLM : CFSG.Blueprint.LieModel (PSimple p J) t n 2 f)
    (hnotD4 : ¬ (t = .POmegaPlus ∧ n = 4)) (htits : t ≠ .Tits)
    (hmem : MI.indAut p J a haJ ∈ innAutDerived (PSimple p J)) :
    InnDiagOn p (Subgroup.zpowers a) J := by
  refine ⟨Subgroup.zpowers_le.2 haJ, ?_⟩
  obtain ⟨hX, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot
      hq.1.commutator_eq_top hLM
  obtain ⟨-, -, -, -, -, -, -, hP⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨htag, hrank, hchar, hdeg⟩ := hP
  have htitsLab : lab.tag ≠ .twF4der := tag_ne_twF4der_of_markTag htag htits
  have hD4Lab : ¬ (lab.tag = .D ∧ lab.rank = 4) := not_D4_of_model htag hrank hnotD4
  have hnd : ¬ MI.DerivedLab lab := not_derivedLab_of_markChar hchar htitsLab
  have hcomm : MI.CAll lab (LargeEvenSimpleGuard GGInndiagCommEq) :=
    (MI.canonAll_iff_legacyAll hlab hnd _).2
      (largeEvenLabelAll_inndiagComm_charTwo hlab hchar htitsLab hD4Lab)
  have hsub : MI.CAll lab (LargeEvenSimpleGuard GGRawInnSubgroup) :=
    (MI.canonAll_iff_legacyAll hlab hnd _).2 (largeEvenLabelAll_innSubgroup hlab)
  have hraw' : CFSG.Assembly.LargeEvenRawDatum lab fun R _ I _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : PQuot p J ⧸ Subgroup.center (PQuot p J) ≃* R,
          ∀ a' ∈ Subgroup.zpowers a, ∃ φ ∈ I, LargeEvenInduces θ (indRel p J a') φ := by
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ (hsub.and hcomm _ hraw)
    rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hsubfun, hcommfun⟩
    obtain ⟨hmul, hinv, hinn⟩ := hsubfun hs hna
    have hEq := hcommfun hs hna
    refine ⟨hs, hna, θ, fun a' ha' => ?_⟩
    have ha'N : a' ∈ Subgroup.normalizer (J : Set Γ) := Subgroup.zpowers_le.2 haJ ha'
    refine ⟨MulAut.congr θ (MI.indAut p J a' ha'N), ?_,
      (MI.induces_indRel_iff ha'N θ).2 rfl⟩
    apply mem_of_mem_ggInndiag hmul hinv hinn
    rw [hEq, CFSG.StandardType.ggInndiagComm_eq_innAutDerived,
      CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
    have e' : MI.indAut p J (a ^ k) ha'N = (MI.indAut p J a haJ) ^ k := by
      unfold MI.indAut
      rw [← map_zpow]
      congr 1
      exact Subtype.ext (by simp [zpow_neg, inv_zpow])
    rw [e']
    exact Subgroup.zpow_mem _ hmem k
  exact ⟨hX, lab, hlab, hraw'⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
