module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPMarking

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI


theorem marking_pair_marking {X : Type} [Group X] {P₁ P₂ : LargeEvenMarkProp X}
    {P' : LargeEvenLabel → LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → CAll lab (LargeEvenSimpleGuard (P' lab)))
    (h₁ : CFSG.Assembly.LargeEvenMarking X P₁) (h₂ : CFSG.Assembly.LargeEvenMarking X P₂) :
    CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ P₂ lab R I F θ ∧ P' lab R I F ∧
      ∃ (lab₁ : LargeEvenLabel) (R₁ : Type) (_ : Group R₁) (I₁ F₁ : Set (MulAut R₁))
        (θ₁ : X ⧸ Subgroup.center X ≃* R₁), LargeEvenInLambda2 lab₁ ∧ IsSimpleGroup R₁ ∧
          (∃ a b : R₁, a * b ≠ b * a) ∧ P₁ lab₁ R₁ I₁ F₁ θ₁ ∧ P' lab₁ R₁ I₁ F₁ ∧
          ∀ φ : MulAut R₁, φ ∈ I₁ ↔ MulAut.congr (θ₁.symm.trans θ) φ ∈ I := by
  have h₁' := canon_marking_and_labelAll_simple' (P' := fun lab R _ I F => P' lab R I F ∧ CMIiff R I F)
    (fun lab hlab => ((hall lab hlab).and (canonMIiff hlab)).mono
      fun R _ I F ⟨h1, h2⟩ hs hna => ⟨h1 hs hna, h2 hs hna⟩) h₁
  have h₂' := canon_marking_and_labelAll_simple' (P' := P') hall h₂
  obtain ⟨-, lab₁, hlab₁, hraw₁⟩ := h₁'
  obtain ⟨hX₂, lab₂, hlab₂, hraw₂⟩ := h₂'
  obtain ⟨R₁, _, I₁, F₁, ⟨hs₁, hna₁, θ₁, ⟨hP₁, hP'₁, hCMI⟩⟩⟩ := Canonical.largeEvenRawDatum_exists hraw₁
  have hraw₂' := hCMI lab₂ hlab₂ _ hraw₂
  refine ⟨hX₂, lab₂, hlab₂, Canonical.largeEvenRawDatum_mono ?_ hraw₂'⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hP₂, hP'₂⟩, hT⟩
  exact ⟨hs, hna, θ, hs, hna, hP₂, hP'₂, lab₁, R₁, _, I₁, F₁, θ₁, hlab₁, hs₁, hna₁, hP₁, hP'₁,
    hT hs hna (θ₁.symm.trans θ)⟩

variable {G : Type} [Group G] [Finite G]

@[expose] def OddAutCentralBody (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ α : MulAut R, α ^ p = 1 → CentralMod I α → ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, α = u * f

@[expose] def ConjBody (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ u ∈ I, ∀ f ∈ Subgroup.closure F, u * f ∉ I → (u * f) ^ p = 1 →
    ∃ f' ∈ F, ∃ u' ∈ I, orderOf f' = p ∧ u * f = u' * f' * u'⁻¹

@[expose] def TransportFacts (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I F =>
  RawInnBody p R I F ∧ FieldCentralBody R I F ∧
    (¬ (lab.tag = .triD4 ∧ p = 3) → OddAutCentralBody p R I F ∧ ConjBody p R I F)

theorem canonTransportFacts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) : CAll lab (LargeEvenSimpleGuard (TransportFacts p lab)) := by
  have h1 := canonRawInnAny hp.ne_one hlab
  have h2 := canonRawFieldCentral hlab
  by_cases h3 : lab.tag = .triD4 ∧ p = 3
  · refine (h1.and h2).mono ?_
    rintro R _ I F ⟨hI, hC⟩ hs hna
    exact ⟨hI hs hna, hC hs hna, fun h => absurd h3 h⟩
  · have h4 := canonOddAutCentral hp hp2 hlab
    have h5 := canonRawFieldConj hp hp2 hlab h3
    refine (((h1.and h2).and h4).and h5).mono ?_
    rintro R _ I F ⟨⟨⟨hI, hC⟩, hO⟩, hL⟩ hs hna
    exact ⟨hI hs hna, hC hs hna, fun _ => ⟨hO hs hna, hL hs hna⟩⟩

theorem fieldOn_marking_transport {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {g : G}
    (hF : FieldOn p g L) {P : LargeEvenMarkProp (PQuot p L)}
    (hP : CFSG.Assembly.LargeEvenMarking (PQuot p L) P) :
    CFSG.Assembly.LargeEvenMarking (PQuot p L) fun lab R _ I F θ => P lab R I F θ ∧
      ((lab.tag ≠ .triD4 ∨ p ≠ 3) →
        GLAPrimeField p lab I F (GLAInduces θ (indRel p L g))) := by
  have h := marking_pair_marking
    (P₁ := fun lab _ _ I F θ => GLAPrimeField p lab I F (GLAInduces θ (indRel p L g))) (P₂ := P)
    (P' := TransportFacts p) (fun lab hlab => canonTransportFacts hp hp2 hlab) hF.2 hP
  refine Canonical.largeEvenMarking_mono ?_ h
  rintro lab R _ I F θ ⟨hs, hna, hPθ, ⟨hI, hC, hlift⟩, lab₁, R₁, _, I₁, F₁, θ₁, hlab₁, hs₁, hna₁, hP₁,
    ⟨hI₁, hC₁, -⟩, hiff⟩
  refine ⟨hPθ, fun hne => ?_⟩
  have h3 : ¬ (lab.tag = .triD4 ∧ p = 3) := by
    rintro ⟨h, h'⟩
    rcases hne with h0 | h0
    · exact h0 h
    · exact h0 h'
  obtain ⟨hOdd, hLS⟩ := hlift h3
  obtain ⟨hmul₁, hinv₁, hconj₁, hFI₁⟩ := hI₁
  obtain ⟨hmul, hinv, hconj, hFI⟩ := hI
  obtain ⟨-, f₁, hf₁, u₁, hu₁, hord₁, hα₁⟩ := fieldOn_data hF.1 θ₁ hP₁
  have h1₁ : (1 : MulAut R₁) ∈ I₁ := by simpa using hconj₁ 1
  set σ : R₁ ≃* R := θ₁.symm.trans θ with hσ
  set α := MulAut.congr θ (indAut p L g hF.1) with hα
  have hrel : MulAut.congr σ (u₁ * f₁ * u₁⁻¹) = α := by
    rw [← hα₁, hσ, hα, congr_comp_congr]
  have hp₁ : (u₁ * f₁ * u₁⁻¹) ^ p = 1 := by
    rw [conj_pow, ← hord₁, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hpα : α ^ p = 1 := by
    rw [← hrel, ← map_pow, hp₁, map_one]
  have hnot₁ : u₁ * f₁ * u₁⁻¹ ∉ I₁ := not_mem_of_conj_field hmul₁ hinv₁ hu₁ (hFI₁ f₁ hf₁ hord₁)
  have hnotα : α ∉ I := fun h => hnot₁ ((hiff _).2 (by rwa [hrel]))
  have hc₁ : CentralMod I₁ (u₁ * f₁ * u₁⁻¹) :=
    centralMod_conj_field hmul₁ hinv₁ h1₁ hC₁ hu₁ (Subgroup.subset_closure hf₁)
  have hcα : CentralMod I α := by
    intro γ
    have h2 := (hiff _).1 (hc₁ (MulAut.congr σ.symm γ))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hrel, congr_congr_symm'] at h2
    exact h2
  obtain ⟨u, hu, f, hf, huf⟩ := hOdd α hpα hcα
  have hnot : u * f ∉ I := huf ▸ hnotα
  have hpow : (u * f) ^ p = 1 := huf ▸ hpα
  obtain ⟨f', hf', u', hu', hord, heq⟩ := hLS u hu f hf hnot hpow
  refine ⟨hne, f', hf', u', hu', hord, ?_⟩
  exact (induces_indRel_iff hF.1 θ).2 (by rw [← hα, huf, heq])

end FP

end CFSG.LocalAnalysis.GLTheoremA
