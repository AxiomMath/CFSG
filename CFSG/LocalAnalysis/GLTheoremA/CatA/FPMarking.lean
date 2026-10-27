module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPMI
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIPComp
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI

section Algebra

variable {R : Type} [Group R] {I : Set (MulAut R)} {F : Set (MulAut R)}

theorem not_mem_of_conj_field {u f : MulAut R} (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I)
    (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I) (hu : u ∈ I) (hf : f ∉ I) : u * f * u⁻¹ ∉ I := by
  intro h
  apply hf
  have := hmul _ (hinv u hu) _ (hmul _ h _ hu)
  simpa [mul_assoc] using this

theorem centralMod_conj_field (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I)
    (h1 : (1 : MulAut R) ∈ I)
    (hcen : ∀ α : MulAut R, ∀ u ∈ I, ∀ f ∈ Subgroup.closure F, α * (u * f) * α⁻¹ * (u * f)⁻¹ ∈ I)
    {u f : MulAut R} (hu : u ∈ I) (hf : f ∈ Subgroup.closure F) :
    CentralMod I (u * f * u⁻¹) := by
  intro γ
  have hc : f * u⁻¹ * f⁻¹ * u ∈ I := by
    have := hcen f u⁻¹ (hinv u hu) 1 (Subgroup.one_mem _)
    simpa using this
  have hn : u * f * u⁻¹ * f⁻¹ ∈ I := by
    have := hmul u hu _ (hmul _ hc _ (hinv u hu))
    have e : u * (f * u⁻¹ * f⁻¹ * u * u⁻¹) = u * f * u⁻¹ * f⁻¹ := by group
    rwa [e] at this
  have := hcen γ _ hn f hf
  have e : u * f * u⁻¹ * f⁻¹ * f = u * f * u⁻¹ := by group
  rwa [e] at this

end Algebra

section Data

@[expose] def FieldCentralBody : LargeEvenRawCont := fun R _ I F =>
  ∀ α : MulAut R, ∀ u ∈ I, ∀ f ∈ Subgroup.closure F, α * (u * f) * α⁻¹ * (u * f)⁻¹ ∈ I

@[expose] def FixConstBody (p : ℕ) : LargeEvenRawCont := fun R _ I _ =>
  ∀ α β : MulAut R, α ^ p = 1 → β ^ p = 1 → α ∉ I → β ∉ I → CentralMod I α → CentralMod I β →
    fixNum α = fixNum β

@[expose] def DataFacts (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I F =>
  RawInnBody p R I F ∧ FieldCentralBody R I F ∧
    (¬ (lab.tag = .triD4 ∧ p = 3) → FixConstBody p R I F)

theorem canonDataFacts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) : CAll lab (LargeEvenSimpleGuard (DataFacts p lab)) := by
  have h1 := canonRawInnAny hp.ne_one hlab
  have h2 := canonRawFieldCentral hlab
  by_cases h3 : lab.tag = .triD4 ∧ p = 3
  · refine (h1.and h2).mono ?_
    rintro R _ I F ⟨hI, hC⟩ hs hna
    exact ⟨hI hs hna, hC hs hna, fun h => absurd h3 h⟩
  · have h4 := canonFixConst hp hp2 hlab h3
    refine ((h1.and h2).and h4).mono ?_
    rintro R _ I F ⟨⟨hI, hC⟩, hF⟩ hs hna
    exact ⟨hI hs hna, hC hs hna, fun _ => hF hs hna⟩

end Data

section Marking

variable {G : Type} [Group G] [Finite G]

theorem congr_comp_congr {S R₁ R₂ : Type*} [Group S] [Group R₁] [Group R₂] (θ₁ : S ≃* R₁)
    (θ₂ : S ≃* R₂) (φ : MulAut S) :
    MulAut.congr (θ₁.symm.trans θ₂) (MulAut.congr θ₁ φ) = MulAut.congr θ₂ φ := by
  ext x; simp [MulAut.congr_apply]

theorem fieldOn_data {p : ℕ} {L : Subgroup G} {g : G} (hgN : g ∈ Subgroup.normalizer (L : Set G))
    {lab : LargeEvenLabel} {R : Type} [Group R] {I F : Set (MulAut R)}
    (θ : PSimple p L ≃* R)
    (h : LargeEvenPrimeField p lab I F (LargeEvenInduces θ (indRel p L g))) :
    (lab.tag ≠ .triD4 ∨ p ≠ 3) ∧ ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
      MulAut.congr θ (indAut p L g hgN) = u * f * u⁻¹ := by
  obtain ⟨hne, f, hf, u, hu, hord, hind⟩ := h
  exact ⟨hne, f, hf, u, hu, hord, ((induces_indRel_iff hgN θ).1 hind).symm⟩

theorem fixNum_eq_of_fieldOn {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {b b' : G}
    (hb : FieldOn p b L) (hb' : FieldOn p b' L) :
    fixNum (indAut p L b hb.1) = fixNum (indAut p L b' hb'.1) := by
  obtain ⟨lab₁, lab₂, R₁, _, I₁, F₁, θ₁, R₂, _, I₂, F₂, θ₂, hlab₁, hlab₂, hs₁, hna₁, hs₂, hna₂,
    hP₁, hP₂, hD₁, hD₂, hT⟩ :=
    marking_pair (P₁ := fun lab _ _ I F θ => GLAPrimeField p lab I F (GLAInduces θ (indRel p L b)))
      (P₂ := fun lab _ _ I F θ => GLAPrimeField p lab I F (GLAInduces θ (indRel p L b')))
      (P' := DataFacts p) (fun lab hlab => canonDataFacts hp hp2 hlab) hb.2 hb'.2
  obtain ⟨hne₁, f₁, hf₁, u₁, hu₁, hord₁, hα₁⟩ := fieldOn_data hb.1 θ₁ hP₁
  obtain ⟨hne₂, f₂, hf₂, u₂, hu₂, hord₂, hα₂⟩ := fieldOn_data hb'.1 θ₂ hP₂
  obtain ⟨⟨hmul₁, hinv₁, hconj₁, hFI₁⟩, hC₁, hFix₁⟩ := hD₁
  obtain ⟨⟨hmul₂, hinv₂, hconj₂, hFI₂⟩, hC₂, -⟩ := hD₂
  have h1₁ : (1 : MulAut R₁) ∈ I₁ := by simpa using hconj₁ 1
  have h1₂ : (1 : MulAut R₂) ∈ I₂ := by simpa using hconj₂ 1
  set σ : R₁ ≃* R₂ := θ₁.symm.trans θ₂ with hσ
  set β₁ := MulAut.congr θ₁ (indAut p L b' hb'.1) with hβ₁
  have hrel : MulAut.congr σ β₁ = u₂ * f₂ * u₂⁻¹ := by
    rw [hβ₁, hσ, congr_comp_congr, hα₂]
  have hp₁ : (u₁ * f₁ * u₁⁻¹) ^ p = 1 := by
    rw [conj_pow, ← hord₁, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hp₂ : (u₂ * f₂ * u₂⁻¹) ^ p = 1 := by
    rw [conj_pow, ← hord₂, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hpβ : β₁ ^ p = 1 := by
    apply (MulAut.congr σ).injective
    rw [map_pow, hrel, hp₂, map_one]
  have hnotα : u₁ * f₁ * u₁⁻¹ ∉ I₁ := not_mem_of_conj_field hmul₁ hinv₁ hu₁ (hFI₁ f₁ hf₁ hord₁)
  have hnotβ : β₁ ∉ I₁ := by
    intro h
    have := (hT β₁).1 h
    rw [hrel] at this
    exact not_mem_of_conj_field hmul₂ hinv₂ hu₂ (hFI₂ f₂ hf₂ hord₂) this
  have hcα : CentralMod I₁ (u₁ * f₁ * u₁⁻¹) :=
    centralMod_conj_field hmul₁ hinv₁ h1₁ hC₁ hu₁ (Subgroup.subset_closure hf₁)
  have hcβ₂ : CentralMod I₂ (u₂ * f₂ * u₂⁻¹) :=
    centralMod_conj_field hmul₂ hinv₂ h1₂ hC₂ hu₂ (Subgroup.subset_closure hf₂)
  have hcβ : CentralMod I₁ β₁ := by
    intro γ
    apply (hT _).2
    simp only [map_mul, map_inv, hrel]
    exact hcβ₂ (MulAut.congr σ γ)
  have h3 : ¬ (lab₁.tag = .triD4 ∧ p = 3) := by
    rintro ⟨h, h'⟩
    rcases hne₁ with h0 | h0
    · exact h0 h
    · exact h0 h'
  have hfix := hFix₁ h3 _ _ hp₁ hpβ hnotα hnotβ hcα hcβ
  rw [← hα₁, hβ₁] at hfix
  rwa [fixNum_congr, fixNum_congr] at hfix

end Marking

theorem fieldCentIndepAt_holds (G : Type) [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : FieldCentIndepAt G p := by
  intro X L B hL _ _ b _ b' _ hb hb'
  have hZ := odd_card_center_pQuot hp hp2 L
  rw [centCard2_eq_twoPart_fixNum hb.1 hZ, centCard2_eq_twoPart_fixNum hb'.1 hZ,
    fixNum_eq_of_fieldOn hp hp2 hb hb']

end FP

end CFSG.LocalAnalysis.GLTheoremA
