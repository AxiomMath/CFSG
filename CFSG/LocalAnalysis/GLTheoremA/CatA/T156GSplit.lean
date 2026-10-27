module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MITD4
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S3 CFSG.LocalAnalysis.GLTheoremA.MI

section Central

variable {R : Type} [Group R] {I F : Set (MulAut R)}

abbrev CentralBody (R : Type) [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ α : MulAut R, ∀ u ∈ I, ∀ f ∈ Subgroup.closure F, α * (u * f) * α⁻¹ * (u * f)⁻¹ ∈ I

theorem centralMod_of_mem (hC : CentralBody R I F) {φ : MulAut R} (hφ : φ ∈ I) : FP.CentralMod I φ := by
  intro γ
  have h := hC γ φ hφ 1 (Subgroup.one_mem _)
  simpa only [mul_one] using h

theorem centralMod_of_field (hC : CentralBody R I F) (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I)
    (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I) {u f : MulAut R} (hu : u ∈ I) (hf : f ∈ F) :
    FP.CentralMod I (u * f * u⁻¹) := by
  have hfc : f ∈ Subgroup.closure F := Subgroup.subset_closure hf
  have h1 : f * u⁻¹ * f⁻¹ * u ∈ I := by
    have := hC f u⁻¹ (hinv u hu) 1 (Subgroup.one_mem _)
    simpa only [mul_one, inv_inv] using this
  have h2 : f * u⁻¹ * f⁻¹ ∈ I := by
    have := hmul _ h1 _ (hinv u hu)
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using this
  have he : u * f * u⁻¹ = (u * (f * u⁻¹ * f⁻¹)) * f := by group
  intro γ
  rw [he]
  exact hC γ _ (hmul u hu _ h2) f hfc

theorem centralMod_of_mul (hC : CentralBody R I F) {u f : MulAut R} (hu : u ∈ I)
    (hf : f ∈ Subgroup.closure F) : FP.CentralMod I (u * f) :=
  fun γ => hC γ u hu f hf

end Central

section Markings


variable {Ω : Type} [Group Ω] [Finite Ω]

@[expose] def CentFacts (p : ℕ) : LargeEvenLabel → LargeEvenRawCont := fun lab R _ I F =>
  CentralBody R I F ∧ MI.RawInnBody p R I F ∧
    (¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) → GGOddAutInnField p I F)

theorem hall_centFacts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (lab : LargeEvenLabel)
    (hlab : LargeEvenInLambda2 lab) : MI.CAll lab (LargeEvenSimpleGuard (CentFacts p lab)) := by
  have h1 := MI.CAll.and (FP.canonRawFieldCentral hlab) (MI.canonRawInn' hp hp2 hlab)
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
  · exact MI.CAll.mono (fun R _ I F h' hs hna => ⟨h'.1 hs hna, h'.2 hs hna, fun h'' => absurd hD h''⟩) h1
  · have h2 := MI.CAll.and h1 (FP.canonOddAut hp hp2 hlab hD)
    exact MI.CAll.mono (fun R _ I F h' hs hna => ⟨h'.1.1 hs hna, h'.1.2 hs hna, fun _ => h'.2 hs hna⟩) h2

theorem centralMarking {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple (PQuot p S)) (hchev : IsChevSimple 2 (PSimple p S)) {c : Ω}
    (hcN : c ∈ Subgroup.normalizer (S : Set Ω)) (hcp : c ^ p = 1)
    (h : InnDiagOn p (Subgroup.zpowers c) S ∨ FieldOn p c S ∨ (p = 3 ∧ IsTD4 3 S)) :
    CFSG.Assembly.LargeEvenMarking (PQuot p S) fun _ R _ I _ θ =>
      ∀ φ : MulAut R, LargeEvenInduces θ (indRel p S c) φ → FP.CentralMod I φ := by
  rcases h with hInn | hF | ⟨rfl, hTD4⟩
  · have hM := FP.canon_marking_and_labelAll_simple' (P' := CentFacts p)
      (fun lab hlab => hall_centFacts hp hp2 lab hlab) hInn.2
    refine Canonical.largeEvenMarking_mono ?_ hM
    rintro lab R _ I F θ ⟨hP, hC, -, -⟩ φ hφ
    obtain ⟨φ₁, hφ₁, hind₁⟩ := hP c (Subgroup.mem_zpowers c)
    have e1 := (induces_indRel_iff hcN θ).1 hind₁
    have e2 := (induces_indRel_iff hcN θ).1 hφ
    rw [e2, ← e1]
    exact centralMod_of_mem hC hφ₁
  · have hM := FP.canon_marking_and_labelAll_simple' (P' := CentFacts p)
      (fun lab hlab => hall_centFacts hp hp2 lab hlab) hF.2
    refine Canonical.largeEvenMarking_mono ?_ hM
    rintro lab R _ I F θ ⟨hP, hC, ⟨hmul, hinv, -, -⟩, -⟩ φ hφ
    obtain ⟨-, f, hf, u, hu, -, hind⟩ := hP
    have e1 := (induces_indRel_iff hcN θ).1 hind
    have e2 := (induces_indRel_iff hcN θ).1 hφ
    rw [e2, ← e1]
    exact centralMod_of_field hC hmul hinv hu hf
  · have hM₀ := Canonical.largeEvenMarking_markedModel
      (CFSG.StandardType.ChevTwo.ys08_holds (PQuot 3 S) hq hchev)
    have hM := FP.canon_marking_and_labelAll_simple' (P' := CentFacts 3)
      (fun lab hlab => hall_centFacts hp hp2 lab hlab) hM₀
    refine Canonical.largeEvenMarking_mono ?_ hM
    rintro lab R _ I F θ ⟨⟨-, hMM⟩, hC, -, hOdd⟩ φ hφ
    have htag : lab.tag = .triD4 := tag_triD4_of_isTD4 hMM hTD4 θ
    have hD : ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ 3 = 3) := by
      rintro ⟨h', -, -⟩
      rw [htag] at h'
      cases h'
    have e2 := (induces_indRel_iff hcN θ).1 hφ
    have hφ3 : φ ^ 3 = 1 := by
      rw [e2, ← map_pow]
      have : indAut 3 S c hcN ^ 3 = 1 := by
        rw [indAut, ← map_pow]
        have h1 : (⟨c⁻¹, Subgroup.inv_mem _ hcN⟩ : ↥(Subgroup.normalizer (S : Set Ω))) ^ 3 = 1 := by
          apply Subtype.ext
          simp [inv_pow, hcp]
        rw [h1, map_one]
      rw [this, map_one]
    obtain ⟨u, hu, f, hf, he⟩ := hOdd hD φ hφ3
    rw [he]
    exact centralMod_of_mul hC hu hf

@[expose] def SplitFacts (p : ℕ) : LargeEvenLabel → LargeEvenRawCont := fun _ R _ I F =>
  (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → MI.RawInnBody p R I F) ∧
  FP.OddAutCentral p R I F ∧ FP.FieldCyc R I F ∧
  (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → FP.CMIiff R I F)

theorem hall_splitFacts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (lab : LargeEvenLabel)
    (hlab : LargeEvenInLambda2 lab) : MI.CAll lab (LargeEvenSimpleGuard (SplitFacts p lab)) := by
  have h := MI.CAll.and (MI.canonRawInn' hp hp2 hlab)
    (MI.CAll.and (FP.canonOddAutCentral hp hp2 hlab)
      (MI.CAll.and (FP.canonFieldCyc hlab) (FP.canonMIiff hlab)))
  exact MI.CAll.mono (fun R _ I F h' => fun _ _ => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2⟩) h

theorem t156_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S A : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple (PQuot p S)) (hchev : IsChevSimple 2 (PSimple p S))
    (hAN : A ≤ Subgroup.normalizer (S : Set Ω)) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hnt : ∀ c ∈ A, NonInnDiag p c S → FieldOn p c S ∨ (p = 3 ∧ IsTD4 3 S)) :
    ∃ A₀ : Subgroup Ω, A₀ ≤ A ∧ InnDiagOn p A₀ S ∧ Nat.card A ≤ p * Nat.card A₀ ∧
      ∀ a ∈ A, InnDiagOn p (Subgroup.zpowers a) S → a ∈ A₀ := by
  have hcent : ∀ c ∈ (A : Set Ω), CFSG.Assembly.LargeEvenMarking (PQuot p S) fun _ R _ I _ θ =>
      ∀ φ : MulAut R, LargeEvenInduces θ (indRel p S c) φ → FP.CentralMod I φ := by
    intro c hc
    refine centralMarking hp hp2 hq hchev (hAN hc) (hexp c hc) ?_
    by_cases hN : NonInnDiag p c S
    · exact Or.inr (hnt c hc hN)
    · left
      by_contra hI
      exact hN ⟨hAN hc, hI⟩
  have M₀ := Canonical.largeEvenMarking_markedModel
    (CFSG.StandardType.ChevTwo.ys08_holds (PQuot p S) hq hchev)
  have hMc := OutCyc.marking_transport_central_family (fun a : Ω => indRel p S a) (A : Set Ω)
    (Set.toFinite _) hcent M₀
  have hMs := FP.canon_marking_and_labelAll_simple' (P' := SplitFacts p)
    (fun lab hlab => hall_splitFacts hp hp2 lab hlab) hMc
  obtain ⟨hX, lab₁, hlab₁, hraw₁⟩ := hMs
  obtain ⟨R₁, _, I₁, F₁, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw₁
  obtain ⟨hs, hna, θ₁, hPc, hP'⟩ := hQ
  haveI : Finite R₁ := Finite.of_equiv (PSimple p S) θ₁.toEquiv
  have hRaw := hP'.1 hs hna
  have hOAC := hP'.2.1 hs hna
  have hFC := hP'.2.2.1
  have hCMI := hP'.2.2.2 hs hna
  have hJI : ∀ y : MulAut R₁, y ∈ OutCyc.rawSubgroup hRaw ↔ y ∈ I₁ := fun y => Iff.rfl
  have hcent' : ∀ a ∈ A, ∀ φ : MulAut R₁, LargeEvenInduces θ₁ (indRel p S a) φ →
      FP.CentralMod I₁ φ := fun a ha => hPc.2 a ha
  obtain ⟨S', g, hJS, hJn, hg, hψS, hgen⟩ :=
    OutCyc.d4_group_data hp.pos S A hAN hexp θ₁ (OutCyc.rawSubgroup hRaw) hJI hcent' hOAC hFC
  exact OutCyc.outCyc_of_source hp.pos S A hAN hexp M₀ θ₁ hCMI (OutCyc.rawSubgroup hRaw) hJI S' g hJS
    hJn hg hψS hgen

end Markings

end CFSG.LocalAnalysis.GLTheoremA.T156

end
