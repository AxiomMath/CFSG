module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrthRecipe
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
public import TauCeti.GroupTheory.QuotientGroup.MulAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GClsOrth

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GField
  CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace CLB

theorem largeEvenMarking_or {X : Type*} [Group X] {P Q : LargeEvenMarkProp X}
    (h : CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∨ Q lab R I F θ) :
    CFSG.Assembly.LargeEvenMarking X P ∨ CFSG.Assembly.LargeEvenMarking X Q := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hraw' : CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, P lab R I F θ) ∨
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, Q lab R I F θ) := by
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hθ | hθ⟩
    exacts [Or.inl ⟨hs, hna, θ, hθ⟩, Or.inr ⟨hs, hna, θ, hθ⟩]
  rcases CFSG.LocalAnalysis.GLTheoremA.MI.canonRawDatum_or hraw' with h' | h'
  exacts [Or.inl ⟨hX, lab, hlab, h'⟩, Or.inr ⟨hX, lab, hlab, h'⟩]

theorem exists_unique_induces {S R : Type} [Group S] [Group R]
    (θ : S ⧸ Subgroup.center S ≃* R) {α : MulAut S} {p : ℕ} (hα : α ^ p = 1) :
    ∃ φ : MulAut R, φ ^ p = 1 ∧ CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = α s) φ ∧
      ∀ u : MulAut R, CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = α s) u → u = φ := by
  have hφ : CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = α s)
      (MulAut.congr θ (MulAut.mapQuotient (Subgroup.center S) α)) := by
    rintro l _ rfl
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.mapQuotient_mk]
  refine ⟨_, ?_, hφ, fun u hu => ?_⟩
  · rw [← map_pow, ← map_pow, hα, map_one, map_one]
  · ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hu s (α s) rfl, hφ s (α s) rfl]

theorem induces_inn_or_field {S R : Type} [Group S] [Group R] {I F : Set (MulAut R)}
    (θ : S ⧸ Subgroup.center S ≃* R) {α : MulAut S} {p : ℕ} (hα : α ^ p = 1)
    (hP : RawOddInnField p R I F) :
    (∃ u ∈ I, CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = α s) u) ∨
      ((∃ i ∈ I, ∃ f ∈ F, CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = α s) (i * f)) ∧
        ¬ ∃ i ∈ I, CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = α s) i) := by
  obtain ⟨φ, hφp, hφ, huniq⟩ := exists_unique_induces θ hα
  by_cases hI : φ ∈ I
  · exact Or.inl ⟨φ, hI, hφ⟩
  rcases hP φ hφp with h | ⟨i, hi, f, hf, rfl⟩
  · exact absurd h hI
  refine Or.inr ⟨⟨i, hi, f, hf, hφ⟩, ?_⟩
  rintro ⟨u, hu, hind⟩
  exact hI (huniq u hind ▸ hu)

end CLB

theorem innDiagKind_or_fieldKind {S : Type} [Group S] {p : ℕ} {α : MulAut S} {labK : GLALabel}
    (hlab : HasLabel S (fun l : GLALabel => l = labK)) (hα : α ^ p = 1)
    (hP : CFSG.StandardType.Canonical.LargeEvenLabelAll labK (RawOddInnField p)) :
    InnDiagKind S labK α ∨ FieldKind S labK α := by
  have h1 : CFSG.Assembly.LargeEvenMarking S fun lab R _ I F _ =>
      lab = labK ∧ RawOddInnField p R I F := by
    obtain ⟨hS, lab, hlabΛ, hraw⟩ := hlab
    obtain ⟨R, _, I, F, -, -, θ, hEq⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    have hEq' : lab = labK := hEq
    subst hEq'
    refine ⟨hS, lab, hlabΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ (hP _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hodd⟩
    exact ⟨hs, hna, θ, rfl, hodd⟩
  refine CLB.largeEvenMarking_or (CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ h1)
  rintro lab R _ I F θ ⟨rfl, hodd⟩
  exact (CLB.induces_inn_or_field θ hα hodd).imp (fun h => ⟨rfl, h⟩) fun h => ⟨rfl, h⟩

theorem canonicalLabelAll_omegaPlus {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : 4 ≤ lab.rank) {P : LargeEvenRawCont}
    (hP : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ lab.n →
      P (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K lab.rank))) (LargeEvenInnSet _)
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K lab.rank))))) :
    CFSG.StandardType.Canonical.LargeEvenLabelAll lab P := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4 hP ⊢
  subst ht
  intro Q hQ
  have h3 : l ≠ 3 := by omega
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  simp only [h3, ↓reduceIte] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQK, hP K hK⟩

theorem canonicalLabelAll_omegaMinus {lab : LargeEvenLabel} (ht : lab.tag = .twD)
    (h4 : 4 ≤ lab.rank) {P : LargeEvenRawCont}
    (hP : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ lab.n → ∀ b c : K,
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      P (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (lab.rank - 1) b c))) (LargeEvenInnSet _)
        (LargeEvenPhiQ (lab.rank - 1) b c
          (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (lab.rank - 1) b c))))) :
    CFSG.StandardType.Canonical.LargeEvenLabelAll lab P := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4 hP ⊢
  subst ht
  intro Q hQ
  have h2 : l ≠ 2 := by omega
  have h3 : l ≠ 3 := by omega
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  simp only [h2, h3, ↓reduceIte] at hQ ⊢
  obtain ⟨K, _, _, hK, b, c, hbc, hQK⟩ := hQ
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQK, hP K hK b c hbc⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GClsOrth
