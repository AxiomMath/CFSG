module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerE
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutCard

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4

@[expose] def PConfig {Y : Type} [Group Y] (α : MulAut Y) (p : ℕ) (X : Subgroup Y) : Prop :=
  IsPGroup p ↥X ∧ X ≠ ⊥ ∧ Subgroup.closure ((fun x : Y => x * (α x)⁻¹) '' (X : Set Y)) = X ∧
    fixSub α ≤ normalizer (X : Set Y)

theorem congr_apply_mk {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (α : MulAut Y) (y : Y) :
    (MulAut.congr e α) (e y) = e (α y) := by
  simp [MulAut.congr_apply]

theorem PConfig.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {α : MulAut Y} {p : ℕ}
    {X : Subgroup Y} (h : PConfig α p X) : PConfig (MulAut.congr e α) p (X.map e.toMonoidHom) := by
  obtain ⟨hX, hX1, hcomm, hN⟩ := h
  refine ⟨hX.map _, ?_, ?_, ?_⟩
  · intro hbot
    apply hX1
    rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hbot
    exact hbot
  · have h1 : (Subgroup.closure ((fun x : Y => x * (α x)⁻¹) '' (X : Set Y))).map e.toMonoidHom =
        Subgroup.closure (e.toMonoidHom '' ((fun x : Y => x * (α x)⁻¹) '' (X : Set Y))) :=
      MonoidHom.map_closure _ _
    have h2 : e.toMonoidHom '' ((fun x : Y => x * (α x)⁻¹) '' (X : Set Y)) =
        (fun y : Y' => y * ((MulAut.congr e α) y)⁻¹) '' ((X.map e.toMonoidHom : Subgroup Y') : Set Y') := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
        simp
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x * (α x)⁻¹, ⟨x, hx, rfl⟩, by simp⟩
    rw [← h2, ← h1, hcomm]
  · intro y' hy'
    have h1 : (MulAut.congr e α) y' = y' := hy'
    have hy : e.symm y' ∈ fixSub α := by
      have h3 : (MulAut.congr e α) (e (e.symm y')) = e (e.symm y') := by simpa using h1
      rw [congr_apply_mk] at h3
      exact e.injective (by simpa using h3)
    have hyN := hN hy
    rw [Subgroup.mem_normalizer_iff]
    intro h'
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have := Subgroup.mem_normalizer_iff.mp hyN (e.symm h')
    simpa [map_mul, map_inv] using this

theorem false_of_coatom_fixSub {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hnonab : ∃ a b : Y, a * b ≠ b * a) {α : MulAut Y} (hco : IsCoatom (fixSub α)) {p : ℕ} [Fact p.Prime]
    {X : Subgroup Y} (h : PConfig α p X) : False := by
  classical
  obtain ⟨hX, hX1, hcomm, hN⟩ := h
  rcases (hco.le_iff).mp hN with hNtop | hNC
  · have hXn : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h0 | h0
    · exact hX1 h0
    · have hT : IsPGroup p Y := by
        have : IsPGroup p ↥(⊤ : Subgroup Y) := h0 ▸ hX
        exact this.of_equiv Subgroup.topEquiv
      have : Nontrivial Y := by
        obtain ⟨a, b, hab⟩ := hnonab
        exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
      have hcn : Nontrivial (center Y) := hT.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h1 | h1
      · obtain ⟨x, hx⟩ := exists_ne (1 : center Y)
        exact hx (Subtype.ext ((Subgroup.eq_bot_iff_forall (center Y)).mp h1 x x.2))
      · obtain ⟨a, b, hab⟩ := hnonab
        have : a ∈ center Y := by rw [h1]; exact mem_top a
        exact hab ((Subgroup.mem_center_iff.mp this b).symm)
  · have hXle : X ≤ fixSub α := hNC ▸ Subgroup.le_normalizer
    apply hX1
    rw [← hcomm, eq_bot_iff, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hfix : α x = x := hXle hx
    simp [hfix]

section Classes

open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

variable {F : Type} [Field F] [Finite F]

theorem isSimpleGroup_psp4_of_odd (hodd : ringChar F ≠ 2) : IsSimpleGroup (StatedProj (StatedSp 2 F)) := by
  have := Fintype.ofFinite F
  have hne1 : Nat.card F ≠ 1 := by
    intro h
    have := Finite.one_lt_card (α := F)
    omega
  have hne2 : Nat.card F ≠ 2 := by
    intro h
    have hc : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
      rw [← Nat.card_eq_fintype_card, h]; norm_num)
    exact hodd (by rw [ringChar.eq F 2])
  have hge : 3 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num) ?_
  by_cases h3 : Nat.card F = 3
  · exact Or.inr (Or.inl ⟨h3, le_refl 2⟩)
  · exact Or.inl (Or.inr (by omega))

theorem nonabelian_psp4 (hodd : ringChar F ≠ 2) : ∃ a b : StatedProj (StatedSp 2 F), a * b ≠ b * a := by
  obtain ⟨ψ, hψ⟩ := exists_quaternion_psp4 hodd
  refine ⟨ψ (QuaternionGroup.a 1), ψ (QuaternionGroup.xa 0), fun h => ?_⟩
  rw [← map_mul, ← map_mul] at h
  have := hψ h
  exact absurd this (by decide)

theorem center_psp4_eq_bot (hodd : ringChar F ≠ 2) : center (StatedProj (StatedSp 2 F)) = ⊥ := by
  have := isSimpleGroup_psp4_of_odd hodd
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (StatedProj (StatedSp 2 F))) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := nonabelian_psp4 hodd
    have : a ∈ center (StatedProj (StatedSp 2 F)) := by rw [h]; exact mem_top a
    exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem fixSub_conj {Y : Type} [Group Y] (u : Y) : fixSub (MulAut.conj u) = centralizer ({u} : Set Y) := by
  ext x
  rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc x * u = (u * x * u⁻¹) * u := by rw [h]
      _ = u * x := by group
  · intro h
    calc u * x * u⁻¹ = (x * u) * u⁻¹ := by rw [h]
      _ = x := by group

@[expose] def CoreInner : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 →
    ∀ u : StatedProj (StatedSp 2 F), u * u = 1 → u ≠ 1 →
      ¬ IsCoatom (centralizer ({u} : Set (StatedProj (StatedSp 2 F)))) →
      ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup (StatedProj (StatedSp 2 F)),
        PConfig (MulAut.conj u) p X → False

@[expose] def CoreII : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → ∀ (A : gsp 2 F) (d : Fˣ),
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (d : F) • 1 →
    (d : F) = (multiplierUnit A : F) → (∀ l : F, l ^ 2 ≠ (multiplierUnit A : F)) →
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup (StatedProj (StatedSp 2 F)),
      PConfig (conjAut 2 F A) p X → False

@[expose] def CoreI : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → ∀ (A : gsp 2 F) (d : Fˣ),
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (d : F) • 1 →
    (d : F) = -(multiplierUnit A : F) → (∀ l : F, l ^ 2 ≠ (multiplierUnit A : F)) →
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup (StatedProj (StatedSp 2 F)),
      PConfig (conjAut 2 F A) p X → False

@[expose] def CoreField : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → ∀ (A : gsp 2 F) (σ : F ≃+* F), σ ≠ 1 → σ ^ 2 = 1 →
    (∃ d : Fˣ, (A : GL (Fin 2 ⊕ Fin 2) F) * glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d) →
    Nat.card F = Nat.card {c : F // σ c = c} ^ 2 →
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup (StatedProj (StatedSp 2 F)),
      PConfig (conjAut 2 F A * fieldAut 2 F σ) p X → False

theorem psp4_model_false (hInner : CoreInner) (hI : CoreI) (hII : CoreII) (hField : CoreField)
    (hodd : ringChar F ≠ 2) {α : MulAut (StatedProj (StatedSp 2 F))} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup (StatedProj (StatedSp 2 F))}
    (h : PConfig α p X) : False := by
  have hsimple := isSimpleGroup_psp4_of_odd hodd
  have hnonab := nonabelian_psp4 (F := F) hodd
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, hlin, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation hodd
      le_rfl).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  · subst hσ
    have hα' : α = conjAut 2 F A := by rw [hα, map_one, mul_one]
    have hAA := mul_self_of_rep A d hd
    by_cases hsq : ∃ l : F, l ^ 2 = (multiplierUnit A : F)
    · obtain ⟨u, hu⟩ := conjAut_mem_range_of_sq A hsq.choose_spec
      have hαu : α = MulAut.conj u := by rw [hα', ← hu]
      have hu1 : u ≠ 1 := fun h1 => hα1 (by rw [hαu, h1, map_one])
      have hu2 : u * u = 1 := by
        have hc : MulAut.conj (u * u) = 1 := by rw [map_mul, ← hαu, hα2]
        have hz : u * u ∈ center (StatedProj (StatedSp 2 F)) := by
          rw [Subgroup.mem_center_iff]
          intro g
          have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ g) hc
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc g * (u * u) = u * u * g * (u * u)⁻¹ * (u * u) := by rw [this]
            _ = u * u * g := by group
        rw [center_psp4_eq_bot hodd] at hz
        exact Subgroup.mem_bot.mp hz
      by_cases hco : IsCoatom (centralizer ({u} : Set (StatedProj (StatedSp 2 F))))
      · rw [hαu] at h
        refine false_of_coatom_fixSub hnonab ?_ h
        rw [fixSub_conj]
        exact hco
      · rw [hαu] at h
        exact hInner F hodd u hu2 hu1 hco p hp2 X h
    · push Not at hsq
      rcases eq_or_eq_neg_multiplier A hAA with hdm | hdm
      · rw [hα'] at h
        exact hII F hodd A d hAA hdm hsq p hp2 X h
      · rw [hα'] at h
        exact hI F hodd A d hAA hdm hsq p hp2 X h
  · rw [hα] at h
    exact hField F hodd A σ hσ hσ2 ⟨d, hd⟩ (hfield hσ).1 p hp2 X h

theorem psp4Core_of_classes (hInner : CoreInner) (hI : CoreI) (hII : CoreII) (hField : CoreField) :
    PSp4Core := by
  intro Y _ _ hY α hα2 hα1 p _ hp2 X hXp hX1 hcomm hN
  obtain ⟨p0, f0, hp0, hf0, hp02, hlie⟩ := hY
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psp_unpack hlie
  have hodd : ringChar F ≠ 2 := ringChar_ne_two_of_card_psp4 hp0 hp02 hcard
  have hcfg := PConfig.of_mulEquiv e (α := α) (p := p) (X := X) ⟨hXp, hX1, hcomm, hN⟩
  have hα'2 : MulAut.congr e α * MulAut.congr e α = 1 := by rw [← map_mul, hα2, map_one]
  have hα'1 : MulAut.congr e α ≠ 1 := fun h => hα1 ((MulAut.congr e).injective (by rw [h, map_one]))
  exact psp4_model_false hInner hI hII hField hodd hα'2 hα'1 hp2 hcfg

end Classes

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
