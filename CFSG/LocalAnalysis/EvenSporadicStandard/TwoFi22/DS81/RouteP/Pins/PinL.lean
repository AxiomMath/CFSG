module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.NormCocode
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F11Pin
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.KClass

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

private lemma mem_normalizer_iff_of_le {G : Type*} [Group G] {L E : Subgroup G} (hE : E ≤ L)
    (x : ↥L) :
    (x : G) ∈ normalizer (E : Set G) ↔
      ∀ y : ↥L, (y : G) ∈ E ↔ ((x * y * x⁻¹ : ↥L) : G) ∈ E := by
  rw [Subgroup.mem_set_normalizer_iff]
  constructor
  · intro h y
    simpa using h (y : G)
  · intro h g
    constructor
    · intro hg
      have hgL : g ∈ L := hE hg
      simpa using (h ⟨g, hgL⟩).mp (by simpa using hg)
    · intro hg
      have hgL : g ∈ L := by
        have hmem : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem x.2) (hE hg)) x.2
        simpa [mul_assoc] using hmem
      exact (h ⟨g, hgL⟩).mpr (by simpa using hg)

theorem mem_normalizer_iff_of_mulEquiv {G G₀ : Type*} [Group G] [Group G₀] {L E : Subgroup G}
    {L₀ E₀ : Subgroup G₀} (hE : E ≤ L) (hE₀ : E₀ ≤ L₀) (ψ : ↥L ≃* ↥L₀)
    (hψ : ∀ x : ↥L, (x : G) ∈ E ↔ ((ψ x : ↥L₀) : G₀) ∈ E₀) (x : ↥L) :
    (x : G) ∈ normalizer (E : Set G) ↔ ((ψ x : ↥L₀) : G₀) ∈ normalizer (E₀ : Set G₀) := by
  rw [mem_normalizer_iff_of_le hE x, mem_normalizer_iff_of_le hE₀ (ψ x)]
  constructor
  · intro h y₀
    have key : ((ψ.symm y₀ : ↥L) : G) ∈ E ↔
        ((ψ x * y₀ * (ψ x)⁻¹ : ↥L₀) : G₀) ∈ E₀ := by
      have h1 := (h (ψ.symm y₀)).trans (hψ (x * ψ.symm y₀ * x⁻¹))
      simpa [map_mul, map_inv] using h1
    calc (y₀ : G₀) ∈ E₀ ↔ ((ψ.symm y₀ : ↥L) : G) ∈ E := by
          simpa using (hψ (ψ.symm y₀)).symm
      _ ↔ ((ψ x * y₀ * (ψ x)⁻¹ : ↥L₀) : G₀) ∈ E₀ := key
  · intro h y
    have key : ((x * y * x⁻¹ : ↥L) : G) ∈ E ↔
        ((ψ x * ψ y * (ψ x)⁻¹ : ↥L₀) : G₀) ∈ E₀ := by
      simpa [map_mul, map_inv] using hψ (x * y * x⁻¹)
    calc (y : G) ∈ E ↔ ((ψ y : ↥L₀) : G₀) ∈ E₀ := hψ y
      _ ↔ ((ψ x * ψ y * (ψ x)⁻¹ : ↥L₀) : G₀) ∈ E₀ := h (ψ y)
      _ ↔ ((x * y * x⁻¹ : ↥L) : G) ∈ E := key.symm

private noncomputable def normalizerInfEquivOfMulEquiv {G G₀ : Type*} [Group G] [Group G₀]
    {L E : Subgroup G} {L₀ E₀ : Subgroup G₀} (ψ : ↥L ≃* ↥L₀)
    (hN : ∀ x : ↥L, (x : G) ∈ normalizer (E : Set G) ↔
      ((ψ x : ↥L₀) : G₀) ∈ normalizer (E₀ : Set G₀)) :
    ↥(normalizer (E : Set G) ⊓ L) ≃ ↥(normalizer (E₀ : Set G₀) ⊓ L₀) where
  toFun g :=
    ⟨ψ ⟨g.1, g.2.2⟩, (hN ⟨g.1, g.2.2⟩).1 g.2.1, (ψ ⟨g.1, g.2.2⟩).2⟩
  invFun g :=
    ⟨(ψ.symm ⟨g.1, g.2.2⟩ : ↥L),
      (hN (ψ.symm ⟨g.1, g.2.2⟩)).2 (by simpa using g.2.1),
      (ψ.symm ⟨g.1, g.2.2⟩ : ↥L).2⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp

theorem card_normalizer_inf_eq_of_mulEquiv {G G₀ : Type*} [Group G] [Group G₀]
    {L E : Subgroup G} {L₀ E₀ : Subgroup G₀} (ψ : ↥L ≃* ↥L₀)
    (hN : ∀ x : ↥L, (x : G) ∈ normalizer (E : Set G) ↔
      ((ψ x : ↥L₀) : G₀) ∈ normalizer (E₀ : Set G₀)) :
    Nat.card ↥(normalizer (E : Set G) ⊓ L) = Nat.card ↥(normalizer (E₀ : Set G₀) ⊓ L₀) := by
  exact Nat.card_congr (normalizerInfEquivOfMulEquiv ψ hN)

section Model


theorem Model.Zq_le_normalizer_E0 : Model.Zq ≤ normalizer (Model.E0 : Set Q3) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Model.conj_mem_E0 hg x hx
  · intro hx
    have h := Model.conj_mem_E0 (Model.Zq.inv_mem hg) _ hx
    simpa [mul_assoc] using h

theorem Model.card_B0_eq_mul_card_duadStab :
    Nat.card ↥Model.B0 = 2 ^ 11 * Nat.card ↥(duadStab (Model.tauM24 0) (Model.tauM24 1)) := by
  have h1 : Nat.card ↥Model.B0 = Nat.card ↥(Model.B0.subgroupOf Model.Zq) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Model.B0_le_Zq).toEquiv).symm
  rw [h1, Model.B0_subgroupOf_Zq_eq_Bduad, Model.cocodeExtension_Zq.card_Bduad, Model.card_E0q]

end Model

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}

theorem Std.exists_pinL
    (h : Std G L E t) (hr : L.relIndex (centralizer ({t} : Set G)) = 2) :
    ∃ ψL : ↥L ≃* ↥Model.L0,
      (∀ x : ↥L, (x : G) ∈ E ↔ ((ψL x : ↥Model.L0) : Q3) ∈ Model.E0) ∧
      ∀ x : ↥L, (x : G) ∈ normalizer (E : Set G) ↔ ((ψL x : ↥Model.L0) : Q3) ∈ Model.Zq := by
  obtain ⟨ψ₁, -, -, -, hψ₁⟩ := Std.exists_modelIso h
  obtain ⟨ψ₂, hψ₂⟩ := Model.exists_equiv_Cd_mem_E0_iff
  let ψL : ↥L ≃* ↥Model.L0 := ψ₁.trans ψ₂.symm
  have hψL : ∀ x : ↥L, ψ₂ (ψL x) = ψ₁ x := fun x => ψ₂.apply_symm_apply (ψ₁ x)
  have hE : ∀ x : ↥L, (x : G) ∈ E ↔ ((ψL x : ↥Model.L0) : Q3) ∈ Model.E0 := fun x => by
    rw [hψ₂ (ψL x), hψL x, hψ₁ x]
  have hE0L0 : Model.E0 ≤ Model.L0 := Model.E0_le_B0.trans Model.B0_le_L0
  have hN := mem_normalizer_iff_of_mulEquiv h.E_le hE0L0 ψL hE
  refine ⟨ψL, hE, fun x => (hN x).trans ?_⟩
  haveI : Finite ↥Model.L0 := Finite.of_equiv _ ψL.toEquiv
  haveI : Finite ↥(normalizer (Model.E0 : Set Q3) ⊓ Model.L0) :=
    Finite.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  obtain ⟨D⟩ := nonempty_normCocode h.m24 Model.tauM24_zero_ne_one
  have hcard : Nat.card ↥(normalizer (Model.E0 : Set Q3) ⊓ Model.L0) = Nat.card ↥Model.B0 := by
    rw [← card_normalizer_inf_eq_of_mulEquiv ψL hN,
      Std.card_normalizer_inf_eq_mul_card_duadStab h hr D Model.tauM24_zero_ne_one,
      Model.card_B0_eq_mul_card_duadStab]
  have hle : Model.B0 ≤ normalizer (Model.E0 : Set Q3) ⊓ Model.L0 := fun y hy =>
    ⟨Model.Zq_le_normalizer_E0 (Model.B0_le_Zq hy), Model.B0_le_L0 hy⟩
  have heq : Model.B0 = normalizer (Model.E0 : Set Q3) ⊓ Model.L0 :=
    Subgroup.eq_of_le_of_card_ge hle hcard.le
  constructor
  · intro hy
    have hyB : ((ψL x : ↥Model.L0) : Q3) ∈ Model.B0 := heq ▸ ⟨hy, (ψL x).2⟩
    exact Model.B0_le_Zq hyB
  · intro hy
    exact Model.Zq_le_normalizer_E0 hy

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
