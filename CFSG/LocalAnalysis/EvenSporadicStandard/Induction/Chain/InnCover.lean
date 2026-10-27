module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Perfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Order

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

theorem exists_mul_of_cover {A K' : Subgroup H} (hKq : CFSG.IsQuasisimple ↥K')
    (hcq : cqOrd A = cqOrd K') (hKN : K' ≤ normalizer (A : Set H))
    (hKAC : ∀ k ∈ K', ∃ a ∈ A, ∃ c ∈ centralizer (A : Set H), k = a * c)
    (hnc : ¬ ∀ k ∈ K', ∀ a ∈ A, k * a = a * k) :
    ∀ a ∈ A, ∃ k ∈ K', ∃ c ∈ centralizer (A : Set H), a = k * c := by
  classical
  let ρ : ↥(normalizer (A : Set H)) →* MulAut ↥A := Subgroup.normalizerMonoidHom A
  have hρ : ∀ (g : ↥(normalizer (A : Set H))) (y : ↥A),
      ((ρ g y : ↥A) : H) = (g : H) * y * (g : H)⁻¹ := fun g y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe A g y
  let ρA : ↥A →* MulAut ↥A := ρ.comp (Subgroup.inclusion Subgroup.le_normalizer)
  let ρK : ↥K' →* MulAut ↥A := ρ.comp (Subgroup.inclusion hKN)
  have hρA : ∀ (a y : ↥A), ((ρA a y : ↥A) : H) = (a : H) * y * (a : H)⁻¹ := fun a y =>
    hρ (Subgroup.inclusion Subgroup.le_normalizer a) y
  have hρK : ∀ (k : ↥K') (y : ↥A), ((ρK k y : ↥A) : H) = (k : H) * y * (k : H)⁻¹ := fun k y =>
    hρ (Subgroup.inclusion hKN k) y
  have hkerA : ρA.ker = center ↥A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h g
      have h1 := congrArg (fun φ : MulAut ↥A => ((φ g : ↥A) : H)) h
      simp only [hρA, MulAut.one_apply] at h1
      apply Subtype.ext
      show (g : H) * a = a * g
      calc (g : H) * a = ((a : H) * g * (a : H)⁻¹) * a := by rw [h1]
        _ = a * g := by group
    · intro h
      ext y
      show ((ρA a y : ↥A) : H) = y
      rw [hρA]
      have this : (y : H) * a = a * y := congrArg Subtype.val (h y)
      calc (a : H) * y * (a : H)⁻¹ = ((y : H) * a) * (a : H)⁻¹ := by rw [this]
        _ = y := by group
  have hcardA : Nat.card ρA.range = cqOrd A := by
    have e1 : (↥A ⧸ ρA.ker) ≃* ρA.range := QuotientGroup.quotientKerEquivRange ρA
    have e2 : (↥A ⧸ ρA.ker) ≃* (↥A ⧸ center ↥A) := QuotientGroup.quotientMulEquivOfEq hkerA
    calc Nat.card ρA.range = Nat.card (↥A ⧸ ρA.ker) := (Nat.card_congr e1.toEquiv).symm
      _ = Nat.card (↥A ⧸ center ↥A) := Nat.card_congr e2.toEquiv
  have hkerK : ρK.ker ≤ center ↥K' := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq ρK.normal_ker with htop | hle
    · exfalso
      apply hnc
      intro k hk a ha
      have hk1 : (⟨k, hk⟩ : ↥K') ∈ ρK.ker := by rw [htop]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hk1
      have h1 := congrArg (fun φ : MulAut ↥A => ((φ ⟨a, ha⟩ : ↥A) : H)) hk1
      simp only [hρK, MulAut.one_apply] at h1
      calc k * a = (k * a * k⁻¹) * k := by group
        _ = a * k := by rw [show k * a * k⁻¹ = a from h1]
    · exact hle
  have hcardK : cqOrd K' ≤ Nat.card ρK.range := card_quot_center_le_card_range ρK hkerK
  have hle : ρK.range ≤ ρA.range := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨a, ha, c, hc, hkac⟩ := hKAC k k.2
    refine ⟨⟨a, ha⟩, ?_⟩
    ext y
    show ((ρA ⟨a, ha⟩ y : ↥A) : H) = ((ρK k y : ↥A) : H)
    rw [hρA, hρK]
    have hcy : (y : H) * c = c * y := Subgroup.mem_centralizer_iff.1 hc y y.2
    show a * (y : H) * a⁻¹ = (k : H) * y * (k : H)⁻¹
    rw [hkac]
    calc a * (y : H) * a⁻¹ = a * (c * (y : H) * c⁻¹) * a⁻¹ := by
          rw [← hcy]; group
      _ = (a * c) * (y : H) * (a * c)⁻¹ := by group
  have : Finite ↥ρA.range := Finite.of_surjective ρA.rangeRestrict ρA.rangeRestrict_surjective
  have hrange : ρK.range = ρA.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardA, hcq]; exact hcardK)
  intro a ha
  have hmem : ρA ⟨a, ha⟩ ∈ ρK.range := by
    rw [hrange]
    exact ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨k, hk⟩ := hmem
  refine ⟨(k : H), k.2, (k : H)⁻¹ * a, ?_, by group⟩
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  have h1 := congrArg (fun φ : MulAut ↥A => ((φ ⟨y, hy⟩ : ↥A) : H)) hk
  simp only [hρK, hρA] at h1
  have h1' : (k : H) * y * (k : H)⁻¹ = a * y * a⁻¹ := h1
  calc y * ((k : H)⁻¹ * a) = (k : H)⁻¹ * ((k : H) * y * (k : H)⁻¹) * a := by group
    _ = (k : H)⁻¹ * (a * y * a⁻¹) * a := by rw [h1']
    _ = (k : H)⁻¹ * a * y := by group

end CFSG.EvenSporadicStandard.Induction
