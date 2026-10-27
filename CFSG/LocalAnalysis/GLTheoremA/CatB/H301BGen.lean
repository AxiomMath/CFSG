module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenXs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open
open scoped commutatorElement

section Grow

variable {G : Type*} [Group G]

theorem exists_mem_normalizer_sdiff {T S : Subgroup G} [Finite S] (hS : IsPGroup 2 S)
    (hTS : T < S) : ∃ x ∈ S, x ∉ T ∧ x ∈ Subgroup.normalizer (T : Set G) := by
  set IP : Subgroup S := T.subgroupOf S with hIP
  have hIPlt : IP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hTS.ne (le_antisymm hTS.le fun x hx => ?_)
    have : (⟨x, hx⟩ : S) ∈ IP := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : IP < Subgroup.normalizer (IP : Set S) :=
    Group.normalizerCondition_of_isNilpotent IP hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, fun hx => hxnot (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (Subgroup.normalizer (T : Set G)).subgroupOf S := by
    rw [Subgroup.subgroupOf_normalizer_eq hTS.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

theorem forall_of_normalizer_step {S T₀ : Subgroup G} [Finite S] (hS : IsPGroup 2 S)
    (P : Subgroup G → Prop) (h₀ : T₀ ≤ S) (hP₀ : P T₀)
    (hstep : ∀ T : Subgroup G, T₀ ≤ T → T < S → P T →
      P (Subgroup.normalizer (T : Set G) ⊓ S)) : P S := by
  have key : ∀ n : ℕ, ∀ T : Subgroup G, T₀ ≤ T → T ≤ S → P T →
      Nat.card S - Nat.card T = n → P S := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hT₀ hTS hPT hn
      by_cases hTeq : T = S
      · exact hTeq ▸ hPT
      · have hlt : T < S := lt_of_le_of_ne hTS hTeq
        obtain ⟨x, hxS, hxT, hxN⟩ := exists_mem_normalizer_sdiff hS hlt
        have hTT' : T < Subgroup.normalizer (T : Set G) ⊓ S := by
          refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hlt.le) fun h => hxT ?_
          rw [h]
          exact Subgroup.mem_inf.2 ⟨hxN, hxS⟩
        haveI : Finite (Subgroup.normalizer (T : Set G) ⊓ S : Subgroup G) :=
          Finite.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
        have hc1 := Subgroup.card_lt_of_lt hTT'
        have hc2 : Nat.card (Subgroup.normalizer (T : Set G) ⊓ S : Subgroup G) ≤ Nat.card S :=
          Subgroup.card_le_of_le inf_le_right
        exact ih (Nat.card S - Nat.card (Subgroup.normalizer (T : Set G) ⊓ S : Subgroup G))
          (by omega) _ (hT₀.trans hTT'.le) inf_le_right (hstep T hT₀ hlt hPT) rfl
  exact key _ T₀ le_rfl h₀ hP₀ rfl

theorem normalizer_inf_le_normalizer {A T S : Subgroup G}
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    A ≤ Subgroup.normalizer ((Subgroup.normalizer (T : Set G) ⊓ S : Subgroup G) : Set G) := by
  have h1 : ∀ a ∈ A, ∀ h ∈ (Subgroup.normalizer (T : Set G) ⊓ S : Subgroup G),
      a * h * a⁻¹ ∈ (Subgroup.normalizer (T : Set G) ⊓ S : Subgroup G) := by
    intro a ha h hh
    obtain ⟨hhN, hhS⟩ := Subgroup.mem_inf.1 hh
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2 fun g => ?_,
      (Subgroup.mem_normalizer_iff.1 (hAS ha) h).1 hhS⟩
    have e : (a * h * a⁻¹) * g * (a * h * a⁻¹)⁻¹ = a * (h * (a⁻¹ * g * a) * h⁻¹) * a⁻¹ := by
      group
    have i1 : g ∈ T ↔ a⁻¹ * g * a ∈ T := by
      simpa using Subgroup.mem_normalizer_iff.1 (hAT (A.inv_mem ha)) g
    have i2 := Subgroup.mem_normalizer_iff.1 hhN (a⁻¹ * g * a)
    have i3 := Subgroup.mem_normalizer_iff.1 (hAT ha) (h * (a⁻¹ * g * a) * h⁻¹)
    rw [e]
    exact i1.trans (i2.trans i3)
  intro a ha
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => h1 a ha h hh, fun hh => ?_⟩
  have := h1 a⁻¹ (A.inv_mem ha) _ hh
  rwa [show a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h by group] at this

end Grow

section Skeleton

variable {G : Type*} [Group G] [Finite G] {R Z R₀ R₁ A : Subgroup G}

theorem isExtraspecial_of_nondeg_chain (hR : timmesfeldIsExtraspecial ↥R)
    (hZ : Z = (Subgroup.center ↥R).map R.subtype) (hZR₀ : Z ≤ R₀) (hR₀R : R₀ ≤ R)
    (hAR₀ : A ≤ Subgroup.normalizer (R₀ : Set G))
    (hU : ∀ T : Subgroup G, IsPGroup 2 T → A ≤ Subgroup.normalizer (T : Set G) →
      T ≤ Subgroup.centralizer (Z : Set G) → T ≤ R)
    (hM : ∀ T : Subgroup G, R₀ ≤ T → T ≤ R → A ≤ Subgroup.normalizer (T : Set G) →
      ∀ s ∈ T, (∀ t ∈ T, s * t = t * s) → s ∈ Z)
    (hR₁ : IsPGroup 2 R₁) (hAR₁ : A ≤ Subgroup.normalizer (R₁ : Set G)) (h01 : R₀ < R₁) :
    R₁ ≤ R ∧ timmesfeldIsExtraspecial ↥R₁ := by
  have hZ2 : Nat.card Z = 2 := by
    rw [hZ, Subgroup.card_map_of_injective R.subtype_injective]
    exact hR.2.2.2
  have hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r := fun z hz r hr =>
    (mem_center_map_iff.1 (hZ ▸ hz)).2 r hr
  obtain ⟨hR₁R, -, hrad⟩ : R₁ ≤ R ∧ A ≤ Subgroup.normalizer (R₁ : Set G) ∧
      ∀ s ∈ R₁, (∀ t ∈ R₁, s * t = t * s) → s ∈ Z :=
    forall_of_normalizer_step hR₁ (fun T => T ≤ R ∧ A ≤ Subgroup.normalizer (T : Set G) ∧
      ∀ s ∈ T, (∀ t ∈ T, s * t = t * s) → s ∈ Z) h01.le
      ⟨hR₀R, hAR₀, hM R₀ le_rfl hR₀R hAR₀⟩ fun T hT₀ hTlt ⟨hTR, hAT, hradT⟩ => by
        have hNc := normalizer_le_centralizer_of_radical hZ2 (hZR₀.trans hT₀)
          (fun z hz s hs => hZc z hz s (hTR hs)) hradT
        have hAT' := normalizer_inf_le_normalizer hAT hAR₁
        have hT'R : (Subgroup.normalizer (T : Set G) ⊓ R₁ : Subgroup G) ≤ R :=
          hU _ (hR₁.to_le inf_le_right) hAT' (inf_le_left.trans hNc)
        exact ⟨hT'R, hAT', hM _ (hT₀.trans (le_inf Subgroup.le_normalizer hTlt.le)) hT'R hAT'⟩
  refine ⟨hR₁R, (isExtraspecial_iff_radical hR hZ (hZR₀.trans h01.le) hR₁R).2 ⟨fun hle => ?_, hrad⟩⟩
  exact lt_irrefl _ (lt_of_le_of_lt (hle.trans hZR₀) h01)

end Skeleton

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
