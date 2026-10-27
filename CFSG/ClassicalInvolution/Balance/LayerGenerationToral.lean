module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationLie
import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

section Index

variable {X : Type*} [Group X]

@[expose] def IndexTwoCentralizes (Ē R : Subgroup X) : Prop :=
  Ē ≤ Subgroup.normalizer (R : Set X) ∧ ∃ a ∈ Ē, ∀ x ∈ Ē,
    (∀ r ∈ R, x * r = r * x) ∨ (∀ r ∈ R, (x * a) * r = r * (x * a))

private theorem exists_two_ne_one_of_card_eq_four'' {F₀ : Subgroup X} (h4 : Nat.card F₀ = 4) :
    ∃ x ∈ F₀, ∃ y ∈ F₀, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hfin : Finite F₀ := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F₀
  have hc : 2 < Fintype.card F₀ := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
  by_cases ha1 : a = 1
  · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro h
      exact hab (ha1.trans (Subtype.ext h).symm)
    · intro h
      exact hac (ha1.trans (Subtype.ext h).symm)
  · by_cases hb1 : b = 1
    · refine ⟨a, a.2, c, c.2, fun h => ha1 (Subtype.ext h), ?_, fun h => hac (Subtype.ext h)⟩
      intro h
      exact hbc (hb1.trans (Subtype.ext h).symm)
    · exact ⟨a, a.2, b, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
        fun h => hab (Subtype.ext h)⟩

theorem exists_ne_one_centralizes_of_indexTwo {Ē R F : Subgroup X} (hE2 : ∀ x ∈ Ē, x * x = 1)
    (hFĒ : F ≤ Ē) (hF4 : Nat.card F = 4) (h : IndexTwoCentralizes Ē R) :
    ∃ f ∈ F, f ≠ 1 ∧ ∀ r ∈ R, f * r = r * f := by
  obtain ⟨-, a, haĒ, hsplit⟩ := h
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_two_ne_one_of_card_eq_four'' hF4
  by_cases hxR : ∀ r ∈ R, x * r = r * x
  · exact ⟨x, hx, hx1, hxR⟩
  by_cases hyR : ∀ r ∈ R, y * r = r * y
  · exact ⟨y, hy, hy1, hyR⟩
  have hxa := (hsplit x (hFĒ hx)).resolve_left hxR
  have hya := (hsplit y (hFĒ hy)).resolve_left hyR
  have hxy' : ∀ r ∈ R, (x * y) * r = r * (x * y) := by
    have e1 : x * a * (y * a) = x * y := by
      calc x * a * (y * a) = x * (a * y) * a := by group
        _ = x * (y * a) * a := by rw [comm_of_sq_eq_one hE2 haĒ (hFĒ hy)]
        _ = x * y * (a * a) := by group
        _ = x * y := by rw [hE2 a haĒ, mul_one]
    intro r hr
    rw [← e1]
    calc x * a * (y * a) * r = x * a * ((y * a) * r) := by group
      _ = x * a * (r * (y * a)) := by rw [hya r hr]
      _ = (x * a * r) * (y * a) := by group
      _ = (r * (x * a)) * (y * a) := by rw [hxa r hr]
      _ = r * (x * a * (y * a)) := by group
  refine ⟨x * y, F.mul_mem hx hy, ?_, hxy'⟩
  intro h
  apply hxy
  have hyy : y * y = 1 := hE2 y (hFĒ hy)
  calc x = x * (y * y) := by rw [hyy, mul_one]
    _ = (x * y) * y := (mul_assoc _ _ _).symm
    _ = y := by rw [h, one_mul]

end Index

section Criterion

variable {X : Type} [Group X] [Finite X]

theorem le_layers_of_indexTwoFamily {L Ē F : Subgroup X} (hL : CFSG.IsComponent L)
    (hlie : IsOddLieComponent L) (hĒ2 : ∀ x ∈ Ē, x * x = 1) (hFĒ : F ≤ Ē) (hF4 : Nat.card F = 4)
    (hFN : F ≤ Subgroup.normalizer (L : Set X)) {𝓡 : Set (Subgroup X)}
    (hgen : L ≤ ⨆ R ∈ 𝓡, R) (hRL : ∀ R ∈ 𝓡, R ≤ L)
    (hidx : ∀ R ∈ 𝓡, IndexTwoCentralizes Ē R)
    (hlay : ∀ R ∈ 𝓡, ¬ IsInvolutionMember R → ∀ f ∈ F, f ≠ 1 → (∀ r ∈ R, f * r = r * f) →
      R ≤ centralizerLayer f) :
    L ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f := by
  have hLopen := (CFSG.isComponent_iff_open L).mp hL
  have hB := involutionCentralizerB_of_isOddLieComponent hLopen.2.2 hlie
  refine hgen.trans (iSup₂_le fun R hR => ?_)
  obtain ⟨f, hfF, hf1, hfR⟩ := exists_ne_one_centralizes_of_indexTwo hĒ2 hFĒ hF4 (hidx R hR)
  have hRlayer : R ≤ centralizerLayer f := by
    by_cases hm : IsInvolutionMember R
    · exact hm.le_centralizerLayer l2PrimeBalance hLopen.2.1 (hRL R hR)
        (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hfR r hr).symm)
        (hB f hf1 (hĒ2 f (hFĒ hfF)) (hFN hfF))
    · exact hlay R hR hm f hfF hf1 hfR
  exact le_iSup₂_of_le f hfF (le_iSup_of_le hf1 hRlayer)

end Criterion

section Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {E : Subgroup G}

omit [Finite G] in
theorem modOdd_mono {a : G} {K K' : Subgroup G} (h : K ≤ K') : modOdd a K ≤ modOdd a K' := by
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, h hk, rfl⟩

theorem LayerGenerationLie.of_indexTwoFamily (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hfam : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
      L ≤ memberJoin Ω a → ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt E a L F₀ →
        ∃ 𝓡 : Set (Subgroup (OddQuot a)), L ≤ ⨆ R ∈ 𝓡, R ∧ (∀ R ∈ 𝓡, R ≤ L) ∧
          (∀ R ∈ 𝓡, IndexTwoCentralizes (modOdd a E) R) ∧
          ∀ R ∈ 𝓡, ¬ IsInvolutionMember R → ∀ f ∈ modOdd a F₀, f ≠ 1 →
            (∀ r ∈ R, f * r = r * f) → R ≤ centralizerLayer f) :
    LayerGenerationLie Ω E a := by
  intro L hL hlie hjoin F₀ hF
  obtain ⟨𝓡, hgen, hRL, hidx, hlay⟩ := hfam L hL hlie hjoin F₀ hF
  obtain ⟨hF₀E, h4, hFn, -⟩ := hF
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hE2 ha (hF₀E hf)).symm
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => hE2 f (hF₀E hf)
  exact OddCentralizerFree.of_le_layers
    (le_layers_of_indexTwoFamily hL hlie
      (modOdd_sq_eq_one hE2 le_rfl) (modOdd_mono hF₀E)
      (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hFn hgen hRL hidx hlay)

end Frame

end CFSG.ClassicalInvolution.Balance
