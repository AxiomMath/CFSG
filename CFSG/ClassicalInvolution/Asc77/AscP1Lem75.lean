module

public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75Eta
public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75Conj
public import CFSG.ClassicalInvolution.Asc77.AscE187Conj
public import CFSG.ClassicalInvolution.Asc77.WP1Section7

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace T75

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {S : Sylow 2 G} {η β : Set (Subgroup G)}

omit [Fact p.Prime] in
theorem conjSub_eq_of_fix {A : Subgroup G} {c : G} (h : ∀ g ∈ A, c * g * c⁻¹ = g) :
    conjSub c A = A := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have h1 := h _ hx
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rw [e] at h1
    rw [h1.symm] at hx
    exact hx
  · intro hx
    have h1 := h x hx
    have e : c⁻¹ * x * c = x := by
      calc c⁻¹ * x * c = c⁻¹ * (c * x * c⁻¹) * c := by rw [h1]
        _ = x := by group
    rw [e]
    exact hx

theorem Data.false_of_sup_mem_RSet (D : Data p f Ω S η β) {U V : Subgroup G} (hU : U ∈ β)
    (hV : V ∈ β) (hne : U ≠ V) (hR : U ⊔ V ∈ RSet Ω) : False := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR
  exact D.symm.distinct hU hV hne hK (le_sup_left.trans hRK.1) (le_sup_right.trans hRK.1)

theorem Data.exists_conj_eq [Finite G] (D : Data p f Ω S η β) :
    ∃ c : G, conjSub c (⨆ A ∈ η, A) = ⨆ A ∈ β, A := by
  classical
  have hex : ∀ V : Subgroup G, V ∈ η → V ∉ β → ∃ U : Subgroup G, U ∈ β ∧ V ⊔ U ∈ RSet Ω := by
    intro V hV hVβ
    obtain ⟨U, ⟨hUβ, hU⟩, -⟩ := D.symm.partner (D.hη.1 hV).1 (D.hη.1 hV).2
    rcases hU with h | hR
    · exact absurd (h ▸ hUβ) hVβ
    · exact ⟨U, hUβ, hR⟩
  choose! partner hpβ hpR using hex
  have key : ∀ F : Finset (Subgroup G), (∀ V ∈ F, V ∈ η ∧ V ∉ β) →
      ∃ c : G, (∀ V ∈ F, conjSub c V = partner V) ∧
        ∀ A ∈ η, A ∉ F → ∀ g ∈ A, c * g * c⁻¹ = g := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, by simp, by simp⟩
    | insert V₀ F hV₀F ih =>
      intro hF
      obtain ⟨hV₀η, hV₀β⟩ := hF V₀ (Finset.mem_insert_self _ _)
      obtain ⟨c, hc1, hc2⟩ := ih fun V hV => hF V (Finset.mem_insert_of_mem hV)
      obtain ⟨y₀, hy₀V, hy₀η, hy₀β⟩ :=
        D.exists_local_conj hV₀η hV₀β (hpβ V₀ hV₀η hV₀β) (hpR V₀ hV₀η hV₀β)
      refine ⟨y₀ * c, ?_, ?_⟩
      · intro V hV
        rcases Finset.mem_insert.mp hV with rfl | hVF
        · have h1 : conjSub c V = V := conjSub_eq_of_fix (hc2 V hV₀η hV₀F)
          rw [conjSub_mul, h1, hy₀V]
        · obtain ⟨hVη, hVβ⟩ := hF V hV
          have hne : V ≠ V₀ := fun h => hV₀F (h ▸ hVF)
          have hne' : partner V ≠ partner V₀ := by
            intro h
            have hU := hpβ V hVη hVβ
            obtain ⟨V'', -, huniq⟩ := D.partner (D.hβ.1 hU).1 (D.hβ.1 hU).2
            have h1 : V = V'' := huniq V ⟨hVη, Or.inr (by rw [sup_comm]; exact hpR V hVη hVβ)⟩
            have h2 : V₀ = V'' := huniq V₀ ⟨hV₀η, Or.inr (by
              rw [sup_comm, h]; exact hpR V₀ hV₀η hV₀β)⟩
            exact hne (h1.trans h2.symm)
          rw [conjSub_mul, hc1 V hVF]
          exact conjSub_eq_of_fix fun g hg => by
            have := hy₀β (partner V) (hpβ V hVη hVβ) hne' g hg
            rw [this]; group
      · intro A hAη hAF g hg
        have hAV₀ : A ≠ V₀ := fun h => hAF (h ▸ Finset.mem_insert_self _ _)
        have hAF' : A ∉ F := fun h => hAF (Finset.mem_insert_of_mem h)
        have h1 := hc2 A hAη hAF' g hg
        calc y₀ * c * g * (y₀ * c)⁻¹ = y₀ * (c * g * c⁻¹) * y₀⁻¹ := by group
          _ = y₀ * g * y₀⁻¹ := by rw [h1]
          _ = g := by rw [hy₀η A hAη hAV₀ g hg]; group
  have hfin := Set.toFinite {V : Subgroup G | V ∈ η ∧ V ∉ β}
  obtain ⟨c, hc1, hc2⟩ := key hfin.toFinset fun V hV => (Set.Finite.mem_toFinset hfin).mp hV
  refine ⟨c, ?_⟩
  have hfixη : ∀ A ∈ η, A ∈ β → conjSub c A = A := fun A hAη hAβ =>
    conjSub_eq_of_fix (hc2 A hAη fun h => ((Set.Finite.mem_toFinset hfin).mp h).2 hAβ)
  have hmapη : ∀ A ∈ η, A ∉ β → conjSub c A = partner A := fun A hAη hAβ =>
    hc1 A ((Set.Finite.mem_toFinset hfin).mpr ⟨hAη, hAβ⟩)
  rw [conjSub_iSup₂]
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    by_cases hAβ : A ∈ β
    · rw [hfixη A hA hAβ]
      exact le_iSup₂ (f := fun A (_ : A ∈ β) => A) A hAβ
    · rw [hmapη A hA hAβ]
      exact le_iSup₂ (f := fun A (_ : A ∈ β) => A) _ (hpβ A hA hAβ)
  · refine iSup₂_le fun U hU => ?_
    by_cases hUη : U ∈ η
    · rw [← hfixη U hUη hU]
      exact le_iSup₂ (f := fun A (_ : A ∈ η) => conjSub c A) U hUη
    · obtain ⟨V, ⟨hVη, hV⟩, -⟩ := D.partner (D.hβ.1 hU).1 (D.hβ.1 hU).2
      rcases hV with h | hR
      · exact absurd (h ▸ hVη) hUη
      · have hVβ : V ∉ β := fun hVβ =>
          D.false_of_sup_mem_RSet hU hVβ (fun h => hUη (h ▸ hVη)) hR
        have hUp : partner V = U := by
          obtain ⟨U', -, huniq⟩ := D.symm.partner (D.hη.1 hVη).1 (D.hη.1 hVη).2
          have h1 : partner V = U' := huniq _ ⟨hpβ V hVη hVβ, Or.inr (hpR V hVη hVβ)⟩
          have h2 : U = U' := huniq _ ⟨hU, Or.inr (by rw [sup_comm]; exact hR)⟩
          exact h1.trans h2.symm
        rw [← hUp, ← hmapη V hVη hVβ]
        exact le_iSup₂ (f := fun A (_ : A ∈ η) => conjSub c A) V hVη

end T75

variable (p f : ℕ) [Fact p.Prime]

theorem l7_5_2_proved : L7_5_2 p f := by
  intro hp hq G _ _ Ω hΩ W hW W' hW'
  obtain ⟨η, ⟨S₁, hη, hηi⟩, rfl⟩ := hW
  obtain ⟨β₀, ⟨S₂, hβ₀, hβ₀i⟩, rfl⟩ := hW'
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₂ S₁
  have hβ : conjSub g '' β₀ ∈ etaSet Ω (S₁ : Subgroup G) := by
    have := conjSub_image_mem_etaSet hΩ.conjInvariant hβ₀ g
    rwa [hg] at this
  have hβi : ∀ s ∈ (S₁ : Subgroup G), ∀ U ∈ conjSub g '' β₀, conjSub s U ∈ conjSub g '' β₀ := by
    rintro s hs _ ⟨U, hU, rfl⟩
    rw [← hg, mem_conjSub_iff] at hs
    refine ⟨conjSub (g⁻¹ * s * g) U, hβ₀i _ hs U hU, ?_⟩
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  obtain ⟨c, hc⟩ := (T75.Data.mk hp hq hΩ hη hηi hβ hβi).exists_conj_eq
  have himg : (⨆ A ∈ conjSub g '' β₀, A) = conjSub g (⨆ A ∈ β₀, A) := by
    rw [conjSub_iSup₂, iSup_image]
  rw [himg] at hc
  have hW'eq : conjSub (g⁻¹ * c) (⨆ A ∈ η, A) = ⨆ A ∈ β₀, A := by
    rw [conjSub_mul, hc, conjSub_inv_conjSub]
  have key : ∀ W₂ : Subgroup G, conjSub (g⁻¹ * c) (⨆ A ∈ η, A) = W₂ →
      Nonempty (↥(muGroup Ω (⨆ A ∈ η, A)) ≃* ↥(muGroup Ω W₂)) := by
    rintro W₂ rfl
    exact ⟨Thompson.muGroupConjEquiv hΩ _ _⟩
  exact key _ hW'eq

end CFSG.ClassicalInvolution.Asc77
