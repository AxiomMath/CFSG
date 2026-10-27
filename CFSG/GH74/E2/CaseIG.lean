module

public import CFSG.GH74.E2.CaseIStruct
public import CFSG.GH74.E2.OddRankG

public section

namespace CFSG.GH74.E2

open Subgroup

@[expose] def NoCaseIQ8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t : G) (K : Subgroup G), IsCompCen t K →
    (ShapeA6 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K) → Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    ∀ A : Subgroup G, CaseI t A → ∀ (B : Subgroup G) (c : G), B ≤ A → B ≤ K → Nat.card B = 9 →
      c ∈ A → orderOf c = 3 → (∀ k ∈ K, c * k = k * c) →
      (∀ a ∈ A, ∃ (i : ℤ) (b : G), b ∈ B ∧ a = c ^ i * b) → False

theorem noCaseI_of (hComp : ComponentList) (hD : K0Data) (hD3 : K0Data3) (hQ8 : Q8Lemma)
    (h : NoCaseIQ8) : NoCaseI := by
  intro G _ _ hH t A hc
  obtain ⟨ht, hAC, hAab, hAcard⟩ := hc
  have hgenC : Gen4 ↥(Cen t) := Gen4.subgroup (Cen t) hH.gen4
  have hcore := hH.pPrimeCore_cen_bot ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA'ab : ElemAb 3 (A.subgroupOf (Cen t)) :=
    ⟨fun a ha b hb => Subtype.ext (hAab.1 a ha b hb), fun a ha => Subtype.ext (hAab.2 a ha)⟩
  have hA'card : Nat.card (A.subgroupOf (Cen t)) = 27 := by
    rw [← hAcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  by_cases hl : CFSG.layer ↥(Cen t) = ⊥
  ·
    have hchar :=
      CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot (↥(Cen t)) 2 hcore hl
    have hQ2 : IsPGroup 2 (CFSG.pCore 2 ↥(Cen t)) := CFSG.pCore_isPGroup
    obtain ⟨r, hcard, hF1⟩ := exists_centralizer_index_pow hQ2
      (fun b _ x hx => (CFSG.pCore_normal (p := 2) (G := ↥(Cen t))).conj_mem x hx b)
      (p := 3) Nat.prime_three (by norm_num) hA'ab
    have hker : A.subgroupOf (Cen t) ⊓ centralizer (CFSG.pCore 2 ↥(Cen t) : Set ↥(Cen t)) = ⊥ := by
      rw [eq_bot_iff]
      rintro c ⟨hcA, hcC⟩
      have hcQ : c ∈ CFSG.pCore 2 ↥(Cen t) := hchar hcC
      exact Subgroup.mem_bot.2 (eq_one_of_pgroup_of_pow hQ2 hcQ (n := 3) (by decide)
        (hA'ab.2 c hcA))
    have hrank := Gen4.rank_le_four hgenC hQ2
    rw [hker, Subgroup.card_bot, mul_one, hA'card] at hcard
    rw [orderOf_two_zmod_three] at hF1
    have hr3 : 3 ≤ r := by
      by_contra hlt
      push Not at hlt
      interval_cases r <;> norm_num at hcard
    omega
  · obtain ⟨K, hK⟩ := exists_isCompCen_of_layer_ne_bot hl
    obtain ⟨hshape, huniq⟩ := hComp G hH t ht K hK
    have hL := localK_of_component hH ht
      (fun K₁ K₂ h₁ h₂ => (huniq K₁ h₁).trans (huniq K₂ h₂).symm) hK
    have hKle : K ≤ Cen t := hK.1
    have hshape' : K0Shape ↥(K.subgroupOf (Cen t)) :=
      K0Shape.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKle).symm hshape
    have htQ : (⟨t, mem_Cen.2 rfl⟩ : Cen t) ∈ CFSG.pCore 2 ↥(Cen t) :=
      (mem_Qt.1 (t_mem_Qt ht)).2
    have ht1 : (⟨t, mem_Cen.2 rfl⟩ : Cen t) ≠ 1 := by
      intro h1
      have : t = 1 := congrArg Subtype.val h1
      rw [this, orderOf_one] at ht
      omega
    have htA : ∀ a ∈ A.subgroupOf (Cen t), a * (⟨t, mem_Cen.2 rfl⟩ : Cen t) =
        (⟨t, mem_Cen.2 rfl⟩ : Cen t) * a := by
      intro a ha
      apply Subtype.ext
      have := hAC ha
      exact mem_Cen'.1 this
    obtain ⟨hr2, hP2, hsh, B, c, hBA, hBK, hBcard, hcA, hcord, hcK, hAdec, φ, hφ, hφord, hφirr,
      hfix⟩ := caseI_structure hgenC hL hshape' hD hD3 hA'ab hA'card htQ ht1 htA
    have hQ2 : IsPGroup 2 (CFSG.pCore 2 ↥(Cen t)) := CFSG.pCore_isPGroup
    have hP2' : ∀ P : Subgroup ↥(CFSG.pCore 2 ↥(Cen t)), Group.rank ↥P ≤ 2 := by
      intro P
      have h1 := hP2 (P.map (CFSG.pCore 2 ↥(Cen t)).subtype) (by
        rintro _ ⟨x, -, rfl⟩
        exact x.2)
      rwa [← Group.rank_congr (P.equivMapOfInjective _ (Subgroup.subtype_injective _))] at h1
    obtain ⟨hQ8iso⟩ := hQ8 ↥(CFSG.pCore 2 ↥(Cen t)) φ hQ2 hr2 hP2' hφord hφirr hfix
    have hQ8G : Nonempty (↥(Qt t) ≃* QuaternionGroup 2) :=
      ⟨((CFSG.pCore 2 ↥(Cen t)).equivMapOfInjective (Cen t).subtype
        (Cen t).subtype_injective).symm.trans hQ8iso⟩
    have hshapeK : ShapeA6 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K := by
      have e := Subgroup.subgroupOfEquivOfLe hKle
      rcases hsh with h1 | h1 | h1
      · exact Or.inl (ShapeA6.of_mulEquiv e h1)
      · exact Or.inr (Or.inl (lieModel_of_mulEquiv e h1))
      · exact Or.inr (Or.inr (isSporadic_of_mulEquiv e h1))
    refine h G hH t K hK hshapeK hQ8G A ⟨ht, hAC, hAab, hAcard⟩ (B.map (Cen t).subtype)
      (c : G) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hBA hx
    · rintro _ ⟨x, hx, rfl⟩
      exact hBK hx
    · rw [Subgroup.card_map_of_injective (Cen t).subtype_injective]
      exact hBcard
    · exact hcA
    · rw [Subgroup.orderOf_coe]
      exact hcord
    · intro k hk
      have := hcK ⟨k, hKle hk⟩ hk
      exact congrArg Subtype.val this
    · intro a ha
      obtain ⟨i, b, hb, hab⟩ := hAdec ⟨a, hAC ha⟩ ha
      refine ⟨i, (b : G), ⟨b, hb, rfl⟩, ?_⟩
      have := congrArg Subtype.val hab
      simpa using this

end CFSG.GH74.E2
