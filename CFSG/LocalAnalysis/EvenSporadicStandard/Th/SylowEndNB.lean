module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndNA

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThLocalIn.mem_S_of_acts_like (W : ThLocalIn L S A B z) {Z : Subgroup G}
    (hZ : IsPGroup 2 Z) (hSZ : S ≤ Z) (hZA : ∀ w ∈ Z, ∀ a ∈ A, w * a * w⁻¹ ∈ A) {l : G}
    (hl : l ∈ L) {y : G} (hyZ : y ∈ Z) (hly : ∀ a ∈ A, l * a * l⁻¹ = y * a * y⁻¹) : l ∈ S := by
  have hB2 : IsPGroup 2 B := IsPGroup.of_card (n := 9) W.B_card
  have hZC : Z ≤ normalizer (centralizer (A : Set G) : Set G) := by
    refine le_normalizer_of_conj_mem fun w hw c hc => ?_
    refine mem_centralizer_iff.2 fun a ha => ?_
    have ha' : w⁻¹ * a * w ∈ A := by
      have := hZA w⁻¹ (Z.inv_mem hw) a ha
      simpa using this
    have h1 := mem_centralizer_iff.1 hc _ ha'
    calc a * (w * c * w⁻¹) = w * ((w⁻¹ * a * w) * c) * w⁻¹ := by group
      _ = w * (c * (w⁻¹ * a * w)) * w⁻¹ := by rw [h1]
      _ = w * c * w⁻¹ * a := by group
  set X := L ⊓ (Z ⊔ centralizer (A : Set G)) with hX
  have hSX : S ≤ X := le_inf W.S_le (le_trans hSZ le_sup_left)
  have hX2 : IsPGroup 2 X := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨x, hxX⟩
    obtain ⟨hxL, hxZ⟩ := Subgroup.mem_inf.1 hxX
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Z _ hZC] at hxZ
    obtain ⟨w, hw, c₁, hc₁, rfl⟩ := hxZ
    have key : ∀ (u a : G) (k : ℕ),
        u ^ (k + 1) * a * (u ^ (k + 1))⁻¹ = u * (u ^ k * a * (u ^ k)⁻¹) * u⁻¹ := by
      intro u a k
      rw [pow_succ', mul_inv_rev]
      simp only [mul_assoc]
    have hpow : ∀ k : ℕ, ∀ a ∈ A, (w * c₁) ^ k * a * ((w * c₁) ^ k)⁻¹ = w ^ k * a * (w ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => intro a ha; simp
      | succ k ih =>
        intro a ha
        have hwk : w ^ k * a * (w ^ k)⁻¹ ∈ A := hZA _ (Z.pow_mem hw k) a ha
        have hc := mem_centralizer_iff.1 hc₁ _ hwk
        rw [key (w * c₁) a k, key w a k, ih a ha]
        calc w * c₁ * (w ^ k * a * (w ^ k)⁻¹) * (w * c₁)⁻¹
            = w * (c₁ * (w ^ k * a * (w ^ k)⁻¹) * c₁⁻¹) * w⁻¹ := by group
          _ = w * (w ^ k * a * (w ^ k)⁻¹) * w⁻¹ := by
              rw [show c₁ * (w ^ k * a * (w ^ k)⁻¹) * c₁⁻¹ = w ^ k * a * (w ^ k)⁻¹ by
                rw [← hc]; group]
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hZ ⟨w, hw⟩
    have hwj : w ^ 2 ^ j = 1 := by
      have := pow_orderOf_eq_one (⟨w, hw⟩ : Z)
      rw [hj] at this
      simpa using congrArg Subtype.val this
    have hxk : (w * c₁) ^ 2 ^ j ∈ B := by
      refine (W.mem_B_iff _ (L.pow_mem hxL _)).2 fun a ha => ?_
      have := hpow (2 ^ j) a ha
      rw [hwj] at this
      simp only [one_mul, inv_one, mul_one] at this
      calc (w * c₁) ^ 2 ^ j * a = ((w * c₁) ^ 2 ^ j * a * ((w * c₁) ^ 2 ^ j)⁻¹) *
          (w * c₁) ^ 2 ^ j := by group
        _ = a * (w * c₁) ^ 2 ^ j := by rw [this]
    obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.1 hB2 ⟨_, hxk⟩
    have hi' : orderOf ((w * c₁) ^ 2 ^ j) = 2 ^ i := by rw [← hi, Subgroup.orderOf_mk]
    have hdvd : orderOf (w * c₁) ∣ 2 ^ (j + i) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_add, pow_mul, ← hi']
      exact pow_orderOf_eq_one _
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨m, by rw [← hm, Subgroup.orderOf_mk]⟩
  have hXS : X ≤ S := W.maximal X inf_le_left hX2 hSX
  have hc : y⁻¹ * l ∈ centralizer (A : Set G) := by
    refine mem_centralizer_iff.2 fun a ha => ?_
    calc a * (y⁻¹ * l) = y⁻¹ * (y * a * y⁻¹) * l := by group
      _ = y⁻¹ * (l * a * l⁻¹) * l := by rw [hly a ha]
      _ = y⁻¹ * l * a := by group
  have hlX : l ∈ X := ⟨hl, by
    have : l = y * (y⁻¹ * l) := by group
    rw [this]
    exact mul_mem_sup hyZ hc⟩
  exact hXS hlX

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

theorem ThCyc.exists_centralizing_mem_normalizer_Tprime
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hT : S ⊔ Bp A t ≤ P)
    (hPN : ¬ P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) :
    ∃ c ∈ P, (∀ a ∈ A, c * a * c⁻¹ = a) ∧
      c ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G) ∧ c ∉ S ⊔ Bp A t := by
  have hTN := H.S_sup_Bp_le_normalizer W
  have hSP : S ≤ P := le_sup_left.trans hT
  have hne : S ⊔ Bp A t ≠ P := fun h => hPN (h ▸ hTN)
  obtain ⟨y, hyP, hyN, hyT⟩ : ∃ y ∈ P, y ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G) ∧
      y ∉ S ⊔ Bp A t := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_of_inf_normalizer_le hP hT fun x hx hxn => hcon x hx hxn)
  have hyA : y ∈ normalizer (A : Set G) :=
    H.normalizer_Tprime_le_normalizer_A W W2 hD hAb hZ hyN
  have hyA' : ∀ a ∈ A, y * a * y⁻¹ ∈ A := fun a ha => (mem_normalizer_iff.1 hyA a).1 ha
  obtain ⟨l, hlL, hl⟩ := W.surj (fun a => y * a * y⁻¹) hyA' (fun a _ b _ => by group)
    (fun a _ b _ hab => by simpa using hab)
  have hSNA : S ≤ normalizer (A : Set G) :=
    le_normalizer_of_conj_mem fun n hn x hx => W.conj_mem_A (mem_iff_conj_of_mem hn) hx
  have hlS : l ∈ S := W.mem_S_of_acts_like (Z := P ⊓ normalizer (A : Set G))
    (hP.to_le inf_le_left) (fun s hs => ⟨hSP hs, hSNA hs⟩)
    (fun w hw a ha => (mem_normalizer_iff.1 hw.2 a).1 ha) hlL ⟨hyP, hyA⟩ (fun a ha => hl a ha)
  have hlT : l ∈ S ⊔ Bp A t := mem_sup_left hlS
  refine ⟨l⁻¹ * y, P.mul_mem (P.inv_mem (hSP hlS)) hyP, fun a ha => ?_,
    mul_mem (inv_mem (Subgroup.le_normalizer hlT)) hyN, fun hc => hyT ?_⟩
  · calc (l⁻¹ * y) * a * (l⁻¹ * y)⁻¹ = l⁻¹ * (y * a * y⁻¹) * l := by group
      _ = l⁻¹ * (l * a * l⁻¹) * l := by rw [hl a ha]
      _ = a := by group
  · have : y = l * (l⁻¹ * y) := by group
    rw [this]
    exact mul_mem hlT hc

end

end CFSG.EvenSporadicStandard.ThStd
