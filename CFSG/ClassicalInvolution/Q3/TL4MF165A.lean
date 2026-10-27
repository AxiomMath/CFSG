module

public import CFSG.ClassicalInvolution.Q3.TL4MF165ARow
public import CFSG.ClassicalInvolution.Q3.TL4MF165APair
public import CFSG.ClassicalInvolution.Q3.TL4Mdl1643A
public import CFSG.LieType.SeitzGeneration.ExcPlanePair
public import CFSG.LieType.Simplicity.Classical
public import CFSG.ClassicalInvolution.Q3.TL4MF165ADefs
public import CFSG.ClassicalInvolution.Q3.TL4MF165AInner

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.Assembly.LowTwoRank


theorem model165Aut_proved : Model165Aut := by
  intro L _ _ hL 𝒳 hinn A hAinn hA2 hcard
  rcases hL with ⟨hsimp, ⟨p, f, hp, hp2, hl⟩ | hM11⟩ | ⟨hperf, hM12⟩
  · have : IsSimpleGroup L := hsimp
    obtain ⟨t, ht, hlt⟩ : ∃ t : StatedLieTag, (t = .PSL ∨ t = .PSU) ∧
        CFSG.Blueprint.LieModel L t 3 p f := by
      rcases hl with hl | hl
      · exact ⟨.PSL, Or.inl rfl, hl⟩
      · exact ⟨.PSU, Or.inr rfl, hl⟩
    by_cases hq3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp hq3
      exact MF165A.alphaOf_eq_bot_of_autOddFreeInner
        (MF165A.autOddFreeInner_of_lieModel_three ht hlt) hinn hAinn hA2 hcard
    · have hf : 1 ≤ f := by
        rcases Nat.eq_zero_or_pos f with rfl | h
        · exfalso
          rcases hlt with ⟨-, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
          · exact absurd hm.1.2.1 (by norm_num)
          all_goals exact absurd h0 (by norm_num)
        · exact h
      have h5 : 5 ≤ p ^ f := by
        have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
        obtain ⟨k, hk⟩ := hodd
        omega
      exact MF165A.alphaOf_eq_bot_of_lieModel ht hp hp2 h5 hlt hinn hAinn hA2 hcard
  · exact MF165A.alphaOf_eq_bot_of_autOddFreeInner (MF165A.autOddFreeInner_of_m11 hM11) hinn
      hAinn hA2 hcard
  · have : Group.IsPerfect L := hperf
    exact MF165A.alphaOf_eq_bot_of_autOddFreeInner (MF165A.autOddFreeInner_of_m12 hM12) hinn
      hAinn hA2 hcard

theorem autAlphaPairs_of_model165Aut (h : Model165Aut) {X : Type} [Group X] [Finite X]
    (hX : (IsSimpleGroup X ∧ ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
        (CFSG.Blueprint.LieModel X .PSL 3 p f ∨ CFSG.Blueprint.LieModel X .PSU 3 p f)) ∨
          CFSG.Blueprint.NativeSporadic.IsSporadic X .M11)) ∨
      (Group.IsPerfect X ∧
        CFSG.Blueprint.NativeSporadic.IsSporadic (X ⧸ Subgroup.center X) .M12))
    (hZ : Subgroup.center X = ⊥) : AutAlphaPairs X := by
  intro 𝒳 hinn a a' ha2 ha1 ha'a hcomm hconj
  have hinj := conj_injective_of_center_eq_bot hZ
  obtain ⟨g, hg⟩ := hconj
  have ha'2 : a' * a' = 1 := by
    rw [← hg]
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have ha'1 : a' ≠ 1 := by
    intro h1
    apply ha1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [hg, h1]; group
  have hu2 : (⟨MulAut.conj a, hinn a⟩ : ↥𝒳) * ⟨MulAut.conj a, hinn a⟩ = 1 :=
    Subtype.ext (by
      show MulAut.conj a * MulAut.conj a = 1
      rw [← map_mul, ha2, map_one])
  have hv2 : (⟨MulAut.conj a', hinn a'⟩ : ↥𝒳) * ⟨MulAut.conj a', hinn a'⟩ = 1 :=
    Subtype.ext (by
      show MulAut.conj a' * MulAut.conj a' = 1
      rw [← map_mul, ha'2, map_one])
  have huv : (⟨MulAut.conj a, hinn a⟩ : ↥𝒳) * ⟨MulAut.conj a', hinn a'⟩ =
      ⟨MulAut.conj a', hinn a'⟩ * ⟨MulAut.conj a, hinn a⟩ :=
    Subtype.ext (by
      show MulAut.conj a * MulAut.conj a' = MulAut.conj a' * MulAut.conj a
      rw [← map_mul, ← map_mul, hcomm])
  have hu1 : (⟨MulAut.conj a, hinn a⟩ : ↥𝒳) ≠ 1 := fun h1 =>
    ha1 (hinj ((congrArg Subtype.val h1).trans (map_one MulAut.conj).symm))
  have hv1 : (⟨MulAut.conj a', hinn a'⟩ : ↥𝒳) ≠ 1 := fun h1 =>
    ha'1 (hinj ((congrArg Subtype.val h1).trans (map_one MulAut.conj).symm))
  have hvu : (⟨MulAut.conj a', hinn a'⟩ : ↥𝒳) ≠ ⟨MulAut.conj a, hinn a⟩ := fun h1 =>
    ha'a (hinj (congrArg Subtype.val h1))
  have hord : ∀ w : ↥𝒳, w * w = 1 → w ≠ 1 → orderOf w = 2 := fun w hw hw1 =>
    orderOf_eq_prime (by rw [sq]; exact hw) hw1
  have hnot : (⟨MulAut.conj a', hinn a'⟩ : ↥𝒳) ∉
      Subgroup.zpowers (⟨MulAut.conj a, hinn a⟩ : ↥𝒳) := by
    intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h2 := hord _ hu2 hu1
    rw [← zpow_mod_orderOf, h2] at hn
    rcases Int.emod_two_eq_zero_or_one n with h0 | h0
    · rw [Nat.cast_ofNat, h0, zpow_zero] at hn
      exact hv1 hn.symm
    · rw [Nat.cast_ofNat, h0, zpow_one] at hn
      exact hvu hn.symm
  have hcard : Nat.card ↥(Subgroup.closure ({⟨MulAut.conj a, hinn a⟩,
      ⟨MulAut.conj a', hinn a'⟩} : Set ↥𝒳)) = 4 :=
    (CFSG.LieType.SeitzGeneration.card_closure_pair_sq Nat.prime_two huv (hord _ hu2 hu1)
      (hord _ hv2 hv1) hnot).trans (by norm_num)
  have hle : Subgroup.closure ({⟨MulAut.conj a, hinn a⟩, ⟨MulAut.conj a', hinn a'⟩} :
      Set ↥𝒳) ≤ (innSubgroup X).comap 𝒳.subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨a, rfl⟩
    · exact ⟨a', rfl⟩
  exact h X hX 𝒳 (by rintro _ ⟨x, rfl⟩; exact hinn x) _ (fun x hx => hle hx)
    (E1643.closure_pair_facts hu2 hv2 huv).2 hcard

theorem autAlphaPairs_of_lieModel (X : Type) [Group X] [Finite X] (p f : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2)
    (h : CFSG.Blueprint.LieModel X .PSL 3 p f ∨ CFSG.Blueprint.LieModel X .PSU 3 p f) :
    AutAlphaPairs X := by
  obtain ⟨t, ht, hlt⟩ : ∃ t : StatedLieTag, (t = .PSL ∨ t = .PSU) ∧
      CFSG.Blueprint.LieModel X t 3 p f := by
    rcases h with hl | hl
    · exact ⟨.PSL, Or.inl rfl, hl⟩
    · exact ⟨.PSU, Or.inr rfl, hl⟩
  have hsimp : IsSimpleGroup X := by
    rcases ht with rfl | rfl <;> rcases hlt with ⟨-, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (LieType.Simplicity.fam_PSL_simplicity X 3 p f hm).2
    all_goals first
      | exact (ClassicalGroups.Unitary.fam_PSU_simplicity X 3 p f hm).2
      | exact absurd h0 (by norm_num)
  have hf : 1 ≤ f := by
    rcases hlt with ⟨-, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hm.1.2.1
    all_goals exact absurd h0 (by norm_num)
  have hZ := MF165A.center_eq_bot_of_lieModel ht hp hp2 hf hlt
  exact autAlphaPairs_of_model165Aut model165Aut_proved (Or.inl ⟨hsimp, Or.inl ⟨p, f, hp, hp2, h⟩⟩)
    hZ

end CFSG.ClassicalInvolution.Q3.TL4
