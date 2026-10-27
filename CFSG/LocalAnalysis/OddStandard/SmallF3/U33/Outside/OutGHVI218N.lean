module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGHVI218B
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma23

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

variable {S : Type} [Group S] [Finite S] {ρ : MulAut S}

private theorem card_invs_sylSU3_4 : Nat.card (L23.Invs SylSU3_4) = 3 :=
  (L23.card_invs_congr L23.sylCongr).trans L23.card_invs_S

theorem FpfNonab.classify (h : FpfNonab S ρ) :
    Nonempty (S ≃* SylSL3_4) ∨ Nonempty (S ≃* SylSU3_4) := by
  have hord : orderOf ρ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp
      (orderOf_dvd_iff_pow_eq_one.mpr h.cube) with h1 | h3
    · exfalso
      have hρ1 : ρ = 1 := orderOf_eq_one_iff.mp h1
      have hall : ∀ g : S, g = 1 := fun g => h.fpf g (by rw [hρ1]; rfl)
      have hsub : Subsingleton S := ⟨fun a b => by rw [hall a, hall b]⟩
      have hle : Nat.card S ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
      have hc := h.card
      omega
    · exact h3
  obtain ⟨A, hAn, hAρ, hAeq, hAc⟩ := h.exists_selfCentralizing_Z4Z4
  have hmain := iv2_2_3 S h.card ρ hord h.fpf A hAn hAρ hAeq hAc
  by_cases hOm : Om1 A = Om1 (⊤ : Subgroup S)
  · exact Or.inr (hmain.1 hOm)
  · exact Or.inl (hmain.2 hOm)

theorem card_le_four_of_sq_eq_one_sylSU (Y : Subgroup SylSU3_4) (hY : ∀ y ∈ Y, y * y = 1) :
    Nat.card Y ≤ 4 := by
  classical
  have hcard3 : Nat.card {t : SylSU3_4 // t * t = 1 ∧ t ≠ 1} = 3 := by
    change Nat.card (L23.Invs SylSU3_4) = 3
    exact card_invs_sylSU3_4
  haveI : Finite {t : SylSU3_4 // t * t = 1 ∧ t ≠ 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard3]; norm_num)
  have hle : Nat.card Y ≤ Nat.card (Option {t : SylSU3_4 // t * t = 1 ∧ t ≠ 1}) := by
    apply Nat.card_le_card_of_injective
      (f := fun y : Y => if hy : (y : SylSU3_4) = 1 then
        (none : Option {t : SylSU3_4 // t * t = 1 ∧ t ≠ 1})
        else some ⟨(y : SylSU3_4), hY y y.2, hy⟩)
    intro y z h
    dsimp only at h
    by_cases hy : (y : SylSU3_4) = 1
    · by_cases hz : (z : SylSU3_4) = 1
      · exact Subtype.ext (by rw [hy, hz])
      · exfalso
        rw [dif_pos hy, dif_neg hz] at h
        exact absurd h (by simp)
    · by_cases hz : (z : SylSU3_4) = 1
      · exfalso
        rw [dif_neg hy, dif_pos hz] at h
        exact absurd h (by simp)
      · rw [dif_neg hy, dif_neg hz] at h
        have h' : (⟨(y : SylSU3_4), hY y y.2, hy⟩ :
              {t : SylSU3_4 // t * t = 1 ∧ t ≠ 1}) =
            ⟨(z : SylSU3_4), hY z z.2, hz⟩ := Option.some.inj h
        exact Subtype.ext (congrArg (fun t : {t : SylSU3_4 // t * t = 1 ∧ t ≠ 1} =>
          (t : SylSU3_4)) h')
  calc Nat.card Y ≤ Nat.card (Option {t : SylSU3_4 // t * t = 1 ∧ t ≠ 1}) := hle
    _ = Nat.card {t : SylSU3_4 // t * t = 1 ∧ t ≠ 1} + 1 := Finite.card_option
    _ = 4 := by rw [hcard3]

theorem GHVI218_E16 (hcard : Nat.card S = 64) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : S, ρ g = g → g = 1) (Y : Subgroup S) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hY16 : Nat.card Y = 16) (hC : centralizer (Y : Set S) = Y) :
    Nonempty (S ≃* SylSL3_4) ∧ Nat.card (center S) = 4 ∧ center S ≤ Y := by
  have hnab : ∃ a b : S, a * b ≠ b * a := by
    by_contra h
    have hcomm : ∀ a b : S, a * b = b * a := by
      intro a b
      by_contra hab
      exact h ⟨a, b, hab⟩
    have htop : centralizer (Y : Set S) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact hcomm y g
    have hYtop : Y = ⊤ := by rw [← hC, htop]
    have hcard_eq : Nat.card Y = Nat.card S := by rw [hYtop, Subgroup.card_top]
    rw [hY16, hcard] at hcard_eq
    omega
  have hf : FpfNonab S ρ := ⟨hcard, hnab, hρ, hfpf⟩
  have hSL : Nonempty (S ≃* SylSL3_4) := by
    rcases FpfNonab.classify hf with hL | hU
    · exact hL
    · exfalso
      obtain ⟨e⟩ := hU
      have hY'card : Nat.card (Y.map e.toMonoidHom) = 16 := by
        rw [Subgroup.card_map_of_injective e.injective, hY16]
      have hY'2 : ∀ y ∈ Y.map e.toMonoidHom, y * y = 1 := by
        intro y hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [← map_mul, hY2 x hx, map_one]
      have hle4 := card_le_four_of_sq_eq_one_sylSU (Y.map e.toMonoidHom) hY'2
      omega
  exact ⟨hSL, FpfNonab.card_center hf,
    (Subgroup.center_le_centralizer (Y : Set S)).trans (le_of_eq hC)⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
