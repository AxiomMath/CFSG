module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ProdAut
public import CFSG.Alternating.Multipliers.Small

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers

theorem card_ker_dvd_six_alt6 {P : Type} [Group P]
    (hP : commutator P = ⊤) {π : P →* alternatingGroup (Fin 6)} (hπs : Function.Surjective π)
    (hπk : π.ker ≤ center P) : Nat.card π.ker ∣ 6 := by
  have : Group.IsPerfect P := (Group.isPerfect_def).2 hP
  have h := Subgroup.card_map_dvd (hopfMultiplier (alternatingGroup (Fin 6)))
    (hopfLift π hπs hπk)
  rwa [map_hopfMultiplier_hopfLift π hπs hπk, hopfMultiplier_alternatingGroup_six.2] at h

theorem alt6_simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt6_commutator : commutator (alternatingGroup (Fin 6)) = ⊤ :=
  commutator_alternatingGroup_eq_top (by simp)

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem alt6_hsimple (N : Subgroup (alternatingGroup (Fin 6))) (hN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  have := hN
  exact alt6_simple.eq_bot_or_eq_top_of_normal N

theorem alt6_central {a : alternatingGroup (Fin 6)} (h : ∀ c, a * c = c * a) : a = 1 := by
  have hc : a ∈ center (alternatingGroup (Fin 6)) :=
    Subgroup.mem_center_iff.2 fun c => (h c).symm
  rcases alt6_hsimple (center (alternatingGroup (Fin 6))) inferInstance with h0 | h1
  · rwa [h0, mem_bot] at hc
  · exfalso
    have hcomm : ∀ x y : alternatingGroup (Fin 6), x * y = y * x := fun x y => by
      have hx : x ∈ center (alternatingGroup (Fin 6)) := by rw [h1]; trivial
      exact (Subgroup.mem_center_iff.1 hx y).symm
    have hbot : commutator (alternatingGroup (Fin 6)) = ⊥ := by
      rw [eq_bot_iff]
      refine commutator_le.2 fun x _ y _ => ?_
      rw [mem_bot, commutatorElement_def]
      have := hcomm x y
      calc x * y * x⁻¹ * y⁻¹ = y * x * x⁻¹ * y⁻¹ := by rw [this]
        _ = 1 := by group
    rw [alt6_commutator] at hbot
    have h5 : (⟨1, one_mem _⟩ : alternatingGroup (Fin 6)) = (1 : alternatingGroup (Fin 6)) := rfl
    have hcard : Nat.card (alternatingGroup (Fin 6)) = 1 := by
      rw [← Subgroup.card_top (G := alternatingGroup (Fin 6)), hbot, Subgroup.card_bot]
    rw [card_alt6] at hcard
    exact absurd hcard (by norm_num)

theorem prod_normal_eq_top_of_simple {S : Type} [Group S]
    (hS : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (hc : ∀ a : S, (∀ c, a * c = c * a) → a = 1)
    (M : Subgroup (S × S)) [hM : M.Normal] {a b : S} (ha : a ≠ 1) (hb : b ≠ 1)
    (hm : (a, b) ∈ M) : M = ⊤ := by
  obtain ⟨c, hc'⟩ : ∃ c : S, a * c ≠ c * a := by
    by_contra h
    push Not at h
    exact ha (hc a h)
  obtain ⟨d, hd⟩ : ∃ d : S, b * d ≠ d * b := by
    by_contra h
    push Not at h
    exact hb (hc b h)
  have h1 : (a * c * a⁻¹ * c⁻¹, (1 : S)) ∈ M := by
    have h := M.mul_mem hm (hM.conj_mem _ (M.inv_mem hm) (c, 1))
    have e : (a, b) * ((c, 1) * (a, b)⁻¹ * (c, 1)⁻¹) = (a * c * a⁻¹ * c⁻¹, (1 : S)) := by
      ext <;> simp [mul_assoc]
    rwa [e] at h
  have h2 : ((1 : S), b * d * b⁻¹ * d⁻¹) ∈ M := by
    have h := M.mul_mem hm (hM.conj_mem _ (M.inv_mem hm) (1, d))
    have e : (a, b) * ((1, d) * (a, b)⁻¹ * (1, d)⁻¹) = ((1 : S), b * d * b⁻¹ * d⁻¹) := by
      ext <;> simp [mul_assoc]
    rwa [e] at h
  have hne1 : a * c * a⁻¹ * c⁻¹ ≠ 1 := by
    intro h
    apply hc'
    calc a * c = a * c * a⁻¹ * c⁻¹ * c * a := by group
      _ = c * a := by rw [h, one_mul]
  have hne2 : b * d * b⁻¹ * d⁻¹ ≠ 1 := by
    intro h
    apply hd
    calc b * d = b * d * b⁻¹ * d⁻¹ * d * b := by group
      _ = d * b := by rw [h, one_mul]
  have hf := ProdAut.fst_of_ne_one hS M hne1 h1
  have hs := ProdAut.snd_of_ne_one hS M hne2 h2
  rw [eq_top_iff]
  rintro ⟨s, s'⟩ -
  have := M.mul_mem (hf s) (hs s')
  simpa using this

end CFSG.EvenSporadicStandard.M24Std.DRes
