module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08PiB

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

namespace PiData

variable {Hh : Type*} [Group Hh] [Finite Hh] {Y : Type*} [Group Y] {π : Hh →* MulAut Y} {t : Hh}
  {S J : Subgroup (MulAut Y)} (h : PiData π t) (A : AutHyp Y S J)
include h A

theorem elementary_le {F : Subgroup Hh} (hFS : F ≤ S.comap π)
    (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hFsq : ∀ x ∈ F, x * x = 1)
    (hcard : Nat.card F = 64) : F = J.comap π := by
  have hFJ : F.map π = J := by
    refine A.J_unique (F.map π) ?_ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hFS hx
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hFc x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hFsq x hx, map_one]
    ·
      set f : F →* MulAut Y := π.comp F.subtype with hf
      have hrange : f.range = F.map π := by
        ext a
        simp only [MonoidHom.mem_range, Subgroup.mem_map, hf, MonoidHom.comp_apply,
          Subgroup.subtype_apply]
        constructor
        · rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
      have hker : Nat.card f.ker ≤ 2 := by
        have hinj : Function.Injective (fun x : f.ker => (⟨(x : F), by
            have := x.2; rw [MonoidHom.mem_ker] at this; exact this⟩ : π.ker)) := by
          intro a b hab
          apply Subtype.ext; apply Subtype.ext
          exact congrArg (fun z : π.ker => (z : Hh)) hab
        have := Nat.card_le_card_of_injective _ hinj
        rwa [h.card_ker] at this
      have hmul : Nat.card f.range * Nat.card f.ker = Nat.card F := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
          Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
      rw [← hrange]
      have hpos : 0 < Nat.card f.ker := Nat.card_pos
      nlinarith
  have hle : F ≤ J.comap π := by
    intro x hx
    rw [Subgroup.mem_comap, ← hFJ]
    exact ⟨x, hx, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.card_comap, A.card_J])

end PiData

namespace AutHyp

variable {Y : Type*} [Group Y] {S J : Subgroup (MulAut Y)} (A : AutHyp Y S J)
include A

theorem mem_of_centralizes_R6 {R6 R10 : Set (MulAut Y)}
    (hU : R6 ∪ R10 = {x | x ∈ J ∧ x ∉ innerImage Y ⊤}) (hc6 : R6.ncard = 6)
    (hn6 : ∀ d ∈ normalizer (J : Set (MulAut Y)), ∀ x ∈ R6, d * x * d⁻¹ ∈ R6)
    {α : MulAut Y} (hα : ∀ x ∈ R6, α * x = x * α) : α ∈ J := by
  have hR6J : ∀ x ∈ R6, x ∈ J ∧ x ∉ innerImage Y ⊤ := fun x hx => by
    have : x ∈ R6 ∪ R10 := Or.inl hx
    rw [hU] at this
    exact this
  set W : Subgroup (MulAut Y) := closure R6 with hW
  have hWJ : W ≤ J := by
    rw [hW, Subgroup.closure_le]
    exact fun x hx => (hR6J x hx).1
  have hWinv : ∀ d ∈ normalizer (J : Set (MulAut Y)), ∀ x ∈ W, d * x * d⁻¹ ∈ W := by
    intro d hd x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hn6 d hd x hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have : d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
      rw [this]; exact W.mul_mem hx hy
    | inv x _ hx =>
      have : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
      rw [this]; exact W.inv_mem hx
  obtain ⟨x₁, hx₁⟩ : R6.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨x₂, hx₂, hx₂ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < R6.ncard) x₁
  have hx₁W : x₁ ∈ W := Subgroup.subset_closure hx₁
  have hx₂W : x₂ ∈ W := Subgroup.subset_closure hx₂
  have ha₀ : x₁⁻¹ * x₂ ∈ J ⊓ innerImage Y ⊤ :=
    ⟨J.mul_mem (J.inv_mem (hR6J x₁ hx₁).1) (hR6J x₂ hx₂).1,
      A.outer_mul_inner (hR6J x₁ hx₁).1 (hR6J x₂ hx₂).1 (hR6J x₁ hx₁).2 (hR6J x₂ hx₂).2⟩
  have ha₀1 : x₁⁻¹ * x₂ ≠ 1 := fun h1 => hx₂ne (by
    have := inv_mul_eq_one.1 h1
    exact this.symm)
  have ha₀W : x₁⁻¹ * x₂ ∈ W := W.mul_mem (W.inv_mem hx₁W) hx₂W
  have hinnerW : ∀ b ∈ J ⊓ innerImage Y ⊤, b ∈ W := by
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]; exact W.one_mem
    · obtain ⟨d, hd, hdb⟩ := A.data.trans_inner _ ha₀ ha₀1 b hb hb1
      rw [← hdb]
      exact hWinv d hd _ ha₀W
  have hJW : J ≤ W := by
    intro j hj
    by_cases hji : j ∈ innerImage Y ⊤
    · exact hinnerW j ⟨hj, hji⟩
    · have : x₁⁻¹ * j ∈ J ⊓ innerImage Y ⊤ :=
        ⟨J.mul_mem (J.inv_mem (hR6J x₁ hx₁).1) hj,
          A.outer_mul_inner (hR6J x₁ hx₁).1 hj (hR6J x₁ hx₁).2 hji⟩
      have h2 := hinnerW _ this
      have : j = x₁ * (x₁⁻¹ * j) := by group
      rw [this]
      exact W.mul_mem hx₁W h2
  have hcentW : W ≤ Subgroup.centralizer ({α} : Set (MulAut Y)) := by
    rw [hW, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hα x hx).symm
  refine A.data.centralizer_le α fun x hx => ?_
  have := hcentW (hJW hx)
  exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm

end AutHyp

namespace PiData

variable {Hh : Type*} [Group Hh] [Finite Hh] {Y : Type*} [Group Y] {π : Hh →* MulAut Y} {t : Hh}
  (h : PiData π t)
include h

theorem ncard_preimage (B : Set (MulAut Y)) : (π ⁻¹' B).ncard = 2 * B.ncard := by
  classical
  have : Fintype Hh := Fintype.ofFinite Hh
  have : Finite (MulAut Y) := Finite.of_surjective π h.surj
  have : Fintype (MulAut Y) := Fintype.ofFinite _
  set s : Finset Hh := Finset.univ.filter (fun x => π x ∈ B) with hs
  set u : Finset (MulAut Y) := Finset.univ.filter (fun a => a ∈ B) with hu
  have hsc : (π ⁻¹' B).ncard = s.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [hs]
  have huc : B.ncard = u.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a
    simp [hu]
  have hfib := Finset.card_eq_sum_card_fiberwise (f := π) (s := s) (t := u) (by
    intro x hx
    simp only [Finset.mem_coe, hs, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, hu, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx)
  have h2 : ∀ a ∈ u, (s.filter (fun x => π x = a)).card = 2 := by
    intro a ha
    simp only [hu, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨x₀, rfl⟩ := h.surj a
    have : s.filter (fun x => π x = π x₀) = {x₀, x₀ * t} := by
      ext x
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨-, hx⟩
        exact h.eq_or_eq_mul_t hx
      · rintro (rfl | rfl)
        · exact ⟨ha, rfl⟩
        · refine ⟨by rw [map_mul, h.pi_t, mul_one]; exact ha, by rw [map_mul, h.pi_t, mul_one]⟩
    rw [this, Finset.card_pair]
    intro hx
    exact h.t_ne (mul_left_cancel (a := x₀) (by rw [mul_one]; exact hx.symm))
  rw [hsc, huc, hfib, Finset.sum_congr rfl h2]
  simp [mul_comm]

end PiData

end CFSG.EvenSporadicStandard.M22Std
