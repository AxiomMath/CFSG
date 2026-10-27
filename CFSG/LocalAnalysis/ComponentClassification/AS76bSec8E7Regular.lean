module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7FrameLine

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

variable {K : Type} [Field K]

section Scale


theorem map_conj_e7FrameScale {F : List (Fin Tag.E7.rank → ℤ)} (hr : ∀ σ ∈ F, IsRoot .E7 σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) (s : Kˣ) :
    (e7FrameLine K F).map (MulAut.conj (e7FrameScale K F s)).toMonoidHom = e7FrameLine K F := by
  rw [e7FrameLine, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨(s : K) ^ 2 * d, (e7FrameScale_conj hr ho s d).symm⟩
  · rintro ⟨d, rfl⟩
    refine ⟨e7FrameElt K F (((s : K) ^ 2)⁻¹ * d), ⟨_, rfl⟩, ?_⟩
    rw [e7FrameScale_conj hr ho s, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 s.ne_zero),
      one_mul]

theorem e7FrameScale_mem_normalizer {F : List (Fin Tag.E7.rank → ℤ)}
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) (s : Kˣ) :
    e7FrameScale K F s ∈ normalizer (e7FrameLine K F : Set (adjointGroup .E7 K)) :=
  mem_normalizer_iff_map_conj_eq.2 (map_conj_e7FrameScale hr ho s)

theorem e7FrameScale_pow_conj {F : List (Fin Tag.E7.rank → ℤ)} (hr : ∀ σ ∈ F, IsRoot .E7 σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) (s : Kˣ) (k : ℕ) (d : K) :
    e7FrameScale K F s ^ k * e7FrameElt K F d * (e7FrameScale K F s ^ k)⁻¹ =
      e7FrameElt K F (((s : K) ^ k) ^ 2 * d) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    calc e7FrameScale K F s ^ (k + 1) * e7FrameElt K F d * (e7FrameScale K F s ^ (k + 1))⁻¹ =
          e7FrameScale K F s ^ k * (e7FrameScale K F s * e7FrameElt K F d *
            (e7FrameScale K F s)⁻¹) * (e7FrameScale K F s ^ k)⁻¹ := by group
      _ = e7FrameElt K F (((s : K) ^ (k + 1)) ^ 2 * d) := by
        rw [e7FrameScale_conj hr ho, ih]
        congr 1
        ring

theorem exists_e7FrameScale_conj [Finite K] [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) {d : K}
    (hd : d ≠ 0) : ∃ s : Kˣ, ∀ e : K,
      e7FrameScale K F s * e7FrameElt K F e * (e7FrameScale K F s)⁻¹ = e7FrameElt K F (d * e) := by
  obtain ⟨r, hr2⟩ := isSquare_of_charTwo' d
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hd (by rw [hr2, zero_mul])
  refine ⟨Units.mk0 r hr0, fun e => ?_⟩
  rw [e7FrameScale_conj hr ho, Units.val_mk0, sq, ← hr2]

end Scale

theorem commute_e7FrameLine_of_ne_zero
    [Finite K] [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0)
    (hcomm : ∀ z ∈ e7FrameLine K F, ∀ g ∈ Exc.cent (e7FramePt K F), z * g = g * z)
    {d : K} (hd : d ≠ 0) {z : adjointGroup .E7 K} (hz : z ∈ e7FrameLine K F)
    {g : adjointGroup .E7 K} (hg : g ∈ Exc.cent (e7FrameElt K F d)) : z * g = g * z := by
  obtain ⟨s, hs⟩ := exists_e7FrameScale_conj hr ho hd
  set h := e7FrameScale K F s with hh
  have hx : e7FrameElt K F d = h * e7FramePt K F * h⁻¹ := by
    rw [← e7FrameElt_one, hs, mul_one]
  have hg' : h⁻¹ * g * h ∈ Exc.cent (e7FramePt K F) := by
    rw [Exc.cent, mem_centralizer_singleton_iff] at hg ⊢
    rw [hx] at hg
    calc h⁻¹ * g * h * e7FramePt K F = h⁻¹ * (g * (h * e7FramePt K F * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * e7FramePt K F * h⁻¹) * g) * h := by rw [hg]
      _ = e7FramePt K F * (h⁻¹ * g * h) := by group
  have hz' : h⁻¹ * z * h ∈ e7FrameLine K F := by
    obtain ⟨e, rfl⟩ := (mem_e7FrameLine hr ho).1 hz
    have h1 := hs (d⁻¹ * e)
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul] at h1
    have h2 : h⁻¹ * e7FrameElt K F e * h = e7FrameElt K F (d⁻¹ * e) := by
      rw [← h1]
      group
    rw [h2]
    exact e7FrameElt_mem_e7FrameLine F _
  have h3 := hcomm _ hz' _ hg'
  calc z * g = h * ((h⁻¹ * z * h) * (h⁻¹ * g * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * g * h) * (h⁻¹ * z * h)) * h⁻¹ := by rw [h3]
    _ = g * z := by group

theorem regular_e7FrameLine
    [Finite K] [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hne : F ≠ []) (hnd : F.Nodup) (hF : ∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0)
    (hcomm : ∀ z ∈ e7FrameLine K F, ∀ g ∈ Exc.cent (e7FramePt K F), z * g = g * z) :
    ∃ u, Exc.Regular (e7FrameLine K F) u := by
  have hr : ∀ σ ∈ F, IsRoot .E7 σ := fun σ hσ => (hF σ hσ).1
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨s₀, hs₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hmem := fun {w : adjointGroup .E7 K} => mem_e7FrameLine (K := K) hr ho (w := w)
  have hne1 : ∀ {d : K}, e7FrameElt K F d = 1 ↔ d = 0 := e7FrameElt_eq_one_iff hne hnd hF
  have hfree : ∀ a ∈ normalizer (e7FrameLine K F : Set (adjointGroup .E7 K)),
      ∀ j ∈ e7FrameLine K F, j ≠ 1 → a * j * a⁻¹ = j →
        a ∈ centralizer (e7FrameLine K F : Set (adjointGroup .E7 K)) := by
    intro a _ j hj hj1 haj
    obtain ⟨d, rfl⟩ := hmem.1 hj
    have hd : d ≠ 0 := fun h => hj1 (hne1.2 h)
    have ha : a ∈ Exc.cent (e7FrameElt K F d) := by
      rw [Exc.cent, mem_centralizer_singleton_iff]
      calc a * e7FrameElt K F d = a * e7FrameElt K F d * a⁻¹ * a := by group
        _ = e7FrameElt K F d * a := by rw [haj]
    rw [mem_centralizer_iff]
    intro z hz
    exact commute_e7FrameLine_of_ne_zero hr ho hcomm hd hz ha
  refine ⟨e7FrameScale K F s₀, ⟨e7FrameScale_mem_normalizer hr ho s₀,
    odd_orderOf_e7FrameScale n.pos hK hr s₀, ?_, hfree, ?_⟩⟩
  ·
    intro j hj hj1 j' hj' hj'1
    obtain ⟨d, rfl⟩ := hmem.1 hj
    obtain ⟨d', rfl⟩ := hmem.1 hj'
    have hd : d ≠ 0 := fun h => hj1 (hne1.2 h)
    have hd' : d' ≠ 0 := fun h => hj'1 (hne1.2 h)
    obtain ⟨s, hs⟩ := exists_e7FrameScale_conj hr ho (mul_ne_zero hd' (inv_ne_zero hd))
    refine ⟨e7FrameScale K F s, e7FrameScale_mem_normalizer hr ho s, ?_⟩
    rw [hs, mul_assoc, inv_mul_cancel₀ hd, mul_one]
  ·
    intro a ha
    have hx : e7FramePt K F ∈ e7FrameLine K F := by
      rw [← e7FrameElt_one]
      exact e7FrameElt_mem_e7FrameLine F 1
    have hax : a * e7FramePt K F * a⁻¹ ∈ e7FrameLine K F :=
      (mem_normalizer_iff.1 ha _).1 hx
    obtain ⟨e, he⟩ := hmem.1 hax
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [e7FrameElt_zero] at he
      have h1 : e7FramePt K F = 1 := by
        rw [← mul_left_cancel_iff (a := a), ← mul_right_cancel_iff (a := a⁻¹), ← he]
        group
      exact one_ne_zero (hne1.1 (by rw [e7FrameElt_one]; exact h1))
    obtain ⟨r, hr2⟩ := isSquare_of_charTwo' e
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact he0 (by rw [hr2, zero_mul])
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 (hs₀ (Units.mk0 r hr0)))
    have hk' : s₀ ^ k = Units.mk0 r hr0 := hk
    refine ⟨k, hfree _ ?_ _ hx ?_ ?_⟩
    · exact mul_mem (inv_mem (pow_mem (e7FrameScale_mem_normalizer hr ho s₀) k)) ha
    · intro h1
      exact one_ne_zero (hne1.1 (by rw [e7FrameElt_one]; exact h1))
    · have h1 := e7FrameScale_pow_conj hr ho s₀ k 1
      have he' : ((s₀ : K) ^ k) ^ 2 * 1 = e := by
        rw [mul_one, ← Units.val_pow_eq_pow_val, hk', Units.val_mk0, sq, ← hr2]
      rw [he', he] at h1
      calc (e7FrameScale K F s₀ ^ k)⁻¹ * a * e7FramePt K F *
            ((e7FrameScale K F s₀ ^ k)⁻¹ * a)⁻¹ =
            (e7FrameScale K F s₀ ^ k)⁻¹ * (a * e7FramePt K F * a⁻¹) *
              (e7FrameScale K F s₀ ^ k) := by group
        _ = (e7FrameScale K F s₀ ^ k)⁻¹ * (e7FrameScale K F s₀ ^ k * e7FrameElt K F 1 *
              (e7FrameScale K F s₀ ^ k)⁻¹) * (e7FrameScale K F s₀ ^ k) := by rw [h1]
        _ = e7FramePt K F := by
          rw [e7FrameElt_one]
          group

theorem centreData_e7FrameLine
    [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hne : F ≠ []) (hnd : F.Nodup) (hF : ∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0)
    (hcomm : ∀ z ∈ e7FrameLine K F, ∀ g ∈ Exc.cent (e7FramePt K F), z * g = g * z)
    (hsyl : Exc.SylowData (e7FramePt K F) (e7FrameLine K F)) :
    Exc.CentreData (e7FramePt K F) (e7FrameLine K F) := by
  have hr : ∀ σ ∈ F, IsRoot .E7 σ := fun σ hσ => (hF σ hσ).1
  refine ⟨?_, ?_, isElemAbelian_e7FrameLine hr ho, e7FrameLine_le_cent hr ho, hcomm, ?_⟩
  · rw [← e7FrameElt_one]
    exact e7FrameElt_mem_e7FrameLine F 1
  · rw [← e7FrameElt_one, Ne, e7FrameElt_eq_one_iff hne hnd hF]
    exact one_ne_zero
  · intro w hw hwc hw2
    refine hsyl w hw (fun b hb => ?_) ⟨1, by rw [pow_one, sq, hw2]⟩
    rw [Exc.cent, mem_centralizer_singleton_iff]
    exact hwc _ hb

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
