module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbFL18a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem card_range_eq_index {H X : Type*} [Group H] (f : H → X) (K : Subgroup H)
    (hK : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ K) : Nat.card (Set.range f) = K.index := by
  rw [Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective (fun q : H ⧸ K => (⟨Quotient.liftOn' q f
    (fun a b hab => (hK a b).mpr (QuotientGroup.leftRel_apply.mp hab)), by
      induction q using QuotientGroup.induction_on with | H a => exact ⟨a, rfl⟩⟩ :
      Set.range f)) ⟨fun q q' hqq => ?_, fun y => ?_⟩).symm
  · induction q using QuotientGroup.induction_on with | H a => ?_
    induction q' using QuotientGroup.induction_on with | H b => ?_
    have e : f a = f b := congrArg Subtype.val hqq
    exact QuotientGroup.eq.mpr ((hK a b).mp e)
  · obtain ⟨_, a, rfl⟩ := y
    exact ⟨QuotientGroup.mk a, rfl⟩

theorem fl_cls2 {Ξ Y D : Subgroup G} {g : G} (hg2 : g * g = 1)
    (hgΞ : ∀ x ∈ Ξ, g * x * g⁻¹ ∈ Ξ) (hgY : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hYΞ : Y ≤ Ξ)
    (hYc : ∀ y ∈ Y, ∀ x ∈ Ξ, x * y = y * x) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hsq : ∀ x ∈ Ξ, x * x ∈ Y) (hΞ : Nat.card Ξ = 256) (hY : Nat.card Y = 16)
    (hCY : Nat.card {y : G // y ∈ Y ∧ g * y = y * g} ≤ 4) (hDΞ : D ≤ Ξ)
    (hD : ∀ x ∈ Ξ, g * x * g⁻¹ * x⁻¹ ∈ Y → x ∈ D) (hDcard : Nat.card D ≤ 64) :
    ∀ x ∈ Ξ, (g * x) * (g * x) = 1 → ∃ p ∈ Ξ, g * x = p * g * p⁻¹ := by
  intro x hxΞ hx2
  have hg_inv : g⁻¹ = g := (inv_eq_iff_mul_eq_one).mpr hg2
  let f : Ξ → G := fun p => g * (p : G) * g⁻¹ * (p : G)⁻¹
  let K : Subgroup Ξ := (Subgroup.centralizer ({g} : Set G)).comap Ξ.subtype
  have hgf : ∀ p : Ξ, g * f p = (p : G) * g * (p : G)⁻¹ := by
    intro p
    calc g * f p = g * (g * (p : G) * g⁻¹ * (p : G)⁻¹) := rfl
      _ = (g * g) * ((p : G) * g⁻¹ * (p : G)⁻¹) := by group
      _ = (p : G) * g⁻¹ * (p : G)⁻¹ := by rw [hg2, one_mul]
      _ = (p : G) * g * (p : G)⁻¹ := by rw [hg_inv]
  have hfinv : ∀ p : Ξ, (g * f p) * (g * f p) = 1 := by
    intro p
    rw [hgf p]
    calc ((p : G) * g * (p : G)⁻¹) * ((p : G) * g * (p : G)⁻¹)
        = (p : G) * (g * g) * (p : G)⁻¹ := by group
      _ = (p : G) * (p : G)⁻¹ := by rw [hg2, mul_one]
      _ = 1 := mul_inv_cancel _
  let T : Set G := {y : G | y ∈ Ξ ∧ (g * y) * (g * y) = 1}
  have hsub : Set.range f ⊆ T := by
    rintro y ⟨p, rfl⟩
    change f p ∈ Ξ ∧ (g * f p) * (g * f p) = 1
    refine ⟨?_, hfinv p⟩
    show g * (p : G) * g⁻¹ * (p : G)⁻¹ ∈ Ξ
    exact Ξ.mul_mem (hgΞ _ p.2) (Ξ.inv_mem p.2)
  have hK : ∀ a b : Ξ, f a = f b ↔ a⁻¹ * b ∈ K := by
    intro a b
    rw [show a⁻¹ * b ∈ K ↔
        ((a : G)⁻¹ * (b : G)) * g = g * ((a : G)⁻¹ * (b : G)) by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      simp]
    constructor
    · intro hf
      have hAG : (a : G) * g * (a : G)⁻¹ = (b : G) * g * (b : G)⁻¹ := by
        rw [← hgf a, ← hgf b, hf]
      have hx : ((a : G)⁻¹ * (b : G)) * g * ((a : G)⁻¹ * (b : G))⁻¹ = g := by
        have h1 : g = (a : G)⁻¹ * (b : G) * g * (b : G)⁻¹ * (a : G) := by
          calc g = (a : G)⁻¹ * ((a : G) * g * (a : G)⁻¹) * (a : G) := by group
            _ = (a : G)⁻¹ * ((b : G) * g * (b : G)⁻¹) * (a : G) := by rw [hAG]
            _ = (a : G)⁻¹ * (b : G) * g * (b : G)⁻¹ * (a : G) := by group
        calc ((a : G)⁻¹ * (b : G)) * g * ((a : G)⁻¹ * (b : G))⁻¹
            = (a : G)⁻¹ * (b : G) * g * (b : G)⁻¹ * (a : G) := by group
          _ = g := h1.symm
      calc ((a : G)⁻¹ * (b : G)) * g
          = (((a : G)⁻¹ * (b : G)) * g * ((a : G)⁻¹ * (b : G))⁻¹)
              * ((a : G)⁻¹ * (b : G)) := by group
        _ = g * ((a : G)⁻¹ * (b : G)) := by rw [hx]
    · intro hc
      have hAG : (a : G) * g * (a : G)⁻¹ = (b : G) * g * (b : G)⁻¹ := by
        have h2 : (b : G) * g = (a : G) * g * (a : G)⁻¹ * (b : G) := by
          calc (b : G) * g = (a : G) * ((a : G)⁻¹ * (b : G)) * g := by group
            _ = (a : G) * (((a : G)⁻¹ * (b : G)) * g) := by group
            _ = (a : G) * (g * ((a : G)⁻¹ * (b : G))) := by rw [hc]
            _ = (a : G) * g * (a : G)⁻¹ * (b : G) := by group
        calc (a : G) * g * (a : G)⁻¹
            = ((a : G) * g * (a : G)⁻¹ * (b : G)) * (b : G)⁻¹ := by group
          _ = ((b : G) * g) * (b : G)⁻¹ := by rw [← h2]
          _ = (b : G) * g * (b : G)⁻¹ := by group
      have hgg : g * f a = g * f b := by rw [hgf a, hgf b, hAG]
      exact mul_left_cancel hgg
  have hrange : Nat.card (Set.range f) = K.index := card_range_eq_index f K hK
  have hK16 : Nat.card K ≤ 16 := by
    have hcent := fl2_card_cent_le (Ξ := Ξ) (Y := Y) (D := D) (g := g)
      hgY hYΞ hY hCY hDΞ hD hDcard
    let ψ : K → {y : G // y ∈ Ξ ∧ g * y = y * g} := fun q =>
      ⟨(q.1 : G), q.1.2, by
        have h1 : (q.1 : G) * g = g * (q.1 : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.mem_comap).mp q.2)
        exact h1.symm⟩
    have hinj : Function.Injective ψ := by
      intro u v huv
      have h1 : (u.1 : G) = (v.1 : G) :=
        congrArg (fun z : {y : G // y ∈ Ξ ∧ g * y = y * g} => (z : G)) huv
      exact Subtype.ext (Subtype.ext h1)
    exact le_trans (Nat.card_le_card_of_injective ψ hinj) hcent
  have hprod : Nat.card K * K.index = 256 := by
    rw [Subgroup.card_mul_index, hΞ]
  have hrange16 : 16 ≤ Nat.card (Set.range f) := by
    rw [hrange]
    by_contra h
    rw [Nat.not_le] at h
    have h1 : K.index ≤ 15 := by omega
    have h2 : Nat.card K * K.index ≤ 16 * 15 := Nat.mul_le_mul hK16 h1
    omega
  have hTncard : T.ncard ≤ 16 :=
    fl2_card_T_le (Ξ := Ξ) (Y := Y) (D := D) (g := g)
      hg2 hgΞ hgY hYΞ hYc hY2 hsq hY hCY hDΞ hD hDcard
  have hRange16 : 16 ≤ (Set.range f).ncard := hrange16
  have hTeq : Set.range f = T :=
    Set.eq_of_subset_of_ncard_le hsub (le_trans hTncard hRange16)
  have hxrange : x ∈ Set.range f := by
    rw [hTeq]
    exact ⟨hxΞ, hx2⟩
  obtain ⟨p, hp⟩ := hxrange
  exact ⟨p, p.2, by rw [← hp]; exact hgf p⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
