module

public import CFSG.GH74.GLS.Bg.TwoGroups.Statements

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup

theorem card_comap_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (S : Subgroup B) :
    Nat.card (S.comap f) = Nat.card S * Nat.card f.ker := by
  have : Finite B := Finite.of_surjective f hf
  have e1 : Nat.card (S.comap f) * (S.comap f).index = Nat.card A := Subgroup.card_mul_index _
  have e2 : Nat.card S * S.index = Nat.card B := Subgroup.card_mul_index S
  have e3 : Nat.card A = Nat.card (A ⧸ f.ker) * Nat.card f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have e5 : Nat.card (A ⧸ f.ker) = Nat.card B :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have e4 : (S.comap f).index = S.index := Subgroup.index_comap_of_surjective S hf
  have hpos : 0 < S.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  rw [e4] at e1
  have : Nat.card (S.comap f) * S.index = (Nat.card S * Nat.card f.ker) * S.index := by
    calc Nat.card (S.comap f) * S.index = Nat.card A := e1
      _ = Nat.card B * Nat.card f.ker := by rw [e3, e5]
      _ = (Nat.card S * S.index) * Nat.card f.ker := by rw [e2]
      _ = (Nat.card S * Nat.card f.ker) * S.index := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem ig_9_16 : IG_9_16 := by
  intro X _ _ N _ x
  classical
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  set Cb : Subgroup (X ⧸ N) := centralizer ({(x : X ⧸ N)} : Set (X ⧸ N)) with hCb
  set D : Subgroup X := Cb.comap π with hD
  set C : Subgroup X := centralizer ({x} : Set X) with hC
  have hmemD : ∀ g : X, g ∈ D ↔ π (x⁻¹ * (g * x * g⁻¹)) = 1 := by
    intro g
    rw [hD, Subgroup.mem_comap, hCb, Subgroup.mem_centralizer_iff]
    have e : π (x⁻¹ * (g * x * g⁻¹)) = (π x)⁻¹ * (π g * π x * (π g)⁻¹) := by simp
    have hx : π x = (x : X ⧸ N) := rfl
    rw [e, hx]
    constructor
    · intro h
      have := h (x : X ⧸ N) (Set.mem_singleton _)
      rw [← this]
      group
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h' : π g * (x : X ⧸ N) = (x : X ⧸ N) * π g := by
        have h2 : (π g) * (x : X ⧸ N) * (π g)⁻¹ = (x : X ⧸ N) := by
          have := h
          calc (π g) * (x : X ⧸ N) * (π g)⁻¹
              = (x : X ⧸ N) * ((x : X ⧸ N)⁻¹ * (π g * (x : X ⧸ N) * (π g)⁻¹)) := by group
            _ = (x : X ⧸ N) * 1 := by rw [this]
            _ = (x : X ⧸ N) := mul_one _
        calc π g * (x : X ⧸ N) = (π g * (x : X ⧸ N) * (π g)⁻¹) * π g := by group
          _ = (x : X ⧸ N) * π g := by rw [h2]
      exact h'.symm
  have hCD : C ≤ D := by
    intro g hg
    rw [hmemD]
    have : g * x = x * g := ((Subgroup.mem_centralizer_iff.mp hg) x (Set.mem_singleton x)).symm
    have e : x⁻¹ * (g * x * g⁻¹) = 1 := by rw [this]; group
    rw [e, map_one]
  have hNsub : ∀ g ∈ D, x⁻¹ * (g * x * g⁻¹) ∈ N := by
    intro g hg
    have := (hmemD g).mp hg
    exact (QuotientGroup.eq_one_iff _).mp this
  have h1 : Nat.card D = Nat.card Cb * Nat.card N := by
    have := card_comap_of_surjective π (QuotientGroup.mk'_surjective N) Cb
    rw [hπ, QuotientGroup.ker_mk'] at this
    exact this
  have h2 : Nat.card D ≤ Nat.card C * Nat.card N := by
    set H : Subgroup D := C.subgroupOf D with hH
    have e1 : Nat.card H * H.index = Nat.card D := Subgroup.card_mul_index H
    have e2 : Nat.card H = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCD).toEquiv
    have key : ∀ a b : D, (a⁻¹ * b : D) ∈ H ↔
        (a : X) * x * (a : X)⁻¹ = (b : X) * x * (b : X)⁻¹ := by
      intro a b
      rw [hH, Subgroup.mem_subgroupOf, hC, Subgroup.mem_centralizer_iff]
      constructor
      · intro h
        have hc := h x (Set.mem_singleton x)
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hc
        have : (b : X) * x * (b : X)⁻¹
            = (a : X) * (((a : X)⁻¹ * (b : X)) * x * ((a : X)⁻¹ * (b : X))⁻¹) * (a : X)⁻¹ := by
          group
        rw [this, ← hc]
        group
      · intro h y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        have : (a : X) * y * (a : X)⁻¹ = (b : X) * y * (b : X)⁻¹ := h
        calc y * ((a : X)⁻¹ * (b : X)) = (a : X)⁻¹ * ((a : X) * y * (a : X)⁻¹) * (b : X) := by group
          _ = (a : X)⁻¹ * ((b : X) * y * (b : X)⁻¹) * (b : X) := by rw [this]
          _ = (a : X)⁻¹ * (b : X) * y := by group
    have e3 : H.index ≤ Nat.card N := by
      rw [Subgroup.index_eq_card]
      let F : D ⧸ H → N := Quotient.lift (s := QuotientGroup.leftRel H)
        (fun g => (⟨x⁻¹ * ((g : X) * x * (g : X)⁻¹), hNsub g g.2⟩ : N)) (by
          intro a b hab
          have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
          have := (key a b).mp hab'
          apply Subtype.ext
          simp only [this])
      have hF : Function.Injective F := by
        intro u v huv
        induction u using QuotientGroup.induction_on with
        | _ a =>
          induction v using QuotientGroup.induction_on with
          | _ b =>
            have h' : (a : X) * x * (a : X)⁻¹ = (b : X) * x * (b : X)⁻¹ := by
              have := congrArg Subtype.val huv
              simp only [F] at this
              exact mul_left_cancel this
            exact QuotientGroup.eq.mpr ((key a b).mpr h')
      exact Nat.card_le_card_of_injective F hF
    calc Nat.card D = Nat.card H * H.index := e1.symm
      _ ≤ Nat.card C * Nat.card N := by rw [e2]; exact Nat.mul_le_mul_left _ e3
  have hNpos : 0 < Nat.card N := Nat.card_pos
  rw [h1] at h2
  exact Nat.le_of_mul_le_mul_right h2 hNpos

end CFSG.GH74.GLS.Bg.TwoGroups
