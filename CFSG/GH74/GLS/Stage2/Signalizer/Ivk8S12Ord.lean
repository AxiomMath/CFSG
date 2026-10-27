module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.ComponentClassification

theorem conj_injective_of_center_eq_bot {Y : Type*} [Group Y] (hZ : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ center Y := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun α : MulAut Y => α x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem card_dvd_card_mulAut {Y : Type*} [Group Y] (hZ : center Y = ⊥) :
    Nat.card Y ∣ Nat.card (MulAut Y) := by
  have hinj := conj_injective_of_center_eq_bot hZ
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem center_eq_bot_of_not_solvable {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (h : ¬ Group.IsSolvable Y) : center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h1 | h1
  · exact h1
  · exfalso
    apply h
    exact Group.isSolvable_of_comm fun a b =>
      (Subgroup.mem_center_iff.1 (h1 ▸ Subgroup.mem_top a) b).symm

theorem card_mulAut_le_of_outer {G : Type*} [Group G] [Finite G] {k : ℕ}
    (h : Nat.card (OuterAutomorphisms.Outer G) ≤ k) :
    Nat.card (MulAut G) ≤ k * Nat.card G := by
  have h1 := (OuterAutomorphisms.inner G).card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card (OuterAutomorphisms.inner G) ≤ Nat.card G := by
    have hsurj : Function.Surjective
        (MonoidHom.rangeRestrict (MulAut.conj : G →* MulAut G)) :=
      MonoidHom.rangeRestrict_surjective _
    exact Nat.card_le_card_of_surjective _ hsurj
  rw [h1]
  exact Nat.mul_le_mul h h2

theorem not_dvd_card_mulAut {Y : Type*} [Group Y] [Finite Y] (hZ : center Y = ⊥) {k N : ℕ}
    (hN : Nat.card Y = N) (hk : Nat.card (MulAut Y) ≤ k * N)
    (hnd : ∀ m : ℕ, 1 ≤ m → m ≤ k → ¬ 2 ^ 8 ∣ N * m) : ¬ 2 ^ 8 ∣ Nat.card (MulAut Y) := by
  intro h
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) DFunLike.coe_injective
  obtain ⟨m, hm⟩ := card_dvd_card_mulAut hZ
  rw [hN] at hm
  have hNpos : 0 < N := hN ▸ Nat.card_pos
  have hpos : 0 < Nat.card (MulAut Y) := Nat.card_pos
  rw [hm] at hk h hpos
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h0
  have hmk : m ≤ k := by
    have : N * m ≤ N * k := by rw [mul_comm N k]; exact hk
    exact Nat.le_of_mul_le_mul_left this hNpos
  exact hnd m hm1 hmk h

theorem isElementaryAbelian_bot_two (G : Type*) [Group G] :
    CFSG.IsElementaryAbelian 2 (⊥ : Subgroup G) := by
  have : Subsingleton (⊥ : Subgroup G) := inferInstance
  exact { is_comm := ⟨fun a b => Subsingleton.elim _ _⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g =>
            Subsingleton.elim _ _ }

theorem exists_isElementaryAbelian_of_le_pRank {G : Type*} [Group G] [Finite G] {k : ℕ}
    (hk : k ≤ CFSG.pRank 2 G) :
    ∃ E : Subgroup G, CFSG.IsElementaryAbelian 2 ↥E ∧ 2 ^ k ≤ Nat.card ↥E := by
  set S : Set ℕ := {r | ∃ A : Subgroup G, CFSG.IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ r}
    with hS
  have hne : S.Nonempty := ⟨0, ⊥, isElementaryAbelian_bot_two G, by simp⟩
  have hbdd : BddAbove S := ⟨Nat.card G, fun r ⟨A, _, hA⟩ => by
    have h1 : Nat.card ↥A ≤ Nat.card G := Subgroup.card_le_card_group A
    have h2 : r < 2 ^ r := Nat.lt_two_pow_self
    omega⟩
  obtain ⟨A, hA, hAcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨A, hA, ?_⟩
  rw [hAcard]
  exact Nat.pow_le_pow_right (by norm_num) hk

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem AFrame.false_of_order (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) {N : ℕ}
    (hN : Nat.card (↥J ⧸ center ↥J) = N) (hNd : ¬ N ∣ Nat.factorial 11)
    (hord : ¬ 2 ^ 8 ∣ Nat.card (MulAut (↥J ⧸ center ↥J))) : False := by
  have hY : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) := fun h =>
    hNd (hN ▸ h.card_dvd (Or.inr rfl))
  obtain ⟨hZ, hu, -⟩ := hfr.reduce hJ hY
  obtain ⟨φ, hinj, -⟩ := hfr.embed_aut hJ hZ hu
  have h1 : Nat.card ↥Sb ∣ Nat.card (MulAut ↥J) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hfr.card] at h1
  let e : (↥J ⧸ center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have h2 : Nat.card (MulAut (↥J ⧸ center ↥J)) = Nat.card (MulAut ↥J) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  exact hord (h2 ▸ h1)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
