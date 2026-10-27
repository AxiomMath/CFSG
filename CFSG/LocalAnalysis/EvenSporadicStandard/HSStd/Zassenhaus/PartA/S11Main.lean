module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Plane
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Setup

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

set_option linter.unusedSectionVars false

section Aux

theorem s11_card_centralizer_equiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (a : A) :
    Nat.card (centralizer ({φ a} : Set B)) = Nat.card (centralizer ({a} : Set A)) := by
  refine Nat.card_congr
    { toFun := fun k => ⟨φ.symm k, by
        rw [mem_centralizer_singleton_iff]
        have := mem_centralizer_singleton_iff.1 k.2
        apply φ.injective
        simpa using this⟩
      invFun := fun k => ⟨φ k, by
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          mem_centralizer_singleton_iff.1 k.2]⟩
      left_inv := fun k => by ext; simp
      right_inv := fun k => by ext; simp }

end Aux

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
variable (hb : PAB G L t E W z) (a : PA10 L t E z)

abbrev S11_O : Subgroup G := Open.fusionOddCoreOf (Cen a.y)

abbrev S11_N : Subgroup ↥(Cen a.y) := Open.fusionOddCore ↥(Cen a.y)

theorem S11_O_mem_Cen {o : G} (ho : o ∈ S11_O a) : o ∈ Cen a.y := fusionOddCoreOf_le _ ho

theorem S11_O_conj {g o : G} (hg : g ∈ Cen a.y) (ho : o ∈ S11_O a) : g * o * g⁻¹ ∈ S11_O a :=
  s11_oddCoreOf_conj _ hg ho

theorem S11_u_mem_Cen : a.u ∈ Cen a.y := (a.K₀_le a.u_mem).2

theorem S11_u₁_facts : orderOf a.u₁ = 2 ∧ a.u₁ ∈ Cen a.y ∧ t * a.u₁ * t⁻¹ = a.u * a.u₁ := by
  obtain ⟨h1, h2, -, h4, -, -, σ, -, hc, -⟩ := a.d8_props a.d8_case
  refine ⟨h1, hc, ?_⟩
  rw [a.ub_eq] at h4
  exact h4

include hb in
theorem S11_u_comm_O : ∀ o ∈ S11_O a, a.u * o = o * a.u := by
  obtain ⟨h1, hc, h3⟩ := S11_u₁_facts a
  have hu₁ : a.u₁ * a.u₁ = 1 := by
    have := pow_orderOf_eq_one a.u₁
    rw [h1, pow_two] at this
    exact this
  refine s11_u_comm_O (O := S11_O a) hb.t_mul_t (S11_u_sq hb a) hu₁ a.y_ord a.y_O ?_
    (S11_y_t hb a).symm (S11_u_y hb a) (mem_Cen.1 hc) ?_ a.O_inv h3
  · intro o ho
    exact mem_Cen.1 (S11_O_mem_Cen a ho)
  · intro o ho
    exact S11_O_conj a hc ho

@[expose] noncomputable def S11_Φ : OQuot (Cen a.y) ≃* Wr2 (Equiv.Perm (Fin 5)) :=
  MulEquiv.ofBijective a.ι ⟨a.ι_inj, by
    have h := a.dcase_iff.1 a.d8_case
    exact MonoidHom.range_eq_top.1 h⟩

theorem S11_card_D : Nat.card (OQuot (Cen a.y)) = 28800 := by
  rw [Nat.card_congr (S11_Φ a).toEquiv, card_wr2, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num [Nat.factorial]

theorem S11_card_Cy : Nat.card (Cen a.y) = 28800 * Nat.card (S11_O a) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.fusionOddCore ↥(Cen a.y))
  have h2 : Nat.card (S11_O a) = Nat.card (Open.fusionOddCore ↥(Cen a.y)) :=
    Subgroup.card_map_of_injective (Cen a.y).subtype_injective
  have h3 := S11_card_D a
  rw [h2, ← h3]
  exact h1

include hb in
theorem S11_card_B : Nat.card ↥(Cen a.y ⊓ Cen a.u) = 288 * Nat.card (S11_O a) := by
  have hu := S11_u_mem_Cen a
  have hodd : Odd (Nat.card (S11_N a)) := s11_odd_fusionOddCore _
  have hu' : (⟨a.u, hu⟩ : ↥(Cen a.y)) * ⟨a.u, hu⟩ = 1 := Subtype.ext (S11_u_sq hb a)
  have hNu : ∀ n ∈ S11_N a, n * (⟨a.u, hu⟩ : ↥(Cen a.y)) = ⟨a.u, hu⟩ * n := by
    intro n hn
    apply Subtype.ext
    exact (S11_u_comm_O hb a n.1 ⟨n, hn, rfl⟩).symm
  have h1 := s11_card_centralizer_odd (S11_N a) hodd hu' hNu
  have h2 : Nat.card (centralizer ({(⟨a.u, hu⟩ : ↥(Cen a.y))} : Set ↥(Cen a.y))) =
      Nat.card ↥(Cen a.y ⊓ Cen a.u) := card_centralizer_subtype (Cen a.y) hu
  have h3 : Nat.card (centralizer ({QuotientGroup.mk' (S11_N a) ⟨a.u, hu⟩} : Set (↥(Cen a.y) ⧸ S11_N a))) = 288 := by
    obtain ⟨σ, hσ, hι⟩ := a.ub_base
    have e1 : (⟨a.ub, a.ub_cy⟩ : ↥(Cen a.y)) = ⟨a.u, hu⟩ := Subtype.ext a.ub_eq
    rw [e1] at hι
    have h4 : S11_Φ a (oMk (Cen a.y) ⟨a.u, hu⟩) = base σ σ := hι
    have h5 : QuotientGroup.mk' (S11_N a) ⟨a.u, hu⟩ = oMk (Cen a.y) ⟨a.u, hu⟩ := rfl
    rw [h5, ← s11_card_centralizer_equiv (S11_Φ a), h4, card_centralizer_base_self,
      s11_card_centralizer_swap σ hσ]
    norm_num
  have h6 : Nat.card (S11_O a) = Nat.card (S11_N a) :=
    Subgroup.card_map_of_injective (Cen a.y).subtype_injective
  rw [← h2, h1, h3, h6, mul_comm]

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
