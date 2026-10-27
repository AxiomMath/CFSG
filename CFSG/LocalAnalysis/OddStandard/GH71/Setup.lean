module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L121Cover
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2

structure Ctx71 (G : Type) [Group G] [Finite G] (z : G) (S U : Subgroup G) (u : G) : Prop where
  ctx : Stage2Ctx G z Kind.ly S
  cover : IsDoubleCoverOfAlt (CentralizerBar z) 11
  U_le : U ≤ S
  U_four : IVK.IsFourSubgroup U
  U_norm : S ≤ normalizer (U : Set G)
  z_mem : z ∈ U
  aut6 : AutOrd (⊤ : Subgroup G) U = 6
  u_mem : u ∈ U
  u_ne_one : u ≠ 1
  u_ne_z : u ≠ z

theorem not_mem_pPrimeCore_of_involution {X : Type*} [Group X] [Finite X] {x : X}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : x ∉ pPrimeCore 2 X := by
  intro hx
  have hodd : Odd (Nat.card (pPrimeCore 2 X)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X))
  have hord : orderOf (⟨x, hx⟩ : pPrimeCore 2 X) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have := orderOf_dvd_natCard (⟨x, hx⟩ : pPrimeCore 2 X)
  rw [hord] at this
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)

theorem isElementaryAbelian_map'' {p : ℕ} {R T : Type*} [Group R] [Group T] {A : Subgroup R}
    (hA : IsElementaryAbelian p A) (f : R →* T) : IsElementaryAbelian p (A.map f) :=
  CFSG.IsElementaryAbelian.subgroup_map hA _

namespace Ctx71

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

theorem simple (h : Ctx71 G z S U u) : IsSimpleGroup G := h.ctx.std.kps.1

theorem nonab (h : Ctx71 G z S U u) : ∃ a b : G, a * b ≠ b * a := h.ctx.std.kps.2.1

theorem one_class (h : Ctx71 G z S U u) :
    ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  have hd := h.ctx.data
  cases hd with
  | ly hs =>
    obtain ⟨n, -, hs⟩ := hs
    exact hs.one_class

theorem orderOf_z (h : Ctx71 G z S U u) : orderOf z = 2 := h.ctx.orderOf_z

theorem S_le (h : Ctx71 G z S U u) : S ≤ centralizer ({z} : Set G) := h.ctx.S_le_Cen

theorem card_S (h : Ctx71 G z S U u) : Nat.card S = 2 ^ 8 := L121.card_S_eq h.ctx

theorem S2 (h : Ctx71 G z S U u) : IsPGroup 2 ↥S :=
  IsPGroup.of_card (h.card_S)

theorem u_S (h : Ctx71 G z S U u) : u ∈ S := h.U_le h.u_mem

theorem sq_eq_one_of_mem_U (h : Ctx71 G z S U u) {x : G} (hx : x ∈ U) : x * x = 1 := by
  have : IsElementaryAbelian 2 ↥U := h.U_four.1
  have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx
  simpa [pow_two] using this

theorem orderOf_u (h : Ctx71 G z S U u) : orderOf u = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.sq_eq_one_of_mem_U h.u_mem) h.u_ne_one

theorem uz_mem (h : Ctx71 G z S U u) : u * z ∈ U := U.mul_mem h.u_mem h.z_mem

theorem z_ne_one (h : Ctx71 G z S U u) : z ≠ 1 := by
  intro h1; have := h.orderOf_z; rw [h1, orderOf_one] at this; omega

theorem uz_ne_one (h : Ctx71 G z S U u) : u * z ≠ 1 := by
  intro h1
  apply h.u_ne_z
  have hz : z * z = 1 := h.sq_eq_one_of_mem_U h.z_mem
  calc u = u * z * z := by rw [mul_assoc, hz, mul_one]
    _ = z := by rw [h1, one_mul]

theorem uz_ne_z (h : Ctx71 G z S U u) : u * z ≠ z := fun h1 =>
  h.u_ne_one (mul_right_cancel (h1.trans (one_mul z).symm))

theorem uz_ne_u (h : Ctx71 G z S U u) : u * z ≠ u := fun h1 =>
  h.z_ne_one (mul_left_cancel (h1.trans (mul_one u).symm))

theorem mem_U (h : Ctx71 G z S U u) {x : G} (hx : x ∈ U) :
    x = 1 ∨ x = z ∨ x = u ∨ x = u * z := by
  classical
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have hsub : (({1, z, u, u * z, x} : Finset G) : Set G) ⊆ (U : Set G) := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact U.one_mem
    · exact h.z_mem
    · exact h.u_mem
    · exact h.uz_mem
    · exact hx
  have hcard5 : ({1, z, u, u * z, x} : Finset G).card = 5 := by
    have hz1 := h.z_ne_one
    have hu1 := h.u_ne_one
    have huz := h.u_ne_z
    have h41 := h.uz_ne_one
    have h4z := h.uz_ne_z
    have h4u := h.uz_ne_u
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton] <;>
      simp_all [eq_comm]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard5] at hle
  have hU4 : (U : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact h.U_four.2
  omega

end Ctx71

end CFSG.OddStandard.GH71
