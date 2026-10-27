module

public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Filter.ClassicalOdd.Basic

public section

namespace CFSG.GH74.Generic.S1

open Subgroup CFSG.GH74.Filter.ClassicalOdd CFSG.GH74

theorem card_le_four_of_quaternion_centralizer {Y : Type} [Group Y] [Finite Y] (hY : Gen4 Y)
    {M : Subgroup Y} (φ : Q8 →* Y) (hφ : Function.Injective φ)
    (hcent : ∀ a : Q8, ∀ m ∈ M, φ a * m = m * φ a)
    (E : Subgroup (↥M ⧸ center ↥M)) (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  by_contra hcon
  have hcon : 4 < Nat.card E := not_le.mp hcon
  set Et : Subgroup ↥M := E.comap (QuotientGroup.mk' (center ↥M)) with hEt
  let f : ↥Et →* Y := M.subtype.comp Et.subtype
  have hcomm : ∀ (m : ↥Et) (a : Q8), Commute (f m) (φ a) := fun m a =>
    (hcent a (m.1 : Y) m.1.2).symm
  let α : ↥Et × Q8 →* Y := f.noncommCoprod φ hcomm
  let g : ↥Et →* ↥E := ((QuotientGroup.mk' (center ↥M)).comp Et.subtype).codRestrict E
    (fun m => m.2)
  let β : ↥Et × Q8 →* ↥E × V4 := g.prodMap q8Frattini
  have hβ : Function.Surjective β := by
    rintro ⟨e, v⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (center ↥M) (e : ↥M ⧸ center ↥M)
    obtain ⟨a, ha⟩ := q8Frattini_surjective v
    have hmE : m ∈ Et := by
      rw [hEt, mem_comap]
      rw [hm]
      exact e.2
    refine ⟨(⟨m, hmE⟩, a), ?_⟩
    exact Prod.ext (Subtype.ext hm) ha
  have hAcomm : ∀ a b : ↥E × V4, a * b = b * a := by
    intro a b
    exact Prod.ext (hE.1.is_comm.comm a.1 b.1) (mul_comm _ _)
  have hAsq : ∀ a : ↥E × V4, a ^ 2 = 1 := by
    intro a
    refine Prod.ext (Subtype.ext ?_) ?_
    · exact hE.2 a.1.1 a.1.2
    · have : ∀ v : V4, v ^ 2 = 1 := by decide
      exact this _
  have hcard : 2 ^ 4 < Nat.card (↥E × V4) := by
    rw [Nat.card_prod, card_V4]
    omega
  refine not_sectionalTwoRankLE_of_surjection 4 α β hβ hAcomm hAsq hcard ?_ hY
  intro k hk
  obtain ⟨m, a⟩ := k
  rw [MonoidHom.mem_ker] at hk ⊢
  have hk' : (m.1 : Y) * φ a = 1 := hk
  have hm : (m.1 : Y) = φ a⁻¹ := by
    rw [map_inv]; exact eq_inv_of_mul_eq_one_left hk'
  have hmz : m.1 ∈ center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    have := hcent a⁻¹ (n : Y) n.2
    simp only [Subgroup.coe_mul]
    rw [hm]
    exact this.symm
  have haz : ∀ b : Q8, a * b = b * a := by
    intro b
    have h1 := hcent b (m.1 : Y) m.1.2
    rw [hm, ← map_mul, ← map_mul] at h1
    have h2 : b * a⁻¹ = a⁻¹ * b := hφ h1
    calc a * b = a * (b * a⁻¹) * a := by group
      _ = a * (a⁻¹ * b) * a := by rw [h2]
      _ = b * a := by group
  have hfa : q8Frattini a = 1 := by
    rcases CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternion_center a haz with
      rfl | rfl
    · exact map_one _
    · decide
  refine Prod.ext (Subtype.ext ?_) hfa
  exact (QuotientGroup.eq_one_iff _).2 hmz

theorem twoRank_le_two_of_quaternion_centralizer {Y : Type} [Group Y] [Finite Y] (hY : Gen4 Y)
    {M : Subgroup Y} (φ : Q8 →* Y) (hφ : Function.Injective φ)
    (hcent : ∀ a : Q8, ∀ m ∈ M, φ a * m = m * φ a) :
    CFSG.Open.twoRank (↥M ⧸ center ↥M) ≤ 2 :=
  CFSG.SectionRank.pRank_le Nat.one_lt_two fun E _ hE =>
    card_le_four_of_quaternion_centralizer hY φ hφ hcent E hE

end CFSG.GH74.Generic.S1
