module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx5

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem S1_ne_Pz (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : S1 S K₁ ≠ Pz S z := by
  obtain ⟨e, he, hri, -⟩ := hs.lemma82_core hII hq hrec
  intro heq
  have h1 : (Pz S z).relIndex (S1 S K₁) = 1 := by
    rw [heq]; exact Subgroup.relIndex_self _
  omega

theorem Q₂_eq_P₁_of_e_one (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (h1 : Nat.card ↥(Qof S K₂) = 1 * Nat.card ↥(Pof S K₁)) : Pof S K₁ = Qof S K₂ :=
  Subgroup.eq_of_le_of_card_ge (hs.P₁_le_Q₂ hII) (by rw [h1, one_mul])

theorem W₂h_inf_Q₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    conjugate W₂ h ⊓ Qof S K₂ = ⊥ := by
  refine Basic.conj_inf_bot (P := Qof S K₂) (Q := Qof S K₂) (V₁ := W₂) ?_ ?_ hs.W₂_le_Q₂ hs.h_move
    (fun x => mem_conjugate_iff) ?_
  · exact (hs.gq_Q₂ hII).uniq
  · exact (hs.gq_Q₂ hII).uniq
  · exact (hs.S_pgroup hII).to_le ((inf_le_right : conjugate W₂ h ⊓ Qof S K₂ ≤ Qof S K₂).trans
      inf_le_left)

theorem W₂h_le_W (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    conjugate W₂ h ≤ Wsub S U := by
  intro x hx
  have hx' : h * x * h⁻¹ ∈ W₂ := mem_conjugate_iff.1 hx
  exact ((Subgroup.mem_normalizer_iff.1 hs.h_W) x).2 (hs.W₂_le_W hII hq hx')

theorem false_of_W₂h_le_S1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hq2 : Nat.card ↥(Qof S K₂) = 2 * Nat.card ↥(Pof S K₁)) (hWS : conjugate W₂ h ≤ S1 S K₁) :
    False := by
  obtain ⟨e, he, hri, hNN, hq1', hq2'⟩ := hs.lemma82_core hII hq hrec
  obtain ⟨hN, hnc⟩ := hs.nc_quot (K := K₂) (Or.inr rfl)
  have hWc : IsCyclic ↥(conjugate W₂ h) := by
    rw [conjugate_eq_comap]
    exact Basic.cyclic_comap_conj _ hs.W₂_max.2.1 h
  have hemb := @Basic.two_mul_card_mul_card_le G _ _ (S1 S K₁) (Qof S K₂) (conjugate W₂ h)
    hN (hs.S1_pgroup hII) (hs.Q₂_le_S1 hII) hnc hWc hWS (hs.W₂h_inf_Q₂ hII)
  rw [conjugate_eq_comap, Basic.card_comap_conj] at hemb
  obtain ⟨ha, hcard⟩ := hs.card_S1 hII
  have hW := hs.card_W₂ hII
  have hP := hs.card_P hII
  have hN₂ : 0 < Nat.card ↥(Pof S K₂) := Nat.card_pos
  apply Basic.numeric82c (N₁ := Nat.card ↥(Pof S K₁)) (N₂ := Nat.card ↥(Pof S K₂))
    (q₂ := Nat.card ↥(Qof S K₂)) (s₁ := Nat.card ↥(S1 S K₁)) (p := Nat.card ↥(Pz S z))
    (a := (Pz S z).relIndex (S1 S K₁)) (le_of_eq hNN.symm) hN₂ (by omega) (by omega) hcard ha
  have hWP : Nat.card ↥W₂ = Nat.card ↥(Pof S K₁) := by omega
  rw [hWP] at hemb
  omega

theorem S_ne_S1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : Qof S K₂ ≠ Pof S K₁ → S ≠ S1 S K₁ := by
  intro hne hSS
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have he2 : e = 2 := by
    rcases he with rfl | rfl
    · exact absurd (hs.Q₂_eq_P₁_of_e_one hII hq2).symm hne
    · rfl
  subst he2
  refine hs.false_of_W₂h_le_S1 hII hq hrec hq2 ?_
  intro x hx
  have hxW : x ∈ Wsub S U := hs.W₂h_le_W hII hq hx
  rw [← hSS]
  exact hxW.1

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
