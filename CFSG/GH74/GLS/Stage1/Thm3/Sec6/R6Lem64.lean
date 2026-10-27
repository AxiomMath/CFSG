module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Quat
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Lem510

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

namespace Std6r1

variable {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G}

theorem Q_pgroup (h : Std6r1 G z S K) : IsPGroup 2 ↥(Qof S K) :=
  h.S_pgroup.to_le (inf_le_left : S ⊓ cSec K ≤ S)

theorem Q_quat (h : Std6r1 G z S K) (hr : pRank 2 ↥(Qof S K) = 1) (hnc : ¬ IsCyclic ↥(Qof S K)) :
    ∃ n, IVK.IsQuaternionTwoGroup ↥(Qof S K) n :=
  quat_of_unique_invol h.Q_pgroup (fun _ ha ha2 ha1 => h.eq_z_of_Q hr ha ha2 ha1) hnc

theorem S1_eq (h : Std6r1 G z S K) : S1 S K = S :=
  inf_eq_left.2 (fun _ hs => h.normalizes_K (h.syl_C.1 hs))

end Std6r1

theorem lemma_6_4 (h46 : Prop4_6) (h49 : Prop4_9) (h4hij : IVK_1_4hij_outer) (htriv : IVK_triv_fAut) :
    Lemma6_4 := by
  intro G _ _ z S K h ha hb
  have hS1 : S1 S K = S := h.S1_eq
  have hcond : Cond6a (S1 S K) K := by rw [hS1]; exact ha
  obtain ⟨hidx, h7, -⟩ := h4hij G z S h.toStd6 K h.comp_rigid hcond
  rw [hS1] at hidx h7
  have hstd : Std4r1 G z S K (Qof S K) :=
    { toStd6r1 := h
      F_le := inf_le_left
      Q_eq := by
        rw [h.Qz_eq, h.Rz_eq]
        exact (inf_eq_left.2 (le_sup_right : S ⊓ cSec K ≤ (S ⊓ K) ⊔ (S ⊓ cSec K))).symm
      index_le := by
        rw [h.Pz_eq]
        exact hidx
      eq_of_2A7 := fun h2 => by
        rw [h.Pz_eq]
        exact h7 h2
      inv_fAut := fun s hs _ hfa => by
        rw [h.Pz_eq]
        exact mem_sup_right ⟨hs, ha s hs hfa⟩
      F_fAut := fun f hf => htriv G z S h.toStd6 K h.comp_rigid f hf.2 }
  have hnc : ¬ IsCyclic ↥(Qof S K) := h46 G z S K (Qof S K) hstd
  exact h49 G z S K (Qof S K) hstd h.Qz_eq (h.Q_quat hb hnc)

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem card_of_doubleCoverAlt7 {X : Type} [Group X] (h : IsDoubleCoverOfAlt X 7) :
    Nat.card X = 5040 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
  rw [Nat.card_congr e.toEquiv, card_alt7, hc] at h1
  omega

theorem no_sol_5040 (q : ℕ) (h5 : 5 ≤ q) (h : q * (q ^ 2 - 1) = 5040) : False := by
  have h18 : q ≤ 18 := by
    by_contra hlt
    push Not at hlt
    have : 19 ≤ q := hlt
    have h3 : q ^ 2 - 1 ≥ 360 := by
      have : 19 * 19 ≤ q * q := Nat.mul_le_mul this this
      rw [sq]; omega
    nlinarith
  interval_cases q <;> omega

theorem not_2A7_of_G2Concl {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G}
    (hc : G2Concl G z S K) : ¬ IsDoubleCoverOfAlt (HatT K) 7 := by
  intro h7
  obtain ⟨q, -, h5, ⟨Fq, _, _, hq, ⟨e⟩⟩, -⟩ := hc
  have h1 : Nat.card (HatT K) = 5040 := card_of_doubleCoverAlt7 h7
  have h2 : Nat.card (HatT K) = Nat.card (IVK.SL2 Fq) := Nat.card_congr e.toEquiv
  have h3 : Nat.card (IVK.SL2 Fq) = Nat.card Fq * (Nat.card Fq ^ 2 - 1) := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 Fq).toEquiv]
    exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two Fq
  rw [h2, h3, hq] at h1
  exact no_sol_5040 q h5 h1

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
