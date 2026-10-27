module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79s
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L1 L2 J : Subgroup G}

private lemma y7c_centIn_normalizer (h : Gl3Pair M L1 L2) :
    L1 ≤ normalizer (centIn M L2 : Set G) :=
  Gl3Pair.L2_le_normalizer_centIn h.symm le_rfl

private lemma y7c_cent_comm (h : Gl3Pair M L1 L2) :
    ∀ a ∈ centIn M L1, ∀ b ∈ centIn M L2, a * b = b * a := by
  haveI : IsMulCommutative ↥M := h.elem.1
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm' (⟨a, (Subgroup.mem_inf.mp ha).1⟩ : M)
    (⟨b, (Subgroup.mem_inf.mp hb).1⟩ : M))

private lemma y7c_centIn_le_centralizer (h : Gl3Pair M L1 L2) :
    M ≤ centralizer (centIn M L2 : Set G) := by
  haveI : IsMulCommutative ↥M := h.elem.1
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (congrArg Subtype.val (mul_comm' (⟨m, hm⟩ : M)
    (⟨w, (Subgroup.mem_inf.mp hw).1⟩ : M))).symm

private lemma y7c_centIn_centIn_bot (h : Gl3Pair M L1 L2)
    (hinf : centIn M L1 ⊓ centIn M L2 = ⊥) :
    centIn (centIn M L2) L1 = ⊥ := by
  refine le_bot_iff.mp (le_trans ?_ (le_of_eq hinf))
  refine le_inf ?_ inf_le_left
  exact le_inf (le_trans inf_le_left inf_le_left) inf_le_right

private lemma y7c_cent_ge_eight {M A B : Subgroup G} (h : Gl3Pair M A B)
    (hinf : centIn M A ⊓ centIn M B = ⊥) (hB : centIn M B ≠ ⊥) :
    8 ≤ Nat.card ↥(centIn M B) := by
  have hnorm : A ≤ normalizer (centIn M B : Set G) :=
    Gl3Pair.L2_le_normalizer_centIn h.symm le_rfl
  have hcent : M ≤ centralizer (centIn M B : Set G) := by
    haveI : IsMulCommutative ↥M := h.elem.1
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (congrArg Subtype.val (mul_comm' (⟨m, hm⟩ : M)
      (⟨w, (Subgroup.mem_inf.mp hw).1⟩ : M))).symm
  have hbot : centIn (centIn M B) A = ⊥ := by
    refine le_bot_iff.mp (le_trans ?_ (le_of_eq hinf))
    refine le_inf ?_ inf_le_left
    exact le_inf (le_trans inf_le_left inf_le_left) inf_le_right
  exact y7c_gl3_card_ge_eight h.ext1 hnorm hcent (h.isElemAbelian_centIn B) hB hbot

theorem y7c_cent_inf (hJ : J ≤ L1 ⊔ L2) (hJM : centIn M J = ⊥) :
    centIn M L1 ⊓ centIn M L2 = ⊥ := by
  rw [← y7c_centIn_sup M L1 L2]
  exact le_bot_iff.mp
    (le_trans (inf_le_inf_left _ (Subgroup.centralizer_le hJ)) (le_of_eq hJM))

theorem y7c_cent_card (h : Gl3Pair M L1 L2) (hJ : J ≤ L1 ⊔ L2) (hJM : centIn M J = ⊥)
    (hU1 : centIn M L1 ≠ ⊥) (hU2 : centIn M L2 ≠ ⊥) :
    Nat.card ↥(centIn M L1) = 8 ∧ Nat.card ↥(centIn M L2) = 8 := by
  have hinf : centIn M L1 ⊓ centIn M L2 = ⊥ := y7c_cent_inf hJ hJM
  have hU2ge : 8 ≤ Nat.card ↥(centIn M L2) := y7c_cent_ge_eight h hinf hU2
  have hU1ge : 8 ≤ Nat.card ↥(centIn M L1) :=
    y7c_cent_ge_eight h.symm (by rw [inf_comm]; exact hinf) hU1
  have hprod : Nat.card ↥(centIn M L1 ⊔ centIn M L2) =
      Nat.card ↥(centIn M L1) * Nat.card ↥(centIn M L2) :=
    y7c_card_sup_of_commute (y7c_cent_comm h) hinf
  have hleM : centIn M L1 ⊔ centIn M L2 ≤ M := sup_le inf_le_left inf_le_left
  have hprod_le : Nat.card ↥(centIn M L1) * Nat.card ↥(centIn M L2) ≤ 64 := by
    have hcard := Subgroup.card_le_of_le hleM
    rw [hprod, h.card] at hcard
    norm_num at hcard
    exact hcard
  constructor
  · refine le_antisymm ?_ hU1ge
    have h8 : Nat.card ↥(centIn M L1) * 8 ≤
        Nat.card ↥(centIn M L1) * Nat.card ↥(centIn M L2) := Nat.mul_le_mul_left _ hU2ge
    have : Nat.card ↥(centIn M L1) * 8 ≤ 64 := le_trans h8 hprod_le
    omega
  · refine le_antisymm ?_ hU2ge
    have h8 : Nat.card ↥(centIn M L2) * 8 ≤
        Nat.card ↥(centIn M L2) * Nat.card ↥(centIn M L1) := Nat.mul_le_mul_left _ hU1ge
    have hle : Nat.card ↥(centIn M L2) * Nat.card ↥(centIn M L1) ≤ 64 := by
      rw [Nat.mul_comm]; exact hprod_le
    have : Nat.card ↥(centIn M L2) * 8 ≤ 64 := le_trans h8 hle
    omega

theorem y7c_cent_sup (h : Gl3Pair M L1 L2) (hJ : J ≤ L1 ⊔ L2) (hJM : centIn M J = ⊥)
    (hU1 : centIn M L1 ≠ ⊥) (hU2 : centIn M L2 ≠ ⊥) :
    centIn M L1 ⊔ centIn M L2 = M := by
  obtain ⟨h1, h2⟩ := y7c_cent_card h hJ hJM hU1 hU2
  have hleM : centIn M L1 ⊔ centIn M L2 ≤ M := sup_le inf_le_left inf_le_left
  refine Subgroup.eq_of_le_of_card_ge hleM ?_
  have hprod : Nat.card ↥(centIn M L1 ⊔ centIn M L2) =
      Nat.card ↥(centIn M L1) * Nat.card ↥(centIn M L2) :=
    y7c_card_sup_of_commute (y7c_cent_comm h) (y7c_cent_inf hJ hJM)
  rw [hprod, h1, h2, h.card]
  norm_num

theorem y7c_cent_irred (h : Gl3Pair M L1 L2) (hJ : J ≤ L1 ⊔ L2) (hJM : centIn M J = ⊥)
    (hU1 : centIn M L1 ≠ ⊥) (hU2 : centIn M L2 ≠ ⊥) {W : Subgroup G} (hW : W ≤ centIn M L2)
    (hWL : L1 ≤ normalizer (W : Set G)) : W = ⊥ ∨ W = centIn M L2 := by
  obtain ⟨_, hcard2⟩ := y7c_cent_card h hJ hJM hU1 hU2
  exact y7c_gl3_irreducible h.ext1 (y7c_centIn_normalizer h) (y7c_centIn_le_centralizer h)
    hcard2 (y7c_centIn_centIn_bot h (y7c_cent_inf hJ hJM)) hW hWL

theorem y7c_cent_le_comm (h : Gl3Pair M L1 L2) (hJ : J ≤ L1 ⊔ L2) (hJM : centIn M J = ⊥)
    (hU1 : centIn M L1 ≠ ⊥) (hU2 : centIn M L2 ≠ ⊥) : centIn M L2 ≤ ⁅L1, L1⁆ := by
  have hU2L1 : centIn M L2 ≤ L1 := le_trans inf_le_left (h.inf ▸ inf_le_left)
  have hCle : ⁅L1, centIn M L2⁆ ≤ centIn M L2 :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp (y7c_centIn_normalizer h)
  rcases y7c_cent_irred h hJ hJM hU1 hU2 hCle
      (Subgroup.normalizer_commutator_ge_left (H₁ := L1) (H₂ := centIn M L2)) with hCbot | hCtop
  · exfalso
    have hL1cent : L1 ≤ centralizer (centIn M L2 : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hCbot
    have hU2cent : centIn M L2 ≤ centralizer (L1 : Set G) :=
      (Subgroup.le_centralizer_iff).mpr hL1cent
    have hle : centIn M L2 ≤ centIn M L1 ⊓ centIn M L2 :=
      le_inf (le_inf inf_le_left hU2cent) le_rfl
    have hbot : centIn M L2 ≤ ⊥ := hle.trans (le_of_eq (y7c_cent_inf hJ hJM))
    exact hU2 (le_bot_iff.mp hbot)
  · rw [← hCtop]
    exact Subgroup.commutator_mono le_rfl hU2L1

end CFSG.OddStandard.HigherRank.YamadaG23
