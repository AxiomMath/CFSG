module

public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GH74.Uniqueness.Bender.Core
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Holt.General.Defs

public section

namespace CFSG.Holt.General

open MulAction

variable {X : Type*} [Group X]

private theorem pPrimeCore_two_eq_bot_of_even [Finite X] [IsSimpleGroup X]
    (h2 : Even (Nat.card X)) : CFSG.pPrimeCore 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h2)
  exact CFSG.RankThree.PartTwo.Sec21.pPrimeCore_two_eq_bot_of_simple ht

private theorem isSimpleGroup_top [IsSimpleGroup X] : IsSimpleGroup (⊤ : Subgroup X) :=
  (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).isSimpleGroup

theorem zStarIn_top_eq_bot [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (h2 : Even (Nat.card X)) : zStarIn (⊤ : Subgroup X) = ⊥ := by
  have := isSimpleGroup_top (X := X)
  have hO : CFSG.pPrimeCore 2 (⊤ : Subgroup X) = ⊥ :=
    pPrimeCore_two_eq_bot_of_even (by rwa [Subgroup.card_top])
  have hnonab' : ∃ a b : (⊤ : Subgroup X), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
  rw [eq_bot_iff]
  intro x hx
  rw [← (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab').2, Subgroup.mem_center_iff]
  intro y
  have hx' := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hx)
    (QuotientGroup.mk' (CFSG.pPrimeCore 2 (⊤ : Subgroup X)) y)
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    hO, Subgroup.mem_bot] at hx'
  exact inv_mul_eq_one.mp hx'

theorem even_card_of_isSimpleGroup [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) : Even (Nat.card X) := by
  by_contra hodd
  have hsolv := CFSG.Milestones.odd_order_solvable (Nat.not_even_iff_odd.mp hodd)
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)

variable {Ω : Type*} [MulAction X Ω]

private noncomputable def quotientZStarTopEquiv [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) : (⊤ : Subgroup X) ⧸ zStarIn (⊤ : Subgroup X) ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq
    (zStarIn_top_eq_bot hnonab (even_card_of_isSimpleGroup hnonab))).trans
    (QuotientGroup.quotientBot.trans Subgroup.topEquiv)

private theorem map_stabilizerImage_top [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (α : Ω) :
    (stabilizerImage Ω α (⊤ : Subgroup X)).map (quotientZStarTopEquiv hnonab).toMonoidHom =
      stabilizer X α := by
  have hcomp : (quotientZStarTopEquiv hnonab).toMonoidHom.comp
      (QuotientGroup.mk' (zStarIn (⊤ : Subgroup X))) = (⊤ : Subgroup X).subtype := by
    ext y
    rfl
  unfold stabilizerImage
  rw [Subgroup.map_map, hcomp, Subgroup.subgroupOf_map_subtype, inf_top_eq]

theorem isGoodZ_top_iff [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (α : Ω) :
    IsGoodZ X Ω α (⊤ : Subgroup X) ↔
      (CFSG.Open.fusionIsBenderGroup X ∧ CFSG.IsStronglyEmbedded (stabilizer X α)) ∨
        ∃ m : ℕ, 2 ≤ m ∧ ∃ e : X ≃* alternatingGroup (Fin (2 * m + 1)),
          (stabilizer X α).map e.toMonoidHom =
            stabilizer (alternatingGroup (Fin (2 * m + 1))) (0 : Fin (2 * m + 1)) := by
  set e := quotientZStarTopEquiv hnonab (X := X)
  have he := map_stabilizerImage_top hnonab α
  have he' : (stabilizer X α).map e.symm.toMonoidHom = stabilizerImage Ω α ⊤ := by
    rw [← he, CFSG.LocalCores.map_map_symm]
  unfold IsGoodZ
  refine or_congr ⟨fun ⟨hB, hS⟩ => ⟨?_, ?_⟩, fun ⟨hB, hS⟩ => ⟨?_, ?_⟩⟩
    ⟨fun ⟨m, hm, e', hmap⟩ => ⟨m, hm, e.symm.trans e', ?_⟩,
      fun ⟨m, hm, e', hmap⟩ => ⟨m, hm, e.trans e', ?_⟩⟩
  · exact CFSG.RankThree.PartTwo.Sec21.fusionIsBenderGroup_of_mulEquiv e hB
  · rw [← he]
    exact CFSG.GH74.Uniqueness.Bender.IsStronglyEmbedded.map hS e
  · exact CFSG.RankThree.PartTwo.Sec21.fusionIsBenderGroup_of_mulEquiv e.symm hB
  · rw [← he']
    exact CFSG.GH74.Uniqueness.Bender.IsStronglyEmbedded.map hS e.symm
  · rw [← hmap, ← he', Subgroup.map_map]
    rfl
  · rw [← hmap, ← he, Subgroup.map_map]
    rfl

end CFSG.Holt.General
