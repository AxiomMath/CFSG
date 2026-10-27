module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoBase

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

private theorem natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h5, h2]
  norm_num

theorem AschbacherHyp.commutator_commutator_eq_top [Finite C] (hC : AschbacherHyp C Q) :
    commutator ↥(commutator C) = ⊤ := by
  have hE : IsExtraspecialPGroup 2 Q := hC.plus.isExtraspecialPGroup
  haveI : Finite Q := hC.plus.finite
  have hQL : Q ≤ commutator C := hC.le_commutator
  have hcenter_le_commQ : centerOf Q ≤ ⁅Q, Q⁆ := by
    intro z hz
    obtain ⟨hzQ, _hzc⟩ := Subgroup.mem_inf.mp hz
    have hz' : ((⟨z, hzQ⟩ : Q) : C) ∈ centerOf Q := hz
    have hzc' : (⟨z, hzQ⟩ : Q) ∈ Subgroup.center Q :=
      (mem_centerOf_iff (Q := Q) ⟨z, hzQ⟩).1 hz'
    have hmem : (⟨z, hzQ⟩ : Q) ∈ _root_.commutator Q := by
      rw [hE.2.1]
      exact hzc'
    have hmap : z ∈ (_root_.commutator Q).map Q.subtype := ⟨⟨z, hzQ⟩, hmem, rfl⟩
    rwa [Subgroup.map_subtype_commutator] at hmap
  have hWnorm : (⁅Q, commutator C⁆).Normal := inferInstance
  have hZW : centerOf Q ≤ ⁅Q, commutator C⁆ :=
    hcenter_le_commQ.trans (Subgroup.commutator_mono le_rfl hQL)
  have hWQ : ⁅Q, commutator C⁆ ≤ Q := Subgroup.commutator_le_left Q (commutator C)
  have hinv : ∀ g ∈ commutator C, ∀ w ∈ ⁅Q, commutator C⁆,
      g * w * g⁻¹ ∈ ⁅Q, commutator C⁆ :=
    fun g _ w hw => hWnorm.conj_mem w hw g
  rcases hC.irreducible ⁅Q, commutator C⁆ hZW hWQ hinv with hW | hW
  ·
    exfalso
    have hcomm_le_Q : commutator C ≤ Q := by
      refine le_of_forall_commutator_mem_centerOf hE hC.centralizer_le (K := commutator C) ?_
      intro g hg x hx
      have hmem : ⁅x, g⁆ ∈ ⁅Q, commutator C⁆ := Subgroup.commutator_mem_commutator hx hg
      have hmem' : ⁅x, g⁆ ∈ centerOf Q := hW ▸ hmem
      have hginv : ⁅g, x⁆ = ⁅x, g⁆⁻¹ := (commutatorElement_inv (g₁ := x) (g₂ := g)).symm
      rw [hginv]
      exact (centerOf Q).inv_mem hmem'
    have hLQ : commutator C = Q := le_antisymm hcomm_le_Q hQL
    obtain ⟨e⟩ := hC.quotient
    have hcard : Nat.card (C ⧸ Q) = 7200 := by
      rw [Nat.card_congr e.toEquiv, natCard_A5WrTwo]
    have h2eq : (2 : ℕ) = 7200 := by
      calc (2 : ℕ) = (commutator C).index := hC.index_commutator.symm
        _ = Q.index := by rw [hLQ]
        _ = Nat.card (C ⧸ Q) := Subgroup.index_eq_card Q
        _ = 7200 := hcard
    exact absurd h2eq (by norm_num)
  ·
    have hQ_le : Q ≤ ⁅commutator C, commutator C⁆ :=
      calc Q = ⁅Q, commutator C⁆ := hW.symm
        _ ≤ ⁅commutator C, commutator C⁆ := Subgroup.commutator_mono hQL le_rfl
    let π : C →* C ⧸ Q := QuotientGroup.mk' Q
    obtain ⟨e⟩ := hC.quotient
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Q
    have hker : π.ker = Q := QuotientGroup.ker_mk' Q
    have hmapC : (commutator C).map π = commutator (C ⧸ Q) := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ]
      rfl
    have hmape : (commutator (C ⧸ Q)).map (e : C ⧸ Q →* A5WrTwo) = commutator A5WrTwo := by
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective (e : C ⧸ Q →* A5WrTwo) e.surjective]
      rfl
    have hperfect : ⁅commutator (C ⧸ Q), commutator (C ⧸ Q)⁆ = commutator (C ⧸ Q) := by
      apply Subgroup.map_injective (f := (e : C ⧸ Q →* A5WrTwo)) e.injective
      rw [Subgroup.map_commutator, hmape, A5WrTwo.commutator_commutator]
    have hmapLL : (⁅commutator C, commutator C⁆).map π = (commutator C).map π := by
      rw [Subgroup.map_commutator, hmapC, hperfect]
    have hL_le : commutator C ≤ ⁅commutator C, commutator C⁆ := by
      intro g hg
      have hg' : π g ∈ (⁅commutator C, commutator C⁆).map π :=
        hmapLL.symm ▸ Subgroup.mem_map_of_mem π hg
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg'
      have hker_mem : y⁻¹ * g ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyg, inv_mul_cancel]
      have hQmem : y⁻¹ * g ∈ Q := by rwa [hker] at hker_mem
      have hg_eq : g = y * (y⁻¹ * g) := by group
      rw [hg_eq]
      exact (⁅commutator C, commutator C⁆).mul_mem hy (hQ_le hQmem)
    have hLL : ⁅commutator C, commutator C⁆ = commutator C :=
      le_antisymm (Subgroup.commutator_le_self _) hL_le
    apply Subgroup.map_injective (f := (commutator C).subtype) (commutator C).subtype_injective
    rw [Subgroup.map_subtype_commutator, hLL]
    rw [show (⊤ : Subgroup ↥(commutator C)).map (commutator C).subtype = commutator C by
      rw [Subgroup.map_top, Subgroup.range_subtype]]

end CFSG.EvenSporadicStandard.HNRecog
