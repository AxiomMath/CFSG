module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGL281Act
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGL281Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem fg_isSimpleGroup_oddCore_l281 [Finite G] {L : Subgroup G} (h : IsL281 L) :
    IsSimpleGroup (L ⧸ oddCore L) :=
  (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
    ⟨.PSL, 2, 3, 4, h.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)⟩).2.2

theorem fg_center_eq_oddCore_l281 [Finite G] {L : Subgroup G} (hq : IsQuasisimple L)
    (h : IsL281 L) : center ↥L = oddCore ↥L :=
  center_eq_oddCore_of_simple hq (fg_isSimpleGroup_oddCore_l281 h)

theorem fg_exists_psl_of_l281 [Finite G] {L : Subgroup G} (hq : IsQuasisimple L)
    (h : IsL281 L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 81 ∧
      Nonempty (↥L ⧸ center ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  have hc : center ↥L = oddCore ↥L := fg_center_eq_oddCore_l281 hq h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)
  refine ⟨K, inferInstance, inferInstance, by rw [hK]; norm_num, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hc).trans
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)

theorem fg_image_perfect {L X : Subgroup G} {E : Type*} [Group E]
    (e : ↥L ⧸ center ↥L ≃* E) (hXL : X ≤ L) (hX : IsQuasisimple X) :
    ⁅(X.subgroupOf L).map (fgRhoE e), (X.subgroupOf L).map (fgRhoE e)⁆ =
      (X.subgroupOf L).map (fgRhoE e) := by
  have hXX : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.mp hX.1
  have h1 : ⁅X.subgroupOf L, X.subgroupOf L⁆ = X.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXL, hXX]
  rw [← Subgroup.map_commutator, h1]

theorem fg_image_ne_bot {L X : Subgroup G} {E : Type*} [Group E]
    (e : ↥L ⧸ center ↥L ≃* E) (hXL : X ≤ L) (hX : IsQuasisimple X) :
    (X.subgroupOf L).map (fgRhoE e) ≠ ⊥ := by
  intro hbot
  have hle : ∀ a ∈ X, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    have hmem : (⟨a, hXL ha⟩ : ↥L) ∈ X.subgroupOf L := ha
    have hker : (⟨a, hXL ha⟩ : ↥L) ∈ (fgRhoE e).ker := by
      rw [MonoidHom.mem_ker]
      have : fgRhoE e ⟨a, hXL ha⟩ ∈ (X.subgroupOf L).map (fgRhoE e) := ⟨_, hmem, rfl⟩
      rw [hbot] at this
      exact this
    rw [fg_ker_rhoE] at hker
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hker ⟨b, hb⟩)).symm
  obtain ⟨-, -, a, b, hab⟩ := hX
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hle a a.2 b (hXL b.2))

theorem fg_aut_cent_l281 [Finite G] {L : Subgroup G} (hq : IsQuasisimple L) (h : IsL281 L)
    {X : Subgroup G} (hXL : X ≤ L) (hX : IsQuasisimple X) {R : Subgroup G}
    (hR : R ≤ normalizer (L : Set G) ⊓ centralizer (X : Set G)) :
    (centralizer (L : Set G)).relIndex R ≤ 2 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := fg_exists_psl_of_l281 hq h
  have hLp : commutator ↥L = ⊤ := hq.1.commutator_eq_top
  have hRN : R ≤ normalizer (L : Set G) := hR.trans inf_le_left
  rw [fg_relIndex_eq_card_range_E hLp e hRN]
  exact fg_card_le_two_of_fixes hK (fg_image_perfect e hXL hX) (fg_image_ne_bot e hXL hX)
    (fg_thetaE_fixes e hR)

end CFSG.OddStandard.SmallF3.Omega
