module

public import CFSG.CGT.Foote82.Climb
public import CFSG.CGT.Foote82.EF2
public import CFSG.CGT.Foote82.EF1Bridge
import CFSG.Quasithin.Background.A4
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCFooteBlocks
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTI

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isFooteBlock_conj {H J : Subgroup G} (hJ : IsFooteBlock H J) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    IsFooteBlock H (J.map (MulAut.conj g).toMonoidHom) := by
  have h := isFooteBlock_map hJ (MulAut.conj g)
  rwa [map_conj_eq_self_of_mem_normalizer hg] at h

theorem not_comm_of_isFooteBlock {H J : Subgroup G} (hJ : IsFooteBlock H J) :
    ¬ ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
  intro hc
  have hbot : ⁅J, J⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hc a ha b hb).symm
  have hJ1 : J = ⊥ := by rw [← IsFooteBlock.commutator_eq hJ, hbot]
  apply not_isPGroup_of_block (IsFooteBlock.self hJ)
  rw [hJ1]
  exact IsPGroup.of_bot

theorem le_of_isSubnormal_of_isFooteBlock {X A B C : Subgroup G} (hA : IsSubnormal A X)
    (hBX : B ≤ X) (hB : IsFooteBlock B B) (hCA : C ≤ A) (hCB : C ≤ B) (hCp : ⁅C, C⁆ = C)
    (hC2 : ¬ IsPGroup 2 C) : B ≤ A := by
  have hAB : IsSubnormal (A ⊓ B) B := hA.inf_of_le hBX
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥B) with hπ
  set S : Subgroup ↥B := (A ⊓ B).subgroupOf B with hS
  have hSn : IsSubnormal S ⊤ := CFSG.Open.IsSubnormal.of_mathlib hAB.subgroupOf
  have hπS : IsSubnormal (S.map π) ⊤ := by
    have := hSn.map π
    rwa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at this
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top
      hB.quasisimple (S.map π) hπS with hc | htop
  · exfalso
    apply hC2
    have hCC : ⁅C, C⁆ ≤ pCoreOf 2 B := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have hmem : ∀ c (hc' : c ∈ C), π ⟨c, hCB hc'⟩ ∈ Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B) := by
        intro c hc'
        exact hc ⟨⟨c, hCB hc'⟩, Subgroup.mem_subgroupOf.mpr ⟨hCA hc', hCB hc'⟩, rfl⟩
      have h1 := Subgroup.mem_center_iff.mp (hmem a ha) (π ⟨b, hCB hb⟩)
      have hab : (⁅(⟨a, hCB ha⟩ : ↥B), ⟨b, hCB hb⟩⁆ : ↥B) ∈ CFSG.pCore 2 ↥B := by
        rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥B), MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_def]
        rw [hπ] at h1
        rw [← h1]
        group
      exact ⟨_, hab, rfl⟩
    rw [← hCp]
    exact (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 B).to_le hCC
  ·
    have hmul : ∀ k ∈ B, ∃ x ∈ A ⊓ B, ∃ r ∈ pCoreOf 2 B, k = x * r := by
      intro k hk
      have hk' : π ⟨k, hk⟩ ∈ S.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨x, hx, hxk⟩ := hk'
      refine ⟨x, Subgroup.mem_subgroupOf.mp hx, ((x⁻¹ * ⟨k, hk⟩ : ↥B) : G), ?_, ?_⟩
      · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxk
        exact ⟨_, hxk, rfl⟩
      · simp
    have hO := CFSG.Quasithin.oTwoUpper_le_of_subnormal_mul hAB
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 B) hmul
    have hBO : B ≤ CFSG.Quasithin.oTwoUpper B :=
      CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.le_of_forall_odd_mem_of_twoResidual hB.residual
        fun _ hx hxo => CFSG.Quasithin.mem_oTwoUpper_of_odd hx hxo
    exact (hBO.trans hO).trans inf_le_left

theorem pCoreOf_le_pCoreOf_of_isSubnormal {A X : Subgroup G} (h : IsSubnormal A X) :
    pCoreOf 2 A ≤ pCoreOf 2 X := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    refine le_pCoreOf_of_normalizes ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H).trans hle)
      ?_ (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
    intro m hm
    have hmH : m ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN hm
    exact CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.normalizer_le_normalizer_pCoreOf H hmH

omit [Finite G] in
theorem pCoreOf_ne_bot_of_isFooteBlock {H J : Subgroup G} (hJ : IsFooteBlock H J) :
    pCoreOf 2 J ≠ ⊥ := by
  intro h
  have hU : blockU J = ⊥ := by
    rw [blockU, show blockQ J = ⊥ from h, Subgroup.commutator_bot_left]
  have hlt := hJ.chief.1
  rw [hU] at hlt
  exact not_lt_bot hlt

omit [Finite G] in
theorem normalizer_le_of_glbIsMaxTwoLocal {M D : Subgroup G} (hM : GLBIsMaxTwoLocal M)
    (hMD : M ≤ Subgroup.normalizer (D : Set G)) (hD : pCoreOf 2 D ≠ ⊥) :
    Subgroup.normalizer (D : Set G) ≤ M := by
  have hN := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.normalizer_le_normalizer_pCoreOf D
  have h2 : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 D : Set G)) :=
    ⟨pCoreOf 2 D, hD, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 D, rfl⟩
  have heq := hM.2 _ h2 (hMD.trans hN)
  exact hN.trans heq.le

end CFSG.CGT.Foote82
