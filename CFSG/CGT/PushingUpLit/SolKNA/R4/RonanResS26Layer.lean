module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestAut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest

section Cit3


theorem layerIdent {r n : ℕ} (hr : 4 ≤ r) (hA : CIT3Below n) (hB : TightBelowR r n)
    (hList : SmallListR) (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m)
    {Q : Type} [Group Q] [Finite Q] (hQn : Nat.card Q < n) {R : Subgroup Q} {S : Sylow 2 R}
    {z : Q} (hd : TightDatum R S z) (hc : TightClsR r Q R S z) (hnO : ¬ TightInO2 z)
    (hE : TightEdgeless R) :
    ∃ L : Subgroup Q, L.Normal ∧ CFSG.IsQuasisimple ↥L ∧
      Subgroup.centralizer (L : Set Q) = Subgroup.center Q ∧ z ∉ Subgroup.center Q ∧
      (∀ y : Q, ∀ m ∈ Subgroup.center Q, y * z * y⁻¹ = z * m → m = 1) ∧
      TightDatum (R.map (QuotientGroup.mk' (Subgroup.center Q)))
        (TwistQ.sylowMap (Subgroup.center Q) S) (QuotientGroup.mk' (Subgroup.center Q) z) ∧
      TightClsR r (Q ⧸ Subgroup.center Q) (R.map (QuotientGroup.mk' (Subgroup.center Q)))
        (TwistQ.sylowMap (Subgroup.center Q) S) (QuotientGroup.mk' (Subgroup.center Q) z) ∧
      ¬ TightInO2 (QuotientGroup.mk' (Subgroup.center Q) z) ∧
      TightEdgeless (R.map (QuotientGroup.mk' (Subgroup.center Q))) ∧
      IsSimpleGroup ↥(socleOf L) ∧ (∃ a b : ↥(socleOf L), a * b ≠ b * a) ∧
      Subgroup.centralizer ((socleOf L : Subgroup (Q ⧸ Subgroup.center Q)) :
        Set (Q ⧸ Subgroup.center Q)) = ⊥ ∧ EdgelessFamily ↥(socleOf L) := by
  classical
  obtain ⟨L, hLq, hLn, hLC⟩ := exists_normal_component hd hc hnO
  have hN2 : IsPGroup 2 ↥(Subgroup.center Q) := isPGroup_center_R hc
  have htN : z ∉ (Subgroup.center Q) := fun h => hnO ⟨(Subgroup.center Q), inferInstance, hN2, h⟩
  have hNc : (Subgroup.center Q) ≤ Subgroup.center Q := le_rfl
  have hnt : ∀ y : Q, ∀ n ∈ (Subgroup.center Q), y * z * y⁻¹ = z * n → n = 1 := by
    intro y n hn hy
    by_contra h1
    exact hd.not_edgeless_of_twin hn h1 hy hE
  have hd' := TwistQ.datum hd hN2 htN hnt
  have hc' := twistQ_clsR hd hNc hN2 htN hc
  have hnO' : ¬ TightInO2 (QuotientGroup.mk' (Subgroup.center Q) z) :=
    fun h => hnO (TwistQ.inO2_of hN2 h)
  haveI := hLn
  have hTs : IsSimpleGroup ↥(socleOf L) := isSimpleGroup_socle hLq hLC
  have hTab := exists_ne_comm_socle hLq hLC
  have hTC := centralizer_socle_eq_bot hLq hLC
  have hAn : Nat.card (Q ⧸ (Subgroup.center Q)) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _
      (QuotientGroup.mk'_surjective (Subgroup.center Q))) hQn
  have hZA : Subgroup.center (Q ⧸ (Subgroup.center Q)) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [← hTC, Subgroup.mem_centralizer_iff]
    intro g _
    exact (Subgroup.mem_center_iff.mp hx g)
  have hE' : TightEdgeless (R.map (QuotientGroup.mk' (Subgroup.center Q))) := by
    rcases (hB (Q ⧸ (Subgroup.center Q)) hAn _ _ _ hd' hc').resolve_right
      (not_goodThreeElement_of_four_le hr hd' hc'.1) with h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4
    · exact absurd h2 hnO'
    · exact he
    · exact he
    · exact absurd h4 (not_tightE4_R hd' hc' hnO' hZA)
  have hT : socleOf L ≤ (MonoidHom.id (Q ⧸ (Subgroup.center Q))).range := fun x _ => ⟨x, rfl⟩
  have h4gen := twoSubgroupsFourGenerated_socle hr hA hB h6 (socleOf L) hTs hTab hTC hAn
    (MonoidHom.id (Q ⧸ (Subgroup.center Q))) Function.injective_id hT hd' hc' hnO'
  have hfam := edgelessFamily_of_embedded hr hList hO (socleOf L) hTs hTab hTC h4gen
    (MonoidHom.id (Q ⧸ (Subgroup.center Q))) Function.injective_id hT hd' hc'
  exact ⟨L, hLn, hLq, hLC, htN, hnt, hd', hc', hnO', hE', hTs, hTab, hTC, hfam⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
