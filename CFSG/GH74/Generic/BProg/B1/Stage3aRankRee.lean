module

public import CFSG.GH74.Generic.BProg.B1.Stage3aRank
public import CFSG.GH74.Generic.BProg.B1.Stage3aRankCerts
import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
public import CFSG.Walter.Ree.Model.JTHyp

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Ree
  CFSG.Walter.Ree.Model Subgroup

theorem reeTitsModel_of_lieModel_twistedG2 {T : Type} [Group T] {f : ℕ}
    (h : LieModel T .twistedG2 0 3 f) : ReeTitsModel T .twistedG2 3 f :=
  (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2

theorem rankCertified_reeModel_two
    {T : Type} [Group T] {f : ℕ} (h : LieModel T .twistedG2 0 3 f) : RankCertified T 2 := by
  have hR : ReeTitsModel T .twistedG2 3 f := reeTitsModel_of_lieModel_twistedG2 h
  obtain ⟨a, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.GLS.IVK.GHInv.ree_model_data hR
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (CFSG.LieType.Chevalley.coxeterSystem ReeTag.G2.tag).length
  obtain ⟨hE, hcard, -⟩ := smallRee_E8_sylow hK hw₀
  exact (rankCertified_of_isElementaryAbelian _ hE (by rw [hcard]; norm_num)).of_mulEquiv e.symm

theorem noJPrimeFor_shape4
    : NoJPrimeFor QShape4 := by
  refine noJPrimeFor_of_bar (fun e h => ?_) ?_
  · obtain ⟨f, hf⟩ := h
    exact ⟨f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hf⟩
  · intro G _ _ hgen x K hx hKpc hG2 hr h4
    obtain ⟨f, hmodel⟩ := h4
    have hR : ReeTitsModel ↥(imgBar x K) .twistedG2 3 f := reeTitsModel_of_lieModel_twistedG2 hmodel
    have hsimple : IsSimpleGroup ↥(imgBar x K) :=
      (CFSG.LieType.Simplicity.fam_2g2_simplicity _ 3 f hR).2
    have hbot : Subgroup.center ↥(imgBar x K) = ⊥ :=
      center_eq_bot_of_simple_of_quasisimple hsimple hG2.1.1
    exact false_of_J2_pair_rank_of_center_bot hgen hx hKpc hr hbot (rankCertified_reeModel_two hmodel)

end CFSG.GH74.Generic.BProg.B1
