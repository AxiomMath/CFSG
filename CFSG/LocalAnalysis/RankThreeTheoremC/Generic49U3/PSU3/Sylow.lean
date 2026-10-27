module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryUnipotentCentralizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open

theorem u3Sylow_index_of_isU3Pred {p : ℕ} {K : Type} [Group K] (h : IsU3Pred p K) :
    ∃ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsUnitaryIndex p d ∧
      d.1.fieldExponent = 1 ∧ Nonempty (K ≃* CFSG.AGLEmbedding.CatGroup d) := by
  obtain ⟨q, hqp, hq1, hv, ⟨e⟩⟩ := h
  have hd : CFSG.AGLEmbedding.IsUnitaryIndex p ⟨.twistedA 2 q, hv⟩ := ⟨q, hqp, rfl⟩
  obtain ⟨q', -, hd', hfe, -⟩ := hd.exists_eq
  injection hd' with _ hqq
  subst hqq
  exact ⟨⟨.twistedA 2 q, hv⟩, hd, by rw [hfe, hq1], ⟨e⟩⟩

theorem u3_sylow_data {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Group K] [Finite K]
    (hK : IsU3Pred p K) (T : Sylow p K) :
    Nat.card (T : Subgroup K) = p ^ 3 ∧ (∀ t ∈ (T : Subgroup K), t ^ p = 1) ∧
      ¬ IsMulCommutative (T : Subgroup K) ∧
      Subgroup.centralizer ((T : Subgroup K) : Set K) ≤ (T : Subgroup K) := by
  obtain ⟨d, hd, hfe, he⟩ := u3Sylow_index_of_isU3Pred hK
  obtain ⟨hcard, hcomm, hexp, -⟩ :=
    CFSG.AGLEmbedding.kFactUnitarySylowStructure K p d (by omega) hd he T
  rw [hfe] at hcard
  have hcard' : Nat.card (T : Subgroup K) = p ^ 3 := by simpa using hcard
  have hnc : ¬ IsMulCommutative (T : Subgroup K) := by
    intro hc
    have h1 : (T : Subgroup K) ≤ Subgroup.centralizer ((T : Subgroup K) : Set K) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hc
    have h2 : ⁅(T : Subgroup K), (T : Subgroup K)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    rw [h2, inf_eq_left.mpr h1] at hcomm
    have h3 : Nat.card (T : Subgroup K) = 1 := by rw [← hcomm]; simp
    have h5 : 5 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3
    have h6 : (1 : ℕ) < p ^ 3 := lt_of_lt_of_le (by norm_num) h5
    omega
  refine ⟨hcard', hexp, hnc, ?_⟩
  obtain ⟨-, hf, hq, K', _, _, J, hJ, hK', hfix, ⟨e⟩⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu
      (CFSG.AGLEmbedding.UnitaryModel.statedClassicalModel hd he)
  obtain ⟨S, hS⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_sylow_eq_rootGroup J hJ hK' hfix hf
  obtain ⟨e', he'⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_equiv_map_eq e T S
  have hU : (T : Subgroup K).map e'.toMonoidHom =
      CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ :=
    he'.trans hS
  intro c hc
  have hcR : e' c ∈ CFSG.UnitaryThreeRecognition.Model.rootGroup J hJ := by
    refine CFSG.AGLEmbedding.UnitaryModel.mem_rootGroup_of_forall_comm J hJ hK' hfix hq
      fun r hr => ?_
    have hr' : e'.symm r ∈ (T : Subgroup K) := by
      have : r ∈ (T : Subgroup K).map e'.toMonoidHom := hU ▸ hr
      exact Subgroup.mem_map_equiv.1 this
    have h1 := Subgroup.mem_centralizer_iff.mp hc (e'.symm r) hr'
    have h2 := congrArg e' h1
    simpa [map_mul] using h2
  have h3 : e' c ∈ (T : Subgroup K).map e'.toMonoidHom := hU ▸ hcR
  have h4 := Subgroup.mem_map_equiv.1 h3
  rwa [MulEquiv.symm_apply_apply] at h4

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
