module

public import CFSG.Blueprint.Catalog
import CFSG.RankThree.PartOne.S15K.SL2Model
import CFSG.Quasithin.Background.G2A5Iso
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.AGLEmbedding

theorem lieModel_PSL_two_of_isLin2Type {G : Type} [Group G] {L : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hlin : CFSG.QuasithinUnique.IsLin2Type L n) :
    CFSG.Blueprint.LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n := by
  obtain ⟨F, instF, instFinF, hFcard, α, hαs, hker, -⟩ := hlin
  letI : Field F := instF
  letI : Fintype F := instFinF
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hFcard]
  haveI hchar : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  have hn2 : 2 ≤ n := hn
  have h2n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hmodel : CFSG.Open.StatedClassicalModel
      (Matrix.SpecialLinearGroup (Fin 2) F) .PSL 2 2 n := by
    refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, instF, Finite.of_fintype F, hF, ?_⟩
    · intro h
      have h' := congrArg Prod.snd h
      simp only at h'
      omega
    · intro h
      have h' := congrArg Prod.snd h
      simp only at h'
      omega
    · exact CFSG.RankThree.PartOne.S15K.nonempty_sl2_mulEquiv_statedProj
  have hL : CFSG.Blueprint.LieModel (Matrix.SpecialLinearGroup (Fin 2) F) .PSL 2 2 n :=
    Or.inl ⟨by decide, hmodel⟩
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL

theorem lieModel_PSL_two_two_two_of_isAltType_five {G : Type} [Group G] {L : Subgroup G}
    (h5 : CFSG.QuasithinUnique.IsAltType L 5) :
    CFSG.Blueprint.LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 2 := by
  obtain ⟨α, hαs, hker, -⟩ := h5
  let K := GaloisField 2 2
  have hK : Nat.card K = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  haveI hchar : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2) (by rw [hK]; norm_num)
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  obtain ⟨e5⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 K hK hcardSL
  obtain ⟨eSL⟩ := CFSG.RankThree.PartOne.S15K.nonempty_sl2_mulEquiv_statedProj (F := K)
  have hmodel : CFSG.Open.StatedClassicalModel (alternatingGroup (Fin 5)) .PSL 2 2 2 :=
    ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩,
      K, inferInstance, inferInstance, hK', ⟨e5.symm.trans eSL⟩⟩
  have hL : CFSG.Blueprint.LieModel (alternatingGroup (Fin 5)) .PSL 2 2 2 :=
    Or.inl ⟨by decide, hmodel⟩
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL

end CFSG.AGLEmbedding

end
