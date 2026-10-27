module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeShapeL28
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQKFC1U33
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
public import CFSG.GH74.KGroups.U33
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

namespace TenNineOneThree


theorem card_mulAut_of_isUThreeThree {K : Type} [Group K] (hK : IsUThreeThree K) :
    Nat.card (MulAut K) = 12096 := by
  obtain ⟨⟨i, hv⟩, ⟨q, hq3, hiq⟩, ⟨e⟩⟩ := hK
  subst hiq
  have hm := CFSG.Models.lieModel_twistedA 2 q hv e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  have hqp : q.p = 3 ∧ q.exponent = 1 := by
    have h := TauCeti.PrimePower.card_def q
    rw [hq3] at h
    have hp : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).mp
      ⟨q.p ^ (q.exponent - 1), by rw [h, ← pow_succ', Nat.sub_add_cancel q.exponent_pos]⟩
    refine ⟨hp, ?_⟩
    rw [hp] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h.symm.trans (pow_one 3).symm)
  rw [hc, hf, hqp.1, hqp.2] at hm
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
    (CFSG.Models.LieModel.toBlueprint (by decide) hm)
  exact CFSG.GH74.KGroups.U33.card_mulAut e'

theorem shapeSimple_of_u33 {K : Type} [Group K] [Finite K] (hK : IsUThreeThree K)
    (S : Sylow 3 K) {P : Subgroup (MulAut K)} (hP : IsPGroup 3 P)
    (hSP : (S : Subgroup K).map (MulAut.conj : K →* MulAut K) ≤ P) : ShapeSimple P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hZ⟩ := CFSG.AGLEmbeddingD2.McLaughlin.u33_simple_card_center hK
  obtain ⟨hS27, hSnc, -, -⟩ := InnerQ.KFC1.u33_local hK S
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [← hZ, Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun α : MulAut K => α x) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  set I := (S : Subgroup K).map (MulAut.conj : K →* MulAut K) with hI
  have hIcard : Nat.card I = 27 := by
    rw [hI, Subgroup.card_map_of_injective hinj, hS27]
  have hPle : Nat.card P ≤ 27 := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hdvd : 3 ^ k ∣ 12096 := hk ▸ card_mulAut_of_isUThreeThree hK ▸
      Subgroup.card_subgroup_dvd_card P
    have hk3 : k ≤ 3 := by
      by_contra! h
      have : 3 ^ 4 ∣ 12096 := (Nat.pow_dvd_pow 3 h).trans hdvd
      norm_num at this
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 27 := by norm_num
  have hPI : I = P := Subgroup.eq_of_le_of_card_ge hSP (by rw [hIcard]; exact hPle)
  have hPcard : Nat.card P = 27 := by rw [← hPI, hIcard]
  have hnc : ¬ ∀ a b : P, a * b = b * a := by
    intro hcomm
    apply hSnc
    intro a ha b hb
    have hc := congrArg Subtype.val (hcomm ⟨MulAut.conj a, hPI ▸ ⟨a, ha, rfl⟩⟩
      ⟨MulAut.conj b, hPI ▸ ⟨b, hb, rfl⟩⟩)
    apply hinj
    rw [map_mul, map_mul]
    exact hc
  exact Or.inr ⟨hnc, pRank_top_le_two_of_card hPcard hnc⟩

theorem kFactCaseIThreeShapeU33 :
    ∀ (B : Type) [Group B] [Finite B] (Kb : Subgroup B) [Kb.Normal] (T : Subgroup B),
      IsPGroup 3 T → (∃ S : Sylow 3 Kb, (S : Subgroup Kb).map Kb.subtype ≤ T) →
      IsUThreeThree Kb →
        ShapeSimple (T ⧸ ((MulAut.conjNormal (H := Kb)).comp T.subtype).ker) := by
  intro B _ _ Kb _ T hT ⟨S, hST⟩ hK
  set φ := (MulAut.conjNormal (H := Kb)).comp T.subtype with hφ
  have hrange : (S : Subgroup Kb).map (MulAut.conj : Kb →* MulAut Kb) ≤ φ.range := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨s, hST ⟨s, hs, rfl⟩⟩, ?_⟩
    ext y
    simp [hφ, MulAut.conjNormal_apply, MulAut.conj_apply]
  have hP : IsPGroup 3 φ.range := hT.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact shapeSimple_congr (QuotientGroup.quotientKerEquivRange φ).symm
    (shapeSimple_of_u33 hK S hP hrange)

@[expose] def KFactCaseIThreeShapeProd : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (Kb : Subgroup B) [Kb.Normal] (T : Subgroup B),
    IsPGroup 3 T → (∃ S : Sylow 3 Kb, (S : Subgroup Kb).map Kb.subtype ≤ T) →
    IsCaseIThreeProd Kb →
      ShapeProd (T ⧸ ((MulAut.conjNormal (H := Kb)).comp T.subtype).ker)

theorem kFactCaseIThreeShape_of_prod (h : KFactCaseIThreeShapeProd) : KFactCaseIThreeShape := by
  intro B _ _ Kb _ T hT hS
  refine ⟨fun hK => ?_, h B Kb T hT hS⟩
  obtain ⟨d, hd | ⟨q, hp, he1, hdq⟩, he⟩ := hK
  · exact kFactCaseIThreeShapeL28 B Kb T hT hS ⟨d, Or.inl ⟨rfl, hd⟩, he⟩
  · refine kFactCaseIThreeShapeU33 B Kb T hT hS ⟨d, ⟨q, ?_, hdq⟩, he⟩
    rw [TauCeti.PrimePower.card_def, hp, he1]
    rfl

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
