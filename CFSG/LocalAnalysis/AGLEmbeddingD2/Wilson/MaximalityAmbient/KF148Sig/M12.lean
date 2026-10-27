module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.Cores
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12E9
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporM12

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig

open Subgroup CFSG CFSG.GH74.GLS CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec14 CFSG.Blueprint CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open CFSG.RankThree.PartTwo.Toolkit.M12 (P0 nine_eq basisE basisF centralizer_E centralizer_F
  automizer_A automizer_A')
open CFSG.GH74.M12.Hyp (G12)

theorem inspectSig148_M12 :
    InspectSig148 NativeSporadic.M12 (fun K => K = ⊤) := by
  intro D K hD hexp hDK hperf hK1 hKle
  have hcommD := comm_of_card_nine D hD
  obtain ⟨F, hF, -, hFK⟩ := sSup_cores_eq D K hcommD hDK hKle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDp : IsPGroup 3 D := IsPGroup.of_card (n := 2) (by rw [hD]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card Res423Two.card_P0_eq hDp
  let c : G12 ≃* G12 := MulAut.conj g⁻¹
  have hB0P : D.map c.toMonoidHom ≤ P0 := Item434AltPerm.map_conj_inv_le hg
  have hB09 : Nat.card (D.map c.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective c.injective, hD]
  have hmem : D.map c.toMonoidHom ∈ {B : Subgroup G12 | B ≤ P0 ∧ Nat.card B = 9} := ⟨hB0P, hB09⟩
  rw [nine_eq] at hmem
  have hElem : CFSG.Assembly.IsElemAbelian 3 D := by
    refine ⟨?_, hexp⟩
    rw [isMulCommutative_iff]
    intro a b
    exact Subtype.ext (hcommD a.1 a.2 b.1 b.2)
  have hcase1 : (∀ v ∈ D.map c.toMonoidHom, v ≠ 1 → Nat.card (centralizer ({v} : Set G12)) = 54) →
      (∀ t : G12, (∀ b ∈ D.map c.toMonoidHom, t * b = b * t) → t ∈ D.map c.toMonoidHom) →
      K = ⊤ := by
    intro hcent hCB
    exfalso
    apply hK1
    rw [← hFK, eq_bot_iff]
    refine sSup_le fun Z hZ => ?_
    obtain ⟨-, hZ3, hDZ⟩ := hF hZ
    have hZ3' := (isPiSubgroup_piCompl_iff Nat.prime_three Z).mp hZ3
    have hcentD : ∀ v ∈ D, v ≠ 1 → Nat.card (centralizer ({v} : Set G12)) = 54 := by
      intro v hv hv1
      have h1 : c v ∈ D.map c.toMonoidHom := ⟨v, hv, rfl⟩
      have h2 : c v ≠ 1 := fun h => hv1 (c.injective (by rw [h, map_one]))
      rw [← card_centralizer_singleton_mulEquiv c v]
      exact hcent _ h1 h2
    have hCBD : ∀ t : G12, (∀ b ∈ D, t * b = b * t) → t ∈ D := by
      intro t ht
      have h1 : c t ∈ D.map c.toMonoidHom := by
        refine hCB (c t) fun b' hb' => ?_
        obtain ⟨b, hb, rfl⟩ := hb'
        change c t * c b = c b * c t
        rw [← map_mul, ← map_mul, ht b hb]
      obtain ⟨t', ht', htt'⟩ := h1
      have : t' = t := c.injective htt'
      exact this ▸ ht'
    have := Item434SporGen.eq_bot_of_le_normalizer_of_cent hElem hD hZ3' hDZ hcentD hCBD
    rw [this]
  rcases hmem with h | h | h | h
  · refine hcase1 ?_ ?_
    · intro v hv hv1
      rw [h] at hv
      exact Item434SporGen.card_centralizer_E hv hv1
    · intro t ht
      rw [h] at ht ⊢
      have hC : Nat.card (centralizer ((CFSG.RankThree.PartTwo.Toolkit.M12.E : Subgroup G12) :
          Set G12)) = 9 := by
        rw [centralizer_E]; exact basisE.card
      exact Item434SporGen.mem_of_commute_of_card basisE.card hC
        (fun a ha b hb => comm_of_card_nine _ basisE.card a ha b hb) t ht
  · refine hcase1 ?_ ?_
    · intro v hv hv1
      rw [h] at hv
      exact Item434SporGen.card_centralizer_F hv hv1
    · intro t ht
      rw [h] at ht ⊢
      have hC : Nat.card (centralizer ((CFSG.RankThree.PartTwo.Toolkit.M12.F : Subgroup G12) :
          Set G12)) = 9 := by
        rw [centralizer_F]; exact basisF.card
      exact Item434SporGen.mem_of_commute_of_card basisF.card hC
        (fun a ha b hb => comm_of_card_nine _ basisF.card a ha b hb) t ht
  · have e0 : Nonempty (autIn ⊤ (D.map c.toMonoidHom) ≃* Equiv.Perm (Fin 3)) := by
      rw [h]
      obtain ⟨e⟩ := automizer_A
      exact ⟨(Sporadic.automizerEquivAutIn _).symm.trans e⟩
    obtain ⟨e0⟩ := e0
    exact KFacts.ks1515M12Cover G12 ⟨MulEquiv.refl _⟩ D K hElem hD
      ⟨(Sporadic.autInTopCongr c D).trans e0⟩ hperf hK1 hDK
  · have e0 : Nonempty (autIn ⊤ (D.map c.toMonoidHom) ≃* Equiv.Perm (Fin 3)) := by
      rw [h]
      obtain ⟨e⟩ := automizer_A'
      exact ⟨(Sporadic.automizerEquivAutIn _).symm.trans e⟩
    obtain ⟨e0⟩ := e0
    exact KFacts.ks1515M12Cover G12 ⟨MulEquiv.refl _⟩ D K hElem hD
      ⟨(Sporadic.autInTopCongr c D).trans e0⟩ hperf hK1 hDK

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig
