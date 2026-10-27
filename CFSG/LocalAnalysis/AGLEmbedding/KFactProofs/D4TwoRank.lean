module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoSylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarResidualReduce
public import CFSG.Quasithin.Recognition.CertD4Bridge
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
import CFSG.Adapters.TauCetiExceptional.EvenB1

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding.D4Two

theorem rank_le_of_sylow {G : Type*} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    (S : Subgroup G) (hS : Nat.card S = p ^ (Nat.card G).factorization p)
    (h : ∀ E : Subgroup G, E ≤ S → IsElemAbelian p E → Nat.card E ≤ p ^ k)
    (E : Subgroup G) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ k := by
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard S hS)
  have hQ : ((g • Q : Sylow p G) : Subgroup G) =
      (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ S := by
    have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hEQ
    rw [← hQ, hg] at this
    exact this
  have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have := h _ hle (isElemAbelian_of_equiv_le hE le_rfl (Subgroup.equivMapOfInjective E _ hf).symm)
  rwa [Subgroup.card_map_of_injective hf] at this

theorem rank_trialityGroup8
    (hG : Nat.card trialityGroup8 = 211341312) :
    ∀ E : Subgroup ↥trialityGroup8, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hle, hcard, hrank⟩ := sylowGroup_facts
  have hv : (Nat.card trialityGroup8).factorization 3 = 4 := by
    rw [hG]
    have h : (211341312 : ℕ) = 3 ^ 4 * 2609152 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  refine fun E hE => rank_le_of_sylow (sylowGroup.subgroupOf trialityGroup8) ?_ ?_ E hE
  · rw [hv, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  · intro E' hE' hEA
    have hinj : Function.Injective trialityGroup8.subtype := Subgroup.subtype_injective _
    have hmap : E'.map trialityGroup8.subtype ≤ sylowGroup := Subgroup.map_le_iff_le_comap.mpr hE'
    have := hrank (E'.map trialityGroup8.subtype) hmap
      (isElemAbelian_of_equiv_le hEA le_rfl (Subgroup.equivMapOfInjective E' _ hinj).symm)
    rwa [Subgroup.card_map_of_injective hinj] at this

theorem d4TwoRankTwo
    : D4TwoRankTwo := by
  intro L _ _ d q hq hq1 hdq ⟨e⟩ E hE
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.trialityD4 q := hdq
  have hcard := card_catGroup_trialityD4_even (d := ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) hq rfl
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel
      (CatGroup ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide)
        (MulEquiv.refl _)⟩
  rw [hq, hq1] at hm
  rw [hq1] at hcard
  have hL : CFSG.Blueprint.LieModel (CatGroup ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩)
      .trialityD4 0 2 1 := CFSG.RankThree.PartOne.Sec66T.lieModel_trialityD4_iff.mpr ⟨rfl, hm⟩
  obtain ⟨e2⟩ := trialityD4ModelBridge_of_lieModel _ hL
  have hk8 : Nat.card GF8 = 8 := by rw [Nat.card_eq_fintype_card]; rfl
  obtain ⟨e3⟩ := d4bG8_equiv_quasithin GF8 hk8
  let φ : L ≃* ↥trialityGroup8 := e.trans (e2.trans e3.symm)
  have hLG : Nat.card trialityGroup8 = 211341312 := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr e.toEquiv, hcard]
    norm_num [ordTrialityD4]
  have h := rank_trialityGroup8 hLG (E.map φ.toMonoidHom)
    (isElemAbelian_of_equiv_le hE le_rfl (Subgroup.equivMapOfInjective E _ φ.injective).symm)
  rwa [Subgroup.card_map_of_injective φ.injective] at h

end CFSG.AGLEmbedding
