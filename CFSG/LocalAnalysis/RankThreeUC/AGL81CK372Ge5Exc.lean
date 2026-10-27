module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CK372Ge5Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Small
public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescSzFix
public import CFSG.LieType.SeitzGeneration.QuasiHigh
import CFSG.RankThree.PartOne.HNB.InnerAction

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)
open CFSG.LocalAnalysis.RankThreeUC.S15.K37 (isPGroup_autIm le_centralizer_of_autIm_eq_bot)

variable {X : Type} [Group X] [Finite X] {p : ℕ} {K E S : Subgroup X}

namespace K372Setting

theorem center_eq_bot_of_not_coverIndex
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h : K372Setting X p K E S) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) (hci : ¬ QuasiHigh.CoverIndex p d.1) :
    Subgroup.center ↥K = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  rcases h.isPGroup_center.card_eq_or_dvd with h1 | hp
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd (QuasiHigh.coverIndex_of_dvd_card_center hGA h.prime hp2
      ⟨Group.isPerfect_def.mp h.quasi.1, h.quasi.2.1⟩ d e hpd hp) hci

theorem le_centralizer_sz32
    (hSz : CFSG.AGLEmbedding.KFactCaseTwoNoTwoSz32) (h : K372Setting X p K E S) (hp5 : p = 5)
    (hZ : Subgroup.center ↥K = ⊥) (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .suzuki 2)
    (e : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) : S ≤ Subgroup.centralizer (K : Set X) := by
  subst hp5
  obtain ⟨x, hv⟩ := d
  simp only at hd
  subst hd
  have hcyc := CFSG.LocalAnalysis.GLTheoremA.HDesc.suzuki_outer_cyclic
    (CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 ⟨hv, ⟨e⟩⟩)
  have : CFSG.IsElementaryAbelian 5 (autIm E K) := h.isElemAbelian_autIm.isElementaryAbelian
  obtain ⟨g, hg1, hgE⟩ := CFSG.RankThree.PartOne.SEITZ2.exists_conj_mem_of_plane_of_cyclic_outer
    (by norm_num) hcyc (autIm E K) h.card_autIm
  have hgΓ : (g : X) ∈ rankThreeGamma 1 5 E := h.mem_gamma_of_conj_mem_autIm hZ hgE hg1 g.2 rfl
  exact le_centralizer_of_autIm_eq_bot h.S_le_normalizer_K
    (hSz 5 ↥K ⟨rfl, ⟨_, hv⟩, rfl, ⟨e⟩⟩ g (h.orderOf_of_conj_mem_autIm hZ hgE hg1) (autIm S K)
      (isPGroup_autIm h.two) (h.conj_mem_normalizer_autIm g.2 hgΓ))

end K372Setting

section Tits


namespace K372Setting

theorem le_centralizer_tits (h : K372Setting X p K E S) (hp5 : p = 5)
    (hZ : Subgroup.center ↥K = ⊥) {hv : TauCeti.LieTypeIndex.tits.Valid}
    (e : ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  classical
  subst hp5
  have hmodel := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := ↥K) ⟨hv, ⟨e⟩⟩
  have hout := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier ↥K 2 1 hmodel).1
  have hin : autIm E K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    have hbot := disjoint_self.mp (IsPGroup.disjoint_of_ne 5 2 (by norm_num) _ _
      ((IsPGroup.of_card h.card_autIm).map
        (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)))
      (hout.to_subgroup _))
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  have hinj := CFSG.RankThree.PartOne.HNB.conj_injective_of_center_eq_bot hZ
  set F : Subgroup ↥K := (autIm E K).comap (MulAut.conj : ↥K →* MulAut ↥K) with hF
  have hF25 : Nat.card F = 5 ^ 2 := by
    rw [← h.card_autIm, ← Subgroup.map_comap_eq_self hin, Subgroup.card_map_of_injective hinj]
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut.exists_sylow_eq ⟨hv, ⟨e⟩⟩ F hF25
  obtain ⟨⟨z, hzF⟩, hz1⟩ : ∃ z : ↥F, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card F = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by
      rw [hcon a, hcon b]⟩, ⟨1⟩⟩
    rw [hF25] at h1
    norm_num at h1
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hFΓ : ∀ g ∈ F, (g : X) ∈ rankThreeGamma 1 5 E := by
    intro g hg
    have hc : MulAut.conj (g * z) = MulAut.conj (z * g) := by
      rw [map_mul, map_mul]
      exact CFSG.Open.IsElemAbelian.comm h.isElemAbelian_autIm hg hzF
    exact h.mem_gamma_of_conj_mem_autIm hZ hzF hz1' g.2 (congrArg Subtype.val (hinj hc))
  exact le_centralizer_of_autIm_eq_bot h.S_le_normalizer_K
    (CFSG.LocalAnalysis.UniquenessCase.UCK.twoSigTriv_tits_five ⟨_, hv⟩ rfl e P (autIm S K)
      (isPGroup_autIm h.two) fun g hg => h.conj_mem_normalizer_autIm g.2 (hFΓ g (hP ▸ hg)))

theorem le_centralizer_of_exc
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSz : CFSG.AGLEmbedding.KFactCaseTwoNoTwoSz32) (h : K372Setting X p K E S)
    (d : TauCeti.ValidLieTypeIndex)
    (hd : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hexc : CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨e⟩ := hd
  have h5 := h.five_le
  rcases hexc with ⟨h3, -⟩ | ⟨hp5, hdt | hds⟩
  · omega
  · have hZ := h.center_eq_bot_of_not_coverIndex hGA d e
      (by rw [hdt, TauCeti.LieTypeIndex.characteristic_tits]; omega) (by rw [hdt]; exact id)
    obtain ⟨dd, hv⟩ := d
    simp only at hdt
    subst hdt
    exact h.le_centralizer_tits hp5 hZ ((InputsSeitz3.equivCenterQuot hZ).trans e)
  · have hZ := h.center_eq_bot_of_not_coverIndex hGA d e
      (by rw [hds, TauCeti.LieTypeIndex.characteristic_suzuki]; omega) (by rw [hds]; exact id)
    exact h.le_centralizer_sz32 hSz hp5 hZ d hds ((InputsSeitz3.equivCenterQuot hZ).trans e)

end K372Setting

end Tits

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5
