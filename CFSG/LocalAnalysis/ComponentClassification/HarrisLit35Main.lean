module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219D
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar
public import CFSG.Dihedral.GorensteinWalter
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup

variable {G : Type} [Group G]

theorem centralizer_eq_inf [Finite G] {W : Subgroup G} (hW2 : ∀ a ∈ W, a * a = 1)
    (hW4 : Nat.card W = 4) {w v : G} (hw : w ∈ W) (hw1 : w ≠ 1) (hv : v ∈ W)
    (hvw : v ∉ zpowers w) :
    orderOf w = 2 ∧ orderOf v = 2 ∧ v ∈ centralizer {w} ∧
      centralizer (W : Set G) = centralizer {w} ⊓ centralizer {v} := by
  have hww := hW2 w hw
  have hvv := hW2 v hv
  have hv1 : v ≠ 1 := fun h => hvw (h ▸ one_mem _)
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq, hww]) hw1
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq, hvv]) hv1
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hc : w * v = v * w := by
    have h1 := hW2 (w * v) (mul_mem hw hv)
    have h2 : w * v = (w * v)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [h2, mul_inv_rev, hwinv, hvinv]
  have hne : v ≠ w := fun h => hvw (h ▸ mem_zpowers w)
  have hwv1 : w * v ≠ 1 := fun h => hvw (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_mem (mem_zpowers w))
  have hwvw : w * v ≠ w := fun h => hv1 (mul_eq_left.mp h)
  have hwvv : w * v ≠ v := fun h => hw1 (mul_eq_right.mp h)
  have hmem : ∀ a ∈ W, a = 1 ∨ a = w ∨ a = v ∨ a = w * v := by
    classical
    intro a ha
    by_contra hna
    simp only [not_or] at hna
    obtain ⟨ha1, haw, hav, hawv⟩ := hna
    have hS : (insert a {1, w, v, w * v} : Finset G).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [ha1, haw, hav, hawv]),
        Finset.card_insert_of_notMem (by simp [hw1.symm, hv1.symm, hwv1.symm]),
        Finset.card_insert_of_notMem (by simp [hne.symm, hwvw.symm]),
        Finset.card_pair hwvv.symm]
    have hsub : ((insert a {1, w, v, w * v} : Finset G) : Set G) ⊆ (W : Set G) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ha
      · exact one_mem W
      · exact hw
      · exact hv
      · exact mul_mem hw hv
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hS, ← Nat.card_coe_set_eq] at hle
    have : Nat.card ↥(W : Set G) = 4 := hW4
    omega
  refine ⟨hw2, hv2, mem_centralizer_singleton_iff.mpr hc.symm, ?_⟩
  apply le_antisymm
  · exact le_inf (centralizer_le (Set.singleton_subset_iff.mpr hw))
      (centralizer_le (Set.singleton_subset_iff.mpr hv))
  · rintro x ⟨hxw, hxv⟩
    rw [mem_centralizer_iff]
    intro a ha
    have hxw' : x * w = w * x := mem_centralizer_singleton_iff.mp hxw
    have hxv' : x * v = v * x := mem_centralizer_singleton_iff.mp hxv
    rcases hmem a ha with rfl | rfl | rfl | rfl
    · group
    · exact hxw'.symm
    · exact hxv'.symm
    · rw [mul_assoc, ← hxv', ← mul_assoc, ← hxw', mul_assoc]

omit [Group G] in
theorem twoLayer_eq_pLayer [Group G] [Finite G] : twoLayer G = pLayer G 2 := by
  unfold twoLayer pLayer
  congr 1
  ext J
  exact isTwoComponent_iff_isPComponent J

theorem map_conj_eq_of_le_centralizer {H : Subgroup G} {v : G} (hH : H ≤ centralizer {v}) :
    H.map (MulAut.conj v).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : y * v = v * y := mem_centralizer_singleton_iff.mp (hH hy)
    have h2 : v * y * v⁻¹ = y := by rw [← h1]; group
    change v * y * v⁻¹ ∈ H
    rw [h2]
    exact hy
  · intro hx
    have h1 : x * v = v * x := mem_centralizer_singleton_iff.mp (hH hx)
    refine ⟨x, hx, ?_⟩
    change v * x * v⁻¹ = x
    rw [← h1]
    group

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      rwa [inv_inv] at h1
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem le_normalizer_layerIn [Finite G] (C : Subgroup G) :
    C ≤ normalizer (GSThmB.layerIn C : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pLayer ↥C 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  have hn : (pLayer ↥C 2).Normal := inferInstance
  intro c hc
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, hn.conj_mem y hy _, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨c, hc⟩⁻¹ * y * ⟨c, hc⟩, ?_, ?_⟩
    · have h1 := hn.conj_mem y hy (⟨c, hc⟩⁻¹)
      rwa [inv_inv] at h1
    · change c⁻¹ * (y : G) * c = x
      have hyx' : (y : G) = c * x * c⁻¹ := hyx
      rw [hyx']
      group

theorem conjClosure_eq_commutator [Finite G] {w v : G} (hv2 : orderOf v = 2)
    (hvM : v ∈ centralizer {w}) {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {w} ⊓ centralizer {v})) :
    GSThmB.conjClosure L (GSThmB.layerIn (centralizer {w})) =
      ⁅L, GSThmB.layerIn (centralizer {w})⁆ := by
  set M := centralizer ({w} : Set G) with hMdef
  set v' : ↥M := ⟨v, hvM⟩
  have hv' : orderOf v' = 2 := by rw [Subgroup.orderOf_mk]; exact hv2
  have hLM : L ≤ M := hL.1.trans inf_le_left
  set L' : Subgroup ↥M := L.subgroupOf M
  have hCv : centralizer ({v'} : Set ↥M) =
      (centralizer {w} ⊓ centralizer {v} : Subgroup G).subgroupOf M := by
    ext x
    rw [mem_subgroupOf, mem_inf]
    constructor
    · intro h
      have h' : x * v' = v' * x := mem_centralizer_singleton_iff.mp h
      exact ⟨x.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h')⟩
    · rintro ⟨-, h⟩
      exact mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp h))
  have hL' : IsTwoComponentIn L' (centralizer ({v'} : Set ↥M)) := by
    rw [hCv]
    have hle : L' ≤ (centralizer {w} ⊓ centralizer {v} : Subgroup G).subgroupOf M :=
      fun x hx => hL.1 hx
    rw [isTwoComponentIn_iff hle, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left : centralizer {w} ⊓ centralizer {v} ≤ M) 2 Nat.prime_two]
    exact (isTwoComponentIn_iff hL.1).mp hL
  obtain ⟨K₀, -, -, -, hcomm, hsup⟩ := (harris82Lemma219Input_holds ↥M v' hv').2 L' hL'
  have hE : GSThmB.layerIn M = (twoLayer ↥M).map M.subtype := by
    rw [twoLayer_eq_pLayer]
    rfl
  have hLmap : L'.map M.subtype = L := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hLM]
  have hconj : ∀ g : ↥M, (L'.map (MulAut.conj g).toMonoidHom).map M.subtype =
      L.map (MulAut.conj (g : G)).toMonoidHom := fun g => Cor441.map_map_conj_subgroupOf hLM g
  have hiSup : (⨆ g : ↥(twoLayer ↥M), L'.map (MulAut.conj (g : ↥M)).toMonoidHom).map M.subtype =
      GSThmB.conjClosure L (GSThmB.layerIn M) := by
    rw [Subgroup.map_iSup]
    unfold GSThmB.conjClosure
    rw [hE]
    apply le_antisymm
    · refine iSup_le fun g => ?_
      refine le_iSup₂_of_le ((g : ↥M) : G)⁻¹ ⟨(g : ↥M)⁻¹, inv_mem g.2, rfl⟩ ?_
      rw [hconj]
      unfold conjugate
      rw [inv_inv]
    · refine iSup₂_le fun y hy => ?_
      obtain ⟨g, hg, rfl⟩ := hy
      refine le_iSup_of_le ⟨g⁻¹, inv_mem hg⟩ ?_
      rw [hconj]
      unfold conjugate
      rfl
  have hcm : (⁅L', twoLayer ↥M⁆ : Subgroup ↥M).map M.subtype = ⁅L, GSThmB.layerIn M⁆ := by
    rw [Subgroup.map_commutator, hLmap, ← hE]
  rw [← hiSup, hsup, ← hcomm, hcm]

theorem map_conj_commutator_eq [Finite G] {w v : G} (hvM : v ∈ centralizer {w}) {L : Subgroup G}
    (hLv : L ≤ centralizer {v}) :
    (⁅L, GSThmB.layerIn (centralizer {w})⁆ : Subgroup G).map (MulAut.conj v).toMonoidHom =
      ⁅L, GSThmB.layerIn (centralizer {w})⁆ := by
  rw [Subgroup.map_commutator, map_conj_eq_of_le_centralizer hLv,
    map_conj_eq_of_mem_normalizer (le_normalizer_layerIn _ hvM)]

theorem statement_holds (hT1 : Harris82Theorem1Input) (hT3 : Harris82Theorem3Input)
    (hID : Harris81Lemma35IdentFact) : Harris81Lemma35Step := by
  intro G _ _ _ hnonab hK hcat p hp hp2 W hW2 hW4 L hL hM k hk hs5 hLsl hLW w hw hw1 v hv hvw K
    hKdef
  obtain ⟨hwL, hwW⟩ := mem_inf.mp hw
  obtain ⟨hw2, hv2, hvM, hCW⟩ := centralizer_eq_inf hW2 hW4 hwW hw1 hv hvw
  have hL' : IsTwoComponentIn L (centralizer {w} ⊓ centralizer {v}) := by
    rw [← hCW]
    exact hL
  have hLv : L ≤ centralizer {v} := hL'.1.trans inf_le_right
  have hFtop := StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnonab
  have eF : ↥(Open.genFittingFStar G) ≃* G :=
    (MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv
  have hFs : IsSimpleGroup ↥(Open.genFittingFStar G) := eF.isSimpleGroup
  have hnch : ¬ IsSimpleChevalleyOver p ↥(Open.genFittingFStar G) := by
    rintro ⟨τ, n, f', hm⟩
    exact hcat (Blueprint.lieModel_catalog G τ n p f' (GSThmB.OddQuot.lieModel_of_equiv eF hm))
  have hKcomm : K = ⁅L, GSThmB.layerIn (centralizer {w})⁆ := by
    rw [hKdef]
    exact conjClosure_eq_commutator hv2 hvM hL'
  have hKv : K.map (MulAut.conj v).toMonoidHom = K := by
    rw [hKcomm]
    exact map_conj_commutator_eq hvM hLv
  have hKc : IsTwoComponentIn K (centralizer {w}) := by
    rcases hT3 G hFs W hW2 hW4 L p hp hp2 hL hM hLW w hw hw1 with h | h
    · rw [hKdef]
      exact h
    · exact absurd h hnch
  have hLK : L ≤ K := by
    rw [hKdef]
    exact GSThmB.B5a.le_conjClosure L _
  have hwK : w ∈ K := hLK hwL
  have hKM : ¬ IsMTypeSchur p ↥K := not_isMTypeSchur_of_theorem1 hT1 hnonab hcat hw2 hKc hwK hp hp2
  obtain ⟨hLeq, hcases⟩ := hID G hnonab hK hcat p hp hp2 w v hw2 (hW2 v hv) hvw hvM L hL' hM k hk
    hs5 hLsl hwL K hKdef hLK hKc hwK hKM hKv
  exact ⟨hwK, hKcomm, hKc, hKv, hLeq, hcases⟩

end CFSG.ComponentClassification.HarrisLit.L35
