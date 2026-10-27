module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FusW
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46Z
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FieldSq

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem l34Lemma46TwoStep_of_facts
    (hRank : L34CenterRankFact) (hSqC : L34SquareCenterFact) (hWit : L34OuterWitnessFact)
    (hConn : L34EightsConnectedFact) (hU : L34UnbalancingUnitaryStep)
    (hC : L34UnitaryCentralizerFact) : L34Lemma46TwoStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS hSyl hZS b
    hbS hba hbne hab hbcent hbn
  obtain ⟨hbase, hU3, hL34, -, hS, haS, -⟩ := id hset
  have : IsSimpleGroup G := hbase.1
  have hJ : ⁅J, J⁆ = J := GSThmB.commutator_eq_self_of_isPComponent hU3.2.2.2.1 hU3.2.2.2.2.1
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hS
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have ha2 : orderOf a = 2 := hU3.1
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  obtain ⟨k, hk⟩ := hba
  have hbb : b * b = 1 := by
    rw [hk, show k⁻¹ * a * k * (k⁻¹ * a * k) = k⁻¹ * (a * a) * k by group, haa]
    group
  have hb1 : b ≠ 1 := fun h => ha1 (by
    rw [show a = k * (k⁻¹ * a * k) * k⁻¹ by group, ← hk, h]
    group)
  have haZ : a ∈ S ⊓ zStarIn J := mem_inf.mpr ⟨haS, hZS a haS ⟨1, by group⟩⟩
  have hbZ : b ∈ S ⊓ zStarIn J := mem_inf.mpr ⟨hbS, hZS b hbS ⟨k, hk⟩⟩
  have h4 : Nat.card ↥(omegaOne (S ⊓ zStarIn J)) ≤ 4 := by
    have h := hRank G J (S ⊓ J) hJ hL34 hP
    rwa [inf_assoc, inf_of_le_right (show zStarIn J ≤ J from map_subtype_le _)] at h
  obtain ⟨c, hc⟩ : ∃ c : G, c = a * b := ⟨_, rfl⟩
  have hab' : a * b = b * a := hbcent a haS
  have hcS : c ∈ S := by rw [hc]; exact mul_mem haS hbS
  have hcZ : c ∈ S ⊓ zStarIn J := by rw [hc]; exact mul_mem haZ hbZ
  have hcc : c * c = 1 := by
    rw [hc]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * a * (b * b) := by rw [← hab']; group
      _ = 1 := by rw [haa, hbb, one_mul]
  have hc1 : c ≠ 1 := fun h => hbne (by
    rw [hc] at h
    calc b = a⁻¹ * (a * b) := by group
      _ = a := by rw [h, mul_one, inv_eq_of_mul_eq_one_right haa])
  have hSc : ∀ s ∈ S, s * c = c * s := fun s hs => by
    rw [hc]
    calc s * (a * b) = s * a * b := by group
      _ = a * s * b := by rw [hcent s hs]
      _ = a * (s * b) := by group
      _ = a * (b * s) := by rw [hbcent s hs]
      _ = a * b * s := by group
  have hca : ∀ g : G, c ≠ g⁻¹ * a * g := fun g h => by
    rcases hab c hcS ⟨g, h⟩ with h' | h'
    · rw [hc] at h'
      exact hb1 (mul_eq_left.mp h')
    · rw [hc] at h'
      exact ha1 (mul_eq_right.mp h')
  have hZc : ∀ v ∈ S ⊓ zStarIn J, v * v = 1 → ∀ s ∈ S, s * v = v * s := by
    intro v hv hvv s hs
    by_cases hv1 : v = 1
    · rw [hv1, mul_one, one_mul]
    by_cases hva : v = a
    · rw [hva]; exact hcent s hs
    by_cases hvb : v = b
    · rw [hvb]; exact hbcent s hs
    rw [GrS4.eq_mul_of_card_omegaOne_le_four h4 haZ hbZ hv haa hbb hvv ha1 hb1 hv1
      (Ne.symm hbne) (Ne.symm hva) (Ne.symm hvb), ← hc]
    exact hSc s hs
  obtain ⟨⟨f, hfZ, hff, -, -, hWF⟩, -⟩ := GrS4.wGroup_facts_of_setting hRank hSqC hWit hConn hU hC
    hset hcent haZ hexp hnc hWx hNJ
  have hWS : ∀ F : Subgroup G, F ≤ S → IsAbelianTwoOfRank 3 F → wGroup F = W := by
    intro F hFS hF
    refine hWF F hFS hF fun y hy v hv => ?_
    have hle : zpowers a ⊔ zpowers f ≤ centralizer ({y} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcent y (hFS hy)).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hZc f hfZ hff y (hFS hy)).symm))
    exact mem_centralizer_singleton_iff.mp (hle hv)
  have hSsyl : IsSylowTwoIn S (centralizer ({c} : Set G)) :=
    GrS4.isSylowTwoIn_of_le_of_sylow hSyl fun s hs => mem_centralizer_singleton_iff.mpr (hSc s hs)
  have hV : IsElemTwo (zpowers a ⊔ zpowers b) ∧ Nat.card ↥(zpowers a ⊔ zpowers b) = 2 * 2 := by
    obtain ⟨hV, hVc⟩ := GrS4.isElemTwo_sup_zpowers (isElemTwo_zpowers haa) hbb
      (fun h => (GrS4.eq_one_or_eq_of_mem_zpowers haa h).elim hb1 hbne) fun e he => by
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
        exact Commute.zpow_left hab' n
    refine ⟨hV, by rw [hVc, Nat.card_zpowers, ha2]⟩
  have hiso : ∀ g : G, g⁻¹ * c * g ∈ S → g⁻¹ * c * g = c := by
    intro g hgS
    obtain ⟨d, hd⟩ : ∃ d : G, d = g⁻¹ * c * g := ⟨_, rfl⟩
    rw [← hd] at hgS ⊢
    have hcd : c = g * d * g⁻¹ := by rw [hd]; group
    have hdd : d * d = 1 := by
      rw [hd, show g⁻¹ * c * g * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g by group, hcc]
      group
    have hd1 : d ≠ 1 := fun h => hc1 (by rw [hcd, h]; group)
    have hda : d ≠ a := fun h => hca g⁻¹ (by rw [hcd, h]; group)
    have hdb : d ≠ b := fun h => hca (k * g⁻¹) (by rw [hcd, h, hk]; group)
    have hdZ : d ∈ zStarIn J := by
      by_contra hdZ
      have hdV : d ∉ zpowers a ⊔ zpowers b := fun h =>
        hdZ (mem_inf.mp ((sup_le (zpowers_le.mpr haZ) (zpowers_le.mpr hbZ)) h)).2
      obtain ⟨hFe, hFc⟩ := GrS4.isElemTwo_sup_zpowers hV.1 hdd hdV fun v hv => by
        have hle : zpowers a ⊔ zpowers b ≤ centralizer ({d} : Set G) := sup_le
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcent d hgS).symm))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hbcent d hgS).symm))
        exact mem_centralizer_singleton_iff.mp (hle hv)
      have hF8 : IsEightGroup (zpowers a ⊔ zpowers b ⊔ zpowers d) := ⟨hFe, by rw [hFc, hV.2]⟩
      have hFd : zpowers a ⊔ zpowers b ⊔ zpowers d ≤ S ⊓ centralizer ({d} : Set G) := by
        refine le_inf (sup_le (sup_le (zpowers_le.mpr haS) (zpowers_le.mpr hbS))
          (zpowers_le.mpr hgS)) fun y hy => mem_centralizer_singleton_iff.mpr ?_
        exact hFe.1 y hy d (mem_sup_right (mem_zpowers d))
      obtain ⟨h, hh, hhS⟩ := GrS4.exists_conj_eq_of_isSylowTwoIn hSsyl hS2 hd
      have hFh : (zpowers a ⊔ zpowers b ⊔ zpowers d).map (MulAut.conj h⁻¹).toMonoidHom ≤ S := by
        rintro _ ⟨y, hy, rfl⟩
        have h1 := hhS y (hFd hy)
        simpa [MulAut.conj_apply] using h1
      have hW1 := hWS _ (hFd.trans inf_le_left) (GrS4.isAbelianTwoOfRank_of_eight hF8)
      have hW2 := hWS _ hFh (GrS4.isAbelianTwoOfRank_of_eight ⟨hF8.1.map_conj h⁻¹,
        by rw [card_map_of_injective (MulAut.conj h⁻¹).injective, hF8.2]⟩)
      have hhM := GrS4.mem_normalizer_of_wGroup_eq hW1 hW2
      have hdc : d = (h⁻¹)⁻¹ * c * h⁻¹ := by rw [inv_inv, ← hh]; group
      apply hdZ
      rw [hdc]
      refine hMO c hcZ hcc h⁻¹ (inv_mem hhM) ?_
      rw [← hdc]
      exact hgS
    rw [hc]
    exact GrS4.eq_mul_of_card_omegaOne_le_four h4 haZ hbZ (mem_inf.mpr ⟨hgS, hdZ⟩) haa hbb hdd
      ha1 hb1 hd1 (Ne.symm hbne) (Ne.symm hda) (Ne.symm hdb)
  obtain ⟨P, rfl⟩ := hSyl
  exact GrS4.false_of_isolated_two_central hbase.2.1 P hcS hSc
    (orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1) hiso

theorem l34Lemma46ClosedStep_of_facts
    (hRank : L34CenterRankFact) (hSqC : L34SquareCenterFact) (hWit : L34OuterWitnessFact)
    (hOut : L34OutSquareFact) (hConn : L34EightsConnectedFact) (hU : L34UnbalancingUnitaryStep)
    (hC : L34UnitaryCentralizerFact) (hMax : MaximalTwoComponentInput) :
    L34Lemma46ClosedStep :=
  l34Lemma46ClosedStep_of_inputs
      (l34Lemma46ZStep_of_inputs (l34Lemma46FusionStep_of_facts hRank hSqC hWit hConn hU hC)
          (l34Lemma46FieldSquareStep_of_inputs hRank hSqC hWit)
          (l34Lemma46SquareRankStep_of_inputs hOut hSqC) hMax)
      (l34Lemma46StrongStep_of_two hRank (l34Lemma46TwoStep_of_facts hRank hSqC hWit hConn hU hC))

end CFSG.ComponentClassification.GrSLit
