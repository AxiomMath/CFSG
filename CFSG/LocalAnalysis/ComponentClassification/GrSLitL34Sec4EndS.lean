module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Tools46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {X : Type} [Group X] [Finite X]

theorem mem_coreActionKernel_of_mem_center (hCF2 : L34SylowCentralizerFact) {J S : Subgroup X}
    (hJ : ⁅J, J⁆ = J) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hS : IsSylowTwoIn S (normalizer (J : Set X)))
    (hZP : ∀ u ∈ S ⊓ J, (∀ p ∈ S ⊓ J, u * p = p * u) → u ∈ zStarIn J)
    {s : X} (hsS : s ∈ S) (hsZ : ∀ t ∈ S, s * t = t * s) : s ∈ coreActionKernel J := by
  have hP : IsSylowTwoIn (S ⊓ J) J := isSylowTwoIn_inf hS
  have hsN : s ∈ normalizer (J : Set X) := hS.1 hsS
  have hsP : ∀ p ∈ S ⊓ J, s * p = p * s := fun p hp => hsZ p (mem_inf.mp hp).1
  obtain ⟨u, huP, hvK, -⟩ := hCF2 X J (S ⊓ J) s hJ hL34 hP hsN hsP
  have huS : u ∈ S := (mem_inf.mp huP).1
  have hvS : u⁻¹ * s ∈ S := mul_mem (inv_mem huS) hsS
  have hvP : ∀ p ∈ S ⊓ J, (u⁻¹ * s) * p = p * (u⁻¹ * s) := by
    intro p hp
    have hpS : p ∈ S := (mem_inf.mp hp).1
    have h1 : p⁻¹ * (u⁻¹ * s)⁻¹ * p * (u⁻¹ * s) ∈ oddIn J :=
      (mem_coreActionKernel.mp hvK).2 p (mem_inf.mp hp).2
    have h2 : p⁻¹ * (u⁻¹ * s)⁻¹ * p * (u⁻¹ * s) ∈ S :=
      mul_mem (mul_mem (mul_mem (inv_mem hpS) (inv_mem hvS)) hpS) hvS
    have h3 := eq_bot_of_le_two_group_of_le_odd (isPGroup_of_isSylowTwoIn hS)
      (odd_card_map_pPrimeCore J) (zpowers_le.mpr h2) (zpowers_le.mpr h1)
    have h4 : p⁻¹ * (u⁻¹ * s)⁻¹ * p * (u⁻¹ * s) = 1 := by
      have h5 := mem_zpowers (p⁻¹ * (u⁻¹ * s)⁻¹ * p * (u⁻¹ * s))
      rwa [h3, mem_bot] at h5
    calc (u⁻¹ * s) * p = (u⁻¹ * s) * p * (p⁻¹ * (u⁻¹ * s)⁻¹ * p * (u⁻¹ * s)) := by
          rw [h4, mul_one]
      _ = p * (u⁻¹ * s) := by group
  have huc : ∀ p ∈ S ⊓ J, u * p = p * u := by
    intro p hp
    have h1 := hsP p hp
    have h2 := hvP p hp
    have hv' : (u⁻¹ * s)⁻¹ * p = p * (u⁻¹ * s)⁻¹ := by
      calc (u⁻¹ * s)⁻¹ * p = (u⁻¹ * s)⁻¹ * (p * (u⁻¹ * s)) * (u⁻¹ * s)⁻¹ := by group
        _ = (u⁻¹ * s)⁻¹ * ((u⁻¹ * s) * p) * (u⁻¹ * s)⁻¹ := by rw [← h2]
        _ = p * (u⁻¹ * s)⁻¹ := by group
    calc u * p = s * ((u⁻¹ * s)⁻¹ * p) := by group
      _ = s * (p * (u⁻¹ * s)⁻¹) := by rw [hv']
      _ = (s * p) * (u⁻¹ * s)⁻¹ := by group
      _ = (p * s) * (u⁻¹ * s)⁻¹ := by rw [h1]
      _ = p * u := by group
  have huZ : u ∈ zStarIn J := hZP u huP huc
  have hzK : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  rw [hzK] at huZ
  have h := mul_mem (mem_inf.mp huZ).2 hvK
  rwa [mul_inv_cancel_left] at h

theorem eq_of_mul_self_eq_one_of_isCyclic {Q : Subgroup X} (hQc : IsCyclic ↥Q) {u v : X}
    (hu : u ∈ Q) (hv : v ∈ Q) (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u = v := by
  classical
  have : Fintype ↥Q := Fintype.ofFinite _
  have : IsCyclic ↥Q := hQc
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥Q) (n := 2) (by norm_num)
  by_contra hne
  have hsub : ({1, ⟨u, hu⟩, ⟨v, hv⟩} : Finset ↥Q) ⊆
      Finset.univ.filter (fun y : ↥Q => y ^ 2 = 1) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by simp [pow_two, hu2])
    · exact Subtype.ext (by simp [pow_two, hv2])
  have h1 : (1 : ↥Q) ≠ ⟨u, hu⟩ := fun h => hu1 (congrArg Subtype.val h).symm
  have h2 : (1 : ↥Q) ≠ ⟨v, hv⟩ := fun h => hv1 (congrArg Subtype.val h).symm
  have h3 : (⟨u, hu⟩ : ↥Q) ≠ ⟨v, hv⟩ := fun h => hne (congrArg Subtype.val h)
  have hcard : ({1, ⟨u, hu⟩, ⟨v, hv⟩} : Finset ↥Q).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3]
  have := Finset.card_le_card hsub
  omega

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

theorem l34EndTypeStep_of_inputs (hA : L34EndStructureStep) (hB : FourCubeSylowFact) :
    L34EndTypeStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv P hPS
  obtain ⟨L, _, _, T, hT, hcT, hφ, Q, ⟨e⟩⟩ :=
    hA G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv ⟨P, hPS⟩
  have eP : ↥(P : Subgroup G) ≃* ↥S := MulEquiv.subgroupCongr hPS
  rcases hB L T hT hcT hφ Q with ⟨R, ⟨f⟩⟩ | ⟨R, ⟨f⟩⟩
  · exact Or.inl ⟨R, ⟨(eP.trans e).trans f⟩⟩
  · exact Or.inr ⟨R, ⟨(eP.trans e).trans f⟩⟩

theorem l34EndSylowStep_of_inputs
    (hMax : MaximalTwoComponentInput) (hU : L34UnbalancingUnitaryStep)
    (hC : L34UnitaryCentralizerFact) (hCF1c : L34SylowCenterCyclicFact)
    (hCF2 : L34SylowCentralizerFact) (hType : L34EndTypeStep) : L34EndSylowStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, hL34, hmax, hS, haS, hxS⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := hbase
  have ha2 : orderOf a = 2 := hU3.1
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  set P : Subgroup G := S ⊓ J with hPdef
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : P ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [hPdef, inf_assoc, inf_eq_right.mpr hZJ]
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hZ4
    norm_num at hZ4
  have haZ : a ∈ S ⊓ zStarIn J := hZ hZne
  have hxU : IsL34Unitary J x := hU G a x J hU3 hL34
  have hxP : x ∈ normalizer (P : Set G) := inf_mem_normalizer (le_normalizer hxS) (hS.1 hxS)
  obtain ⟨hxinv, -⟩ := hC G J P x hJper hL34 hxU hP hxP
  set Q : Subgroup G := S ⊓ coreActionKernel J with hQdef
  have hzK : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hZQ : S ⊓ zStarIn J ≤ Q := by
    intro z hz
    have hz2 := (mem_inf.mp hz).2
    rw [hzK] at hz2
    exact mem_inf.mpr ⟨(mem_inf.mp hz).1, (mem_inf.mp hz2).2⟩
  have hcen : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s = 1 ∨ s = a := by
    intro s hsS hsZ
    have hsK := mem_coreActionKernel_of_mem_center hCF2 hJper hL34 hS
      (fun u hu huc => hCF1c G J P hJper hL34 hP (by rwa [hZP]) (by rwa [hZP]) u hu huc) hsS hsZ
    have hsQ : s ∈ Q := mem_inf.mpr ⟨hsS, hsK⟩
    have hsx : x⁻¹ * s * x = s := by
      calc x⁻¹ * s * x = x⁻¹ * (s * x) := by group
        _ = x⁻¹ * (x * s) := by rw [hsZ x hxS]
        _ = s := by group
    have hs2 : s * s = 1 := by
      by_contra hs2
      obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp (isPGroup_of_isSylowTwoIn hS) ⟨s, hsS⟩
      rw [Subgroup.orderOf_mk] at hm
      have hm2 : 2 ≤ m := by
        by_contra hlt
        apply hs2
        have hdvd : orderOf s ∣ 2 := by
          rw [hm]
          exact (Nat.pow_dvd_pow 2 (by omega : m ≤ 1)).trans (by norm_num)
        rw [← pow_two]
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      set w : G := s ^ (2 ^ (m - 2)) with hw
      have hwo : orderOf w = 4 := by
        rw [hw, orderOf_pow_of_dvd (by positivity)
          (by rw [hm]; exact Nat.pow_dvd_pow 2 (Nat.sub_le m 2)), hm,
          Nat.pow_div (Nat.sub_le m 2) (by norm_num), show m - (m - 2) = 2 by omega]
      have hw4 : w ^ 4 = 1 := by
        rw [← hwo]
        exact pow_orderOf_eq_one w
      have hwZ : w ∈ S ⊓ zStarIn J :=
        mem_of_pow_four_eq_one_of_cyclic hQc hZQ hZ4 (pow_mem hsQ _) hw4
      have h1 : x⁻¹ * w * x = w⁻¹ := hxinv w (by rwa [hZP])
      have h2 : x⁻¹ * w * x = w := by
        have h3 := conj_pow (a := x⁻¹) (b := s) (i := 2 ^ (m - 2))
        rw [inv_inv, hsx] at h3
        rw [hw, ← h3]
      have h4 : w ^ 2 = 1 := by
        rw [pow_two]
        have h5 : w = w⁻¹ := h2.symm.trans h1
        calc w * w = w * w⁻¹ := by rw [← h5]
          _ = 1 := mul_inv_cancel w
      have h6 := orderOf_dvd_of_pow_eq_one h4
      rw [hwo] at h6
      norm_num at h6
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · exact Or.inr (eq_of_mul_self_eq_one_of_isCyclic hQc hsQ (hZQ haZ) hs2 haa hs1 ha1)
  have hNS : normalizer (S : Set G) ≤ normalizer (J : Set G) := by
    intro y hy
    apply centralizer_le_normalizer_of_gsMaximalSetting hMax hgs
    have hbS : y⁻¹ * a * y ∈ S := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hy) a).mp haS
      rwa [inv_inv] at h1
    have hbZ : ∀ t ∈ S, (y⁻¹ * a * y) * t = t * (y⁻¹ * a * y) := by
      intro t ht
      have ht' : y * t * y⁻¹ ∈ S := (mem_normalizer_iff.mp hy t).mp ht
      have hc := hcent _ ht'
      calc y⁻¹ * a * y * t = y⁻¹ * (a * (y * t * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * t * y⁻¹) * a) * y := by rw [hc]
        _ = t * (y⁻¹ * a * y) := by group
    rw [mem_centralizer_singleton_iff]
    rcases hcen _ hbS hbZ with h | h
    · exfalso
      apply ha1
      calc a = y * (y⁻¹ * a * y) * y⁻¹ := by group
        _ = 1 := by rw [h]; group
    · calc y * a = y * (y⁻¹ * a * y) := by rw [h]
        _ = a * y := by group
  obtain ⟨T, hTS⟩ := exists_sylow_eq_of_normalizer_le_of_isSylowTwoIn hS hNS
  exact ⟨T, hTS, hType G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv T hTS⟩

end CFSG.ComponentClassification.GrSLit
