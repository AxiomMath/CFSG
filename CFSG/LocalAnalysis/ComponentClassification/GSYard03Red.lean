module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Defs
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39KC
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigBigCenter

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard03

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

section Core

variable {K₁ Q : Type} [Group K₁] [Group Q]

private theorem isKleinFour_map_inj {X Y : Type} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Injective f) {E : Subgroup X} (hE : IsKleinFour E) :
    IsKleinFour (E.map f) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · rw [Subgroup.card_map_of_injective hf, hE.card_four]
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hE hv, map_one]

private noncomputable abbrev indHom (φ : K₁ →* Q) (N₁ : Subgroup K₁) [N₁.Normal]
    (Ō : Subgroup Q) [Ō.Normal] (hker : ∀ k, φ k ∈ Ō ↔ k ∈ N₁) : K₁ ⧸ N₁ →* Q ⧸ Ō :=
  QuotientGroup.map N₁ Ō φ fun k hk => (hker k).mpr hk

private theorem indHom_mk (φ : K₁ →* Q) (N₁ : Subgroup K₁) [N₁.Normal]
    (Ō : Subgroup Q) [Ō.Normal] (hker : ∀ k, φ k ∈ Ō ↔ k ∈ N₁) (k : K₁) :
    indHom φ N₁ Ō hker (QuotientGroup.mk k) = QuotientGroup.mk (φ k) := rfl

private theorem indHom_injective (φ : K₁ →* Q) (N₁ : Subgroup K₁) [N₁.Normal]
    (Ō : Subgroup Q) [Ō.Normal] (hker : ∀ k, φ k ∈ Ō ↔ k ∈ N₁) :
    Function.Injective (indHom φ N₁ Ō hker) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [indHom_mk, QuotientGroup.eq_one_iff] at hx
  exact (QuotientGroup.eq_one_iff k).mpr ((hker k).mp hx)

private theorem exists_mem_range_inv_mul_mem_centralizer (φ : K₁ →* Q) (N₁ : Subgroup K₁)
    [N₁.Normal] (Ō : Subgroup Q) [Ō.Normal] (hker : ∀ k, φ k ∈ Ō ↔ k ∈ N₁)
    (hQ : ∀ q : Q, ∃ k : K₁, ∀ k' : K₁,
      (φ k')⁻¹ * ((φ k)⁻¹ * q)⁻¹ * φ k' * ((φ k)⁻¹ * q) ∈ Ō) (y : Q ⧸ Ō) :
    ∃ x ∈ (indHom φ N₁ Ō hker).range,
      x⁻¹ * y ∈ centralizer ((indHom φ N₁ Ō hker).range : Set (Q ⧸ Ō)) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ := hQ q
  refine ⟨QuotientGroup.mk (φ k), ⟨QuotientGroup.mk k, indHom_mk φ N₁ Ō hker k⟩, ?_⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨w, rfl⟩
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective w
  rw [indHom_mk]
  simp only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  symm
  rw [QuotientGroup.eq]
  have h := hk k'
  convert h using 1
  group

private theorem mem_center_of_mem_center {Y : Type} [Group Y] (X : Subgroup Y) {z : Y}
    (hzX : z ∈ X) (hzc : ∀ x ∈ X, x * z = z * x)
    (hXC : ∀ y : Y, ∃ x ∈ X, x⁻¹ * y ∈ centralizer (X : Set Y)) : z ∈ center Y := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x, hx, hc⟩ := hXC y
  have hy : y = x * (x⁻¹ * y) := by group
  have hzc' : z * (x⁻¹ * y) = (x⁻¹ * y) * z := (mem_centralizer_iff.mp hc) z hzX
  rw [hy, mul_assoc, ← hzc', ← mul_assoc, hzc x hx, mul_assoc]

theorem not_isTwoDisconnected_of_central_quot [Finite Q] (hJ : CentralInvolutionJoin)
    (φ : K₁ →* Q) (N₁ : Subgroup K₁) [N₁.Normal] (Ō : Subgroup Q) [Ō.Normal]
    (hker : ∀ k, φ k ∈ Ō ↔ k ∈ N₁)
    (hQ : ∀ q : Q, ∃ k : K₁, ∀ k' : K₁,
      (φ k')⁻¹ * ((φ k)⁻¹ * q)⁻¹ * φ k' * ((φ k)⁻¹ * q) ∈ Ō)
    (hodd : Odd (Nat.card Ō)) {τ : K₁ ⧸ N₁} (hτc : τ ∈ center (K₁ ⧸ N₁)) (hτ2 : orderOf τ = 2)
    (hX2 : ¬ IsTwoDisconnected (K₁ ⧸ N₁)) (hF1 : CentralSquareFour (K₁ ⧸ N₁))
    {A : Subgroup Q} (hA : CFSG.Open.IsElemAbelian 2 A) (hA8 : Nat.card A = 8) :
    ¬ IsTwoDisconnected Q := by
  intro hdisc
  set ι := indHom φ N₁ Ō hker with hιdef
  have hι : Function.Injective ι := indHom_injective φ N₁ Ō hker
  have hXC := exists_mem_range_inv_mul_mem_centralizer φ N₁ Ō hker hQ
  have hzc : ∀ x ∈ ι.range, x * ι τ = ι τ * x := by
    rintro _ ⟨w, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hτc) w]
  have hY : ¬ IsTwoDisconnected (Q ⧸ Ō) := by
    refine hJ (Q ⧸ Ō) ι.range (ι τ) ?_ ⟨τ, rfl⟩
      (mem_center_of_mem_center ι.range ⟨τ, rfl⟩ hzc hXC) hXC ?_ ?_
    · rw [orderOf_injective ι hι, hτ2]
    · exact fun h => hX2 (isTwoDisconnected_of_mulEquiv (MonoidHom.ofInjective hι).symm h)
    · rintro _ ⟨x₀, rfl⟩ hxx
      have hx₀ : x₀ * x₀ ∈ center (K₁ ⧸ N₁) := by
        rw [Subgroup.mem_center_iff]
        intro w
        apply hι
        have h := (mem_centralizer_iff.mp hxx) (ι w) ⟨w, rfl⟩
        simp only [map_mul]
        exact h
      obtain ⟨A₀, hA₀, hA₀c⟩ := hF1 x₀ hx₀
      refine ⟨A₀.map ι, isKleinFour_map_inj hι hA₀, Subgroup.map_le_range ι A₀, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ rfl
      have h := (mem_centralizer_iff.mp (hA₀c ha)) x₀ rfl
      rw [← map_mul, ← map_mul, h]
  obtain ⟨E, F, hE, hF, hEF⟩ := hdisc
  refine hEF (reflTransGen_of_twoConnected_quot (QuotientGroup.mk' Ō)
    (QuotientGroup.mk'_surjective Ō) ?_ hY hA hA8 hE hF)
  rwa [QuotientGroup.ker_mk']

end Core

section Concrete

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

private theorem le_Qprime (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') : K ≤ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K' :=
  le_inf ((le_twoLayerIn_of_isTwoComponentIn hK.1).trans le_sup_right)
    (le_coreActionKernel_of_ne hK' hK hne.symm)

private theorem le_normalizer_of_le_sup (hK : IsTwoComponentIn K N) {Q : Subgroup G}
    (hQM : Q ≤ oddTwoCoreIn N ⊔ twoLayerIn N) : Q ≤ normalizer (K : Set G) := by
  intro q hq
  obtain ⟨k, hk, hc⟩ := exists_inv_mul_mem_coreActionKernel hK (hQM hq)
  have h := mul_mem (Subgroup.le_normalizer hk) (mem_coreActionKernel.mp hc).1
  rwa [mul_inv_cancel_left] at h

private theorem normal_subgroupOf_oddCoreIn {Q : Subgroup G} (hQ : Q ≤ normalizer (K : Set G)) :
    ((oddCoreIn K).subgroupOf Q).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  rw [← map_conj_oddCoreIn (hQ g.2)]
  exact ⟨n, hn, by simp [MulAut.conj_apply]⟩

theorem not_isTwoDisconnected_of_leaves_Qprime (hJ : CentralInvolutionJoin)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    (h3 : 3 ≤ CFSG.Open.pRank 2 K) (hZ : center (coreQuot K) ≠ ⊥)
    (hX2 : ¬ IsTwoDisconnected (coreQuot K)) (hF1 : CentralSquareFour (coreQuot K)) :
    ¬ IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K' with hQdef
  have hKQ : K ≤ Q := le_Qprime hK hK' hne
  have hQM : Q ≤ oddTwoCoreIn N ⊔ twoLayerIn N := inf_le_left
  haveI : ((oddCoreIn K).subgroupOf Q).Normal :=
    normal_subgroupOf_oddCoreIn (le_normalizer_of_le_sup hK.1 hQM)
  obtain ⟨τ, hτ, hτ2⟩ := exists_orderOf_eq_two_mem_center
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2) hZ
  have h3top : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥K) := by
    rw [← SectionRank.pRank_eq_open_pRank_top, pRank_coe_eq]
    exact h3
  obtain ⟨Ab, -, hAb, hAb8⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) h3top
  refine not_isTwoDisconnected_of_central_quot hJ (Subgroup.inclusion hKQ) (pPrimeCore 2 ↥K)
    ((oddCoreIn K).subgroupOf Q) ?_ ?_ ?_ hτ hτ2 hX2 hF1
    (CFSG.Open.IsElemAbelian.map hAb (Subgroup.inclusion hKQ)) ?_
  · intro k
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_iff_mem K.subtype_injective
  · intro q
    obtain ⟨k, hk, hc⟩ := exists_inv_mul_mem_coreActionKernel hK.1 (hQM q.2)
    refine ⟨⟨k, hk⟩, fun k' => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    exact (mem_coreActionKernel.mp hc).2 (k' : G) k'.2
  · have hOQ : oddCoreIn K ≤ Q := (Subgroup.map_subtype_le (pPrimeCore 2 ↥K)).trans hKQ
    have h1 : Nat.card ((oddCoreIn K).subgroupOf Q) = Nat.card (oddCoreIn K) := by
      rw [← Subgroup.card_map_of_injective Q.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hOQ]
    rw [h1]
    exact Nat.coprime_two_left.mp (coprime_card_oddCoreIn K)
  · rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKQ), hAb8]
    norm_num

end Concrete

theorem solomonQTwoDisconnectedSylowInvFor_of_bigCenter
    (hBig : QuasisimpleBigCenterRankThree) (hJ : CentralInvolutionJoin)
    (hSJ : QuasisimpleSylowFourJoinedSCN) (hF1 : QuasisimpleCentralSquareFour) :
    SolomonQTwoDisconnectedSylowInvFor := by
  intro G _ _ hG N hN hr K hK K' hK' hne hdisc h3 _ _ hZ hZ4 _
  by_contra hI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX2 := not_isTwoDisconnected_coreQuot_of_not_isSolomonI hBig hSJ hG hK h3 hI
  have hO : pPrimeCore 2 (coreQuot K) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2
  have hq := isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
  have hcat :=
    catalog_coreQuotient_of_mem_solomonKStar (kStarKProper_of_simpleAmbient hG) hK.1 hK.2
  have h3' : 3 ≤ CFSG.pRank 2 (coreQuot K) := by
    rw [FooteLit.pRank_quotient_pPrimeCore, pRank_coe_eq]
    exact h3
  exact not_isTwoDisconnected_of_leaves_Qprime hJ hK hK' hne h3 hZ hX2
    (hF1 (coreQuot K) hq hO hcat h3' hZ4 hI) hdisc

theorem solomonQTwoDisconnectedSylowInvFor_of_leaves
    (hJ : CentralInvolutionJoin) (hSJ : QuasisimpleSylowFourJoinedSCN)
    (hF1 : QuasisimpleCentralSquareFour) :
    SolomonQTwoDisconnectedSylowInvFor :=
  solomonQTwoDisconnectedSylowInvFor_of_bigCenter quasisimpleBigCenterRankThree_holds hJ hSJ hF1

end CFSG.ComponentClassification.Sol76.Sig.GSYard03
