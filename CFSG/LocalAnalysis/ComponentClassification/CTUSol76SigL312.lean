module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL312a
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigGood
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL311

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N H : Subgroup G}

theorem inf_centralizer_le_theta {f u : G} (huH : u ∈ H) (hu2 : orderOf u = 2)
    (hfu : f * u = u * f)
    (hf : oddCoreIn H ⊓ centralizer ({f} : Set G) ≤ oddCoreIn (centralizer ({f} : Set G)))
    (hu : oddCoreIn H ⊓ centralizer ({u} : Set G) ≤ oddCoreIn (centralizer ({u} : Set G))) :
    oddCoreIn H ⊓ centralizer ({f} : Set G) ≤ theta (zpowers u) f := by
  set X := oddCoreIn H ⊓ centralizer ({f} : Set G) with hX
  have huf : u ∈ centralizer ({f} : Set G) := mem_centralizer_singleton_iff.mpr hfu.symm
  have huX : zpowers u ≤ normalizer (X : Set G) := zpowers_le.mpr
    (mem_normalizer_inf (le_normalizer_oddCoreIn H huH) (le_normalizer huf))
  have hXcop : Nat.Coprime 2 (Nat.card X) :=
    Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn H)
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two (zpowers u) X
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])) huX hXcop
  rw [← hfac, theta, centralizer_zpowers_eq]
  refine sup_le (le_sup_of_le_left (Subgroup.commutator_mono hf le_rfl)) ?_
  refine le_sup_of_le_right (le_inf (inf_le_left.trans hf) ?_)
  exact (inf_le_inf_right _ inf_le_left).trans hu

theorem oddCoreIn_map_conj_le {F : Subgroup G} (hF : IsKleinFour F) (hFH : F ≤ H) {u : G}
    (huH : u ∈ H) (hu2 : orderOf u = 2) (hFu : F ≤ centralizer ({u} : Set G))
    (hbalF : ∀ f ∈ F, f ≠ 1 →
      oddCoreIn H ⊓ centralizer ({f} : Set G) ≤ oddCoreIn (centralizer ({f} : Set G)))
    (hbalu : oddCoreIn H ⊓ centralizer ({u} : Set G) ≤ oddCoreIn (centralizer ({u} : Set G)))
    {c : G} (hθ : ∀ f ∈ F, f ≠ 1 →
      theta (zpowers (MulAut.conj c u)) (MulAut.conj c f) ≤ oddCoreIn H) :
    (oddCoreIn H).map (MulAut.conj c).toMonoidHom ≤ oddCoreIn H := by
  have hFO : F ≤ normalizer (oddCoreIn H : Set G) := hFH.trans (le_normalizer_oddCoreIn H)
  have hgen := le_iSup_inf_centralizer_of_isKleinFour hF hFO (coprime_card_oddCoreIn H)
  have hle : oddCoreIn H ≤ ⨆ (f : G) (_ : f ∈ F) (_ : f ≠ 1), theta (zpowers u) f := by
    refine hgen.trans (iSup₂_le fun f hf => iSup_le fun hf1 => ?_)
    refine le_trans ?_ (le_iSup₂_of_le f hf (le_iSup_of_le hf1 le_rfl))
    exact inf_centralizer_le_theta huH hu2 (mem_centralizer_singleton_iff.mp (hFu hf))
      (hbalF f hf hf1) hbalu
  refine (map_mono hle).trans ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun f => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hf => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hf1 => ?_
  rw [map_theta, MonoidHom.map_zpowers]
  exact hθ f hf hf1

theorem centralizer_le_of_cover (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hKH : ∀ K ∈ kStarComponents N, K ≤ H)
    (hcov : ∀ K ∈ kStarComponents N, ∃ M ∈ kStarComponents H, K ≤ M ∧ K ⊔ oddCoreIn M = M)
    (hgood : ∀ K ∈ kStarComponents N, ∀ x ∈ K, orderOf x = 2 →
      twoLayerIn (centralizer ({x} : Set G)) ≤ H ∧ oddCoreIn (centralizer ({x} : Set G)) ≤ H ∧
        oddCoreIn H ⊓ centralizer ({x} : Set G) ≤ oddCoreIn (centralizer ({x} : Set G)))
    (hHO : normalizer (oddCoreIn H : Set G) ≤ H) {K : Subgroup G} (hK : K ∈ kStarComponents N)
    {s : G} (hsK : s ∈ K) (hs2 : orderOf s = 2) :
    centralizer ({s} : Set G) ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({s} : Set G) with hC
  have hLH : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ H := fun K hK s hs hs2 => (hgood K hK s hs hs2).1
  have hgoodM : ∀ M ∈ kStarComponents H, ∀ x ∈ M, orderOf x = 2 →
      twoLayerIn (centralizer ({x} : Set G)) ≤ H ∧ oddCoreIn (centralizer ({x} : Set G)) ≤ H ∧
        oddCoreIn H ⊓ centralizer ({x} : Set G) ≤ oddCoreIn (centralizer ({x} : Set G)) := by
    intro M hM x hxM hx2
    obtain ⟨K', hK', hK'M, hsup⟩ := exists_cover_eq_of_mem_kStarComponents hq hG hN hcov hM
    obtain ⟨m, hmM, hmK⟩ := exists_conj_mem_of_sup_oddCoreIn hK'M hsup hxM hx2
    have hm2 : orderOf (m⁻¹ * x * m) = 2 := by rw [orderOf_inv_mul_mul, hx2]
    exact good_facts_of_conj (hM.1.1 hmM) (hgood K' hK' _ hmK hm2)
  have hconjJ : ∀ c ∈ C, ∀ J ∈ kStarComponents C,
      J.map (MulAut.conj c).toMonoidHom ∈ kStarComponents C := fun c hc J hJ =>
    ⟨isTwoComponentIn_map_conj hJ.1 (le_normalizer hc), map_mem_solomonKStar _ hJ.2⟩
  have hJM : ∀ J ∈ kStarComponents C, ∃ M ∈ kStarComponents H, J ≤ M := fun J hJ =>
    exists_le_of_mem_kStarComponents_centralizer hN hKH hLH hcov hK hsK hs2 hJ
  suffices hmain : ∀ c ∈ C, (oddCoreIn H).map (MulAut.conj c).toMonoidHom ≤ oddCoreIn H by
    intro c hc
    refine hHO (mem_normalizer_iff_map_conj_eq.mpr ?_)
    refine eq_of_le_of_card_ge (hmain c hc) (le_of_eq ?_)
    exact (card_map_of_injective (MulAut.conj c).injective).symm
  intro c hc
  set φ := MulAut.conj c with hφ
  obtain ⟨MK, hMK, hKMK, hKsup⟩ := hcov K hK
  have hsMK : s ∈ MK ⊔ oddCoreIn H := mem_sup_left (hKMK hsK)
  have hφs : φ s = s := by
    rw [hφ, MulAut.conj_apply, mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have hF : ∀ J ∈ kStarComponents C, ∃ F : Subgroup G, F ≤ J ∧ IsKleinFour F := by
    intro J hJ
    obtain ⟨b, hbJ, hb2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hJ.2
    obtain ⟨F, hFJ, hF, -⟩ := exists_isKleinFour_mem (two_le_pRank_of_mem_solomonKStar hJ.2) hbJ
      hb2
    exact ⟨F, hFJ, hF⟩
  by_cases hcard : ∃ J ∈ kStarComponents C, ∃ J' ∈ kStarComponents C, J ≠ J'
  ·
    obtain ⟨J, hJ, J', hJ', hJJ'⟩ := hcard
    obtain ⟨F, hFJ, hFK⟩ := hF J hJ
    obtain ⟨M₁, hM₁, hJM₁⟩ := hJM J hJ
    obtain ⟨M₂, hM₂, hJ'M₂⟩ := hJM J' hJ'
    have hFQ : F ≤ coreActionKernel J' :=
      hFJ.trans (Foote5.SolMax.le_coreActionKernel_of_ne hJ'.1 hJ.1 hJJ'.symm)
    have hcovJ' := inf_centralizer_sup_oddCoreIn_eq (isPGroup_of_isKleinFour hFK) hFQ
    have hr : 1 ≤ CFSG.Open.pRank 2 (J' ⊓ centralizer (F : Set G)) :=
      ((by norm_num : 1 ≤ 2).trans (two_le_pRank_of_mem_solomonKStar hJ'.2)).trans
        (pRank_le_of_sup_oddCoreIn inf_le_left hcovJ')
    obtain ⟨u, huY, hu2⟩ := exists_orderOf_eq_two_of_pRank hr
    have huJ' : u ∈ J' := huY.1
    have hFu : F ≤ centralizer ({u} : Set G) := fun f hf =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp huY.2) f hf)
    have hFH : F ≤ H := (hFJ.trans hJM₁).trans hM₁.1.1
    have huH : u ∈ H := hM₂.1.1 (hJ'M₂ huJ')
    have hFinv : ∀ f ∈ F, f ≠ 1 → orderOf f = 2 := fun f hf hf1 =>
      orderOf_eq_two_of_isKleinFour hFK hf hf1
    refine oddCoreIn_map_conj_le hFK hFH huH hu2 hFu
      (fun f hf hf1 => (hgoodM M₁ hM₁ f (hJM₁ (hFJ hf)) (hFinv f hf hf1)).2.2)
      (hgoodM M₂ hM₂ u (hJ'M₂ huJ') hu2).2.2 fun f hf hf1 => ?_
    have hJc := hconjJ c hc J hJ
    have hJ'c := hconjJ c hc J' hJ'
    obtain ⟨N₁, hN₁, hJN₁⟩ := hJM _ hJc
    obtain ⟨N₂, hN₂, hJ'N₂⟩ := hJM _ hJ'c
    have hN₁₂ : N₁ ≠ N₂ := by
      intro h
      have := eq_of_le_of_mem_kStarComponents_centralizer hq hR1 hG hN hKH hLH hcov hK hsK hs2
        hN₁ hJc hJ'c hJN₁ (h ▸ hJ'N₂)
      exact hJJ' (map_injective (MulAut.conj c).injective this)
    have hfc : φ f ∈ N₁ := hJN₁ (mem_map_of_mem _ (hFJ hf))
    have huc : φ u ∈ N₂ := hJ'N₂ (mem_map_of_mem _ huJ')
    have hfc2 : orderOf (φ f) = 2 := by rw [MulEquiv.orderOf_eq]; exact hFinv f hf hf1
    have huc2 : orderOf (φ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu2
    have hcomm : φ f * φ u = φ u * φ f := by
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hFu hf)]
    exact theta_zpowers_le_oddCoreIn hN₁.1 hN₂.1 hN₁₂ hfc2 huc2 hcomm (mem_sup_left hfc)
      (mem_sup_left huc) (hgoodM N₁ hN₁ _ hfc hfc2).2.1 (hgoodM N₂ hN₂ _ huc huc2).2.1
  ·
    push Not at hcard
    obtain ⟨K', hK', hne⟩ := exists_mem_kStarComponents_ne hN K
    obtain ⟨P, hP, B', hB', hPB', hK'B', -⟩ := exists_pump_le hq hR1 hG hN hKH hLH hK' hK hne hsK
      hs2
    obtain ⟨M', hM', hK'M', hK'sup⟩ := hcov K' hK'
    have hB'M' : B' = M' := eq_of_le_of_le_isTwoComponentIn hB' hM'.1 hK'B' hK'M'
      (UnbalancedCorr.commutator_eq_of_isPComponent hK'.1.1 hK'.1.2)
      (exists_orderOf_eq_two_of_mem_solomonKStar hK'.2)
    subst hB'M'
    have hPC : P ∈ kStarComponents C := hP.1
    have hMM : B' ≠ MK := by
      intro h
      apply hne
      rw [h] at hK'B' hK'sup
      exact eq_of_le_sup_oddCoreIn hK' hK hK'B' hKMK (hK'B'.trans hKsup.ge)
    obtain ⟨F, hFP, hFK⟩ := hF P hPC
    have hFH : F ≤ H := (hFP.trans hPB').trans hM'.1.1
    have hFs : F ≤ centralizer ({s} : Set G) := hFP.trans hPC.1.1
    have hFinv : ∀ f ∈ F, f ≠ 1 → orderOf f = 2 := fun f hf hf1 =>
      orderOf_eq_two_of_isKleinFour hFK hf hf1
    refine oddCoreIn_map_conj_le hFK hFH (hKH K hK hsK) hs2 hFs
      (fun f hf hf1 => (hgoodM B' hM' f (hPB' (hFP hf)) (hFinv f hf hf1)).2.2)
      (hgood K hK s hsK hs2).2.2 fun f hf hf1 => ?_
    have hPc : P.map φ.toMonoidHom = P := hcard _ (hconjJ c hc P hPC) P hPC
    have hfc : φ f ∈ B' := hPB' (hPc ▸ mem_map_of_mem _ (hFP hf))
    have hfc2 : orderOf (φ f) = 2 := by rw [MulEquiv.orderOf_eq]; exact hFinv f hf hf1
    have hcomm : φ f * φ s = φ s * φ f := by
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hFs hf)]
    rw [hφs] at hcomm ⊢
    exact theta_zpowers_le_oddCoreIn hM'.1 hMK.1 hMM hfc2 hs2 hcomm (mem_sup_left hfc) hsMK
      (hgoodM B' hM' _ hfc hfc2).2.1 (hgood K hK s hsK hs2).2.1

end CFSG.ComponentClassification.Sol76.Sig
