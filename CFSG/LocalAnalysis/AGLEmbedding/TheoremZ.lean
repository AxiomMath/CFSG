module

public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig
public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreePair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.NoXBlock

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem normalizer_le_of_forall_maxTwoLocal_eq {G : Type*} [Group G] [Finite G]
    {H J R T C : Subgroup G} (hT : IsPGroup 2 T) (hJT : J ≤ Subgroup.normalizer (T : Set G))
    (hRT : R ≤ Subgroup.normalizer (T : Set G))
    (huniq : ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → J ≤ H' → R ≤ H' → H' = H)
    (hCT : C ≤ T) (hC : C ≠ ⊥) (hchar : (C.subgroupOf T).Characteristic) :
    Subgroup.normalizer (C : Set G) ≤ H := by
  have hTC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := T) (C.subgroupOf T)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCT] at h
  obtain ⟨H', hle, hmax⟩ := CFSG.PreuniquenessRankFour.Helpers.exists_maximal_twoLocal
    (⟨C, hC, hT.to_le hCT, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C : Set G)))
  rw [← huniq H' hmax (hJT.trans (hTC.trans hle)) (hRT.trans (hTC.trans hle))]
  exact hle

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem false_of_normal_inf_le_sup (h : AGLPair p M H R) {X T D : Subgroup G}
    (hX : IsPGroup p X) (hXH : X ≤ H) (hTN : T ≤ GLBPrimeCore p H) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ (T.subgroupOf (GLBPrimeCore p H)).index) (hT1 : T ≠ ⊥)
    (hloc : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H)
    (hDM : D ≤ M) (hMD : M ≤ Subgroup.normalizer (D : Set G)) (hQD : pCoreOf 2 M ≤ D)
    (hND : GLBPrimeCore p H ≤ D) (hDH : D ⊓ H ≤ X ⊔ GLBPrimeCore p H)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : Subgroup.normalizer (T : Set G) ≤ H :=
    hloc T le_rfl hT1 (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hTD : ¬ 2 ∣ (T.subgroupOf D).index :=
    not_dvd_index_of_inf_normalizer_le hTN hND hT2 hTidx fun U hU hUD =>
      le_of_le_sup_of_isPGroup_of_ne h.ne_two hX (hXH.trans (le_normalizer_glbPrimeCore p H)) hU
        fun u hu => hDH ⟨(hUD hu).1, hTH (hUD hu).2⟩
  have hcgs : cgsIn D T = D := by
    by_contra hne
    have hDtop : D ≠ ⊤ := fun htop => h.not_le ((top_le_iff.mp (htop ▸ hDM) : M = ⊤) ▸ le_top)
    have hK : Open.IsKGroup ↥D :=
      isKGroup_of_catalogSimpleSections (catalogSimpleSections_of_isKProper h.glob.kProper D hDtop)
    have hQcore : pCoreOf 2 M ≤ pCoreOf 2 D :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hQD
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr
          (hDM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)))
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    have hchar : CharTwo D := fun x hx =>
      hQcore (h.charTwo.1 ⟨hDM hx.1, Subgroup.centralizer_le hQcore hx.2⟩)
    obtain ⟨Y, hYD, hYsub, hYX, -⟩ := hCGT G D T hK hchar ⟨hTN.trans hND, hT2, hTD⟩ hne
    exact hD2 M Y h.maxTwoLocal_M (hYD.trans hDM)
      (isSubnormal_of_isSubnormal_of_normal hYsub hDM
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hDM).mpr hMD)) hYX
  have hDH' : D ≤ H :=
    calc D = cgsIn D T := hcgs.symm
      _ ≤ D ⊓ H := iSup_le fun C => iSup_le fun hCT => iSup_le fun hC => iSup_le fun hchar =>
          inf_le_inf_left D (hloc C hCT hC hchar)
      _ ≤ X ⊔ GLBPrimeCore p H := hDH
      _ ≤ H := sup_le hXH (glbPrimeCore_le p H)
  have hMH : M ≤ H := by
    intro m hm
    obtain ⟨d, hd, hdm⟩ :=
      exists_mem_inv_mul_mem_normalizer_of_not_dvd_index (hTN.trans hND) hT2 hTD (hMD hm)
    have e : m = d * (d⁻¹ * m) := by group
    rw [e]
    exact H.mul_mem (hDH' hd) (hTH hdm)
  exact h.not_le (h.maxTwoLocal_M.2 H h.maxTwoLocal_H.1 hMH).le

theorem false_of_unique_over (h : AGLPair p M H R) {X J : Subgroup G}
    (hXR : X ≤ R)
    (hXQ : ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal)
    (hNX : ⁅GLBPrimeCore p H, X⁆ ≤ pCoreOf 2 M)
    (hCX : (H ⊓ M) ⊓ Subgroup.centralizer (X : Set G) ≤ X ⊔ GLBPrimeCore p H)
    (hNJ : ⁅GLBPrimeCore p H, J⁆ ≤ pCoreOf 2 H)
    (huniq : ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → J ≤ H' → R ≤ H' → H' = H)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp2 : p.Coprime 2 := (Nat.coprime_primes h.prime Nat.prime_two).mpr h.ne_two
  have hX : IsPGroup p X := h.isPGroup_R.to_le hXR
  have hXM : X ≤ M := hXR.trans h.le_M
  have hSN : pCoreOf 2 H ≤ GLBPrimeCore p H := h.twoCore_le_primeCore
  have hQS : pCoreOf 2 M ≤ pCoreOf 2 H := h.twoCore_M_le
  have hQM : pCoreOf 2 M ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hQcop : p.Coprime (Nat.card (pCoreOf 2 M)) := by
    obtain ⟨k, hk⟩ :=
      IsPGroup.iff_card.mp (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    exact hk ▸ hp2.pow_right k
  have hMXQ : M ≤ Subgroup.normalizer ((X ⊔ pCoreOf 2 M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hXM hQM)).mp hXQ
  obtain ⟨T, hTN, hT2, hTidx, hRT, hST⟩ := h.exists_sylowTwo_primeCore
  have hT1 : T ≠ ⊥ := fun hbot => CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_pCoreOf_ne_bot H
    h.maxTwoLocal_H.1 (le_bot_iff.mp (hbot ▸ hST))
  have hJT : J ≤ Subgroup.normalizer (T : Set G) := by
    refine le_normalizer_of_forall_mul_mul_inv_mem fun j hj t ht => ?_
    have hc := hNJ (Subgroup.commutator_mem_commutator ((GLBPrimeCore p H).inv_mem (hTN ht)) hj)
    rw [commutatorElement_def, inv_inv] at hc
    have e : j * t * j⁻¹ = t * (t⁻¹ * j * t * j⁻¹) := by group
    rw [e]
    exact T.mul_mem ht (hST hc)
  refine h.false_of_normal_inf_le_sup (D := pCoreOf 2 M ⊔ (M ⊓ Subgroup.centralizer (X : Set G)))
    hX (hXR.trans h.le_H) hTN hT2 hTidx hT1
    (fun C hCT hC hchar => normalizer_le_of_forall_maxTwoLocal_eq hT2 hJT hRT huniq hCT hC hchar)
    (sup_le hQM inf_le_left) (le_normalizer_sup_inf_centralizer hX hQcop hXM hQM hMQ hMXQ)
    le_sup_left (fun n hn => mem_sup_inf_centralizer_of_commutator_mem hX hQcop hXM hQM hMQ hMXQ
      (h.primeCore_le hn) fun x hx => ?_) ?_ hCGT hD2
  · have hc := hNX (Subgroup.commutator_mem_commutator hn hx)
    rwa [commutatorElement_def] at hc
  · rintro d ⟨hd, hdH⟩
    obtain ⟨q, hq, c, hc, rfl⟩ := exists_mul_of_mem_sup_inf_centralizer hMQ hd
    have hqN : q ∈ GLBPrimeCore p H := hSN (hQS hq)
    have hcH : c ∈ H := by
      have e : c = q⁻¹ * (q * c) := by group
      rw [e]
      exact H.mul_mem (H.inv_mem (glbPrimeCore_le p H hqN)) hdH
    exact (X ⊔ GLBPrimeCore p H).mul_mem (Subgroup.mem_sup_right hqN) (hCX ⟨⟨hcH, hc.1⟩, hc.2⟩)

end AGLPair

end CFSG.AGLEmbeddingD2

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace D1PhaseThree

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem isPGroup_R (h : D1PhaseThree p P M H R) : IsPGroup p R :=
  h.toPair.isPGroup_R

theorem exists_sylowTwo_primeCore (h : D1PhaseThree p P M H R) :
    ∃ T : Subgroup G, T ≤ GLBPrimeCore p H ∧ IsPGroup 2 T ∧
      ¬ 2 ∣ (T.subgroupOf (GLBPrimeCore p H)).index ∧
      R ≤ Subgroup.normalizer (T : Set G) ∧ pCoreOf 2 H ≤ T :=
  h.toPair.exists_sylowTwo_primeCore

theorem false_of_normal_inf_le_sup (h : D1PhaseThree p P M H R) {X T D : Subgroup G}
    (hX : IsPGroup p X) (hXH : X ≤ H) (hTN : T ≤ GLBPrimeCore p H) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ (T.subgroupOf (GLBPrimeCore p H)).index) (hT1 : T ≠ ⊥)
    (hloc : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H)
    (hDM : D ≤ M) (hMD : M ≤ Subgroup.normalizer (D : Set G)) (hQD : pCoreOf 2 M ≤ D)
    (hND : GLBPrimeCore p H ≤ D) (hDH : D ⊓ H ≤ X ⊔ GLBPrimeCore p H)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : False :=
  h.toPair.false_of_normal_inf_le_sup hX hXH hTN hT2 hTidx hT1 hloc hDM hMD hQD hND hDH hCGT
    (hD2 G h.glob)

theorem false_of_unique_over (h : D1PhaseThree p P M H R) {X J : Subgroup G}
    (hXR : X ≤ R)
    (hXQ : ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal)
    (hNX : ⁅GLBPrimeCore p H, X⁆ ≤ pCoreOf 2 M)
    (hCX : (H ⊓ M) ⊓ Subgroup.centralizer (X : Set G) ≤ X ⊔ GLBPrimeCore p H)
    (hNJ : ⁅GLBPrimeCore p H, J⁆ ≤ pCoreOf 2 H)
    (huniq : ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → J ≤ H' → R ≤ H' → H' = H)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : False :=
  h.toPair.false_of_unique_over hXR hXQ hNX hCX hNJ huniq hCGT (hD2 G h.glob)

end D1PhaseThree

end CFSG.AGLEmbedding
