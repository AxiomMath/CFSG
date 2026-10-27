module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316Tools

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem oddCore_sup_twoLayerIn_le_of_shadow {C Y M : Subgroup G}
    (hYC : Y ≤ C) (hYL : Y ≤ twoLayerIn C) (hYM : Y ≤ M)
    (hYr : 2 ≤ CFSG.Open.pRank 2 Y)
    (hCY : ∀ b ∈ Y, orderOf b = 2 → centralizer ({b} : Set G) ≤ M)
    (hclosure : conjClosure Y (twoLayerIn C) ≤ oddCoreIn C ⊔ Y) :
    oddCoreIn C ⊔ twoLayerIn C ≤ M := by
  have hOM : oddCoreIn C ≤ M :=
    le_of_coprime_of_pRank hYr hCY (coprime_card_oddCoreIn C)
      (hYC.trans (le_normalizer_oddCoreIn C))
  have hclosureM : conjClosure Y (twoLayerIn C) ≤ M :=
    hclosure.trans (sup_le hOM hYM)
  obtain ⟨b, hbY, hb2⟩ :=
    exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hYr)
  refine sup_le hOM (twoLayerIn_le_of_forall fun P hP => ?_)
  by_cases hmove : Y ≤ coreActionKernel P
  · refine le_of_mem_coreActionKernel hP hb2 (hmove hbY) (hCY b hbY hb2) ?_
    exact le_of_coprime_of_pRank hYr hCY (coprime_card_oddCoreIn P) fun y hy =>
      mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hmove hy).1)
  · exact (le_conjClosure_of_not_le_coreActionKernel hP hYL hmove).trans hclosureM

theorem eq_twoLayerIn_inf_of_mem_pumpSet_of_le (hq : QuasisimpleTwoPartInput)
    (hG : KStarKProper G) {M K : Subgroup G} (hKM : IsTwoComponentIn K M)
    (hKs : K ∈ solomonKStar G) (hCK : ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M)
    {a : G} (ha : orderOf a = 2) (haQ : a ∈ coreActionKernel K) {J : Subgroup G}
    (hJ : J ∈ pumpSet K (centralizer ({a} : Set G))) :
    J = twoLayerIn (K ⊓ centralizer ({a} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : K ∈ kStarComponents M := ⟨hKM, hKs⟩
  set Ca := centralizer ({a} : Set G) with hCa
  set Y := twoLayerIn (K ⊓ Ca) with hY
  obtain ⟨hY2, hYsup, ⟨eY⟩, h212, hYr⟩ := pump_facts hK haQ ha
  have hKMle : K ≤ M := hKM.1
  have hYK : Y ≤ K := hY2.1.trans inf_le_left
  have hYCa : Y ≤ Ca := hY2.1.trans inf_le_right
  have hYM : Y ≤ M := hYK.trans hKMle
  have hYL : Y ≤ twoLayerIn Ca := h212.trans (solomonKStarOf_le_twoLayerIn Ca)
  have hYres : oddResidualIn Y = Y := oddResidualIn_eq_self_of_isPComponent hY2.1 hY2.2
  have hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y) :=
    isQuasisimple_quotient_of_isPComponent hY2.1 hY2.2
  have hCY : ∀ v ∈ Y, orderOf v = 2 → centralizer ({v} : Set G) ≤ M := fun v hv hv2 =>
    hCK v (hYK hv) hv2
  have hOCa : oddCoreIn Ca ≤ M :=
    le_of_coprime_of_pRank hYr hCY (coprime_card_oddCoreIn Ca)
      (hYCa.trans (le_normalizer_oddCoreIn Ca))
  have hKq' : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    isQuasisimple_quotient_of_isPComponent hKM.1 hKM.2
  have hnc := exists_noncentral_involution_coreQuot hq hG hKM hKs
  have hJC : IsTwoComponentIn J Ca := hJ.1.1
  have hmove : ¬ Y ≤ coreActionKernel J := hJ.2
  have hJperf : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJC.1 hJC.2
  have hcard : Nat.card (↥J ⧸ Open.fusionZStar ↥J) = Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) := by
    rw [card_fusionZStar_of_mem_pumpSet hK haQ ha hJ]
    exact (Nat.card_congr eY.toEquiv).symm
  set Q := coreActionKernel J with hQ
  have hJQ : J ≤ normalizer (Q : Set G) := fun j hj =>
    FooteLit.mem_normalizer_coreActionKernel (le_normalizer hj)
  have hYJ : Y ≤ normalizer (J : Set G) :=
    hYL.trans (FooteLit.twoLayerIn_le_normalizer hJC.1 hJC.2)
  have hYQ : Y ≤ normalizer (Q : Set G) := fun y hy =>
    FooteLit.mem_normalizer_coreActionKernel (hYJ hy)
  have hLJQ : twoLayerIn Ca ≤ J ⊔ Q := twoLayerIn_le_of_forall fun P hP => by
    by_cases hPJ : P = J
    · rw [hPJ]
      exact le_sup_left
    · exact (GSThmB.B5a.le_coreActionKernel_of_ne hJC.1 hP.1 hJC.2 hP.2 (Ne.symm hPJ)).trans
        le_sup_right
  have hYJQ : Y ≤ J ⊔ Q := hYL.trans hLJQ
  have hJYQ : J ≤ Y ⊔ Q :=
    le_sup_coreActionKernel_of_card_fusionZStar hYq hYres hJQ hYQ hYJQ hmove hcard
  have hOJM : oddCoreIn J ≤ M := (oddCoreIn_le_of_isTwoComponentIn hJC).trans hOCa
  have hinv : ∀ b ∈ Y, orderOf b = 2 → b ∈ Q ⊔ (J ⊓ M) := by
    intro b hb hb2
    have hbQJ : b ∈ Q ⊔ J := by
      rw [sup_comm]
      exact hYJQ hb
    obtain ⟨q, hqQ, j, hj, hbqj⟩ := exists_mul_of_mem_sup_normalizer hJQ hbQJ
    have hqO : q ∈ normalizer (oddCoreIn J : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn hqQ.1)
    have hfix : b * j * b⁻¹ * j⁻¹ ∈ oddCoreIn J := by
      have h1 : j⁻¹⁻¹ * q⁻¹ * j⁻¹ * q ∈ oddCoreIn J := hqQ.2 j⁻¹ (inv_mem hj)
      have h2 : q * (j⁻¹⁻¹ * q⁻¹ * j⁻¹ * q) * q⁻¹ ∈ oddCoreIn J :=
        (mem_normalizer_iff.mp hqO _).mp h1
      rw [hbqj, show q * j * j * (q * j)⁻¹ * j⁻¹ = q * (j⁻¹⁻¹ * q⁻¹ * j⁻¹ * q) * q⁻¹ by
        group]
      exact h2
    obtain ⟨c, -, hcb, hcO⟩ := exists_commute_mem_coset (hYJ hb) hb2 hj hfix
    have hcM : c ∈ M := hCY b hb hb2 (mem_centralizer_singleton_iff.mpr hcb)
    have hjM : j ∈ M := by
      have h1 := mul_mem (inv_mem (hOJM hcO)) hcM
      rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at h1
    rw [hbqj]
    exact mul_mem (mem_sup_left hqQ) (mem_sup_right ⟨hj, hjM⟩)
  have hYQJM : Y ≤ Q ⊔ (J ⊓ M) :=
    le_of_forall_involution hYK hYsup hYres hKq' hnc
      (le_normalizer_sup hYQ (le_normalizer_inf' hYJ (hYM.trans le_normalizer))) hinv
  have hJQJM : J ≤ Q ⊔ (J ⊓ M) := hJYQ.trans (sup_le hYQJM le_sup_left)
  have hdec : ∀ j ∈ J, ∃ b ∈ J ⊓ M, b⁻¹ * j ∈ Q := by
    intro j hj
    obtain ⟨q, hqQ, y, hy, hjqy⟩ :=
      exists_mul_of_mem_sup_normalizer (inf_le_left.trans hJQ) (hJQJM (inv_mem hj))
    refine ⟨y⁻¹, inv_mem hy, ?_⟩
    have hj' : j = (q * y)⁻¹ := by rw [← hjqy, inv_inv]
    rw [hj', show y⁻¹⁻¹ * (q * y)⁻¹ = q⁻¹ by group]
    exact inv_mem hqQ
  have hJM : J ≤ M :=
    calc J = J ⊓ M ⊔ oddCoreIn J :=
          (sup_oddCoreIn_eq_of_forall_coreActionKernel inf_le_left hJperf hdec).symm
      _ ≤ M := sup_le inf_le_right hOJM
  have hJMC : IsTwoComponentIn J (M ⊓ Ca) :=
    ⟨le_inf hJM hJC.1, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hJM hJC.1)
      inf_le_right hJC.2⟩
  have hYMC : IsTwoComponentIn Y (M ⊓ Ca) := isTwoComponentIn_inf_of_isTwoComponentIn hKM hY2
  by_contra hne
  exact hmove (GSThmB.B5a.le_coreActionKernel_of_ne hJMC.1 hYMC.1 hJMC.2 hYMC.2 hne)

theorem isTwoComponentIn_twoLayerIn_inf_centralizer_of_le (hq : QuasisimpleTwoPartInput)
    (hG : KStarKProper G) {M K : Subgroup G} (hKM : IsTwoComponentIn K M)
    (hKs : K ∈ solomonKStar G) (hCK : ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M)
    {a : G} (ha : orderOf a = 2) (haQ : a ∈ coreActionKernel K) :
    twoLayerIn (K ⊓ centralizer ({a} : Set G)) ∈ kStarComponents (centralizer ({a} : Set G)) := by
  obtain ⟨J, hJ⟩ := pumpSet_nonempty (N := M) ⟨hKM, hKs⟩ haQ ha
  rw [← eq_twoLayerIn_inf_of_mem_pumpSet_of_le hq hG hKM hKs hCK ha haQ hJ]
  exact hJ.1

theorem isTwoComponentIn_twoLayerIn_inf_centralizer (hq : QuasisimpleTwoPartInput)
    (hG : KStarKProper G) {N : Subgroup G}
    (hCb : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G))
    {K : Subgroup G} (hK : K ∈ kStarComponents N) {a : G} (ha : orderOf a = 2)
    (haQ : a ∈ coreActionKernel K) :
    twoLayerIn (K ⊓ centralizer ({a} : Set G)) ∈ kStarComponents (centralizer ({a} : Set G)) :=
  isTwoComponentIn_twoLayerIn_inf_centralizer_of_le hq hG (mem_kStarComponents_normalizer hK).1
    hK.2 (hCb K hK) ha haQ

theorem twoLayerIn_centralizer_le_of_mem_coreActionKernel (hq : QuasisimpleTwoPartInput)
    (hG : KStarKProper G) {M K : Subgroup G} (hKM : IsTwoComponentIn K M)
    (hKs : K ∈ solomonKStar G) (hCK : ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M)
    {a : G} (ha : orderOf a = 2) (haQ : a ∈ coreActionKernel K) :
    twoLayerIn (centralizer ({a} : Set G)) ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G) with hCa
  set Y := twoLayerIn (K ⊓ Ca) with hY
  obtain ⟨hY2, -, -, h212, hYr⟩ := pump_facts (N := M) ⟨hKM, hKs⟩ haQ ha
  have hYC := (isTwoComponentIn_twoLayerIn_inf_centralizer_of_le hq hG hKM hKs hCK ha haQ).1
  have hYK : Y ≤ K := hY2.1.trans inf_le_left
  have hYM : Y ≤ M := hYK.trans hKM.1
  have hYL : Y ≤ twoLayerIn Ca := h212.trans (solomonKStarOf_le_twoLayerIn Ca)
  have hCY : ∀ v ∈ Y, orderOf v = 2 → centralizer ({v} : Set G) ≤ M := fun v hv hv2 =>
    hCK v (hYK hv) hv2
  have hcl : conjClosure Y (twoLayerIn Ca) ≤ Y := by
    rw [conjClosure_eq_iSup]
    refine iSup₂_le fun l hl => ?_
    have hlY : l⁻¹ ∈ normalizer (Y : Set G) :=
      inv_mem (FooteLit.twoLayerIn_le_normalizer hYC.1 hYC.2 hl)
    exact (mem_normalizer_iff_map_conj_eq.mp hlY).le
  exact le_sup_right.trans
    (oddCore_sup_twoLayerIn_le_of_shadow hYC.1 hYL hYM hYr hCY
      (hcl.trans le_sup_right))

theorem twoLayerIn_centralizer_le_of_pow_of_mem (hq : QuasisimpleTwoPartInput)
    (hG : KStarKProper G) {M K : Subgroup G} (hKM : IsTwoComponentIn K M)
    (hKs : K ∈ solomonKStar G) (hCK : ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M)
    {t : G} {k : ℕ} (htk : t ^ (2 ^ k) = 1) (ht1 : t ≠ 1) (htQ : t ∈ coreActionKernel K) :
    twoLayerIn (centralizer ({t} : Set G)) ≤ M := by
  obtain ⟨a, haT, ha2⟩ := exists_orderOf_eq_two_mem_zpowers htk ht1
  have haQ : a ∈ coreActionKernel K := (zpowers_le.mpr htQ) haT
  have hCt : centralizer ({t} : Set G) ≤ centralizer ({a} : Set G) := by
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp haT
    rw [mem_centralizer_singleton_iff] at hx ⊢
    exact (Commute.zpow_right hx n).eq
  have h1 := twoLayerIn_centralizer_le_of_mem_coreActionKernel hq hG hKM hKs hCK ha2 haQ
  have htC : t ∈ centralizer ({a} : Set G) := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp haT
    rw [mem_centralizer_singleton_iff]
    exact (Commute.zpow_right (Commute.refl t) n).eq
  have hT2 : IsPGroup 2 (zpowers t) := isPGroup_zpowers_of_pow htk
  have h2 := GrSLit.pLayer_inf_centralizer_le (Y := centralizer ({a} : Set G)) (A := zpowers t)
    (zpowers_le.mpr htC) hT2
  have hCz : centralizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hCz, inf_eq_right.mpr hCt] at h2
  exact h2.trans h1

theorem twoLayerIn_centralizer_le_normalizer_of_pow_of_mem (hq : QuasisimpleTwoPartInput)
    (hG : KStarKProper G) {N : Subgroup G}
    (hCb : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G))
    {K : Subgroup G} (hK : K ∈ kStarComponents N) {t : G} {k : ℕ} (htk : t ^ (2 ^ k) = 1)
    (ht1 : t ≠ 1) (htQ : t ∈ coreActionKernel K) :
    twoLayerIn (centralizer ({t} : Set G)) ≤ normalizer (solomonKStarOf N : Set G) :=
  twoLayerIn_centralizer_le_of_pow_of_mem hq hG (mem_kStarComponents_normalizer hK).1 hK.2
    (hCb K hK) htk ht1 htQ

end CFSG.ComponentClassification.Sol76T13
