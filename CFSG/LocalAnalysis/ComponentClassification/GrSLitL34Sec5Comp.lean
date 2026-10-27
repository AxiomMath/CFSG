module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Balance

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem solomon_involutions (hSol : SolomonCommutingCoreInput) {s u : G} (hs : orderOf s = 2)
    (hu : orderOf u = 2) (hsu : s * u = u * s) :
    ⁅(oTwoPrimeTwo ↥(centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype,
        oddIn (centralizer ({s} : Set G)) ⊓ centralizer ({u} : Set G)⁆ ≤
        oddIn (centralizer ({u} : Set G)) ∧
      ∀ L : Subgroup G, L ≤ centralizer ({u} : Set G) →
        IsPComponent 2 (L.subgroupOf (centralizer ({u} : Set G))) →
        oddIn (centralizer ({s} : Set G)) ⊓ centralizer ({u} : Set G) ≤
            normalizer (L : Set G) ∧
          (¬ ⁅L, oddIn (centralizer ({s} : Set G)) ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn L →
            s ∈ normalizer (L : Set G) ∧
              oddIn L ⊔ ⁅L, oddIn (centralizer ({s} : Set G)) ⊓ centralizer ({u} : Set G)⁆ = L ∧
              oddIn L ⊔ ⁅L, zpowers s⁆ = L) := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hu1 : u ≠ 1 := by rintro rfl; simp at hu
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hS : zpowers s ≠ ⊥ := fun h => hs1 (zpowers_eq_bot.mp h)
  have hT : zpowers u ≠ ⊥ := fun h => hu1 (zpowers_eq_bot.mp h)
  have hST : ∀ a ∈ zpowers s, ∀ b ∈ zpowers u, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute s u from hsu) i j).eq
  have h := hSol G (zpowers s) (zpowers u) hS hT (isElemTwo_zpowers hs2).1
    (isElemTwo_zpowers hs2).2 (isElemTwo_zpowers hu2).1 (isElemTwo_zpowers hu2).2 hST
  obtain ⟨⟨h1, -⟩, h2, -⟩ := h
  have h1' : ⁅(oTwoPrimeTwo ↥(centralizer ((zpowers u : Subgroup G) : Set G))).map
        (centralizer ((zpowers u : Subgroup G) : Set G)).subtype,
      (pPrimeCore 2 (centralizer ((zpowers s : Subgroup G) : Set G))).map
        (centralizer ((zpowers s : Subgroup G) : Set G)).subtype ⊓
        centralizer ((zpowers u : Subgroup G) : Set G)⁆ ≤
      (pPrimeCore 2 (centralizer ((zpowers u : Subgroup G) : Set G))).map
        (centralizer ((zpowers u : Subgroup G) : Set G)).subtype := h1
  rw [centralizer_zpowers_eq s, centralizer_zpowers_eq u] at h1' h2
  refine ⟨h1', fun L hLu hL => ?_⟩
  obtain ⟨hDN, hnot⟩ := h2 L hLu hL
  refine ⟨hDN, fun hLD => ?_⟩
  obtain ⟨hne, hD, hz⟩ := hnot hLD
  have hsN : s ∈ normalizer (L : Set G) := by
    by_contra hsN
    apply hne
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
    rcases (LocalB.mem_zpowers_iff_of_involution s y hs).mp hy1 with h | h
    · exact h ▸ one_mem _
    · exact absurd (h ▸ hy2) hsN
  have hzN : zpowers s ⊓ normalizer (L : Set G) = zpowers s :=
    inf_eq_left.mpr (zpowers_le.mpr hsN)
  rw [hzN] at hz
  exact ⟨hsN, hD, hz⟩

omit [Finite G] in
theorem commutator_subgroupOf_normal {M A : Subgroup G} (hA : A ≤ normalizer (M : Set G)) :
    (⁅M, A⁆.subgroupOf M).Normal := by
  rw [normal_subgroupOf_iff (commutator_le_of_le_normalizer hA)]
  intro k m hk hm
  have h1 : ⁅M, A⁆ ≤ (⁅M, A⁆).comap (MulAut.conj m).toMonoidHom := by
    rw [commutator_le]
    intro a ha b hb
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e1 : m * ⁅a, b⁆ * m⁻¹ = ⁅m * a, b⁆ * ⁅m, b⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact mul_mem (commutator_mem_commutator (mul_mem hm ha) hb)
      (inv_mem (commutator_mem_commutator hm hb))
  exact h1 hk

theorem gsUnbalancingTriple_of_not_le (hSol : SolomonCommutingCoreInput) {s u : G}
    (hs : orderOf s = 2) (hu : orderOf u = 2) (hsu : s * u = u * s) {K Y : Subgroup G}
    (hKu : K ≤ centralizer ({u} : Set G))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set G))))
    (hYD : Y ≤ oddIn (centralizer ({s} : Set G)) ⊓ centralizer ({u} : Set G))
    (hY : ¬ ⁅K, Y⁆ ≤ oddIn K) : GSUnbalancingTriple u s K := by
  obtain ⟨-, h2⟩ := solomon_involutions hSol hs hu hsu
  obtain ⟨hDN, hnot⟩ := h2 K hKu hK
  have hKD : ¬ ⁅K, oddIn (centralizer ({s} : Set G)) ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K :=
    fun h => hY ((commutator_mono le_rfl hYD).trans h)
  obtain ⟨hsN, hD, hz⟩ := hnot hKD
  have hperf : Group.IsPerfect K := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hK
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKu).toMonoidHom)
      (subgroupOfEquivOfLe hKu).surjective
  have hT1 : ⁅K, zpowers s⁆ = K := eq_of_pPrimeCore_sup_eq
    (commutator_le_of_le_normalizer (zpowers_le.mpr hsN))
    (commutator_subgroupOf_normal (zpowers_le.mpr hsN)) hperf hz
  have hT2 : ⁅K, oddIn (centralizer ({s} : Set G)) ⊓ centralizer ({u} : Set G)⁆ = K :=
    eq_of_pPrimeCore_sup_eq (commutator_le_of_le_normalizer hDN)
      (commutator_subgroupOf_normal hDN) hperf hD
  rw [gsUnbalancingTriple_iff]
  exact ⟨hu, hs, hsu.symm, hKu, hK, hT1, hT2⟩

theorem exists_isPComponent_not_le (hSol : SolomonCommutingCoreInput) {s u : G}
    (hs : orderOf s = 2) (hu : orderOf u = 2) (hsu : s * u = u * s) {Y : Subgroup G}
    (hYD : Y ≤ oddIn (centralizer ({s} : Set G)) ⊓ centralizer ({u} : Set G))
    (hY : ¬ Y ≤ oddIn (centralizer ({u} : Set G))) :
    ∃ K : Subgroup G, K ≤ centralizer ({u} : Set G) ∧
      IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set G))) ∧ ¬ ⁅K, Y⁆ ≤ oddIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, -⟩ := solomon_involutions hSol hs hu hsu
  set C := centralizer ({u} : Set G) with hC
  by_contra hall
  push Not at hall
  apply hY
  have hYC : Y ≤ C := hYD.trans inf_le_right
  have hle : Y.subgroupOf C ≤ pPrimeCore 2 ↥C := by
    apply le_pPrimeCore_of_commute
    · rw [Nat.card_congr (subgroupOfEquivOfLe hYC).toEquiv]
      refine Odd.of_dvd_nat ?_ (card_dvd_of_le (hYD.trans inf_le_left))
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    · intro m hm d hd
      have hm' : (m : G) ∈ (oTwoPrimeTwo ↥C).map C.subtype := mem_map_of_mem C.subtype hm
      have h2 : C.subtype (m * d * m⁻¹ * d⁻¹) ∈ oddIn C := by
        have := commutator_mem_commutator hm' (hYD (mem_subgroupOf.mp hd))
        rw [commutatorElement_def] at this
        simpa using h1 this
      exact (mem_map_iff_mem C.subtype_injective).mp h2
    · intro M' hM' m hm d hd
      set M : Subgroup G := M'.map C.subtype with hMdef
      have hMC : M ≤ C := map_subtype_le _
      have hMs : M.subgroupOf C = M' := comap_map_eq_self_of_injective C.subtype_injective _
      have hMp : IsPComponent 2 (M.subgroupOf C) := hMs ▸ hM'
      have hmM : (m : G) ∈ M := mem_map_of_mem C.subtype hm
      have h2 : (m : G) * d * (m : G)⁻¹ * (d : G)⁻¹ ∈ oddIn M := by
        have := commutator_mem_commutator hmM (mem_subgroupOf.mp hd : (d : G) ∈ Y)
        rw [commutatorElement_def] at this
        exact hall M hMC hMp this
      have h3 : C.subtype (m * d * m⁻¹ * d⁻¹) ∈ oddIn C := by
        have e : C.subtype (m * d * m⁻¹ * d⁻¹) = (m : G) * d * (m : G)⁻¹ * (d : G)⁻¹ := by simp
        rw [e]
        exact GSLit.map_pPrimeCore_le_of_isPComponent hMC hMp h2
      exact (mem_map_iff_mem C.subtype_injective).mp h3
  have h := map_mono (f := C.subtype) hle
  rwa [map_subgroupOf_eq_of_le hYC] at h

end CFSG.ComponentClassification.GrSLit.GrS5
