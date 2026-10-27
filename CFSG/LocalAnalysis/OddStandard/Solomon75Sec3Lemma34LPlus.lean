module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma34Solv
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusNPlus
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Core
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Desc

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Lemma34

theorem comm_mem_pPrimeCore_of_mem_LPlus {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hM : IsPComponent 2 M) {u : G} (hu : u ∈ M) (hc : ∀ m ∈ M, ⁅m, u⁆ ∈ pPrimeCore 2 G) :
    ∀ y ∈ LPlus G, ⁅y, u⁆ ∈ pPrimeCore 2 G := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := pPrimeCore 2 G with hO
  set q : G →* G ⧸ O := QuotientGroup.mk' O with hq
  have hbot : pPrimeCore 2 (G ⧸ O) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have h3 : pCore 3 (G ⧸ O) = ⊥ := pCore_three_eq_bot hbot
  have hcomm : ∀ l : G, ⁅l, u⁆ ∈ O → q l * q u = q u * q l := fun l hl => by
    have h1 : q ⁅l, u⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hl
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hmap : (pLayer G 2).map q = layer (G ⧸ O) :=
    ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient (H := G) (p := 2)
  have hMlayer : M ≤ pLayer G 2 := le_sSup hM
  have hqu : q u ∈ layer (G ⧸ O) := hmap ▸ Subgroup.mem_map_of_mem q (hMlayer hu)
  have hlayer : layer (G ⧸ O) ≤ centralizer ({q u} : Set (G ⧸ O)) := by
    rw [← hmap, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL' l hl => ?_
    have hL : IsPComponent 2 L := hL'
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    by_cases hLM : L = M
    · subst hLM
      exact hcomm l (hc l hl)
    · obtain ⟨-, hne⟩ := distinct_p_components_core_commutation 2 Nat.prime_two L M hL hM
      obtain ⟨-, -, hcore, -⟩ := hne hLM
      have h1 : ⁅l, u⁆ ∈ ⁅L, M⁆ := Subgroup.commutator_mem_commutator hl hu
      have h2 := (hcore h1).1
      have hLsub : L.IsSubnormal := (isPComponent_two_iff.1 hL).1
      rw [CFSG.ComponentClassification.UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal
        hLsub] at h2
      exact hcomm l h2.2
  have hN : ∀ N : Subgroup (G ⧸ O), N.Normal → Group.IsSolvable ↥N →
      N ≤ centralizer ({q u} : Set (G ⧸ O)) := by
    intro N hNn hNs n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := (CFSG.LocalCores.component_solvable_centralizer hNs hNn.isSubnormal).2
    have h2 : ⁅q u, n⁆ ∈ ⁅layer (G ⧸ O), N⁆ := Subgroup.commutator_mem_commutator hqu hn
    rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  have hN1 := hN _ NOne_normal (isSolvable_NOne h3)
  have hN2 := hN _ NTwo_normal (isSolvable_NTwo h3)
  intro y hy
  have hy' : q y ∈ EPlus (G ⧸ O) := hy
  have hcen : EPlus (G ⧸ O) ≤ centralizer ({q u} : Set (G ⧸ O)) :=
    sup_le (sup_le hlayer hN1) hN2
  have h1 : q y * q u = q u * q y := Subgroup.mem_centralizer_singleton_iff.1 (hcen hy')
  apply (QuotientGroup.eq_one_iff _).1
  show q ⁅y, u⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 h1

variable {X : Type} [Group X] [Finite X]

theorem IsIntrinsicIn.mem_zStar_LPlusIn {H M : Subgroup X} {u : X} (h : IsIntrinsicIn X H M u) :
    u ∈ zStar (LPlusIn H) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMH : M ≤ H := h.2.2.1.1
  have huH : u ∈ H := hMH h.2.1
  have hM' : IsPComponent 2 (M.subgroupOf H) := h.2.2.1.2
  have huM' : (⟨u, huH⟩ : ↥H) ∈ M.subgroupOf H := h.2.1
  have hMsub : (M.subgroupOf H).IsSubnormal := (isPComponent_two_iff.1 hM').1
  have hc : ∀ m ∈ M.subgroupOf H, ⁅m, (⟨u, huH⟩ : ↥H)⁆ ∈ pPrimeCore 2 ↥H := by
    intro m hm
    have h1 : ⁅(m : X), u⁆ ∈ pPrimeCoreOf 2 M := h.comm_mem _ hm
    have h2 : ⁅(m : X), u⁆ ∈ pPrimeCoreOf 2 H :=
      pPrimeCoreOf_le_oddCoreOf hMH hMsub h1
    obtain ⟨w, hw, hwe⟩ := h2
    have : w = ⁅m, (⟨u, huH⟩ : ↥H)⁆ := Subtype.ext hwe
    rwa [← this]
  have hL3 := comm_mem_pPrimeCore_of_mem_LPlus hM' huM' hc
  have huY : u ∈ LPlusIn H := by
    refine ⟨⟨u, huH⟩, ?_, rfl⟩
    rw [LPlus_eq_pLayer_sup_NPlus]
    exact Subgroup.mem_sup_left ((le_sSup hM' : M.subgroupOf H ≤ pLayer ↥H 2) huM')
  refine ⟨huY, Subgroup.le_normalizer huY, mem_normalizer_pPrimeCoreOf_of_mem huY, fun y hy => ?_⟩
  have hy' := hy
  obtain ⟨yG, hyG, rfl⟩ := hy
  have h1 : ⁅yG, (⟨u, huH⟩ : ↥H)⁆ ∈ pPrimeCore 2 ↥H := hL3 yG hyG
  have h2 : ⁅(yG : X), u⁆ ∈ pPrimeCoreOf 2 H := ⟨_, h1, by simp [map_commutatorElement]⟩
  have h3 : ⁅(yG : X), u⁆ ∈ LPlusIn H := by
    rw [commutatorElement_def]
    exact (LPlusIn H).mul_mem ((LPlusIn H).mul_mem ((LPlusIn H).mul_mem hy' huY)
      ((LPlusIn H).inv_mem hy')) ((LPlusIn H).inv_mem huY)
  exact inf_pPrimeCoreOf_le_pPrimeCoreOf (LPlusIn_le H) ⟨h3, h2⟩

omit [Finite X] in
theorem aux_exists_mul_eq_of_mem_zStar_involution_zpow {t : X} (ht2 : t ^ 2 = 1) (k : ℤ) :
    t ^ k = 1 ∨ t ^ k = t := by
  have h2 : t ^ (2 : ℤ) = 1 := by exact_mod_cast ht2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have hk : k = 2 * (k / 2) := by omega
    rw [hk, zpow_mul, h2, one_zpow]
  · right
    have hk : k = 2 * (k / 2) + 1 := by omega
    rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

omit [Finite X] in
theorem aux_exists_mul_eq_of_mem_zStar_involution_comm {t m : X}
    (ht2 : t ^ 2 = 1) (hm : m ∈ normalizer ((Subgroup.zpowers t : Subgroup X) : Set X)) :
    m * t = t * m := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    ((Subgroup.mem_normalizer_iff.1 hm t).1 (Subgroup.mem_zpowers t))
  rcases aux_exists_mul_eq_of_mem_zStar_involution_zpow ht2 k with h | h
  · rw [h] at hk
    have h1 : t = 1 := by
      have h2 : m * t * m⁻¹ = 1 := hk.symm
      simpa using h2
    subst h1
    simp
  · rw [h] at hk
    calc m * t = (m * t * m⁻¹) * m := by group
      _ = t * m := by rw [← hk]

theorem exists_mul_eq_of_mem_zStar_involution {K : Subgroup X} {t : X} (ht : t ∈ zStar K)
    (ht2 : t ^ 2 = 1) {y : X} (hy : y ∈ K) :
    ∃ o ∈ pPrimeCoreOf 2 K, ∃ r ∈ K ⊓ centralizer ({t} : Set X), y = o * r := by
  obtain ⟨htK, -, htP, hcomm⟩ := ht
  have hOK : pPrimeCoreOf 2 K ≤ K := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hZO : Subgroup.zpowers t ≤ normalizer (pPrimeCoreOf 2 K : Set X) :=
    Subgroup.zpowers_le.2 htP
  have hZK : Subgroup.zpowers t ≤ K := Subgroup.zpowers_le.2 htK
  have hAK : pPrimeCoreOf 2 K ⊔ Subgroup.zpowers t ≤ K := sup_le hOK hZK
  have hdec : ∀ a : X, a ∈ pPrimeCoreOf 2 K ⊔ Subgroup.zpowers t →
      ∃ o ∈ pPrimeCoreOf 2 K, ∃ ζ ∈ Subgroup.zpowers t, o * ζ = a := by
    intro a ha
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZO] at ha
    exact ha
  have hct : ∀ c ∈ K, c * t * c⁻¹ ∈ pPrimeCoreOf 2 K ⊔ Subgroup.zpowers t := by
    intro c hc
    have h1 : c * t * c⁻¹ = ⁅c, t⁆ * t := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hcomm c hc))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hAn : ∀ c ∈ K, ∀ a ∈ pPrimeCoreOf 2 K ⊔ Subgroup.zpowers t,
      c * a * c⁻¹ ∈ pPrimeCoreOf 2 K ⊔ Subgroup.zpowers t := by
    intro c hc a ha
    obtain ⟨o, ho, ζ, hζ, rfl⟩ := hdec a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hζ
    have h1 : c * (o * t ^ k) * c⁻¹ = (c * o * c⁻¹) * (c * t * c⁻¹) ^ k := by
      rw [conj_zpow]; group
    rw [h1]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1
        (mem_normalizer_pPrimeCoreOf_of_mem hc) o).1 ho))
      (Subgroup.zpow_mem _ (hct c hc) k)
  have hsyl : IsSylowTwoIn (pPrimeCoreOf 2 K ⊔ Subgroup.zpowers t) (Subgroup.zpowers t) :=
    isSylowTwoIn_of_le_sup_odd le_sup_right (aux_isPGroup_zpowers_of_sq ht2)
      (odd_card_oddCoreOf K) hZO le_rfl
  obtain ⟨a, ha, m, hm, rfl⟩ := exists_mul_mem_normalizer_of_isSylowTwoIn hAK hAn hsyl hy
  obtain ⟨o, ho, ζ, hζ, rfl⟩ := hdec a ha
  have hmt : m * t = t * m := aux_exists_mul_eq_of_mem_zStar_involution_comm ht2 hm.1
  have hζt : ζ * t = t * ζ := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hζ
    exact (Commute.self_zpow t j).eq.symm
  refine ⟨o, ho, ζ * m, ⟨Subgroup.mul_mem _ (hZK hζ) hm.2, ?_⟩, mul_assoc o ζ m⟩
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  calc ζ * m * t = ζ * (m * t) := mul_assoc _ _ _
    _ = ζ * (t * m) := by rw [hmt]
    _ = (ζ * t) * m := (mul_assoc _ _ _).symm
    _ = (t * ζ) * m := by rw [hζt]
    _ = t * (ζ * m) := mul_assoc _ _ _

end Lemma34

end CFSG.OddStandard.Solomon75
