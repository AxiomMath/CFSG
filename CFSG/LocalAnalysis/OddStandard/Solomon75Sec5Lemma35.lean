module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseF4

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.Goldschmidt

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem lemma35_inv {n : ℕ} {Z N : Subgroup X} (hZ : IsPGroup 2 ↥Z)
    (hN : N = normalizer (Z : Set X))
    (h33 : ∀ s : X, s ∈ N → orderOf s = 2 →
      (∀ k ∈ K0 X n N, ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n N)) →
      centralizer ({s} : Set X) =
        oddCoreOf (centralizer ({s} : Set X)) ⊔ (N ⊓ centralizer ({s} : Set X)))
    (S : Sylow 2 ↥N)
    (hT : ∀ c ∈ N, c * c = 1 →
      (∀ y ∈ (S : Subgroup ↥N).map N.subtype ⊓ K0 X n N, c * y = y * c) →
        ∀ k ∈ K0 X n N, ⁅k, c⁆ ∈ pPrimeCoreOf 2 (K0 X n N)) :
    IsSylowTwoIn (⊤ : Subgroup X) ((S : Subgroup ↥N).map N.subtype) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set SX : Subgroup X := (S : Subgroup ↥N).map N.subtype with hSX
  have hSXp : IsPGroup 2 ↥SX := S.isPGroup'.map N.subtype
  have hZSX : Z ≤ SX := le_map_sylow_of_isPGroup_normalizer hZ hN S
  obtain ⟨S₀, hS₀⟩ := hSXp.exists_le_sylow
  have hmain : SX = (S₀ : Subgroup X) := by
    by_cases h1 : (S₀ : Subgroup X) = ⊥
    · rw [h1] at hS₀ ⊢
      exact le_bot_iff.1 hS₀
    have hnt : Nontrivial ↥(S₀ : Subgroup X) := (Subgroup.nontrivial_iff_ne_bot _).2 h1
    have hcn : Nontrivial ↥(Subgroup.center ↥(S₀ : Subgroup X)) :=
      S₀.isPGroup'.center_nontrivial
    have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥(S₀ : Subgroup X)) := by
      obtain ⟨k, hk⟩ :=
        (S₀.isPGroup'.to_subgroup (Subgroup.center ↥(S₀ : Subgroup X))).exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        have h1' : Nat.card ↥(Subgroup.center ↥(S₀ : Subgroup X)) = 1 := by simpa using hk
        exact (Finite.one_lt_card_iff_nontrivial.2 hcn).ne' (by
          simpa [Nat.card_eq_fintype_card] using h1')
      rw [hk]
      exact dvd_pow_self 2 hk0
    obtain ⟨s, hs2⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    set s₀ : ↥(S₀ : Subgroup X) := (s : ↥(S₀ : Subgroup X)) with hs₀
    set sX : X := (s₀ : X) with hsX
    have hs₀c : ∀ y : ↥(S₀ : Subgroup X), y * s₀ = s₀ * y := fun y =>
      (Subgroup.mem_center_iff.1 s.2 y)
    have hsXc : ∀ y ∈ (S₀ : Subgroup X), y * sX = sX * y := fun y hy => by
      have := congrArg (fun w : ↥(S₀ : Subgroup X) => (w : X)) (hs₀c ⟨y, hy⟩)
      simpa using this
    have hsX2 : orderOf sX = 2 := by
      rw [hsX, Subgroup.orderOf_coe, hs₀, Subgroup.orderOf_coe]
      exact hs2
    have hsC : sX ∈ centralizer (Z : Set X) :=
      Subgroup.mem_centralizer_iff.2 fun z hz => hsXc z (hS₀ (hZSX hz))
    have hsN : sX ∈ N := hN ▸ Subgroup.centralizer_le_normalizer (Z : Set X) hsC
    have hcomm : ∀ y ∈ SX ⊓ K0 X n N, sX * y = y * sX := fun y hy =>
      (hsXc y (hS₀ hy.1)).symm
    have hsXsq : sX * sX = 1 := by
      have := pow_orderOf_eq_one sX
      rwa [hsX2, sq] at this
    have hC := h33 sX hsN hsX2 (hT sX hsN hsXsq hcomm)
    set C : Subgroup X := centralizer ({sX} : Set X) with hCdef
    have hS₀C : (S₀ : Subgroup X) ≤ C := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (hsXc y hy)
    set Oc : Subgroup X := oddCoreOf C with hOc
    set CN : Subgroup X := N ⊓ C with hCN
    have hOcodd : Odd (Nat.card Oc) := odd_card_oddCoreOf C
    have hCcard : Nat.card C ∣ Nat.card Oc * Nat.card CN := by
      have hOn : (Oc.subgroupOf C).Normal := by
        rw [hOc, oddCoreOf_subgroupOf]
        infer_instance
      have hsup : CN.subgroupOf C ⊔ Oc.subgroupOf C = ⊤ := by
        have h1 : (Oc ⊔ CN).subgroupOf C = Oc.subgroupOf C ⊔ CN.subgroupOf C :=
          Subgroup.subgroupOf_sup (oddCoreOf_le C) inf_le_right
        rw [← hC, Subgroup.subgroupOf_self] at h1
        rw [sup_comm, ← h1]
      have h2 := Subgroup.relIndex_sup_right (H := CN.subgroupOf C) (K := Oc.subgroupOf C)
      rw [hsup, Subgroup.relIndex_top_right] at h2
      have h3 : (Oc.subgroupOf C).relIndex (CN.subgroupOf C) ∣ Nat.card (CN.subgroupOf C) :=
        Subgroup.relIndex_dvd_card _ _
      have h4 := Subgroup.index_mul_card (H := Oc.subgroupOf C)
      have hc1 : Nat.card (CN.subgroupOf C) = Nat.card CN :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      have hc2 : Nat.card (Oc.subgroupOf C) = Nat.card Oc :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (oddCoreOf_le C)).toEquiv
      rw [hc2, h2] at h4
      rw [← h4, mul_comm]
      exact mul_dvd_mul_left _ (hc1 ▸ h3)
    have hS₀card : Nat.card (S₀ : Subgroup X) ∣ Nat.card CN := by
      have h1 : Nat.card (S₀ : Subgroup X) ∣ Nat.card Oc * Nat.card CN :=
        (Subgroup.card_dvd_of_le hS₀C).trans hCcard
      obtain ⟨k, hk⟩ := S₀.isPGroup'.exists_card_eq
      have hcop : Nat.Coprime (Nat.card (S₀ : Subgroup X)) (Nat.card Oc) := by
        rw [hk]
        exact (Nat.coprime_two_left.2 hOcodd).pow_left k
      exact hcop.dvd_of_dvd_mul_left h1
    have hCNN : Nat.card CN ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    have hS₀N : Nat.card (S₀ : Subgroup X) ∣ Nat.card N := hS₀card.trans hCNN
    obtain ⟨k, hk⟩ := S₀.isPGroup'.exists_card_eq
    have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
    have hk' : k ≤ (Nat.card N).factorization 2 := by
      rw [hk] at hS₀N
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).1 hS₀N
    have hSX_card : Nat.card SX = 2 ^ (Nat.card N).factorization 2 := by
      rw [hSX, Subgroup.card_map_of_injective N.subtype_injective]
      exact S.card_eq_multiplicity
    have hle : Nat.card (S₀ : Subgroup X) ≤ Nat.card SX := by
      rw [hk, hSX_card]
      exact Nat.pow_le_pow_right (by norm_num) hk'
    exact Subgroup.eq_of_le_of_card_ge hS₀ hle
  have hSXS₀ : IsSylowTwoIn (⊤ : Subgroup X) SX := by
    rw [hmain]
    refine ⟨le_top, S₀.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S₀.not_dvd_index
  exact hSXS₀


theorem lemma35_of_n {n : ℕ} (hn : 8 ≤ n) {Z : Subgroup X} (hZ : IsPGroup 2 ↥Z)
    (h33 : Lemma33a X n Z) (S : Sylow 2 ↥(normalizer (Z : Set X))) :
    IsSylowTwoIn (⊤ : Subgroup X)
      ((S : Subgroup ↥(normalizer (Z : Set X))).map (normalizer (Z : Set X)).subtype) :=
  lemma35_inv hZ rfl h33 S fun _ hcN hc2 hc =>
    comm_mem_oddCoreOf_of_centralizes_sylow hn S hcN hc2 hc

theorem SolCEx.lemma52_of_n (h : SolCEx X) (hGold : CoreStatement) {n : ℕ} (hn : 8 ≤ n) {z : X}
    {Z : Subgroup X} (hp : IsSec5Pair X n z Z) (ha : Lemma33b X n Z) (hb : Lemma33a X n Z)
    (hc : Lemma34K X n Z) (S : Sylow 2 ↥(normalizer (Z : Set X))) : Lemma52 X n Z S := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := lemma35_of_n hn hp.isPGroup hb S
  refine ⟨ha, hb, hc, hd, ?_⟩
  set T : Subgroup X := (S : Subgroup ↥(normalizer (Z : Set X))).map
    (normalizer (Z : Set X)).subtype with hT
  have hTidx : ¬ 2 ∣ T.index := by
    have := hd.2.2
    rwa [Subgroup.relIndex_top_right] at this
  let S₀ : Sylow 2 X := hd.2.1.toSylow hTidx
  have hZS₀ : Z ≤ (S₀ : Subgroup X) :=
    le_map_sylow_of_isPGroup_normalizer hp.isPGroup rfl S
  exact h.lemma36_set hGold hp S₀ hZS₀

end CFSG.OddStandard.Solomon75
