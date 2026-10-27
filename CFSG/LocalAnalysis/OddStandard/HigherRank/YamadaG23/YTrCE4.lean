module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement Pointwise

private lemma commutatorElement_mul_mul_of_central {G : Type} [Group G] {Z K N : Subgroup G}
    (hZN : Z ≤ N) (hKN : K ≤ N) (hZc : ∀ z ∈ Z, ∀ g ∈ N, z * g = g * z)
    {z₁ k₁ z₂ k₂ : G} (hz₁ : z₁ ∈ Z) (hk₁ : k₁ ∈ K) (hz₂ : z₂ ∈ Z) (hk₂ : k₂ ∈ K) :
    ⁅z₁ * k₁, z₂ * k₂⁆ = ⁅k₁, k₂⁆ := by
  have hk₁N : k₁ ∈ N := hKN hk₁
  have hk₂N : k₂ ∈ N := hKN hk₂
  have hc₁ : ⁅k₁, z₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hZc z₂ hz₂ k₁ hk₁N).symm
  have hc₂ : ⁅z₁, z₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hZc z₁ hz₁ z₂ (hZN hz₂))
  have hc₃ : ⁅z₁, k₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hZc z₁ hz₁ k₂ hk₂N)
  have hcN : ⁅k₁, k₂⁆ ∈ N :=
    Subgroup.commutator_le_self N (commutator_mem_commutator hk₁N hk₂N)
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_mul_right_eq_mul_conj, hc₁, hc₂, hc₃]
  simp only [one_mul, mul_one, inv_one]
  have hinner : z₂ * ⁅k₁, k₂⁆ * z₂⁻¹ = ⁅k₁, k₂⁆ := by
    rw [hZc z₂ hz₂ ⁅k₁, k₂⁆ hcN]; group
  rw [hinner, hZc z₁ hz₁ ⁅k₁, k₂⁆ hcN]
  group

theorem centExt_comm_complement {G : Type} [Group G] [Finite G] {N N₁ Z A F : Subgroup G}
    (hZN : Z ≤ N) (hZc : ∀ z ∈ Z, ∀ g ∈ N, z * g = g * z) (hZ3 : Nat.card ↥Z ∣ 3)
    (hFN : F ≤ N) (hFE : IsE 3 ↥F) (hFn : ∀ g ∈ N, ∀ f ∈ F, g * f * g⁻¹ ∈ F)
    (hCF : ∀ g ∈ N, (∀ f ∈ F, g * f = f * g) → g ∈ Z ⊔ F)
    (hQ : SecProp N (Z ⊔ F)
      (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))))
    (hN₁ : N₁ ≤ N) (hZA : Z ⊔ A ≤ N₁) (hA2 : IsPGroup 2 ↥A)
    (hAn : ∀ g ∈ N₁, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hQ₁ : SecProp N₁ (Z ⊔ A) (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))) :
    ⁅N, N⁆ ⊔ Z = N ∧ ⁅N, N⁆ ⊓ Z = ⊥ := by
  have hF_le : F ≤ ⁅N, N⁆ := centExt_F_le_comm hZN hFN hZc hZ3 hFn hFE hCF hQ
  have hcomm_sup : ⁅N, N⁆ ⊔ (Z ⊔ F) = N := centExt_comm_sup_eq (sup_le hZN hFN) hQ
  have hsup : (⁅N, N⁆ ⊔ Z) ⊔ F = N := by rw [sup_assoc, hcomm_sup]
  have hN_eq : ⁅N, N⁆ ⊔ Z = N := by
    rw [sup_eq_left.mpr (hF_le.trans le_sup_left)] at hsup
    exact hsup
  refine ⟨hN_eq, ?_⟩
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hZ3 with hZ1 | hZ3card
  · have hZbot : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z hZ1
    rw [hZbot, inf_bot_eq]
  · have hFcard : Nat.card ↥F = 8 := by rw [hFE.2]; norm_num
    have hZF : Z ⊓ F = ⊥ :=
      disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by rw [hZ3card, hFcard]; norm_num))
    have hFcent : F ≤ Subgroup.centralizer (Z : Set G) := by
      intro f hf
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact hZc z hz f (hFN hf)
    have hFnorm : F ≤ Subgroup.normalizer (Z : Set G) :=
      hFcent.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
    have hZFcard : Nat.card ↥(Z ⊔ F) = 24 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z F hFnorm
        (disjoint_iff.mpr hZF), hZ3card, hFcard]
    have hNcard : Nat.card ↥N = 4032 := by
      rw [centExt_card_of_secProp_gl32 (sup_le hZN hFN) hQ, hZFcard]
    obtain ⟨κ, hκN₁, hκ3, hκn⟩ :=
      exists_threeElem_not_mem_of_secProp_perm3 (hKN := hZA) hQ₁
    have hκN : κ ∈ N := hN₁ hκN₁
    have hκcube : κ ^ 3 = 1 :=
      centExt_cube_eq_one hZA (fun z hz g hg => hZc z hz g (hN₁ hg)) hZ3 hA2 hAn hQ₁ hκN₁ hκ3 hκn
    have hκZ : κ ∉ Z := fun h => hκn (Subgroup.mem_sup_left h)
    have hκne : κ ≠ 1 := fun h => hκZ (h ▸ Z.one_mem)
    have hκord : orderOf κ = 3 := by
      have hdvd : orderOf κ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hκcube
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hκne
      · exact h
    have hK₀card : Nat.card ↥(zpowers κ) = 3 := by rw [Nat.card_zpowers, hκord]
    have hZK₀ : Z ⊓ zpowers κ = ⊥ := by
      haveI : Fact (Nat.card ↥Z).Prime := ⟨by rw [hZ3card]; norm_num⟩
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((Z ⊓ zpowers κ).subgroupOf Z) with h | h
      · have h' : (Z ⊓ zpowers κ) ⊓ Z = ⊥ := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
        simpa [inf_assoc, inf_comm, inf_left_comm, inf_idem] using h'
      · have hZle : Z ≤ zpowers κ := (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_right
        have hZeq : Z = zpowers κ := Subgroup.eq_of_le_of_card_ge hZle (by omega)
        exact absurd (by rw [hZeq]; exact Subgroup.mem_zpowers κ) hκZ
    have hZP : Z ≤ Z ⊔ zpowers κ := le_sup_left
    have hK₀P : zpowers κ ≤ Z ⊔ zpowers κ := le_sup_right
    have hPN : Z ⊔ zpowers κ ≤ N := sup_le hZN (Subgroup.zpowers_le.mpr hκN)
    have hPcard : Nat.card ↥(Z ⊔ zpowers κ) = 9 := by
      have hK₀cent : zpowers κ ≤ Subgroup.centralizer (Z : Set G) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro z hz
        exact hZc z hz κ hκN
      have hK₀norm : zpowers κ ≤ Subgroup.normalizer (Z : Set G) :=
        hK₀cent.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z (zpowers κ)
        hK₀norm (disjoint_iff.mpr hZK₀), hZ3card, hK₀card]
    have hPpg : IsPGroup 3 ↥(Z ⊔ zpowers κ) :=
      IsPGroup.of_card (p := 3) (n := 2) (by rw [hPcard]; norm_num)
    have hPrel : ¬ 3 ∣ (Z ⊔ zpowers κ).relIndex N := by
      have hrel : (Z ⊔ zpowers κ).relIndex N * Nat.card ↥((Z ⊔ zpowers κ) ⊓ N) = Nat.card ↥N :=
        Subgroup.relIndex_mul_card (Z ⊔ zpowers κ) N
      rw [inf_eq_left.mpr hPN, hPcard, hNcard] at hrel
      have h448 : (Z ⊔ zpowers κ).relIndex N = 448 := by omega
      rw [h448]; norm_num
    have hZpg : IsPGroup 3 ↥Z :=
      IsPGroup.of_card (p := 3) (n := 1) (by rw [hZ3card]; norm_num)
    obtain ⟨K, hKN, hZK, hZKN⟩ :=
      centExt_split_of_sylow_split (K₀ := zpowers κ) hZN hZc hZpg hPN hPpg hPrel hZP hK₀P hZK₀ rfl
    have hN'_le_K : ⁅N, N⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have hKcent : K ≤ Subgroup.centralizer (Z : Set G) := by
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact hZc z hz k (hKN hk)
      have hKnorm : K ≤ Subgroup.normalizer (Z : Set G) :=
        hKcent.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
      have hcoe : (N : Set G) = (Z : Set G) * (K : Set G) := by
        rw [← hZKN, Subgroup.coe_mul_of_right_le_normalizer_left Z K hKnorm]
      have hg₁' : g₁ ∈ (Z : Set G) * (K : Set G) := by rw [← hcoe]; exact hg₁
      have hg₂' : g₂ ∈ (Z : Set G) * (K : Set G) := by rw [← hcoe]; exact hg₂
      rw [Set.mem_mul] at hg₁' hg₂'
      obtain ⟨z₁, hz₁, k₁, hk₁, rfl⟩ := hg₁'
      obtain ⟨z₂, hz₂, k₂, hk₂, rfl⟩ := hg₂'
      rw [commutatorElement_mul_mul_of_central hZN hKN hZc hz₁ hk₁ hz₂ hk₂]
      exact Subgroup.commutator_le_self K (commutator_mem_commutator hk₁ hk₂)
    have hle : ⁅N, N⁆ ⊓ Z ≤ K ⊓ Z := inf_le_inf_right Z hN'_le_K
    rw [inf_comm K Z, hZK] at hle
    exact le_bot_iff.mp hle

end CFSG.OddStandard.HigherRank.YamadaG23
