module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterSylowBasic
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterTorus
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterLocal

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

namespace EqualParameterData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem exists_core_centralizer (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    {Q₁ : Subgroup G} (hQ₁ : IsSylowOf p Q₁ (C t)) :
    ∃ M : Subgroup G, M ≤ Subgroup.centralizer (Q₁ : Set G) ∧ Odd (Nat.card M) ∧
      (∀ x ∈ Subgroup.centralizer (Q₁ : Set G), Odd (orderOf x) → x ∈ M) ∧
      (∀ x ∈ Subgroup.centralizer (Q₁ : Set G), x ∈ M ⊔ Subgroup.zpowers t) ∧
      ∀ S : Sylow 2 (Subgroup.centralizer (Q₁ : Set G)), Nat.card S = 2 := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL := h.localData
  obtain ⟨hcard, -, -, hCC, -⟩ := h.sylow_C_facts hQ₁
  have hQC : Q₁ ≤ C t := hQ₁.le
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hL.t_sq) hL.t_ne_one
  have htCq : t ∈ Subgroup.centralizer (Q₁ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hQC hy)
  have htp : IsPGroup 2 (Subgroup.zpowers (⟨t, htCq⟩ : Subgroup.centralizer (Q₁ : Set G))) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht2, pow_one]
  obtain ⟨S', hS'⟩ := htp.exists_le_sylow
  have htS : t ∈ (S' : Subgroup (Subgroup.centralizer (Q₁ : Set G))).map
      (Subgroup.centralizer (Q₁ : Set G)).subtype :=
    ⟨⟨t, htCq⟩, hS' (Subgroup.mem_zpowers _), rfl⟩
  have hSCq : (S' : Subgroup (Subgroup.centralizer (Q₁ : Set G))).map
      (Subgroup.centralizer (Q₁ : Set G)).subtype ≤ Subgroup.centralizer (Q₁ : Set G) :=
    Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 ((S' : Subgroup (Subgroup.centralizer (Q₁ : Set G))).map
      (Subgroup.centralizer (Q₁ : Set G)).subtype) := S'.isPGroup'.map _
  have hQ1 : Q₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  have hno4 : ∀ T : Subgroup G, T ≤ (S' : Subgroup (Subgroup.centralizer (Q₁ : Set G))).map
      (Subgroup.centralizer (Q₁ : Set G)).subtype → ¬ IsKleinFour T := by
    intro T hT hT4
    apply hQ1
    refine h.eq_bot_of_le_centralizer_kleinFour.2 T Q₁ hT4 hQ₁.isPGroup ?_
    rw [Subgroup.le_centralizer_iff]
    exact hT.trans hSCq
  have hSt : (S' : Subgroup (Subgroup.centralizer (Q₁ : Set G))).map
      (Subgroup.centralizer (Q₁ : Set G)).subtype ≤ C t :=
    le_centralizer_of_isPGroup_two_of_no_kleinFour hS2 hno4 htS ht2
  have hSle : (S' : Subgroup (Subgroup.centralizer (Q₁ : Set G))).map
      (Subgroup.centralizer (Q₁ : Set G)).subtype ≤
        C t ⊓ Subgroup.centralizer (Q₁ : Set G) := le_inf hSt hSCq
  rw [hCC] at hSle
  have hBnorm : Q₁ ≤ Subgroup.normalizer (((N t).map (C t).subtype : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_of_conj_mem fun y hy => hL.B_conj x (hQC hx) y hy
  have hQB := card_sup_dvd_mul_of_le_normalizer hBnorm
  have htnorm : Q₁ ⊔ (N t).map (C t).subtype ≤
      Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro x hx
    have hxC : x ∈ C t := sup_le hQC hL.B_le hx
    have hc : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp hxC
    apply mem_normalizer_of_conj_mem
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers t k
  have hQBt := card_sup_dvd_mul_of_le_normalizer htnorm
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hdvd : 2 ^ k ∣ 2 * (Nat.card Q₁ * Nat.card ((N t).map (C t).subtype)) := by
    rw [← hk, mul_comm 2]
    refine (Subgroup.card_dvd_of_le hSle).trans (hQBt.trans ?_)
    rw [Nat.card_zpowers, ht2]
    exact Nat.mul_dvd_mul_right hQB 2
  have hodd : Odd (Nat.card Q₁ * Nat.card ((N t).map (C t).subtype)) := by
    rw [hcard]
    exact h.odd.pow.mul h.odd_card_B
  have hdvd2 : 2 ^ k ∣ 2 :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)).dvd_of_dvd_mul_right hdvd
  have hScard : Nat.card ((S' : Subgroup (Subgroup.centralizer (Q₁ : Set G))).map
      (Subgroup.centralizer (Q₁ : Set G)).subtype) = 2 := by
    rw [hk]
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
    · exfalso
      rw [← hk, Subgroup.card_eq_one] at h1
      rw [h1, Subgroup.mem_bot] at htS
      exact hL.t_ne_one htS
    · exact h1
  have hS'card : Nat.card S' = 2 :=
    (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm.trans hScard
  have hall : ∀ T : Sylow 2 (Subgroup.centralizer (Q₁ : Set G)), Nat.card T = 2 := by
    intro T
    exact (Sylow.card_eq_multiplicity T).trans ((Sylow.card_eq_multiplicity S').symm.trans hS'card)
  have hcyc : IsCyclic (S' : Subgroup (Subgroup.centralizer (Q₁ : Set G))) :=
    isCyclic_of_prime_card (p := 2) hS'card
  have hS'eq : (S' : Subgroup (Subgroup.centralizer (Q₁ : Set G))) =
      Subgroup.zpowers ⟨t, htCq⟩ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hS'
    rw [hS'card, Nat.card_zpowers, Subgroup.orderOf_mk, ht2]
  obtain ⟨-, hprod, -, -, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S' hcyc
  refine ⟨(CFSG.pPrimeCore 2 (Subgroup.centralizer (Q₁ : Set G))).map
      (Subgroup.centralizer (Q₁ : Set G)).subtype, Subgroup.map_subtype_le _, ?_,
    (odd_mem_pPrimeCore_of_isCyclic_sylow S' hcyc).2, ?_, hall⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2))
  · intro x hx
    have hmem := Set.mem_univ (⟨x, hx⟩ : Subgroup.centralizer (Q₁ : Set G))
    rw [← hprod] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
    have hb' : b ∈ Subgroup.zpowers (⟨t, htCq⟩ : Subgroup.centralizer (Q₁ : Set G)) := by
      rw [← hS'eq]
      exact hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have hx' : x = (a : G) * t ^ j := by
      have := congrArg Subtype.val hab
      simpa using this.symm
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, ha, rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers t j))

theorem exists_odd_sup
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 3) {Q₁ : Subgroup G} (hQ₁ : IsSylowOf p Q₁ (C t))
    (hsW : Subgroup.zpowers s₀ ⊔ torusW G t s₀ ≤ Subgroup.normalizer (Q₁ : Set G))
    (hCN : C t ⊓ Subgroup.normalizer (Q₁ : Set G) =
      Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔
        (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)) :
    ∃ R : Subgroup G, Odd (Nat.card R) ∧ torusW G t s₀ ≤ R ∧ (N t).map (C t).subtype ≤ R ∧
      Q₁ ≤ R ∧ R ≤ Subgroup.normalizer (Q₁ : Set G) ∧
      Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (R : Set G) ∧
      R ⊓ torusH G t s₀ = torusW G t s₀ ⊔ (N t).map (C t).subtype ∧
      ∀ x ∈ Subgroup.normalizer (Q₁ : Set G), Odd (orderOf x) → x ∈ R := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hL := h.localData
  obtain ⟨hcard, -, hab, hCC, -⟩ := h.sylow_C_facts hQ₁
  obtain ⟨M, hMC, hModd, hMmem, hMdec, hS2⟩ := h.exists_core_centralizer hQ₁
  have hQC : Q₁ ≤ C t := hQ₁.le
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hL.t_sq) hL.t_ne_one
  have htCq : t ∈ Subgroup.centralizer (Q₁ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hQC hy)
  have hCqN : Subgroup.centralizer (Q₁ : Set G) ≤ Subgroup.normalizer (Q₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hWV : torusW G t s₀ ≤ Subgroup.centralizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G) := by
    rw [torusW]
    exact Subgroup.map_subtype_le _
  have htW : t ∈ Subgroup.normalizer ((torusW G t s₀ : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem fun w hw => by
      rw [(h.mem_centralizer_V_iff.mp (hWV hw)).1, mul_inv_cancel_right]
      exact hw
  have hsW' : s₀ ∈ Subgroup.normalizer ((torusW G t s₀ : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem fun w hw => by
      rw [(h.mem_centralizer_V_iff.mp (hWV hw)).2, mul_inv_cancel_right]
      exact hw
  have hWN : torusW G t s₀ ≤ Subgroup.normalizer (Q₁ : Set G) := le_sup_right.trans hsW
  have hsN : s₀ ∈ Subgroup.normalizer (Q₁ : Set G) :=
    hsW (Subgroup.mem_sup_left (Subgroup.mem_zpowers s₀))
  have hNM : Subgroup.normalizer (Q₁ : Set G) ≤ Subgroup.normalizer (M : Set G) := by
    intro g hg
    apply mem_normalizer_of_conj_mem
    intro m hm
    apply hMmem _ (conj_mem_centralizer hg (hMC hm))
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact Odd.of_dvd_nat hModd (Subgroup.orderOf_dvd_natCard _ hm)
  have hRodd : Odd (Nat.card (torusW G t s₀ ⊔ M : Subgroup G)) :=
    Odd.of_dvd_nat (h.odd_card_W.mul hModd) (card_sup_dvd_mul_of_le_normalizer (hWN.trans hNM))
  have hQM : Q₁ ≤ M := fun x hx =>
    hMmem x (Subgroup.mem_centralizer_iff.mpr fun y hy => hab y hy x hx)
      (Odd.of_dvd_nat h.odd.pow (hcard ▸ Subgroup.orderOf_dvd_natCard _ hx))
  have hBCq : (N t).map (C t).subtype ≤ Subgroup.centralizer (Q₁ : Set G) := by
    have : (N t).map (C t).subtype ≤ C t ⊓ Subgroup.centralizer (Q₁ : Set G) := by
      rw [hCC]
      exact (le_sup_right : (N t).map (C t).subtype ≤ Q₁ ⊔ (N t).map (C t).subtype).trans
        le_sup_left
    exact this.trans inf_le_right
  have hBM : (N t).map (C t).subtype ≤ M := fun x hx => hMmem x (hBCq hx) (hL.B_odd x hx)
  have hRN : torusW G t s₀ ⊔ M ≤ Subgroup.normalizer (Q₁ : Set G) :=
    sup_le hWN (hMC.trans hCqN)
  have hVR : Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤
      Subgroup.normalizer ((torusW G t s₀ ⊔ M : Subgroup G) : Set G) := by
    rw [sup_le_iff, Subgroup.zpowers_le, Subgroup.zpowers_le]
    exact ⟨sup_mem_normalizer htW (hNM (hCqN htCq)), sup_mem_normalizer hsW' (hNM hsN)⟩
  have hRH : (torusW G t s₀ ⊔ M) ⊓ torusH G t s₀ = torusW G t s₀ ⊔ (N t).map (C t).subtype := by
    apply h.odd_subgroup_H_eq_of_mod_four_eq_three he inf_le_right
    · exact Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le inf_le_left)
    · exact le_inf (sup_le le_sup_left (hBM.trans le_sup_right)) (sup_le h.W_le_H' h.B_le_H')
  have hV2 : IsPGroup 2 (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) := by
    have := h.isKleinFour_V
    exact IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  refine ⟨torusW G t s₀ ⊔ M, hRodd, le_sup_left, hBM.trans le_sup_right, hQM.trans le_sup_right,
    hRN, hVR, hRH, ?_⟩
  intro x hx hxodd
  obtain ⟨c, hc, hcx⟩ := exists_mul_mem_centralizer_of_card_sylow_two htCq ht2 hS2
    (mem_normalizer_centralizer_of_mem hx)
  have h1 : c * x ∈ C t ⊓ Subgroup.normalizer (Q₁ : Set G) :=
    ⟨hcx, Subgroup.mul_mem _ (hCqN hc) hx⟩
  rw [hCN] at h1
  have hle1 : Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔
      (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀) ≤
        (torusW G t s₀ ⊔ M) ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀) :=
    sup_le_sup_right (sup_le (sup_le (hQM.trans le_sup_right) le_sup_left)
      (hBM.trans le_sup_right)) _
  have hle2 : M ⊔ Subgroup.zpowers t ≤
      (torusW G t s₀ ⊔ M) ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀) :=
    sup_le_sup le_sup_right le_sup_left
  have h2 : x ∈ (torusW G t s₀ ⊔ M) ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hle2 (hMdec c hc))) (hle1 h1)
    rwa [inv_mul_cancel_left] at this
  exact mem_of_odd_of_mem_sup hVR hV2 h2 hxodd

end EqualParameterData

end CFSG.Semidihedral.FixedCoreNontrivial
