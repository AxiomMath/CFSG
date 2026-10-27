module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WPrimeShapeTable
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdLemmas
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapPair


public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

@[expose] def AllowedPair (n : ℕ) (p : Perm (Fin 8) × Perm (Fin 8)) : Prop :=
  p.1 * p.1 = 1 ∧ p.2 * p.2 = 1 ∧ altCentCard8 p.1 * altCentCard8 p.2 ≤ n
private def wp_allowedIn (n : ℕ) (I : Subgroup (Perm (Fin 8) × Perm (Fin 8))) :
    Set (Perm (Fin 8) × Perm (Fin 8)) :=
  {p | AllowedPair n p ∧ p ∈ (I : Set _)}
private def wp_inv8 (j : ℕ) : Finset (Perm (Fin 8)) :=
  Finset.univ.filter (fun σ => σ.cycleType = Multiset.replicate j 2)
private lemma wp_card_inv8_three : (wp_inv8 3).card = 420 := by
  have h := Equiv.Perm.card_of_cycleType (α := Fin 8) (Multiset.replicate 3 2)
  rw [wp_inv8, h]
  norm_num [Multiset.sum_replicate, Multiset.prod_replicate, Multiset.card_replicate,
    Multiset.toFinset_replicate, Nat.factorial]
private lemma wp_card_inv8_two : (wp_inv8 2).card = 210 := by
  have h := Equiv.Perm.card_of_cycleType (α := Fin 8) (Multiset.replicate 2 2)
  rw [wp_inv8, h]
  norm_num [Multiset.sum_replicate, Multiset.prod_replicate, Multiset.card_replicate,
    Multiset.toFinset_replicate, Nat.factorial]
private lemma wp_mem_inv8_of_card {σ : Perm (Fin 8)} (hσ : σ * σ = 1) {j : ℕ} :
    σ ∈ wp_inv8 j ↔ Multiset.card σ.cycleType = j := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : σ ^ 2 = 1 := by rwa [pow_two]
  have hcyc := Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) h2
  simp only [wp_inv8, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; rw [h, Multiset.card_replicate]
  · intro h; rw [hcyc, h]

private lemma wp_sign_eq_of_mem_inv8 {σ : Perm (Fin 8)} {j : ℕ} (h : σ ∈ wp_inv8 j) :
    sign σ = (-1 : ℤˣ) ^ (j * 2 + j) := by
  have hc : σ.cycleType = Multiset.replicate j 2 := by
    simpa only [wp_inv8, Finset.mem_filter, Finset.mem_univ, true_and] using h
  rw [Equiv.Perm.sign_of_cycleType, hc, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul]

private lemma wp_sign_neg_one_of_mem_inv8_three {σ : Perm (Fin 8)} (h : σ ∈ wp_inv8 3) :
    sign σ = -1 := by
  rw [wp_sign_eq_of_mem_inv8 h]; decide

private lemma wp_sign_one_of_mem_inv8_two {σ : Perm (Fin 8)} (h : σ ∈ wp_inv8 2) :
    sign σ = 1 := by
  rw [wp_sign_eq_of_mem_inv8 h]; decide

private lemma wp_altCentCard8_eq_48_iff {σ : Perm (Fin 8)} (hσ : σ * σ = 1) :
    altCentCard8 σ = 48 ↔ σ ∈ wp_inv8 3 := by
  rw [wp_mem_inv8_of_card hσ]
  constructor
  · intro h
    set k := Multiset.card σ.cycleType with hk
    have hkle : k ≤ 4 := by rw [hk]; exact card_cycleType_le_four hσ
    interval_cases k
    · have h1 : σ = 1 := Equiv.Perm.card_cycleType_eq_zero.mp hk.symm
      rw [h1, altCentCard8_one] at h; omega
    · have h2 := altCentCard8_eq_of_card_cycleType_eq_one hσ hk.symm; omega
    · have h2 := altCentCard8_eq_of_card_cycleType_eq_two hσ hk.symm; omega
    · rfl
    · have h2 := altCentCard8_eq_of_card_cycleType_eq_four hσ hk.symm; omega
  · intro hk; exact altCentCard8_eq_of_card_cycleType_eq_three hσ hk

private lemma wp_altCentCard8_eq_96_iff {σ : Perm (Fin 8)} (hσ : σ * σ = 1) :
    altCentCard8 σ = 96 ↔ σ ∈ wp_inv8 2 := by
  rw [wp_mem_inv8_of_card hσ]
  constructor
  · intro h
    set k := Multiset.card σ.cycleType with hk
    have hkle : k ≤ 4 := by rw [hk]; exact card_cycleType_le_four hσ
    interval_cases k
    · have h1 : σ = 1 := Equiv.Perm.card_cycleType_eq_zero.mp hk.symm
      rw [h1, altCentCard8_one] at h; omega
    · have h2 := altCentCard8_eq_of_card_cycleType_eq_one hσ hk.symm; omega
    · rfl
    · have h2 := altCentCard8_eq_of_card_cycleType_eq_three hσ hk.symm; omega
    · have h2 := altCentCard8_eq_of_card_cycleType_eq_four hσ hk.symm; omega
  · intro hk; exact altCentCard8_eq_of_card_cycleType_eq_two hσ hk

private lemma wp_N10_two : N10 2 = 11520 := by norm_num [N10, Nat.factorial]

private lemma wp_N10_three : N10 3 = 2304 := by norm_num [N10, Nat.factorial]

private lemma wp_sign_mul_eq_of_ne {x y a b : ℤˣ} (hxy : x ≠ y) (hab : a ≠ b) :
    x * a = y * b := by
  rcases Int.units_eq_one_or x with rfl | rfl <;>
    rcases Int.units_eq_one_or y with rfl | rfl <;>
    rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;> simp_all

private theorem wp_sign_eq_of_card_half (I : Subgroup (Perm (Fin 8) × Perm (Fin 8)))
    (hA : ∀ a ∈ alternatingGroup (Fin 8), ∀ b ∈ alternatingGroup (Fin 8), (a, b) ∈ I)
    {g : Perm (Fin 8) × Perm (Fin 8)} (hg : g ∈ I) (hg1 : sign g.1 = -1) (hg2 : sign g.2 = -1)
    (hcard : 2 * Nat.card I = 40320 ^ 2) :
    ∀ u v : Perm (Fin 8), (u, v) ∈ I → sign u = sign v := by
  intro u v huv
  by_contra hne
  have htop : I = ⊤ := by
    rw [eq_top_iff]
    intro p _
    rcases p with ⟨a, b⟩
    by_cases hab : sign a = sign b
    · exact mem_of_sign_eq_of_prod_le I hA hg hg1 hg2 hab
    · have h1 : sign (u⁻¹ * a) = sign (v⁻¹ * b) := by
        rw [map_mul, map_mul, Equiv.Perm.sign_inv, Equiv.Perm.sign_inv]
        exact wp_sign_mul_eq_of_ne hne hab
      have hmem : (u⁻¹ * a, v⁻¹ * b) ∈ I := mem_of_sign_eq_of_prod_le I hA hg hg1 hg2 h1
      have hmul := I.mul_mem huv hmem
      have heq : (u, v) * (u⁻¹ * a, v⁻¹ * b) = (a, b) := by
        ext <;> simp [Equiv.Perm.mul_apply]
      rwa [heq] at hmul
  have hcardperm : Nat.card (Perm (Fin 8)) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hcardPP : Nat.card (Perm (Fin 8) × Perm (Fin 8)) = 40320 ^ 2 := by
    rw [Nat.card_prod, hcardperm]
    norm_num [pow_two]
  have hcardI : Nat.card I = 40320 ^ 2 := by
    rw [htop, Subgroup.card_top]
    exact hcardPP
  rw [hcardI] at hcard
  norm_num at hcard

private lemma wp_five_altCent_cases {p : Perm (Fin 8) × Perm (Fin 8)}
    (hpA : AllowedPair (N10 5) p) :
    (altCentCard8 p.1 = 48 ∨ altCentCard8 p.1 = 96) ∧
      (altCentCard8 p.2 = 48 ∨ altCentCard8 p.2 = 96) ∧
      ¬ (altCentCard8 p.1 = 96 ∧ altCentCard8 p.2 = 96) := by
  obtain ⟨hp1, hp2, hprod⟩ := hpA
  rw [N10_five] at hprod
  have hle1 : altCentCard8 p.1 ≤ 160 := by
    have hmul : altCentCard8 p.1 * 48 ≤ altCentCard8 p.1 * altCentCard8 p.2 :=
      Nat.mul_le_mul_left _ (forty_eight_le_altCentCard8 hp2)
    omega
  have hle2 : altCentCard8 p.2 ≤ 160 := by
    have hmul : altCentCard8 p.2 * 48 ≤ altCentCard8 p.1 * altCentCard8 p.2 := by
      rw [Nat.mul_comm (altCentCard8 p.2) 48]
      exact Nat.mul_le_mul_right _ (forty_eight_le_altCentCard8 hp1)
    omega
  refine ⟨?_, ?_, ?_⟩
  · rcases altCentCard8_mem hp1 with h | h | h | h | h <;> omega
  · rcases altCentCard8_mem hp2 with h | h | h | h | h <;> omega
  · rintro ⟨h1, h2⟩; rw [h1, h2] at hprod; norm_num at hprod

private def wp_fiveUnion : Finset (Perm (Fin 8) × Perm (Fin 8)) :=
  (wp_inv8 3 ×ˢ wp_inv8 3) ∪ (wp_inv8 3 ×ˢ wp_inv8 2) ∪ (wp_inv8 2 ×ˢ wp_inv8 3)

theorem eq_one_of_two_mul_le_N10 {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5)
    (h : 2 * 40320 ≤ N10 k) : k = 1 := by
  interval_cases k <;> norm_num [N10, Nat.factorial] at h <;> rfl

theorem false_of_allowedPair_four {p : Perm (Fin 8) × Perm (Fin 8)}
    (h : AllowedPair (N10 4) p) : False := by
  obtain ⟨hp1, hp2, hprod⟩ := h
  rw [N10_four] at hprod
  have h1 := forty_eight_le_altCentCard8 hp1
  have h2 := forty_eight_le_altCentCard8 hp2
  have : 48 * 48 ≤ 1536 := le_trans (Nat.mul_le_mul h1 h2) hprod
  norm_num at this

theorem false_of_allowedPair_one {p : Perm (Fin 8) × Perm (Fin 8)}
    (h : AllowedPair (N10 1) p) (hD : 20160 ≤ altCentCard8 p.1 ∨ 20160 ≤ altCentCard8 p.2) :
    False := by
  obtain ⟨hp1, hp2, hprod⟩ := h
  rw [N10_one] at hprod
  have h1 := forty_eight_le_altCentCard8 hp1
  have h2 := forty_eight_le_altCentCard8 hp2
  rcases hD with hD | hD
  · have : 20160 * 48 ≤ 161280 := le_trans (Nat.mul_le_mul hD h2) hprod; norm_num at this
  · have : 48 * 20160 ≤ 161280 := le_trans (Nat.mul_le_mul h1 hD) hprod; norm_num at this

theorem false_of_allowedPair_two {p : Perm (Fin 8) × Perm (Fin 8)}
    (h : AllowedPair (N10 2) p) (hD : 360 ≤ altCentCard8 p.1 ∨ 360 ≤ altCentCard8 p.2) :
    False := by
  obtain ⟨hp1, hp2, hprod⟩ := h
  rw [wp_N10_two] at hprod
  have h1 := forty_eight_le_altCentCard8 hp1
  have h2 := forty_eight_le_altCentCard8 hp2
  rcases hD with hD | hD
  · have hge : 720 ≤ altCentCard8 p.1 := by
      rcases altCentCard8_mem hp1 with h' | h' | h' | h' | h' <;> omega
    have : 720 * 48 ≤ 11520 := le_trans (Nat.mul_le_mul hge h2) hprod
    norm_num at this
  · have hge : 720 ≤ altCentCard8 p.2 := by
      rcases altCentCard8_mem hp2 with h' | h' | h' | h' | h' <;> omega
    have : 48 * 720 ≤ 11520 := le_trans (Nat.mul_le_mul h1 hge) hprod
    norm_num at this

theorem false_of_allowedPair_three (I : Subgroup (Perm (Fin 8) × Perm (Fin 8)))
    (hA : ∀ a ∈ alternatingGroup (Fin 8), ∀ b ∈ alternatingGroup (Fin 8), (a, b) ∈ I)
    {g : Perm (Fin 8) × Perm (Fin 8)} (hg : g ∈ I) (hg1 : sign g.1 = -1) (hg2 : sign g.2 = -1)
    (h : 2 * Nat.card I ≤
      N10 3 * {p : Perm (Fin 8) × Perm (Fin 8) | AllowedPair (N10 3) p ∧ p ∈ (I : Set _)}.ncard) :
    False := by
  have hT : 2 * Nat.card I ≤ N10 3 * (wp_allowedIn (N10 3) I).ncard := h
  have hsub : wp_allowedIn (N10 3) I ⊆
      ((wp_inv8 3 ×ˢ wp_inv8 3 : Finset (Perm (Fin 8) × Perm (Fin 8))) : Set _) := by
    intro p hp
    obtain ⟨hpA, -⟩ := hp
    obtain ⟨hp1, hp2, hprod⟩ := hpA
    rw [wp_N10_three] at hprod
    have hmul : altCentCard8 p.1 * 48 ≤ altCentCard8 p.1 * altCentCard8 p.2 :=
      Nat.mul_le_mul_left _ (forty_eight_le_altCentCard8 hp2)
    have hmul' : altCentCard8 p.2 * 48 ≤ altCentCard8 p.1 * altCentCard8 p.2 := by
      rw [Nat.mul_comm (altCentCard8 p.2) 48]
      exact Nat.mul_le_mul_right _ (forty_eight_le_altCentCard8 hp1)
    have h1 : altCentCard8 p.1 = 48 := by
      rcases altCentCard8_mem hp1 with h' | h' | h' | h' | h' <;> omega
    have h2 : altCentCard8 p.2 = 48 := by
      rcases altCentCard8_mem hp2 with h' | h' | h' | h' | h' <;> omega
    simp only [Finset.mem_coe, Finset.mem_product]
    exact ⟨(wp_altCentCard8_eq_48_iff hp1).mp h1, (wp_altCentCard8_eq_48_iff hp2).mp h2⟩
  have hbound : (wp_allowedIn (N10 3) I).ncard ≤ 176400 := by
    calc (wp_allowedIn (N10 3) I).ncard
        ≤ ((wp_inv8 3 ×ˢ wp_inv8 3 : Finset _) : Set _).ncard := Set.ncard_le_ncard hsub
      _ = (wp_inv8 3 ×ˢ wp_inv8 3).card := Set.ncard_coe_finset _
      _ = (wp_inv8 3).card * (wp_inv8 3).card := Finset.card_product _ _
      _ = 420 * 420 := by rw [wp_card_inv8_three]
      _ = 176400 := by norm_num
  have hbig : 2 * Nat.card I ≤ 2304 * 176400 := by
    calc 2 * Nat.card I ≤ N10 3 * (wp_allowedIn (N10 3) I).ncard := hT
      _ = 2304 * (wp_allowedIn (N10 3) I).ncard := by rw [wp_N10_three]
      _ ≤ 2304 * 176400 := Nat.mul_le_mul_left _ hbound
  rcases card_eq_of_prod_le I hA hg hg1 hg2 with hcase | hcase
  · rw [hcase] at hbig; norm_num at hbig
  · rw [hcase] at hbig; norm_num at hbig

theorem false_of_allowedPair_five (I : Subgroup (Perm (Fin 8) × Perm (Fin 8)))
    (hA : ∀ a ∈ alternatingGroup (Fin 8), ∀ b ∈ alternatingGroup (Fin 8), (a, b) ∈ I)
    {g : Perm (Fin 8) × Perm (Fin 8)} (hg : g ∈ I) (hg1 : sign g.1 = -1) (hg2 : sign g.2 = -1)
    (h : 2 * Nat.card I ≤
      N10 5 * {p : Perm (Fin 8) × Perm (Fin 8) | AllowedPair (N10 5) p ∧ p ∈ (I : Set _)}.ncard) :
    False := by
  have hT : 2 * Nat.card I ≤ N10 5 * (wp_allowedIn (N10 5) I).ncard := h
  have hcardUnion : wp_fiveUnion.card ≤ 352800 := by
    have h1 : ((wp_inv8 3 ×ˢ wp_inv8 3) ∪ (wp_inv8 3 ×ˢ wp_inv8 2)).card
        ≤ 420 * 420 + 420 * 210 := by
      have := Finset.card_union_le (wp_inv8 3 ×ˢ wp_inv8 3) (wp_inv8 3 ×ˢ wp_inv8 2)
      simpa only [Finset.card_product, wp_card_inv8_three, wp_card_inv8_two] using this
    have h2 := Finset.card_union_le
      ((wp_inv8 3 ×ˢ wp_inv8 3) ∪ (wp_inv8 3 ×ˢ wp_inv8 2)) (wp_inv8 2 ×ˢ wp_inv8 3)
    simp only [Finset.card_product, wp_card_inv8_three, wp_card_inv8_two] at h2
    dsimp only [wp_fiveUnion]
    omega
  have hsubB : wp_allowedIn (N10 5) I ⊆ (wp_fiveUnion : Set _) := by
    intro p hp
    obtain ⟨hpA, -⟩ := hp
    obtain ⟨h1, h2, hbad⟩ := wp_five_altCent_cases hpA
    obtain ⟨hp1, hp2, -⟩ := hpA
    show p ∈ wp_fiveUnion
    dsimp only [wp_fiveUnion]
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_product, Finset.mem_product,
      Finset.mem_product]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (Or.inl ⟨(wp_altCentCard8_eq_48_iff hp1).mp h1,
        (wp_altCentCard8_eq_48_iff hp2).mp h2⟩)
    · exact Or.inl (Or.inr ⟨(wp_altCentCard8_eq_48_iff hp1).mp h1,
        (wp_altCentCard8_eq_96_iff hp2).mp h2⟩)
    · exact Or.inr ⟨(wp_altCentCard8_eq_96_iff hp1).mp h1, (wp_altCentCard8_eq_48_iff hp2).mp h2⟩
    · exact absurd ⟨h1, h2⟩ hbad
  have hboundB : (wp_allowedIn (N10 5) I).ncard ≤ 352800 := by
    calc (wp_allowedIn (N10 5) I).ncard ≤ (wp_fiveUnion : Set _).ncard :=
          Set.ncard_le_ncard hsubB
      _ = wp_fiveUnion.card := Set.ncard_coe_finset _
      _ ≤ 352800 := hcardUnion
  rcases card_eq_of_prod_le I hA hg hg1 hg2 with hcase | hcase
  · have hsign := wp_sign_eq_of_card_half I hA hg hg1 hg2 hcase
    have hsubA : wp_allowedIn (N10 5) I ⊆
        ((wp_inv8 3 ×ˢ wp_inv8 3 : Finset (Perm (Fin 8) × Perm (Fin 8))) : Set _) := by
      intro p hp
      obtain ⟨hpA, hpI⟩ := hp
      obtain ⟨h1, h2, hbad⟩ := wp_five_altCent_cases hpA
      obtain ⟨hp1, hp2, -⟩ := hpA
      have hpair : altCentCard8 p.1 = 48 ∧ altCentCard8 p.2 = 48 := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact ⟨h1, h2⟩
        · exfalso
          have hs1 := wp_sign_neg_one_of_mem_inv8_three ((wp_altCentCard8_eq_48_iff hp1).mp h1)
          have hs2 := wp_sign_one_of_mem_inv8_two ((wp_altCentCard8_eq_96_iff hp2).mp h2)
          exact (by decide : (-1 : ℤˣ) ≠ 1) (hs1.symm.trans ((hsign p.1 p.2 hpI).trans hs2))
        · exfalso
          have hs1 := wp_sign_one_of_mem_inv8_two ((wp_altCentCard8_eq_96_iff hp1).mp h1)
          have hs2 := wp_sign_neg_one_of_mem_inv8_three ((wp_altCentCard8_eq_48_iff hp2).mp h2)
          exact (by decide : (1 : ℤˣ) ≠ -1) (hs1.symm.trans ((hsign p.1 p.2 hpI).trans hs2))
        · exact absurd ⟨h1, h2⟩ hbad
      simp only [Finset.mem_coe, Finset.mem_product]
      exact ⟨(wp_altCentCard8_eq_48_iff hp1).mp hpair.1,
        (wp_altCentCard8_eq_48_iff hp2).mp hpair.2⟩
    have hboundA : (wp_allowedIn (N10 5) I).ncard ≤ 176400 := by
      calc (wp_allowedIn (N10 5) I).ncard
          ≤ ((wp_inv8 3 ×ˢ wp_inv8 3 : Finset _) : Set _).ncard := Set.ncard_le_ncard hsubA
        _ = (wp_inv8 3 ×ˢ wp_inv8 3).card := Set.ncard_coe_finset _
        _ = (wp_inv8 3).card * (wp_inv8 3).card := Finset.card_product _ _
        _ = 420 * 420 := by rw [wp_card_inv8_three]
        _ = 176400 := by norm_num
    have hle : 2 * Nat.card I ≤ 7680 * 176400 := by
      calc 2 * Nat.card I ≤ N10 5 * (wp_allowedIn (N10 5) I).ncard := hT
        _ = 7680 * (wp_allowedIn (N10 5) I).ncard := by rw [N10_five]
        _ ≤ 7680 * 176400 := Nat.mul_le_mul_left _ hboundA
    rw [hcase] at hle; norm_num at hle
  · have hle : 2 * Nat.card I ≤ 7680 * 352800 := by
      calc 2 * Nat.card I ≤ N10 5 * (wp_allowedIn (N10 5) I).ncard := hT
        _ = 7680 * (wp_allowedIn (N10 5) I).ncard := by rw [N10_five]
        _ ≤ 7680 * 352800 := Nat.mul_le_mul_left _ hboundB
    rw [hcase] at hle; norm_num at hle

end CFSG.OddStandard.AltStdSec.SwapPartner
