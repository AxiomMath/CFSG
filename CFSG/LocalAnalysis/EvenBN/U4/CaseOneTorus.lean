module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseOnePrelim
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusEight

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup)
open scoped MatrixGroups

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)


theorem exists_transitive_torus_V2 (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂]
    [Fintype k₂] (hk₂ : Fintype.card k₂ = (2 ^ f) ^ 2)
    (ψ : miyamotoM2G h L η t Q ≃* SL(2, k₂)) :
    ∃ J : Subgroup G, J ≤ normalizer (𝓦 : Set G) ∧
      J ≤ normalizer (miyamotoEG h L η Q : Set G) ∧
      ∀ a ∈ 𝓥, ∀ b ∈ 𝓥, a ≠ 1 → b ≠ 1 → ∃ j ∈ J, j * a * j⁻¹ = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k₂ 2 := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [hk₂, ← pow_mul, mul_comm])
  set M := miyamotoM2G h L η t Q with hMdef
  obtain ⟨hMH, -, hNM, -, hVM, -, -, -⟩ := hS.sec3_12_two
  obtain ⟨d, hd⟩ := (isCyclic_miyamotoIN2G h L η).exists_generator
  have hdM : (d : G) ∈ M := hNM (mem_inf.1 d.2).2
  set d' : M := ⟨d, hdM⟩ with hd'
  have hcardIN := card_miyamotoIN2G h L η
  have hq4 := hS.four_le
  have hd1 : (d : G) ≠ 1 := by
    intro e
    have hall : ∀ x : miyamotoIN2G h L η, x = 1 := fun x => by
      obtain ⟨n, hn⟩ := hd x
      rw [← hn]
      simp only [show d = 1 from Subtype.ext e, one_zpow]
    have : Nat.card (miyamotoIN2G h L η) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => by rw [hall x, hall y]⟩, ⟨1⟩⟩
    omega
  have hd'1 : d' ≠ 1 := fun e => hd1 (by simpa [hd'] using congrArg Subtype.val e)
  have hdpow : (d : G) ^ (Nat.card k₂ - 1) = 1 := by
    have e : d ^ Nat.card (miyamotoIN2G h L η) = 1 := pow_card_eq_one'
    rw [hcardIN] at e
    have e' : (d : G) ^ (2 ^ f - 1) = 1 := by simpa using congrArg Subtype.val e
    rw [Nat.card_eq_fintype_card, hk₂]
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ f = m + 1 :=
      ⟨2 ^ f - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    have e2 : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      rw [hm, Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 1 + 1) + 1 by ring,
        Nat.add_sub_cancel]
    rw [e2, pow_mul, e', one_pow]
  have hd'pow : d' ^ (Nat.card k₂ - 1) = 1 := Subtype.ext (by simpa [hd'] using hdpow)
  have hVcard : Nat.card (𝓥 : Subgroup G) = Nat.card k₂ := by
    rw [hS.card_V2, Nat.card_eq_fintype_card, hk₂]
  have hdV : (d : G) ∈ normalizer ((𝓥 : Subgroup G) : Set G) := hS.IN2G_le_normalizer_V2 d.2
  set V' : Subgroup M := (𝓥 : Subgroup G).subgroupOf M with hV'
  have hV'card : Nat.card V' = Nat.card k₂ := by
    rw [hV', Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv, hVcard]
  have hd'V : d' ∈ normalizer (V' : Set M) := by
    rw [mem_normalizer_iff]
    intro v
    exact mem_normalizer_iff.1 (hS.IN2G_le_normalizer_V2 d.2) v
  have hCN := Common.centralizer_zpowers_le_normalizer ψ hd'1 hd'pow hV'card hd'V
  set J : Subgroup G := (centralizer (zpowers d' : Set M)).map M.subtype with hJ
  have hJM : J ≤ M := map_subtype_le _
  have hJC : J ≤ centralizer (miyamotoIN2G h L η : Set G) := by
    rintro _ ⟨j, hj, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨n, hn⟩ := hd ⟨y, hy⟩
    have hyn : y = (d : G) ^ n := by
      have := congrArg Subtype.val hn
      simp only [SubgroupClass.coe_zpow] at this
      exact this.symm
    have hc := congrArg Subtype.val
      (mem_centralizer_iff.1 hj (d' ^ n) (zpow_mem_zpowers d' n))
    simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow, hd'] at hc
    rw [hyn]
    exact hc
  have hJV : J ≤ normalizer (𝓥 : Set G) := by
    rintro _ ⟨j, hj, rfl⟩
    refine mem_normalizer_fintype fun v hv => ?_
    have hv' : (⟨v, hVM hv⟩ : M) ∈ V' := hv
    exact (mem_normalizer_iff.1 (hCN hj) ⟨v, hVM hv⟩).1 hv'
  refine ⟨J, fun j hj => ?_, fun j hj => ?_, fun a ha b hb ha1 hb1 => ?_⟩
  ·
    have hjI : j ∈ centralizer (miyamotoIG h L η : Set G) := by
      rw [mem_centralizer_iff]
      intro i hi
      obtain ⟨i₂, hi₂, e, he, rfl⟩ := hS.exists_I2_mul_IN2 hi
      have h1 : i₂ * j = j * i₂ :=
        mem_centralizer_iff.1 ((hMH.trans inf_le_right) (hJM hj)) i₂ hi₂
      have h2 : e * j = j * e := mem_centralizer_iff.1 (hJC hj) e he
      rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
    have hjR : j ∈ normalizer (miyamotoRG h L η t Q : Set G) := by
      rw [← hS.F2_sup_V2]
      exact mem_normalizer_sup ((hMH.trans inf_le_left) (hJM hj)) (hJV hj)
    exact mem_normalizer_inf hjR (mem_normalizer_centralizer (mem_normalizer_of_mem_centralizer'
      (centralizer_le (SetLike.coe_subset_coe.2 hS.I1G_le_IG) hjI)))
  · exact mem_normalizer_of_mem_centralizer' (hS.M2G_le_centralizer_E (hJM hj))
  · obtain ⟨c, hcM, hcd, hcab⟩ :=
      Common.exists_conj_eq_of_mem_of_card' ψ hdM hd1 hdpow hVM hVcard hdV ha hb ha1 hb1
    refine ⟨c, ⟨⟨c, hcM⟩, ?_, rfl⟩, hcab⟩
    have hcd' : (⟨c, hcM⟩ : M) * d' = d' * ⟨c, hcM⟩ := Subtype.ext hcd
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact ((Commute.zpow_left (Commute.symm hcd') n).symm).eq.symm

theorem mem_F1_or_mem_F2_of_case_one (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂]
    [Fintype k₂] (hk₂ : Fintype.card k₂ = (2 ^ f) ^ 2)
    (ψ : miyamotoM2G h L η t Q ≃* SL(2, k₂)) {x : G} (hx : x ∈ miyamotoRG h L η t Q)
    (hxx : x * x = 1) : x ∈ miyamotoF1G h L η t ∨ x ∈ miyamotoF2G h L η t Q := by
  obtain ⟨J, hJW, hJE, htrans⟩ := hS.exists_transitive_torus_V2 hk₂ ψ
  exact hS.mem_F1_or_mem_F2_of_mul_self hJW hJE htrans hx hxx

theorem centerIn_U_le_F_of_case_one (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂]
    [Fintype k₂] (hk₂ : Fintype.card k₂ = (2 ^ f) ^ 2)
    (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂)) {k : Type} [Field k] [Fintype k]
    (hk : Fintype.card k = (2 ^ f) ^ 2) (ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)) :
    CFSG.centerIn (miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)) ≤ miyamotoFG h L η t Q := by
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ 𝓦 ⊓ prodFactorOne ψ, w ≠ 1 := by
    have h1 : 1 < Nat.card (𝓦 ⊓ prodFactorOne ψ : Subgroup G) := by
      rw [(hS.W_eq_sup (ψ := ψ) hk).2.1]
      exact Nat.one_lt_pow two_ne_zero (Nat.one_lt_two_pow (by have := hS.two_le; omega))
    have : Nontrivial (𝓦 ⊓ prodFactorOne ψ : Subgroup G) := Finite.one_lt_card_iff_nontrivial.1 h1
    obtain ⟨⟨w, hw⟩, hw1⟩ := exists_ne (1 : (𝓦 ⊓ prodFactorOne ψ : Subgroup G))
    exact ⟨w, hw, fun e => hw1 (Subtype.ext e)⟩
  have hwW : w ∈ 𝓦 := (mem_inf.1 hw).1
  intro z hz
  have hzF1 : z ∈ miyamotoF1G h L η t := hS.centerIn_U_le_F1 hz
  have hzw : z * w = w * z := (mem_centralizer_iff.1 (mem_inf.1 hz).2 w (mem_sup_right hw)).symm
  have hzR : z * w ∈ miyamotoRG h L η t Q :=
    mul_mem (le_sup_left.trans hS.P1_le_miyamotoRG hzF1) (mem_inf.1 hwW).1
  have hzz : z * z = 1 := hS.F1_mul_self z hzF1
  have hww : w * w = 1 := hS.W_mul_self hwW
  have hx2 : z * w * (z * w) = 1 := by
    rw [show z * w * (z * w) = z * (w * z) * w by group, ← hzw,
      show z * (z * w) * w = (z * z) * (w * w) by group, hzz, hww, one_mul]
  rcases hS.mem_F1_or_mem_F2_of_case_one hk₂ ψ₂ hzR hx2 with hF1 | hF2
  · exfalso
    apply hw1
    have hwF1 : w ∈ miyamotoF1G h L η t := by
      have := mul_mem (inv_mem hzF1) hF1
      rwa [inv_mul_cancel_left] at this
    have : w ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoI1G h L η : Set G) :=
      mem_inf.2 ⟨hwF1, (mem_inf.1 hwW).2⟩
    rwa [hS.F1_inf_centralizer_I1, mem_bot] at this
  · have hzF2 : z ∈ miyamotoF2G h L η t Q := by
      have := mul_mem hF2 (inv_mem (hS.W_le_F2 hwW))
      rwa [mul_inv_cancel_right] at this
    rw [← hS.F2_inf_F1]
    exact mem_inf.2 ⟨hzF2, hzF1⟩

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
