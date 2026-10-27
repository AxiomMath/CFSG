module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem false_of_cyclic_quotient (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) (B : Subgroup G)
    (hB : IsSylowOf 2 B (normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G)))
    (hQB : yamadaP d t ⊔ zpowers t ≤ B) (hcyc : ∃ x ∈ B, B = yamadaP d t ⊔ zpowers x) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hPp, htP, htN, hSP, -, -, -⟩ := h.yamada_5_32_of_layerHyp d hlay
  have hNQ : normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G) = ncs d t ⊔ yamadaP d t :=
    h.normalizer_yamadaP_sup_zpowers d hlay (h.commutator_yamadaP_sup_zpowers d hlay)
      (fun _ hx => h.mul_self_mem_yamadaF₄_of_mem_yamadaP d hlay hx)
  have hBN : B ≤ normalizer (yamadaP d t : Set G) := by
    refine hB.le.trans ?_
    rw [hNQ]
    exact sup_le (ncs_le_normalizer_yamadaP h d hlay) le_normalizer
  have hPB : yamadaP d t ≤ B := le_sup_left.trans hQB
  have htB : t ∈ B := hQB (mem_sup_right (mem_zpowers t))
  haveI hPnorm : ((yamadaP d t).subgroupOf B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hBN
  obtain ⟨x, hxB, hBx⟩ := hcyc
  have hxN : x ∈ normalizer (yamadaP d t : Set G) := hBN hxB
  have hcycB : IsCyclic (B ⧸ (yamadaP d t).subgroupOf B) := by
    refine isCyclic_of_surjective
      ((QuotientGroup.mk' ((yamadaP d t).subgroupOf B)).comp
        (zpowers (⟨x, hxB⟩ : B)).subtype) fun q => ?_
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hb' : b ∈ ((yamadaP d t ⊔ zpowers x : Subgroup G) : Set G) := by
      rw [← hBx]
      exact hb
    rw [coe_mul_of_right_le_normalizer_left _ _ ((zpowers_le).2 hxN), Set.mem_mul] at hb'
    obtain ⟨p, hp, z, hz, rfl⟩ := hb'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
    refine ⟨⟨(⟨x, hxB⟩ : B) ^ k, Subgroup.zpow_mem_zpowers _ k⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, mem_subgroupOf]
    have hnk : x ^ k ∈ normalizer (yamadaP d t : Set G) := zpow_mem hxN k
    have h1 := (mem_normalizer_iff.1 (inv_mem hnk) p).1 hp
    have e : (x ^ k)⁻¹ * (p * x ^ k) = (x ^ k)⁻¹ * p * ((x ^ k)⁻¹)⁻¹ := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    rw [e]
    exact h1
  set Inv : Set G := {y | y ∈ B ∧ y * y = 1} with hInv
  have hQcl : closure Inv = yamadaP d t ⊔ zpowers t := by
    apply le_antisymm
    · rw [closure_le]
      rintro y ⟨hyB, hy2⟩
      by_cases hyP : y ∈ yamadaP d t
      · exact mem_sup_left hyP
      ·
        set u : B ⧸ (yamadaP d t).subgroupOf B := QuotientGroup.mk ⟨y, hyB⟩ with hu
        set w : B ⧸ (yamadaP d t).subgroupOf B := QuotientGroup.mk ⟨t, htB⟩ with hw
        have hu1 : u ≠ 1 := by
          rw [hu, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
          exact hyP
        have hw1 : w ≠ 1 := by
          rw [hw, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
          exact htP
        have hu2 : u * u = 1 := by
          rw [hu, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
          change y * y ∈ yamadaP d t
          rw [hy2]
          exact one_mem _
        have hw2 : w * w = 1 := by
          rw [hw, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
          change t * t ∈ yamadaP d t
          rw [h.t_mul_t]
          exact one_mem _
        have huw := Common.eq_of_mul_self_eq_one_of_isCyclic hw1 hu1 hw2 hu2
        rw [hw, hu, QuotientGroup.eq, mem_subgroupOf] at huw
        have hy' : t⁻¹ * y ∈ yamadaP d t := huw
        have e : y = t * (t⁻¹ * y) := by group
        rw [e]
        exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hy')
    · refine sup_le ?_ ((zpowers_le).2 (subset_closure ⟨htB, h.t_mul_t⟩))
      refine (yamadaP_le_closure_involutions h d hlay).trans (closure_mono ?_)
      rintro x ⟨hxP, hx2⟩
      exact ⟨hPB hxP, hx2⟩
  have hNBQ : normalizer (B : Set G) ≤
      normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [← hQcl]
    refine le_normalizer_closure_iff.mpr fun n hn y hy => subset_closure ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp hn y).mp hy.1
    · calc n * y * n⁻¹ * (n * y * n⁻¹) = n * (y * y) * n⁻¹ := by group
        _ = 1 := by rw [hy.2]; group
  have hBsyl : ∃ T : Sylow 2 G, (T : Subgroup G) = B :=
    Common.exists_sylow_eq_of_isSylowOf_of_normalizer_le hB hNBQ
  have h521 := h.yamada_5_21 d hlay
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h.one_le)
  have hB2 : 2 ≤ Nat.card (yamadaY₂ d t) := by
    rw [(h.yamada_5_9_2 d hlay).2.1]
    calc 2 ≤ 2 ^ f := hq
      _ = (2 ^ f) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_right (by positivity) (by norm_num)
  have hX : ∀ y ∈ yamadaP d t, y * y = 1 → ∃ E : Subgroup G, IsElemAbelian 2 E ∧
      E ≤ centralizer ({y} : Set G) ∧ 2 * (2 ^ f) ^ 5 < Nat.card E := by
    intro y hy hy2
    obtain ⟨E, hE, hEC, hcard⟩ := exists_isElemAbelian_two_mul_card_le h521.2.1
      (le_sup_right.trans (h.yamadaW₂_le_yamadaW₃ d hlay)) hB2 hy2
      (h.commutator_mem_yamadaY₂_of_mem_yamadaP d hlay y hy)
    refine ⟨E, hE, hEC, ?_⟩
    rw [h521.2.2, (h.yamada_5_9_2 d hlay).2.1] at hcard
    exact two_mul_pow_five_lt_of_two_mul_pow_ten_le hq hcard
  have hfus : ∀ g : G, g⁻¹ * t * g ∉ yamadaP d t := fun g => by
    simpa using h.conj_t_not_mem_of_lt_card d hX g⁻¹
  have hFT := Common.firstTransferData_of_isCyclic hBsyl hPB hcycB htB htP h.ht hfus
  have := h.isPerfect
  exact CFSG.LocalAnalysis.perfect_first_transfer_exclusion ⟨_, _, _, hFT⟩

end CFSG.LocalAnalysis.EvenBN.TrialityD4
