module

public import CFSG.LocalAnalysis.EvenBN.U5.LinLayer
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineNotNormal

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin_pow_dvd_M₂ (hl : d.LinCtx) : (2 ^ f) ^ 6 ∣ Nat.card d.M₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 d.M₂
  obtain ⟨R₁, R₂, hrad⟩ := lin_exists_radicals_of_isSylowOf_M₂ hl hR
  have hc : Nat.card R = ((2 ^ f) ^ 2) ^ 3 := hrad.card
  have h1 := Subgroup.card_dvd_of_le hR.le
  rw [hc, ← pow_mul] at h1
  exact h1

theorem lin_E_inf_M₂ (hl : d.LinCtx) (hE2 : IsPGroup 2 d.E)
    (hME : d.M₂ ≤ normalizer (d.E : Set G)) : d.E ⊓ d.M₂ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hΛs, -, -⟩ := lin_layer_facts hl
  haveI := hΛs
  set Y : Subgroup ↥d.M₂ := (d.E ⊓ d.M₂).subgroupOf d.M₂ with hY
  have hYp : IsPGroup 2 Y := (hE2.to_inf_left).comap_subtype
  have hYn : Y.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hY, mem_subgroupOf] at hn ⊢
    exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hME g.2) n).1 (Subgroup.mem_inf.1 hn).1,
      mul_mem (mul_mem g.2 (Subgroup.mem_inf.1 hn).2) (inv_mem g.2)⟩
  have hπn : (Y.map (linπ hl)).Normal := hYn.map _ (lin_π_surjective hl)
  haveI := hπn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.map (linπ hl)) with h0 | h1
  ·
    have hYker : Y ≤ (linπ hl).ker := fun y hy => by
      have : linπ hl y ∈ Y.map (linπ hl) := mem_map_of_mem _ hy
      rw [h0, mem_bot] at this
      exact this
    have hodd := lin_π_ker_odd hl
    have hYodd : Odd (Nat.card Y) :=
      Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hYker)
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hYp
    have hn0 : n = 0 := by
      by_contra hne
      have : Even (Nat.card Y) := by
        rw [hn]
        exact (Nat.even_pow.2 ⟨even_two, hne⟩)
      exact (Nat.not_even_iff_odd.2 hYodd) this
    have hYcard : Nat.card Y = 1 := by rw [hn, hn0]; rfl
    have hY1 : Y = ⊥ := Subgroup.eq_bot_of_card_eq _ hYcard
    rw [eq_bot_iff]
    intro x hx
    have hxM : x ∈ d.M₂ := hx.2
    have : (⟨x, hxM⟩ : ↥d.M₂) ∈ Y := Subgroup.mem_subgroupOf.2 hx
    rw [hY1, mem_bot] at this
    exact (mem_bot.2 (congrArg Subtype.val this))
  ·
    exfalso
    have hΛ2 : IsPGroup 2 ↥(CFSG.layer (d.s38dH ⧸ d.s38dO)) := by
      intro z
      have hz : z ∈ Y.map (linπ hl) := by rw [h1]; exact mem_top z
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨m, hm⟩ := hYp ⟨y, hy⟩
      have hy1 : y ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      exact ⟨m, by rw [← map_pow, hy1, map_one]⟩
    exact s39c_not_isPGroup_of_simple (lin_layer_nonabelian hl) hΛ2

theorem lin_card_S_ge (hl : d.LinCtx) (k : d.Know92) {S : Subgroup G}
    (hS : IsSylowOf 2 S d.L₂) : (2 ^ f) ^ 20 ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : d.L₂ = d.E ⊔ d.M₂ := k.s8.1
  have hME : d.M₂ ≤ normalizer (d.E : Set G) :=
    ((hL ▸ le_sup_right : d.M₂ ≤ d.L₂)).trans d.L₂_le_normalizer_E
  have hE2 : IsPGroup 2 d.E := hl.hyp.isPGroup_E hl.gms
  have hEM := lin_E_inf_M₂ hl hE2 hME
  have h1 := Common.card_sup_mul_card_inf_eq hME
  rw [← hL, hEM, Subgroup.card_bot, mul_one, hl.hyp.card_E hl.gms] at h1
  have h2 : (2 ^ f) ^ 20 ∣ Nat.card d.L₂ := by
    rw [h1, show (2 ^ f) ^ 20 = (2 ^ f) ^ 14 * (2 ^ f) ^ 6 by ring]
    exact mul_dvd_mul_left _ (lin_pow_dvd_M₂ hl)
  obtain ⟨Q, rfl⟩ := hS
  have h3 := Q.pow_dvd_card_of_pow_dvd_card (p := 2) (n := f * 20)
    (by rw [pow_mul]; exact h2)
  rw [Subgroup.card_map_of_injective d.L₂.subtype_injective]
  have h4 := Nat.le_of_dvd Nat.card_pos h3
  rwa [pow_mul] at h4

theorem lin_sec39_notNormal (hl : d.LinCtx) (k : d.Know92) (he : d.Sec39e)
    (hi : d.Sec39Input) : d.Sec39NotNormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hN
  have hf2 : 2 ≤ f := hl.hyp.two_le
  obtain ⟨kf, _, _, hkf, ⟨e0⟩⟩ := hi.field
  have hrank : ∀ P : Subgroup (Bar d.D), P ≤ centralizer ((bar d.D d.N₁ : Subgroup (Bar d.D)) :
      Set (Bar d.D)) → IsPGroup 2 P → Nat.card P ≤ 2 := hi.rank
  obtain ⟨S, hS, hPS⟩ := s39c_exists_sylow_L₂ hl.toCaseHyp
  obtain ⟨hSED, -, hDchar⟩ := k.s9_1 S hS hPS
  have hDS : d.D ≤ S := hSED ▸ le_sup_right
  have hSN : S ≤ normalizer (d.D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDS).1 inferInstance
  have hSpg : IsPGroup 2 S := hS.isPGroup
  have hbSpg : IsPGroup 2 (bar d.D S) := isPGroup_bar hSpg
  have hcardbar : Nat.card (bar d.D S) * Nat.card d.D = Nat.card S := card_bar_mul hDS hSN
  have hq4 : (2 ^ f) ^ 4 ≤ Nat.card (bar d.D S) := by
    have h1 := lin_card_S_ge hl k hS
    have h2 := s39c_card_D_le hl.toCaseHyp he hi
    rw [← hcardbar] at h1
    have h3 : (2 ^ f) ^ 4 * (2 ^ f) ^ 16 ≤ Nat.card (bar d.D S) * (2 ^ f) ^ 16 :=
      calc (2 ^ f) ^ 4 * (2 ^ f) ^ 16 = (2 ^ f) ^ 20 := by ring
        _ ≤ Nat.card (bar d.D S) * Nat.card d.D := h1
        _ ≤ Nat.card (bar d.D S) * (2 ^ f) ^ 16 := Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)
  have hnum := s39c_four_mul_lt f hf2
  have hbig : 2 * (2 ^ (2 * f) * (2 * f)) < Nat.card (bar d.D S) := by
    have h5 : 2 ^ (2 * f) * (4 * f) < (2 ^ f) ^ 4 :=
      calc 2 ^ (2 * f) * (4 * f) < 2 ^ (2 * f) * 2 ^ (2 * f) :=
            Nat.mul_lt_mul_of_pos_left hnum (by positivity)
        _ = (2 ^ f) ^ 4 := by ring
    calc 2 * (2 ^ (2 * f) * (2 * f)) = 2 ^ (2 * f) * (4 * f) := by ring
      _ < (2 ^ f) ^ 4 := h5
      _ ≤ Nat.card (bar d.D S) := hq4
  exact s39c_not_normal_of_card (by omega) hkf e0 hi.order_two hi.centralizes hi.normal hrank
    hbSpg hbig hN

end Data

end CFSG.LocalAnalysis.EvenBN.U5
