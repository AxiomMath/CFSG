module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X] {Z A : Subgroup X} [Z.Normal]

private lemma relIndex_sup_eq_relIndex_inf {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} [K.Normal] : H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K := by
  have hI : H.relIndex (H ⊔ K) * Nat.card H = Nat.card (H ⊔ K : Subgroup G) := by
    have h : Nat.card (H ⊓ (H ⊔ K) : Subgroup G) = Nat.card H := by rw [inf_sup_self]
    rw [← h, Subgroup.relIndex_mul_card]
  have hIV : (H ⊓ K).relIndex H * Nat.card (H ⊓ K : Subgroup G) = Nat.card H := by
    have h : Nat.card ((H ⊓ K) ⊓ H : Subgroup G) = Nat.card (H ⊓ K : Subgroup G) := by
      rw [inf_eq_left.mpr inf_le_left]
    rw [← h, Subgroup.relIndex_mul_card]
  have hIII : (H ⊓ K).relIndex K * Nat.card (H ⊓ K : Subgroup G) = Nat.card K := by
    have h : Nat.card ((H ⊓ K) ⊓ K : Subgroup G) = Nat.card (H ⊓ K : Subgroup G) := by
      rw [inf_eq_left.mpr inf_le_right]
    rw [← h, Subgroup.relIndex_mul_card]
  have hb : K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
    rw [Subgroup.relIndex_sup_right, inf_comm, Subgroup.inf_relIndex_right]
  have hII : K.relIndex (H ⊔ K) * Nat.card K = Nat.card (H ⊔ K : Subgroup G) := by
    have h : Nat.card (K ⊓ (H ⊔ K) : Subgroup G) = Nat.card K := by
      rw [inf_eq_left.mpr le_sup_right]
    rw [← h, Subgroup.relIndex_mul_card]
  have key : H.relIndex (H ⊔ K) * Nat.card H =
      (H ⊓ K).relIndex K * Nat.card H := by
    calc H.relIndex (H ⊔ K) * Nat.card H = Nat.card (H ⊔ K : Subgroup G) := hI
      _ = K.relIndex (H ⊔ K) * Nat.card K := hII.symm
      _ = (H ⊓ K).relIndex H * Nat.card K := by rw [hb]
      _ = (H ⊓ K).relIndex H *
            ((H ⊓ K).relIndex K * Nat.card (H ⊓ K : Subgroup G)) := by rw [hIII]
      _ = (H ⊓ K).relIndex K *
            ((H ⊓ K).relIndex H * Nat.card (H ⊓ K : Subgroup G)) := by ring
      _ = (H ⊓ K).relIndex K * Nat.card H := by rw [hIV]
  exact Nat.mul_right_cancel
    ((Nat.card_pos_iff (α := H)).mpr ⟨⟨1, H.one_mem⟩, inferInstance⟩) key

theorem LitCtx.isPGroup_A (h : LitCtx Z A) : IsPGroup 2 A :=
  IsPGroup.of_card (n := 6) (by rw [h.card_A]; norm_num)

theorem lit_Z_inf_oddCore (h : LitCtx Z A) : Z ⊓ CFSG.oddCore X = ⊥ := by
  rw [← disjoint_iff]
  apply Subgroup.disjoint_of_coprime_natCard
  rw [h.card_Z]
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2
    (Nat.card (CFSG.oddCore X))).mpr (lit_odd_card_oddCore X).coprime_two_left

theorem lit_A_inf_oddCore (h : LitCtx Z A) : A ⊓ CFSG.oddCore X = ⊥ := by
  rw [← disjoint_iff]
  apply Subgroup.disjoint_of_coprime_natCard
  rw [h.card_A]
  have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
  rw [h64]
  exact (Nat.coprime_pow_left_iff (by norm_num : 0 < 6) 2
    (Nat.card (CFSG.oddCore X))).mpr (lit_odd_card_oddCore X).coprime_two_left

theorem lit_card_litP (h : LitCtx Z A) : Nat.card (litP Z) = 4 * Nat.card (CFSG.oddCore X) := by
  have hd : Disjoint Z (CFSG.oddCore X) := disjoint_iff.mpr (lit_Z_inf_oddCore h)
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      Z (CFSG.oddCore X) (Subgroup.le_normalizer_of_normal (H := Z) (K := CFSG.oddCore X)) hd
  simpa [litP, h.card_Z] using hcard

theorem lit_A_inf_litP (h : LitCtx Z A) : A ⊓ litP Z = Z := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxA, hxZP⟩ := hx
    change x ∈ Z ⊔ CFSG.oddCore X at hxZP
    rw [Subgroup.mem_sup_of_normal_left] at hxZP
    obtain ⟨y, hyZ, z, hzO, hyz⟩ := hxZP
    have hzA : z ∈ A := by
      have hz : z = y⁻¹ * x := by rw [← hyz]; group
      rw [hz]
      exact mul_mem (inv_mem (h.Z_le_A hyZ)) hxA
    have hzbot : z ∈ A ⊓ CFSG.oddCore X := ⟨hzA, hzO⟩
    rw [lit_A_inf_oddCore h] at hzbot
    have hz1 : z = 1 := by simpa using hzbot
    rw [← hyz, hz1, mul_one]
    exact hyZ
  · intro x hx
    exact ⟨h.Z_le_A hx, Subgroup.mem_sup_left hx⟩

theorem lit_A_sylow_sup (h : LitCtx Z A) : ¬ 2 ∣ A.relIndex (A ⊔ litP Z) := by
  haveI : (litP Z).Normal := Subgroup.sup_normal Z (CFSG.oddCore X)
  have hrel : A.relIndex (A ⊔ litP Z) = (A ⊓ litP Z).relIndex (litP Z) :=
    relIndex_sup_eq_relIndex_inf (H := A) (K := litP Z)
  rw [hrel, lit_A_inf_litP h]
  have hZP : Z.relIndex (litP Z) = Nat.card (CFSG.oddCore X) := by
    have hZI : Nat.card (Z ⊓ litP Z : Subgroup X) = Nat.card Z := by
      rw [inf_eq_left.mpr (show Z ≤ litP Z from le_sup_left)]
    have hrc := Subgroup.relIndex_mul_card (H := Z) (K := litP Z)
    rw [hZI, h.card_Z, lit_card_litP h] at hrc
    have h' : Z.relIndex (litP Z) * 4 = Nat.card (CFSG.oddCore X) * 4 := by
      rw [hrc]; ring
    exact Nat.mul_right_cancel (by norm_num : (0 : ℕ) < 4) h'
  rw [hZP]
  exact (lit_odd_card_oddCore X).not_two_dvd_nat

theorem lit_A_le_litC (h : LitCtx Z A) : A ≤ litC Z A := by
  intro a ha
  rw [mem_litC]
  exact ⟨Subgroup.le_normalizer ha, fun b hb => h.comm_mem b hb a ha⟩

theorem lit_normalizer_inf_litP_le (h : LitCtx Z A) :
    normalizer (A : Set X) ⊓ litP Z ≤ litC Z A := by
  intro n hn
  rw [Subgroup.mem_inf] at hn
  obtain ⟨hnN, hnP⟩ := hn
  rw [mem_litC]
  refine ⟨hnN, fun a ha => ?_⟩
  have hAn : n * a⁻¹ * n⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hnN (a⁻¹)).mp (inv_mem ha)
  haveI : (litP Z).Normal := Subgroup.sup_normal Z (CFSG.oddCore X)
  have hPn : a * n * a⁻¹ ∈ litP Z := (inferInstance : (litP Z).Normal).conj_mem n hnP a
  have hmemA : ⁅a, n⁆ ∈ A := by
    have : ⁅a, n⁆ = a * (n * a⁻¹ * n⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem ha hAn
  have hmemP : ⁅a, n⁆ ∈ litP Z := by
    have : ⁅a, n⁆ = (a * n * a⁻¹) * n⁻¹ := by rw [commutatorElement_def]
    rw [this]
    exact mul_mem hPn (inv_mem hnP)
  have hmem : ⁅a, n⁆ ∈ A ⊓ litP Z := ⟨hmemA, hmemP⟩
  rwa [lit_A_inf_litP h] at hmem

end CFSG.OddStandard.HigherRank.YamadaG23
