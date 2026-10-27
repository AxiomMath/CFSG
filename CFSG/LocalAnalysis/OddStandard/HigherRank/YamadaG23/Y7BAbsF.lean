module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsC
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem sq_eq_one_of_natCard_eq_two {H : Type*} [Group H] (h : Nat.card H = 2) (x : H) :
    x ^ 2 = 1 := by
  have hb : (⊥ : Subgroup H).index = 2 := by rw [Subgroup.index_bot]; exact h
  have := Subgroup.sq_mem_of_index_two (H := (⊥ : Subgroup H)) hb x
  simpa using this

private theorem isMulCommutative_of_natCard_eq_two {H : Type*} [Group H] (h : Nat.card H = 2) :
    IsMulCommutative H := by
  refine IsMulCommutative.of_comm fun x y => ?_
  have hx2 : x ^ 2 = 1 := sq_eq_one_of_natCard_eq_two h x
  have hy2 : y ^ 2 = 1 := sq_eq_one_of_natCard_eq_two h y
  have hxy2 : (x * y) ^ 2 = 1 := sq_eq_one_of_natCard_eq_two h (x * y)
  have hx : x⁻¹ = x := by
    have h2 : x * x = 1 := by rw [← pow_two]; exact hx2
    exact (eq_inv_of_mul_eq_one_left h2).symm
  have hy : y⁻¹ = y := by
    have h2 : y * y = 1 := by rw [← pow_two]; exact hy2
    exact (eq_inv_of_mul_eq_one_left h2).symm
  calc x * y = (x * y)⁻¹ := by
        have h2 : (x * y) * (x * y) = 1 := by rw [← pow_two]; exact hxy2
        exact eq_inv_of_mul_eq_one_left h2
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx, hy]

private theorem commutatorElement_mem_of_relIndex_two {M K : Subgroup G}
    (h2 : M.relIndex K = 2) : ∀ a ∈ K, ∀ a' ∈ K, ⁅a, a'⁆ ∈ M := by
  intro a ha a' ha'
  haveI : (M.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two h2
  haveI : IsMulCommutative (↥K ⧸ M.subgroupOf K) :=
    isMulCommutative_of_natCard_eq_two h2
  have hq : QuotientGroup.mk' (M.subgroupOf K)
      ⁅(⟨a, ha⟩ : ↥K), (⟨a', ha'⟩ : ↥K)⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' _ _
  have hmem : ⁅(⟨a, ha⟩ : ↥K), (⟨a', ha'⟩ : ↥K)⁆ ∈ M.subgroupOf K := by
    rw [← QuotientGroup.ker_mk' (M.subgroupOf K), MonoidHom.mem_ker]
    exact hq
  exact Subgroup.mem_subgroupOf.mp hmem

private theorem mem_sup_exists_mul_of_le_normalizer_aux {H K : Subgroup G}
    (h : H ≤ normalizer (K : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  change x ∈ (↑(H ⊔ K) : Set G) ↔ ∃ a ∈ H, ∃ b ∈ K, x = a * b
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H K h, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩; exact ⟨a, ha, b, hb, hab.symm⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

private theorem le_normalizer_of_relIndex_two_aux {W M : Subgroup G} (hMW : M ≤ W)
    (h2 : M.relIndex W = 2) : W ≤ normalizer (M : Set G) := by
  haveI : (M.subgroupOf W).Normal := Subgroup.normal_of_index_eq_two h2
  exact Subgroup.le_normalizer_of_normal_subgroupOf hMW

theorem relIndex_eq_of_card_eq_mul [Finite G] {H K : Subgroup G} (hHK : H ≤ K) {n : ℕ}
    (h : Nat.card ↥K = n * Nat.card ↥H) : H.relIndex K = n := by
  have hcard := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [inf_of_le_left hHK, h] at hcard
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard

theorem y7b_sq_mem_of_relIndex_two {M K : Subgroup G} (hMK : M ≤ K) (h2 : M.relIndex K = 2) :
    ∀ a ∈ K, a ^ 2 ∈ M := by
  intro a ha
  have := Subgroup.sq_mem_of_index_two (H := M.subgroupOf K) h2 (⟨a, ha⟩ : ↥K)
  simpa [Subgroup.mem_subgroupOf] using this

theorem comm_sq_mem_sup_of_relIndex_two {M K₁ K₂ : Subgroup G} (h₁ : M ≤ K₁) (h₂ : M ≤ K₂)
    (i₁ : M.relIndex K₁ = 2) (i₂ : M.relIndex K₂ = 2) (hint : K₁ ⊓ K₂ = M)
    (hn₁ : K₁ ≤ normalizer (K₂ : Set G)) (hn₂ : K₂ ≤ normalizer (K₁ : Set G)) :
    (∀ w ∈ K₁ ⊔ K₂, ∀ w' ∈ K₁ ⊔ K₂, ⁅w, w'⁆ ∈ M) ∧ ∀ w ∈ K₁ ⊔ K₂, w ^ 2 ∈ M := by
  have hM1 : ∀ a ∈ K₁, ∀ m ∈ M, a * m * a⁻¹ ∈ M :=
    fun a ha m hm =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_of_relIndex_two_aux h₁ i₁ ha) m).mp hm
  have hM2 : ∀ b ∈ K₂, ∀ m ∈ M, b * m * b⁻¹ ∈ M :=
    fun b hb m hm =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_of_relIndex_two_aux h₂ i₂ hb) m).mp hm
  have hAA : ∀ a ∈ K₁, ∀ a' ∈ K₁, ⁅a, a'⁆ ∈ M := commutatorElement_mem_of_relIndex_two i₁
  have hBB : ∀ b ∈ K₂, ∀ b' ∈ K₂, ⁅b, b'⁆ ∈ M := commutatorElement_mem_of_relIndex_two i₂
  have hcross : ∀ a ∈ K₁, ∀ b ∈ K₂, ⁅a, b⁆ ∈ M := by
    intro a ha b hb
    have hb2 : a * b * a⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.mp (hn₁ ha) b).mp hb
    have ha2 : b * a⁻¹ * b⁻¹ ∈ K₁ :=
      (Subgroup.mem_normalizer_iff.mp (hn₂ hb) a⁻¹).mp (K₁.inv_mem ha)
    have hmem2 : ⁅a, b⁆ ∈ K₂ := by
      rw [commutatorElement_def]
      exact K₂.mul_mem hb2 (K₂.inv_mem hb)
    have hmem1 : ⁅a, b⁆ ∈ K₁ := by
      rw [commutatorElement_def,
        show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
      exact K₁.mul_mem ha ha2
    have hmem : ⁅a, b⁆ ∈ K₁ ⊓ K₂ := Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩
    rwa [hint] at hmem
  constructor
  · intro w hw w' hw'
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_exists_mul_of_le_normalizer_aux hn₁).mp hw
    obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_exists_mul_of_le_normalizer_aux hn₁).mp hw'
    have hx1 : ⁅b, a'⁆ ∈ M := by
      rw [← commutatorElement_inv (g₁ := a') (g₂ := b)]
      exact M.inv_mem (hcross a' ha' b hb)
    have hx3 : ⁅a, a'⁆ ∈ M := hAA a ha a' ha'
    rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_mul_right_eq_mul_conj]
    refine M.mul_mem ?_ ?_
    · refine hM1 a ha (⁅b, a'⁆ * a' * ⁅b, b'⁆ * a'⁻¹) ?_
      rw [show ⁅b, a'⁆ * a' * ⁅b, b'⁆ * a'⁻¹
          = ⁅b, a'⁆ * (a' * ⁅b, b'⁆ * a'⁻¹) by group]
      exact M.mul_mem hx1 (hM1 a' ha' (⁅b, b'⁆) (hBB b hb b' hb'))
    · rw [show ⁅a, a'⁆ * a' * ⁅a, b'⁆ * a'⁻¹
          = ⁅a, a'⁆ * (a' * ⁅a, b'⁆ * a'⁻¹) by group]
      exact M.mul_mem hx3 (hM1 a' ha' (⁅a, b'⁆) (hcross a ha b' hb'))
  · intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_exists_mul_of_le_normalizer_aux hn₁).mp hw
    have hba : ⁅b, a⁆ ∈ M := by
      rw [← commutatorElement_inv (g₁ := a) (g₂ := b)]
      exact M.inv_mem (hcross a ha b hb)
    have hconj : a * ⁅b, a⁆ * a⁻¹ ∈ M := hM1 a ha (⁅b, a⁆) hba
    have ha2 : a ^ 2 ∈ M := y7b_sq_mem_of_relIndex_two h₁ i₁ a ha
    have hb2 : b ^ 2 ∈ M := y7b_sq_mem_of_relIndex_two h₂ i₂ b hb
    have hexp : (a * b) ^ 2 = a * ⁅b, a⁆ * a⁻¹ * (a ^ 2 * b ^ 2) := by
      simp only [commutatorElement_def, pow_two]; group
    rw [hexp]
    exact M.mul_mem hconj (M.mul_mem ha2 hb2)

end CFSG.OddStandard.HigherRank.YamadaG23
