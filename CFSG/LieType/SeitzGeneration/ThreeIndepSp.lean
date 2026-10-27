module

public import CFSG.LieType.SeitzGeneration.ThreeIndep
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.SpBlockPlanes
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock isSupp_longBlock coords
  suppGroup suppGroup_mono longBlock_injective mem_coords)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCSpFull (coprime_card_ker_proj)
open scoped MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

theorem eq_one_of_block_prod {a b c : Fin r} (hab : a ≠ b) (hac : a ≠ c) {X Y Z : SL(2, K)}
    (h : longBlock K r a X * longBlock K r b Y * longBlock K r c Z = 1) : X = 1 := by
  have hb : longBlock K r b Y ∈ suppGroup (K := K) (coords b ∪ coords c) :=
    suppGroup_mono Set.subset_union_left (isSupp_longBlock b Y)
  have hc : longBlock K r c Z ∈ suppGroup (K := K) (coords b ∪ coords c) :=
    suppGroup_mono Set.subset_union_right (isSupp_longBlock c Z)
  have h1 : longBlock K r a X = (longBlock K r b Y * longBlock K r c Z)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
    exact h
  have h2 : longBlock K r a X ∈ suppGroup (K := K) (coords b ∪ coords c) := by
    rw [h1]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hb hc)
  have hdisj : Disjoint (coords a) (coords b ∪ coords c) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    rcases mem_coords.1 hu with rfl | rfl <;> rcases hu' with hu' | hu' <;>
      rcases mem_coords.1 hu' with h | h <;>
      first
        | exact hab (Sum.inl_injective h) | exact hab (Sum.inr_injective h)
        | exact hac (Sum.inl_injective h) | exact hac (Sum.inr_injective h) | cases h
  have := eq_one_of_isSupp_disjoint hdisj (isSupp_longBlock a X) h2
  exact longBlock_injective a (by rw [map_one]; exact this)

theorem hasThreeIndep_psp [Finite K] (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K ^ 2 - 1) : HasThreeIndep (StatedProj (StatedSp r K)) p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card (SL(2, K)) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Dvd.dvd.mul_left hpq _
  obtain ⟨A, hA⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hAp : A ^ p = 1 := hA ▸ pow_orderOf_eq_one A
  let k₀ : Fin r := ⟨0, by omega⟩
  let k₁ : Fin r := ⟨1, by omega⟩
  let k₂ : Fin r := ⟨2, by omega⟩
  have h01 : k₀ ≠ k₁ := fun h => by simpa [k₀, k₁] using congrArg Fin.val h
  have h02 : k₀ ≠ k₂ := fun h => by simpa [k₀, k₂] using congrArg Fin.val h
  have h12 : k₁ ≠ k₂ := fun h => by simpa [k₁, k₂] using congrArg Fin.val h
  have hker : Nat.Coprime (Nat.card (proj r K).ker) p :=
    coprime_card_ker_proj (r := r) (K := K) (by omega) hp hp2
  have hc01 : ∀ X Y : SL(2, K), Commute (longBlock K r k₀ X) (longBlock K r k₁ Y) :=
    fun X Y => commute_longBlock h01 X Y
  have hc02 : ∀ X Y : SL(2, K), Commute (longBlock K r k₀ X) (longBlock K r k₂ Y) :=
    fun X Y => commute_longBlock h02 X Y
  have hc12 : ∀ X Y : SL(2, K), Commute (longBlock K r k₁ X) (longBlock K r k₂ Y) :=
    fun X Y => commute_longBlock h12 X Y
  have hpow : ∀ k : Fin r, longBlock K r k A ^ p = 1 := fun k => by
    rw [← map_pow, hAp, map_one]
  refine HasThreeIndep.of_hom (proj r K) (hc01 A A) (hc02 A A) (hc12 A A) (hpow k₀) (hpow k₁)
    (hpow k₂) fun i j k h => ?_
  set g : StatedSp r K := longBlock K r k₀ A ^ i * longBlock K r k₁ A ^ j *
    longBlock K r k₂ A ^ k with hg
  have hg' : g = longBlock K r k₀ (A ^ i) * longBlock K r k₁ (A ^ j) *
      longBlock K r k₂ (A ^ k) := by rw [hg, map_zpow, map_zpow, map_zpow]
  have hzp : ∀ (x : StatedSp r K) (m : ℤ), x ^ p = 1 → (x ^ m) ^ p = 1 := fun x m hx => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hgp : g ^ p = 1 := by
    have hc : Commute (longBlock K r k₀ A ^ i * longBlock K r k₁ A ^ j)
        (longBlock K r k₂ A ^ k) :=
      ((hc02 A A).zpow_zpow i k).mul_left ((hc12 A A).zpow_zpow j k)
    rw [hg, hc.mul_pow, ((hc01 A A).zpow_zpow i j).mul_pow, hzp _ i (hpow k₀),
      hzp _ j (hpow k₁), hzp _ k (hpow k₂)]
    simp
  have hg1 : g = 1 := by
    have hker' : g ∈ (proj r K).ker := h
    have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
    have h2 : orderOf g ∣ Nat.card (proj r K).ker := by
      let y : (proj r K).ker := ⟨g, hker'⟩
      calc orderOf g = orderOf y := Subgroup.orderOf_coe y
        _ ∣ Nat.card (proj r K).ker := orderOf_dvd_natCard y
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hker h2 h1)
  rw [hg'] at hg1
  have hAi : (p : ℤ) ∣ i := by
    have := eq_one_of_block_prod h01 h02 hg1
    rw [← hA]
    exact orderOf_dvd_iff_zpow_eq_one.2 this
  have hAj : (p : ℤ) ∣ j := by
    have h' : longBlock K r k₁ (A ^ j) * longBlock K r k₀ (A ^ i) * longBlock K r k₂ (A ^ k) =
        1 := by rw [← hg1, ← (hc01 (A ^ i) (A ^ j)).eq]
    have := eq_one_of_block_prod h01.symm h12 h'
    rw [← hA]
    exact orderOf_dvd_iff_zpow_eq_one.2 this
  have hAk : (p : ℤ) ∣ k := by
    have h' : longBlock K r k₂ (A ^ k) * longBlock K r k₀ (A ^ i) * longBlock K r k₁ (A ^ j) =
        1 := by
      rw [← hg1, mul_assoc, mul_assoc, ((hc02 (A ^ i) (A ^ k)).symm.mul_right
        (hc12 (A ^ j) (A ^ k)).symm).eq, ← mul_assoc]
    have := eq_one_of_block_prod h02.symm h12.symm h'
    rw [← hA]
    exact orderOf_dvd_iff_zpow_eq_one.2 this
  exact ⟨hAi, hAj, hAk⟩

end CFSG.LieType.SeitzGeneration
