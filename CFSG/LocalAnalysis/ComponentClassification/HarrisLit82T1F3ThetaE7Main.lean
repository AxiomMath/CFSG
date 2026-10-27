module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaE7Tw
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaE7

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_three_dvd_three_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : ¬ 3 ∣ 3 ^ f - 1 := by
  intro h
  have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  have hpos : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
  have h1 : 3 ∣ 3 ^ f - (3 ^ f - 1) := Nat.dvd_sub h3 h
  rw [Nat.sub_sub_self hpos] at h1
  norm_num at h1

theorem eq_one_of_pow_eq_one_of_pow_three {G : Type*} [Group G] {y : G} {k : ℕ} (hk : ¬ 3 ∣ k)
    (h1 : y ^ k = 1) (h3 : y ^ 3 = 1) : y = 1 := by
  have h : y ^ Nat.gcd 3 k = 1 := pow_gcd_eq_one.2 ⟨h3, h1⟩
  rwa [(Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hk |>.gcd_eq_one, pow_one] at h


theorem eq_one_of_pow_three_rows_E7 {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (α : MulAut (adjointGroup .E7 K)) (hα : orderOf α = 2)
    {B : Subgroup (MulAut (adjointGroup .E7 K))}
    (hB : (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range ≤ B)
    {y : MulAut (adjointGroup .E7 K)} (hy : y ∈ oddCoreIn B α) (hy3 : y ^ 3 = 1) : y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three hf hK
  rcases burgRowExp_E7 Nat.prime_three (by norm_num) hK α hα with h | h | ⟨g, a, rfl, hns, hcore⟩
  · rw [oddCoreIn_eq_bot_of_core (center_adjointGroup_eq_bot_field .E7 K) hB h, mem_bot] at hy
    exact hy
  · exact eq_one_of_pow_eq_one_of_pow_three (by rw [hK]; exact not_three_dvd_three_pow_sub_one hf)
      (h B hB y hy) hy3
  · let L := AlgebraicClosure K
    have : CharP L 3 := charP_of_injective_algebraMap (algebraMap K L).injective 3
    rcases TwE7.twisted_core_or_mask_three (by norm_num) hf hK L hα hns with h0 |
        ⟨-, r, hr, h3, g₁, hg₁G, hconj, hcoc⟩
    · exact absurd h0 hcore
    · exact TwE7.eq_one_of_pow_three_twisted_three hf hK L hr h3 hg₁G hconj hcoc hB hy hy3

theorem oddCoreIn_eq_bot_rows_E7_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (α : MulAut (adjointGroup .E7 K)) (hα : orderOf α = 2)
    {B : Subgroup (MulAut (adjointGroup .E7 K))}
    (hB : (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range ≤ B) :
    oddCoreIn B α = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK1 : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have : CharP K 3 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      le_rfl hK1
  rcases burgRowExp_E7 Nat.prime_three (by norm_num) hK1 α hα with h | h | ⟨g, a, rfl, hns, hcore⟩
  · exact oddCoreIn_eq_bot_of_core (center_adjointGroup_eq_bot_field .E7 K) hB h
  · rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    have h2 : y ^ 2 = 1 := by
      have := h B hB y hy
      rwa [hK] at this
    have hodd := odd_orderOf_of_mem_oddCoreIn hy
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2) with h1 | h1
    · exact orderOf_eq_one_iff.1 h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  · exfalso
    let L := AlgebraicClosure K
    have : CharP L 3 := charP_of_injective_algebraMap (algebraMap K L).injective 3
    rcases TwE7.twisted_core_or_mask_three (by norm_num) le_rfl hK1 L hα hns with h0 | ⟨h5, -⟩
    · exact hcore h0
    · omega

theorem eq_one_of_pow_three_of_mem_oddCentralizerCore_E7 (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {n f : ℕ}
    (hL : LieModel (GeneralizedFitting.subgroup X) .E7 n 3 f) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) (hy3 : y ^ 3 = 1) : y = 1 := by
  rcases hL with ⟨hcl, -⟩ | ⟨-, -, hmod⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
  · exfalso
    simp [classicalTags] at hcl
  · obtain ⟨⟨-, hf, -⟩, hU⟩ := hmod
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hU
    set ψ := socleAction e with hψdef
    have hψ : Function.Injective ψ := socleAction_injective hsimple hnab e
    have hB : (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range ≤
        ψ.range := by
      rintro _ ⟨x, rfl⟩
      exact conj_mem_range_socleAction e x
    have hα : orderOf (ψ t) = 2 := by rw [orderOf_injective ψ hψ]; exact ht
    have hy' : ψ y ∈ oddCoreIn ψ.range (ψ t) := by
      rw [← map_oddCentralizerCore_of_injective hψ]
      exact ⟨y, hy, rfl⟩
    apply hψ
    rw [map_one]
    exact eq_one_of_pow_three_rows_E7 hf hK (ψ t) hα hB hy' (by rw [← map_pow, hy3, map_one])
  · exfalso
    simp [reeTitsTags] at hree
  · exact absurd h (by decide)

theorem oddCentralizerCore_eq_bot_E7_three (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {n : ℕ}
    (hL : LieModel (GeneralizedFitting.subgroup X) .E7 n 3 1) (t : X)
    (ht : orderOf t = 2) : oddCentralizerCore t = ⊥ := by
  rcases hL with ⟨hcl, -⟩ | ⟨-, -, hmod⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
  · exfalso
    simp [classicalTags] at hcl
  · obtain ⟨-, hU⟩ := hmod
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hU
    have hψ := socleAction_injective hsimple hnab e
    have hB : (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range ≤
        (socleAction e).range := by
      rintro _ ⟨x, rfl⟩
      exact conj_mem_range_socleAction e x
    have hα : orderOf (socleAction e t) = 2 := by
      rw [orderOf_injective _ hψ]
      exact ht
    exact PSL.eq_bot_of_oddCoreIn hψ (oddCoreIn_eq_bot_rows_E7_three (by rw [hK, pow_one]) _ hα
      hB) le_rfl
  · exfalso
    simp [reeTitsTags] at hree
  · exact absurd h (by decide)

end CFSG.ComponentClassification.Burgoyne.E2
