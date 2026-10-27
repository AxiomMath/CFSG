module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.LocalAnalysis.RankFourTheoremC.PPointOutPSL2

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.ComponentClassification.OuterAutomorphisms Subgroup

universe u

theorem isMulCommutative_outer_of_mulEquiv_psl2 {K : Type*} [Group K] (F : Type u) [Field F]
    [Finite F] {p f : ℕ} [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f)
    (hFcard : Nat.card F = p ^ f) (hcard : 3 < Nat.card F)
    (e : K ≃* CFSG.GorensteinWalter.PSL2 F) : IsMulCommutative (Outer K) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  obtain ⟨k, hk⟩ := exists_conj_eq_commutator_of_mulEquiv_psl2 F hpodd hf hFcard hcard e
    β⁻¹ α⁻¹
  refine ⟨k, MulEquiv.ext fun z => ?_⟩
  have := hk z
  simpa [mul_assoc, MulAut.conj_apply] using this.symm

theorem exists_conj_of_mem_commutator {N K : Type*} [Group N] [Group K] (F : Type u) [Field F]
    [Finite F] {p f : ℕ} [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f)
    (hFcard : Nat.card F = p ^ f) (hcard : 3 < Nat.card F)
    (e : K ≃* CFSG.GorensteinWalter.PSL2 F) (a : N →* MulAut K) {y : N}
    (hy : y ∈ commutator N) : ∃ k : K, ∀ z : K, a y z = k * z * k⁻¹ := by
  have := isMulCommutative_outer_of_mulEquiv_psl2 F hpodd hf hFcard hcard e
  have h1 : y ∈ ((QuotientGroup.mk' (inner K)).comp a).ker :=
    Abelianization.commutator_subset_ker _ hy
  have h2 : a y ∈ inner K := (QuotientGroup.eq_one_iff (a y)).mp h1
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, fun z => by
    have := congrArg (fun φ : MulAut K => φ z) hk
    simpa [MulAut.conj_apply] using this.symm⟩

theorem commute_of_inner_action {X : Type*} [Group X] {K R : Subgroup X} (hRp : IsPGroup 3 R)
    (hKC : ∀ k ∈ K, k ∈ centralizer (K : Set X) → k = 1)
    (hKab : ∀ A : Subgroup X, A ≤ K → IsPGroup 3 A → ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCab : ∀ A : Subgroup X, A ≤ centralizer (K : Set X) → IsPGroup 3 A →
      ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hinner : ∀ r ∈ R, ∃ k ∈ K, ∀ z ∈ K, r * z * r⁻¹ = k * z * k⁻¹) :
    ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
  set C : Subgroup X := centralizer (K : Set X) with hC
  have hdec : ∀ r ∈ R, ∃ k ∈ K, ∃ c ∈ C, r = k * c := by
    intro r hr
    obtain ⟨k, hk, hkz⟩ := hinner r hr
    refine ⟨k, hk, k⁻¹ * r, ?_, by group⟩
    rw [hC, mem_centralizer_iff]
    intro z hz
    have h := hkz z hz
    calc z * (k⁻¹ * r) = k⁻¹ * (k * z * k⁻¹) * r := by group
      _ = k⁻¹ * (r * z * r⁻¹) * r := by rw [h]
      _ = k⁻¹ * r * z := by group
  have hcomm : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k := fun k hk c hc =>
    mem_centralizer_iff.mp hc k hk
  let I : Subgroup X :=
    { carrier := {k | k ∈ K ∧ ∃ c ∈ C, k * c ∈ R}
      mul_mem' := by
        rintro k k' ⟨hk, c, hc, hkc⟩ ⟨hk', c', hc', hkc'⟩
        refine ⟨K.mul_mem hk hk', c * c', C.mul_mem hc hc', ?_⟩
        have : k * k' * (c * c') = (k * c) * (k' * c') := by
          calc k * k' * (c * c') = k * (k' * c) * c' := by group
            _ = k * (c * k') * c' := by rw [hcomm k' hk' c hc]
            _ = (k * c) * (k' * c') := by group
        rw [this]
        exact R.mul_mem hkc hkc'
      one_mem' := ⟨K.one_mem, 1, C.one_mem, by simp⟩
      inv_mem' := by
        rintro k ⟨hk, c, hc, hkc⟩
        refine ⟨K.inv_mem hk, c⁻¹, C.inv_mem hc, ?_⟩
        have : k⁻¹ * c⁻¹ = (k * c)⁻¹ := by
          have hcm : Commute k c := hcomm k hk c hc
          rw [mul_inv_rev]
          exact hcm.inv_inv.eq
        rw [this]
        exact R.inv_mem hkc }
  let J : Subgroup X :=
    { carrier := {c | c ∈ C ∧ ∃ k ∈ K, k * c ∈ R}
      mul_mem' := by
        rintro c c' ⟨hc, k, hk, hkc⟩ ⟨hc', k', hk', hkc'⟩
        refine ⟨C.mul_mem hc hc', k * k', K.mul_mem hk hk', ?_⟩
        have : k * k' * (c * c') = (k * c) * (k' * c') := by
          calc k * k' * (c * c') = k * (k' * c) * c' := by group
            _ = k * (c * k') * c' := by rw [hcomm k' hk' c hc]
            _ = (k * c) * (k' * c') := by group
        rw [this]
        exact R.mul_mem hkc hkc'
      one_mem' := ⟨C.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro c ⟨hc, k, hk, hkc⟩
        refine ⟨C.inv_mem hc, k⁻¹, K.inv_mem hk, ?_⟩
        have : k⁻¹ * c⁻¹ = (k * c)⁻¹ := by
          have hcm : Commute k c := hcomm k hk c hc
          rw [mul_inv_rev]
          exact hcm.inv_inv.eq
        rw [this]
        exact R.inv_mem hkc }
  have hI : IsPGroup 3 I := by
    rintro ⟨k, hk, c, hc, hkc⟩
    obtain ⟨m, hm⟩ := hRp ⟨k * c, hkc⟩
    have hm' : (k * c) ^ 3 ^ m = 1 := congrArg Subtype.val hm
    have hcm : Commute k c := hcomm k hk c hc
    rw [hcm.mul_pow] at hm'
    refine ⟨m, Subtype.ext ?_⟩
    show k ^ 3 ^ m = 1
    have h1 : k ^ 3 ^ m = (c ^ 3 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm'
    refine hKC _ (K.pow_mem hk _) ?_
    rw [h1]
    exact C.inv_mem (C.pow_mem hc _)
  have hJ : IsPGroup 3 J := by
    rintro ⟨c, hc, k, hk, hkc⟩
    obtain ⟨m, hm⟩ := hRp ⟨k * c, hkc⟩
    have hm' : (k * c) ^ 3 ^ m = 1 := congrArg Subtype.val hm
    have hcm : Commute k c := hcomm k hk c hc
    rw [hcm.mul_pow] at hm'
    refine ⟨m, Subtype.ext ?_⟩
    show c ^ 3 ^ m = 1
    have h1 : c ^ 3 ^ m = (k ^ 3 ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hm'
    have h2 : c ^ 3 ^ m ∈ K := by
      rw [h1]
      exact K.inv_mem (K.pow_mem hk _)
    exact hKC _ h2 (C.pow_mem hc _)
  intro r hr s hs
  obtain ⟨k, hk, c, hc, rfl⟩ := hdec r hr
  obtain ⟨k', hk', c', hc', rfl⟩ := hdec s hs
  have hkI : k ∈ I := ⟨hk, c, hc, hr⟩
  have hk'I : k' ∈ I := ⟨hk', c', hc', hs⟩
  have hcJ : c ∈ J := ⟨hc, k, hk, hr⟩
  have hc'J : c' ∈ J := ⟨hc', k', hk', hs⟩
  have hkk : k * k' = k' * k := hKab I (fun a ha => ha.1) hI k hkI k' hk'I
  have hcc : c * c' = c' * c := hCab J (fun a ha => ha.1) hJ c hcJ c' hc'J
  calc k * c * (k' * c') = k * (c * k') * c' := by group
    _ = k * (k' * c) * c' := by rw [hcomm k' hk' c hc]
    _ = (k * k') * (c * c') := by group
    _ = (k' * k) * (c' * c) := by rw [hkk, hcc]
    _ = k' * (k * c') * c := by group
    _ = k' * (c' * k) * c := by rw [hcomm k hk c' hc']
    _ = k' * c' * (k * c) := by group

end CFSG.LocalAnalysis.RankFourTheoremC
