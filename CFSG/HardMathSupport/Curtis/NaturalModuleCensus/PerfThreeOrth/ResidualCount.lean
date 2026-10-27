module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.ResidualDecomp
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.CharSum
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.ResidualEichler

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal

section Orth

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem res_map_comb {w a u : V} (hw : Q w = 0) (ha : Q a = 0) (hwa : polar Q w a = 1)
    (huw : polar Q u w = 0) (hua : polar Q u a = 0) (α β : K) :
    Q (α • w + β • a + u) = α * β + Q u := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  have hau : polar Q a u = 0 := by rw [polar_comm, hua]
  rw [QuadraticMap.map_add Q (α • w + β • a) u, QuadraticMap.map_add Q (α • w) (β • a)]
  simp only [QuadraticMap.map_smul, polar_add_left, polar_smul_left, polar_smul_right, hw, ha, hwa,
    hwu, hau, smul_eq_mul]
  ring

end Orth

section Count

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem res_exists_two_singular (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x)
    (hdim : finrank K V = 8)
    (hmax : ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0)
    (hfix : finrank K (fixedSpace x) = 4) {w a : V} (hwx : x w = w) (hax : x a = a)
    (hQw : Q w = 0) (hQa : Q a = 0) (hwa : polar Q w a = 1) :
    ∃ s₁ s₂ : V, x s₁ = s₁ ∧ x s₂ = s₂ ∧ Q s₁ = 0 ∧ Q s₂ = 0 ∧
      polar Q s₁ w = 0 ∧ polar Q s₁ a = 0 ∧ polar Q s₂ w = 0 ∧ polar Q s₂ a = 0 ∧
      polar Q s₁ s₂ ≠ 0 := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Fintype V := Fintype.ofFinite V
  have : Fintype K := Fintype.ofFinite K
  have hQ := res_polarBilin_nondegenerate hx
  obtain ⟨U, hU, hUQ⟩ := hmax
  have hS : ∑ v, chi (Q v) = 16 := by
    rw [charSum_eq_of_totallySingular hK hQ hUQ (by omega), Module.natCard_eq_pow_finrank (K := K),
      hK, hU]
    norm_num
  have hmod := charSum_modEq_fixed Q x (fun v => res_map_x hx v) hx.pow_eq_one
  set F1 : Finset V := Finset.univ.filter (fun v => x v = v) with hF1
  have hF1card : F1.card = 16 := by
    have h1 : Nat.card (fixedSpace x) = 16 := by
      rw [Module.natCard_eq_pow_finrank (K := K), hK, hfix]
      norm_num
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    rw [← h1, hF1]
    congr 1
    ext v
    simp [mem_fixedSpace]
  set N : Finset V := F1.filter (fun u => polar Q u w = 0 ∧ polar Q u a = 0) with hN
  have hmemN : ∀ u, u ∈ N ↔ x u = u ∧ polar Q u w = 0 ∧ polar Q u a = 0 := by
    intro u
    simp [hN, hF1]
  have hww : polar Q w w = 0 := CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hQw
  have haa : polar Q a a = 0 := CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hQa
  have haw : polar Q a w = 1 := by rw [polar_comm, hwa]
  have hleft : ∀ v ∈ F1, (polar Q v a • w + polar Q v w • a + (v - polar Q v a • w - polar Q v w • a)) = v := by
    intro v _
    module
  have hbij : ∀ f : V → ℤ, ∑ v ∈ F1, f v =
      ∑ p ∈ (Finset.univ : Finset (K × K)) ×ˢ N, f (p.1.1 • w + p.1.2 • a + p.2) := by
    intro f
    refine Finset.sum_nbij'
      (fun v => ((polar Q v a, polar Q v w), v - polar Q v a • w - polar Q v w • a))
      (fun p => p.1.1 • w + p.1.2 • a + p.2) ?_ ?_ ?_ ?_ ?_
    · intro v hv
      have hv' : x v = v := by simpa [hF1] using hv
      simp only [Finset.mem_product, Finset.mem_univ, true_and, hmemN, map_sub, map_smul, hv', hwx,
        hax, polar_sub_left, polar_smul_left, hww, haw, hwa, haa, smul_eq_mul]
      constructor <;> ring
    · rintro ⟨⟨α, β⟩, u⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, true_and, hmemN] at hp
      simp only [hF1, Finset.mem_filter, Finset.mem_univ, true_and, map_add, map_smul, hwx, hax,
        hp.1]
    · exact hleft
    · rintro ⟨⟨α, β⟩, u⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, true_and, hmemN] at hp
      obtain ⟨-, h1, h2⟩ := hp
      simp only [polar_add_left, polar_smul_left, h1, h2, hww, haw, hwa, haa, smul_eq_mul]
      simp only [mul_one, mul_zero, add_zero, zero_add, Prod.mk.injEq, true_and]
      abel
    · intro v hv
      rw [hleft v hv]
  have hsplit : ∑ v ∈ F1, chi (Q v) = (∑ c : K × K, chi (c.1 * c.2)) * ∑ u ∈ N, chi (Q u) := by
    rw [hbij, Finset.sum_product, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨-, h1, h2⟩ := (hmemN u).1 hu
    rw [res_map_comb hQw hQa hwa h1 h2, chi_add hK]
  have hNcard : N.card = 4 := by
    have h := hbij (fun _ => (1 : ℤ))
    rw [Finset.sum_const, Finset.sum_const, Finset.card_product, Finset.card_univ,
      Fintype.card_prod, ← Nat.card_eq_fintype_card, hK, hF1card] at h
    simp only [nsmul_eq_mul, mul_one] at h
    omega
  have hKK : ∑ c : K × K, chi (c.1 * c.2) = 2 := by
    have huniv : (Finset.univ : Finset K) = {0, 1} := by
      have hc : ({0, 1} : Finset K).card = Fintype.card K := by
        rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK]
      exact (Finset.eq_univ_of_card _ hc).symm
    rw [Fintype.sum_prod_type]
    simp [huniv, chi_zero, chi_of_ne_zero (one_ne_zero (α := K))]
  rw [hS, hsplit, hKK, sum_chi_eq_card_sub] at hmod
  have hsum := Finset.card_filter_add_card_filter_not (s := N) (fun v => Q v = 0)
  set Z : Finset V := N.filter (fun v => Q v = 0) with hZ
  have h0 : (0 : V) ∈ Z := by
    simp [hZ, hmemN, polar_zero_left]
  have hZcard : Z.card = 3 := by
    have hpos : 0 < Z.card := Finset.card_pos.2 ⟨0, h0⟩
    unfold Int.ModEq at hmod
    omega
  have hT : (Z.erase 0).card = 2 := by rw [Finset.card_erase_of_mem h0, hZcard]
  obtain ⟨s₁, s₂, hne, hTe⟩ := Finset.card_eq_two.1 hT
  have hs₁ : s₁ ∈ Z.erase 0 := by rw [hTe]; simp
  have hs₂ : s₂ ∈ Z.erase 0 := by rw [hTe]; simp
  simp only [Finset.mem_erase, hZ, Finset.mem_filter, hmemN] at hs₁ hs₂
  refine ⟨s₁, s₂, hs₁.2.1.1, hs₂.2.1.1, hs₁.2.2, hs₂.2.2, hs₁.2.1.2.1, hs₁.2.1.2.2,
    hs₂.2.1.2.1, hs₂.2.1.2.2, ?_⟩
  intro hp
  have hQs : Q (s₁ + s₂) = 0 := by
    rw [QuadraticMap.map_add Q, hs₁.2.2, hs₂.2.2, hp]
    simp
  have hmem : s₁ + s₂ ∈ Z.erase 0 := by
    simp only [Finset.mem_erase, hZ, Finset.mem_filter, hmemN]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, hQs⟩
    · intro h
      apply hne
      have : -s₂ = s₂ := neg_eq_of_add_eq_zero_right (res_add_self K s₂)
      rw [← this]
      exact eq_neg_of_add_eq_zero_left h
    · rw [map_add, hs₁.2.1.1, hs₂.2.1.1]
    · rw [polar_add_left, hs₁.2.1.2.1, hs₂.2.1.2.1, add_zero]
    · rw [polar_add_left, hs₁.2.1.2.2, hs₂.2.1.2.2, add_zero]
  rw [hTe] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact hs₂.1 (by simpa using h)
  · exact hs₁.1 (by simpa using h)

end Count

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
