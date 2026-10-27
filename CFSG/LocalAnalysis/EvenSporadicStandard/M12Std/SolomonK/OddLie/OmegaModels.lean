module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.OmegaFrameGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.PosE64
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open CFSG.ClassicalGroups.Orthogonal CFSG.GH74.Filter CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin

section Transfer

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem posE64_statedProj_statedOmega [Finite K] {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) (h2 : (2 : K) ≠ 0) (Fr : EqFrame7 Q) :
    PosE64 (StatedProj (StatedOmega Q₀)) := by
  have hΩ := statedOmega_eq_comap hQ
  let Φ : StatedOmega Q₀ →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (toLinEquiv ι K).toMonoidHom.comp (StatedOmega Q₀).subtype
  have hΦinj : Function.Injective Φ := (toLinEquiv ι K).injective.comp Subtype.val_injective
  have hmem : ∀ g : (ι → K) ≃ₗ[K] (ι → K),
      g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      (toLinEquiv ι K).symm g ∈ StatedOmega Q₀ := fun g hg => by
    rw [hΩ, Subgroup.mem_comap]
    simpa using hg
  let X : ∀ g : (ι → K) ≃ₗ[K] (ι → K),
      g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      StatedOmega Q₀ := fun g hg => ⟨(toLinEquiv ι K).symm g, hmem g hg⟩
  have hΦX : ∀ g hg, Φ (X g hg) = g := fun g hg => (toLinEquiv ι K).apply_symm_apply g
  let x : Fin 6 → StatedOmega Q₀ := fun k => X (Fr.g k) (Fr.g_mem h2 k)
  let T : StatedOmega Q₀ := X Fr.tau (Fr.tau_mem h2)
  have hΦx : ∀ k, Φ (x k) = Fr.g k := fun k => hΦX _ (Fr.g_mem h2 k)
  have hΦT : Φ T = Fr.tau := hΦX _ (Fr.tau_mem h2)
  let π := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q₀))
  have hπ : ∀ z : StatedOmega Q₀, π z = 1 → Φ z ∈ scalars K (ι → K) := fun z hz => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      mem_statedScalars_iff] at hz
    exact hz
  have hxsq : ∀ k, x k * x k = 1 := fun k =>
    hΦinj (by rw [map_mul, hΦx, map_one, Fr.g_sq])
  have : Finite (StatedProj (StatedOmega Q₀)) := inferInstance
  refine posE64_of_frame (fun k => π (x k)) (π T) cyc5 ?_ ?_ ?_ ?_ ?_ cyc5_pow
  · intro k
    rw [← map_mul, hxsq, map_one]
  · intro i j
    rw [← map_mul, ← map_mul]
    exact congrArg π (hΦinj (by rw [map_mul, map_mul, hΦx, hΦx, Fr.g_comm]))
  · intro a ha hone
    apply Fr.g_not_mem_scalars h2 a ha
    have h1 : π (List.ofFn fun i => x i ^ (a i : ℕ)).prod = 1 := by
      rw [map_list_prod, List.map_ofFn]
      simpa [Function.comp_def, map_pow] using hone
    have h3 : Φ (List.ofFn fun i => x i ^ (a i : ℕ)).prod =
        (List.ofFn fun k => Fr.g k ^ (a k : ℕ)).prod := by
      rw [map_list_prod, List.map_ofFn]
      simp [Function.comp_def, map_pow, hΦx]
    rw [← h3]
    exact hπ _ h1
  · intro i j hij
    have hij' : π (x i) = π (x j) := hij
    by_contra hne
    apply Fr.g_mul_g_not_mem_scalars h2 hne
    have h1 : π (x i * x j) = 1 := by
      rw [map_mul, hij', ← map_mul, hxsq, map_one]
    have h3 := hπ _ h1
    rwa [map_mul, hΦx, hΦx] at h3
  · intro k
    rw [← map_inv, ← map_mul, ← map_mul]
    refine congrArg π (hΦinj ?_)
    rw [map_mul, map_mul, map_inv, hΦT, hΦx, hΦx, Fr.tau_conj h2]

end Transfer

section Models

open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

theorem posE64_POmegaOdd {G : Type} [Group G] {n p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel G .POmegaOdd n p f) : PosE64 G := by
  obtain ⟨⟨hp, hf, hn3, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP p hp2
  obtain ⟨s, t, hst⟩ := (odd_field_two_dimensional_quaternion_matrices
    (by rw [ringChar.eq K p]; exact hp2)).1
  exact PosE64.of_mulEquiv e.symm (posE64_statedProj_statedOmega (coe_quadOdd n K) h2
    ((oddRefFrame K hn3).toEqFrame7 hst))

theorem posE64_POmegaPlus {G : Type} [Group G] {n p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel G .POmegaPlus n p f) : PosE64 G := by
  obtain ⟨⟨hp, hf, hn4⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP p hp2
  obtain ⟨s, t, hst⟩ := (odd_field_two_dimensional_quaternion_matrices
    (by rw [ringChar.eq K p]; exact hp2)).1
  exact PosE64.of_mulEquiv e.symm (posE64_statedProj_statedOmega (coe_quadPlus n K) h2
    ((plusRefFrame K hn4).toEqFrame7 hst))

theorem posE64_POmegaMinus {G : Type} [Group G] {n p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel G .POmegaMinus n p f) : PosE64 G := by
  obtain ⟨⟨hp, hf, hn4⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP p hp2
  obtain ⟨s, t, hst⟩ := (odd_field_two_dimensional_quaternion_matrices
    (by rw [ringChar.eq K p]; exact hp2)).1
  exact PosE64.of_mulEquiv e.symm (posE64_statedProj_statedOmega (coe_quadMinus n K b c) h2
    ((minusRefFrame K b c hn4).toEqFrame7 hst))

end Models

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
