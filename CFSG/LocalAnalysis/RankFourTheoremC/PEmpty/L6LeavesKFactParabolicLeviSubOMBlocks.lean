module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOMRank
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.GroupTheory.WeirSylow

theorem orthMinus_add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · refine ⟨q - 1, ?_⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    refine Nat.sub_eq_of_eq_add ?_
    ring

section GLBlocks

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem orthMinus_three_le_of_pow_eq_one {f k : ℕ} (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) {x : GL (Fin k) K} (hx : x ^ p = 1)
    (hx1 : x ≠ 1) : 3 ≤ k := by
  by_contra hk
  push Not at hk
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime hx hx1
  have hdvd : p ∣ Nat.card (GL (Fin k) K) := hord ▸ orderOf_dvd_natCard x
  rw [LinearFlag.card_GL_eq] at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
  · exact orthMinus_not_dvd_card_of_two_pow hK hp (by omega) (hp.dvd_of_dvd_pow h1)
  · obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h1
    rw [Finset.mem_Icc] at hj
    have hj2 : j ∣ 2 := by
      have : j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl <;> simp
    exact hpq (hpj.trans (Nat.pow_sub_one_dvd_pow_sub_one _ hj2))

theorem orthMinus_gl_block_data {f k : ℕ} (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) {x : GL (Fin k) K} (hx : x ^ p = 1)
    (hx1 : x ≠ 1) :
    CFSG.Open.IsQuasisimple ↥(slRange K k) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥(slRange K k)) ∧
      p ∣ Nat.card (↥(slRange K k) ⧸ Subgroup.center ↥(slRange K k)) ∧
      3 ∣ Nat.card (↥(slRange K k) ⧸ Subgroup.center ↥(slRange K k)) := by
  have hk3 := orthMinus_three_le_of_pow_eq_one hK hp h5 hpq hx hx1
  have hpK : ¬ p ∣ Nat.card K - 1 := fun h => hpq (h.trans (Nat.sub_one_dvd_pow_sub_one _ 2))
  obtain ⟨-, h2, h3, h4, h5'⟩ := slBlock_data (by omega) (Or.inl hk3) hp hpK hx hx1
  exact ⟨h2, h3, h4, h5'⟩

end GLBlocks

section Res

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem orthMinus_card_orthogonalGroup_tail_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm K b c))) =
      2 * (Nat.card K + 1) := by
  let ψ : (quadTail 0 (minusTailForm K b c)).IsometryEquiv (quadMinus 1 K b c) :=
    minusTailIsometry 1 K b c
  have hψ := natCard_orthogonalGroup_congr ψ
  have hO := natCard_orthogonalGroup_quadMinus hirr 0
  rw [← hψ] at hO
  have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := by simp
  rw [h0, Finset.prod_empty] at hO
  simp only [zero_mul, pow_zero, mul_one, zero_add, pow_one] at hO
  exact_mod_cast hO

theorem orthMinus_res_block_data {f m : ℕ} (hK : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1)
    {x : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)))}
    (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    CFSG.Open.IsQuasisimple ↥(orthResDer K b c m) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥(orthResDer K b c m)) ∧
      p ∣ Nat.card (↥(orthResDer K b c m) ⧸ Subgroup.center ↥(orthResDer K b c m)) ∧
      3 ∣ Nat.card (↥(orthResDer K b c m) ⧸ Subgroup.center ↥(orthResDer K b c m)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime hx hx1
  haveI : Finite (((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin m ⊕ Fin m → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exfalso
    have hdvd : p ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (quadTail 0 (minusTailForm K b c))) := hord ▸ orderOf_dvd_natCard x
    rw [orthMinus_card_orthogonalGroup_tail_zero hirr] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
      omega
    · exact hpq (h2.trans (orthMinus_add_one_dvd_sq_sub_one _))
  · have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · have := Finite.one_lt_card (α := K)
        rw [hK] at this
        norm_num at this
      · exact h
    obtain ⟨hsimple, hna, hcard⟩ := orthResDer_facts hK hm hirr
    haveI := hsimple
    obtain ⟨hq, hZ⟩ := orthMinus_isQuasisimple_of_simple hna
    have hxΩ := orthMinus_mem_orthResDer_of_pow_eq_one hK hm hirr hp (by omega) hx
    let x' : ↥(orthResDer K b c m) := ⟨x, hxΩ⟩
    have hx'p : x' ^ p = 1 := by
      apply Subtype.ext
      have := congrArg (fun y : ↥(TauCeti.QuadraticMap.orthogonalGroup
        (quadTail m (minusTailForm K b c))) => (y : ((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃ₗ[K]
          ((Fin m ⊕ Fin m → K) × (Fin 2 → K)))) hx
      simpa [x'] using this
    have hx'1 : x' ≠ 1 := by
      intro h
      apply hx1
      apply Subtype.ext
      have h2 := congrArg Subtype.val h
      exact h2
    have hpΩ : p ∣ Nat.card ↥(orthResDer K b c m) :=
      (orderOf_eq_prime hx'p hx'1) ▸ orderOf_dvd_natCard x'
    have h3 : 3 ∣ Nat.card ↥(orthResDer K b c m) := by
      rw [hcard]
      exact orthMinus_three_dvd_ordTwistedD hf hm
    exact blk_of_trivial_center hq hZ hp hpΩ h3

end Res

section Blocks

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

theorem orthMinus_orthParab_hblk {f : ℕ} (hd : OrthCuts r d) (hK : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) (g : ↥(orthParab r (minusTailForm K b c) d))
    (hg : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ j, CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥(orthLeviBlock K r d b c j)) ∧
      p ∣ Nat.card (↥(orthLeviBlock K r d b c j) ⧸
        Subgroup.center ↥(orthLeviBlock K r d b c j)) ∧
      3 ∣ Nat.card (↥(orthLeviBlock K r d b c j) ⧸
        Subgroup.center ↥(orthLeviBlock K r d b c j)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf g = p := orderOf_eq_prime hg hg1
  have hβ : orthLeviHom b c hd g ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := isPGroup_ker_orthLeviHom hd ⟨g, h⟩
    have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2k : p ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hk'
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2k)
    omega
  obtain ⟨j, hj⟩ : ∃ j, orthLeviHom b c hd g j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hβ (funext hcon)
  have hpow : (orthLeviHom b c hd g) ^ p = 1 := by rw [← map_pow, hg, map_one]
  refine ⟨j, ?_⟩
  rcases j with l | u
  · have h2 := congrFun hpow (.inl l)
    rw [Pi.pow_apply, Pi.one_apply] at h2
    exact orthMinus_gl_block_data hK hp h5 hpq h2 hj
  · let x' : ↥(TauCeti.QuadraticMap.orthogonalGroup
        (quadTail (r - d (Fin.last s)) (minusTailForm K b c))) :=
      ⟨orthResHom (minusTailForm K b c) hd g, orthResHom_mem_orthogonalGroup hd g⟩
    have hx' : x' ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change (orthResHom (minusTailForm K b c) hd g) ^ p = 1
      rw [← map_pow, hg, map_one]
    have hx'1 : x' ≠ 1 := fun h => hj (congrArg Subtype.val h)
    exact orthMinus_res_block_data hK hirr hp h5 hpq hx' hx'1

end Blocks

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
