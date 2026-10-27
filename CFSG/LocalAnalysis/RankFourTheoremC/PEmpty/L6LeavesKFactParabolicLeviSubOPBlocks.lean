module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOPRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOUCore
import CFSG.Timmesfeld.Orders.ClassicalOmega

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbedding Matrix QuadraticMap
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin

@[expose] def OrthPlusBlockData (p : ℕ) {B : Type} [Group B] (S : Subgroup B) : Prop :=
  CFSG.Open.IsQuasisimple ↥S ∧ ¬ p ∣ Nat.card (Subgroup.center ↥S) ∧
    p ∣ Nat.card (↥S ⧸ Subgroup.center ↥S) ∧ 3 ∣ Nat.card (↥S ⧸ Subgroup.center ↥S)

@[expose] def OrthPlusLeviData (Q : Type) [Group Q] (p : ℕ) : Prop :=
  ∃ (ι : Type) (_ : DecidableEq ι) (G : ι → Type) (_ : ∀ j, Group (G j)) (β : Q →* ∀ j, G j)
    (S : ∀ j, Subgroup (G j)), IsPGroup 2 β.ker ∧ Subgroup.pi Set.univ S ≤ β.range ∧
    ∀ g : Q, g ^ p = 1 → g ≠ 1 → ∃ j, OrthPlusBlockData p (S j)

theorem orthPlus_leviAt_of_leviData {S Q : Type} [Group S] [Finite S] [Group Q] [Finite Q]
    {K₀ : Subgroup S} (ρ : Q →* S) (hρK : ρ.range ≤ K₀) (hρ : Function.Injective ρ) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (hpQ : p ∣ Nat.card Q) (hL : OrthPlusLeviData Q p)
    (hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)) :
    ∃ (f : ℕ) (Y W : Subgroup S), f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧
      2 ≤ CFSG.Open.pRank f (⊤ : Subgroup S) ∧
      Y ≤ K₀ ∧ S622IsSimpleSection Y W ∧ f ∣ W.relIndex Y ∧
      p ∣ W.relIndex Y ∧ ¬ p ∣ Nat.card W := by
  obtain ⟨ι, _, G, _, β, Sj, hker, hpi, hblk⟩ := hL
  refine leviAt_of_blocks ρ hρK hp h5 hpQ β hker Sj hpi (fun g hg hg1 => ?_) (fun y hy j => ?_)
    hrank
  · obtain ⟨j, hj⟩ := hblk g hg hg1
    exact ⟨j, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2⟩
  · rw [hρ (hy.trans (map_one ρ).symm), map_one]
    exact Subgroup.one_mem _

theorem orthPlus_leviData_of_sum {Q : Type} [Group Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ι₁ ι₂ : Type} [Finite ι₁] [Finite ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {G₁ : ι₁ → Type} [∀ j, Group (G₁ j)] {G₂ : ι₂ → Type} [∀ j, Group (G₂ j)]
    (S₁ : ∀ j, Subgroup (G₁ j))
    (S₂ : ∀ j, Subgroup (G₂ j)) (β₁ : ∀ j, Q →* G₁ j) (β₂ : ∀ j, Q →* G₂ j)
    (hker : ∀ N : Subgroup Q, (∀ q ∈ N, (∀ j, β₁ j q = 1) ∧ ∀ j, β₂ j q = 1) → IsPGroup 2 N)
    (hs₁ : ∀ j, ∀ x ∈ S₁ j, ∃ q, β₁ j q = x ∧ (∀ j', j' ≠ j → β₁ j' q = 1) ∧ ∀ j', β₂ j' q = 1)
    (hs₂ : ∀ j, ∀ x ∈ S₂ j, ∃ q, β₂ j q = x ∧ (∀ j', j' ≠ j → β₂ j' q = 1) ∧ ∀ j', β₁ j' q = 1)
    (hb₁ : ∀ j (g : Q), β₁ j g ^ p = 1 → β₁ j g ≠ 1 → OrthPlusBlockData p (S₁ j))
    (hb₂ : ∀ j (g : Q), β₂ j g ^ p = 1 → β₂ j g ≠ 1 → OrthPlusBlockData p (S₂ j)) :
    OrthPlusLeviData Q p := by
  haveI : Fact p.Prime := ⟨hp⟩
  let S : ∀ j, Subgroup (plusSumGroup G₁ G₂ j) := fun j => match j with
    | .inl a => S₁ a
    | .inr b => S₂ b
  let β' : ∀ j, Q →* plusSumGroup G₁ G₂ j := fun j => match j with
    | .inl a => β₁ a
    | .inr b => β₂ b
  have hker' : IsPGroup 2 (MonoidHom.pi β').ker := by
    refine hker _ fun q hq => ⟨fun j => ?_, fun j => ?_⟩
    · exact congrFun (MonoidHom.mem_ker.1 hq) (Sum.inl j)
    · exact congrFun (MonoidHom.mem_ker.1 hq) (Sum.inr j)
  refine ⟨ι₁ ⊕ ι₂, inferInstance, plusSumGroup G₁ G₂, inferInstance, MonoidHom.pi β', S, hker',
    ?_, ?_⟩
  · rw [Subgroup.pi_le_iff]
    rintro (a | b) _ ⟨x, hx, rfl⟩
    · obtain ⟨q, hq, h1, h2⟩ := hs₁ a x hx
      refine ⟨q, funext fun j => ?_⟩
      rcases j with a' | b'
      · by_cases ha : a' = a
        · subst ha
          simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
          exact hq
        · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
          rw [Pi.mulSingle_eq_of_ne (fun h => ha (Sum.inl_injective h))]
          exact h1 a' ha
      · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
        rw [Pi.mulSingle_eq_of_ne Sum.inr_ne_inl]
        exact h2 b'
    · obtain ⟨q, hq, h1, h2⟩ := hs₂ b x hx
      refine ⟨q, funext fun j => ?_⟩
      rcases j with a' | b'
      · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
        rw [Pi.mulSingle_eq_of_ne Sum.inl_ne_inr]
        exact h2 a'
      · by_cases hb : b' = b
        · subst hb
          simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
          exact hq
        · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
          rw [Pi.mulSingle_eq_of_ne (fun h => hb (Sum.inr_injective h))]
          exact h1 b' hb
  · intro g hg hg1
    have hβ : MonoidHom.pi β' g ≠ 1 := by
      intro h
      obtain ⟨k, hk⟩ := hker' ⟨g, h⟩
      have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h2k : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      rw [orderOf_eq_prime hg hg1] at h2k
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2k))
    obtain ⟨j, hj⟩ : ∃ j, MonoidHom.pi β' g j ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hβ (funext hcon)
    refine ⟨j, ?_⟩
    have hpow : (MonoidHom.pi β' g j) ^ p = 1 := by
      rw [← Pi.pow_apply, ← map_pow, hg, map_one]
      rfl
    rcases j with a | b
    · exact hb₁ a g hpow hj
    · exact hb₂ b g hpow hj

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem orthPlus_gl_block_data {k p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K - 1)
    {x : GL (Fin k) K} (hx : x ^ p = 1) (hx1 : x ≠ 1) : OrthPlusBlockData p (slRange K k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card (GL (Fin k) K) := by
    rw [← orderOf_eq_prime hx hx1]
    exact orderOf_dvd_natCard x
  rw [LinearFlag.card_GL_eq] at hdvd
  obtain ⟨f, -, hqf⟩ := spFlag_card_eq_two_pow (K := K)
  have hp2 : p ≠ 2 := by omega
  have hpq : ¬ p ∣ Nat.card K ^ (k * (k - 1) / 2) := by
    intro h
    have h' := hp.dvd_of_dvd_pow h
    rw [hqf] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h'))
  have hprod : p ∣ ∏ j ∈ Finset.Icc 1 k, (Nat.card K ^ j - 1) :=
    ((Nat.Prime.dvd_mul hp).1 hdvd).resolve_left hpq
  obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hprod
  rw [Finset.mem_Icc] at hj
  have hj2 : 2 ≤ j := by
    by_contra h
    have h1 : j = 1 := by omega
    rw [h1, pow_one] at hpj
    exact hpK hpj
  have hk2 : 2 ≤ k := by omega
  have hq3 : 3 ≤ k ∨ 4 ≤ Nat.card K := by
    rcases spFlag_card_eq_two_or_four_le (K := K) with hq2 | hq4
    · left
      by_contra hlt
      push Not at hlt
      have hj' : j = 2 := by omega
      rw [hj', hq2] at hpj
      have h3 : p ∣ 3 := by simpa using hpj
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · exact Or.inr hq4
  exact (slBlock_data hk2 hq3 hp hpK hx hx1).2

theorem card_orthogonalGroup_quadPlus {m : ℕ} (hm : 3 ≤ m) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)) =
      2 * Nat.card (orthElementaryGroup (quadPlus m K)) := by
  have hn0 : 0 < m := by omega
  have hnd := nondegenerate_polarBilin_quadPlus m K
  exact CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_eq_two_mul hnd
    (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    (regular_quadPlus (by omega)).2
    (orthogonalGroup_le_closure_of_two_eq_zero (plusFamily_orth hn0) hnd CharTwo.two_eq_zero
      (fun x hx _ => eq_zero_of_mem_tailSpace_plusFamily hn0 hx)
      (fun x hx hx0 => absurd (eq_zero_of_mem_tailSpace_plusFamily hn0 hx) hx0) (by omega))

theorem orthPlus_mem_orthElementaryGroup_of_pow_eq_one {m : ℕ} (hm : 3 ≤ m) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)) (hx : x ^ p = 1) :
    x ∈ orthElementaryGroup (quadPlus m K) := by
  haveI := finite_plusAut (K := K) m
  have hcard := card_orthogonalGroup_quadPlus (K := K) hm
  have hEcard : Nat.card ((orthElementaryGroup (quadPlus m K)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K))) =
      Nat.card (orthElementaryGroup (quadPlus m K)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (orthElementaryGroup_le _)).toEquiv
  have hpos : 0 < Nat.card (orthElementaryGroup (quadPlus m K)) := Nat.card_pos
  have hidx : ((orthElementaryGroup (quadPlus m K)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K))).index = 2 := by
    have h1 := Subgroup.card_mul_index ((orthElementaryGroup (quadPlus m K)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)))
    rw [hEcard, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])
  have h := mem_of_pow_eq_one_of_index_two hidx hp hp2
    (x := (⟨x, hxO⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K))))
    (Subtype.ext (by simpa using hx))
  exact Subgroup.mem_subgroupOf.1 h

theorem three_dvd_card_plusElementary {m : ℕ} (hm : 3 ≤ m) :
    3 ∣ Nat.card (orthElementaryGroup (quadPlus m K)) := by
  have h := card_plusElementary (K := K) hm
  have h3 : (3 : ℤ) ∣ (Nat.card K : ℤ) ^ (2 * 1) - 1 := by
    have h1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    have h2 : ((3 : ℕ) : ℤ) ∣ ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 orthPlus_three_dvd_card_sq_sub_one
    push_cast [Nat.cast_sub h1] at h2
    simpa using h2
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 (m - 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hprod : (3 : ℤ) ∣ ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
    h3.trans (Finset.dvd_prod_of_mem (fun i => ((Nat.card K : ℤ) ^ (2 * i) - 1)) hmem)
  have hz : (3 : ℤ) ∣ (Nat.card (orthElementaryGroup (quadPlus m K)) : ℤ) := by
    rw [h]
    exact Dvd.dvd.mul_left hprod _
  exact_mod_cast hz

theorem orthPlus_res_block_data {m p : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (h5 : 5 ≤ p)
    {x : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)) (hx : x ^ p = 1)
    (hx1 : x ≠ 1) : OrthPlusBlockData p (orthElementaryGroup (quadPlus m K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxE : x ∈ orthElementaryGroup (quadPlus m K) :=
    orthPlus_mem_orthElementaryGroup_of_pow_eq_one hm hp (by omega) hxO hx
  have hord : orderOf (⟨x, hxE⟩ : ↥(orthElementaryGroup (quadPlus m K))) = p :=
    orderOf_eq_prime (Subtype.ext (by simpa using hx)) fun h => hx1 (congrArg Subtype.val h)
  have hpE : p ∣ Nat.card ↥(orthElementaryGroup (quadPlus m K)) := hord ▸ orderOf_dvd_natCard _
  exact blk_of_trivial_center (isQuasisimple_plusElementary hm).1
    (isQuasisimple_plusElementary hm).2 hp hpE (three_dvd_card_plusElementary hm)

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
