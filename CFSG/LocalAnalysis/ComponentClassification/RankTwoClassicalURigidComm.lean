module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidPerf

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

theorem eq_of_commute_eichM {Z : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K}
    (hZ : ∀ (a : Fin ε → K) (c : K), c + h.bar c = ∑ k, h.bar (a k) * a k →
      Z * eichM h.bar a c = eichM h.bar a c * Z) :
    ∃ μ β : K, Z = μ • 1 + β • Matrix.single hE hF 1 := by
  have h1 := hZ 0 1 (by simp [CharTwo.add_self_eq_zero])
  have hce : ∀ i, i ≠ hE → Z i hE = 0 := fun i hi => by
    have := congrFun (congrFun h1 i) hF
    rcases i with i | k | i
    · exact absurd (by rw [Fin.eq_zero i]) hi
    all_goals simpa [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero] using this
  have hrf : ∀ j, j ≠ hF → Z hF j = 0 := fun j hj => by
    have := congrFun (congrFun h1 hE) j
    rcases j with j | l | j
    · simpa [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, eq_comm] using this
    · simpa [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, eq_comm] using this
    · exact absurd (by rw [Fin.eq_zero j]) hj
  have hμ : Z hE hE = Z hF hF := by
    have := congrFun (congrFun h1 hE) hF
    simp [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero] at this
    linear_combination this
  have hk : ∀ (k : Fin ε) (t : K), t * Z hE (.inr (.inl k)) = h.bar t * Z (.inr (.inl k)) hF ∧
      (t = 1 → (∀ l, Z (.inr (.inl l)) (.inr (.inl k)) = if l = k then Z hF hF else 0) ∧
        ∀ l, Z (.inr (.inl k)) (.inr (.inl l)) = if l = k then Z hE hE else 0) := by
    intro k t
    obtain ⟨c, hc⟩ := exists_valid h (Pi.single k t)
    have hX := hZ _ _ hc
    refine ⟨?_, fun ht => ⟨fun l => ?_, fun l => ?_⟩⟩
    · have := congrFun (congrFun hX hE) hF
      simp [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, Pi.single_apply, apply_ite,
        ite_mul, Finset.sum_ite_eq'] at this
      linear_combination this - c * hμ
    · subst ht
      have := congrFun (congrFun hX (.inr (.inl l))) hF
      by_cases hlk : l = k
      · subst hlk
        simp [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, Pi.single_apply, apply_ite,
          ite_mul, Finset.sum_ite_eq', hce] at this ⊢
        linear_combination this
      · simp [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, Pi.single_apply, apply_ite,
          ite_mul, Finset.sum_ite_eq', hce, hlk] at this ⊢
        exact this
    · subst ht
      have := congrFun (congrFun hX hE) (.inr (.inl l))
      by_cases hlk : l = k
      · subst hlk
        simp [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, Pi.single_apply, apply_ite,
          ite_mul, Finset.sum_ite_eq', hrf] at this ⊢
        linear_combination -this
      · simp [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, Pi.single_apply, apply_ite,
          ite_mul, Finset.sum_ite_eq', hrf, hlk] at this ⊢
        exact this
  obtain ⟨θ, hθ⟩ := h.exists_bar_ne
  have hez : ∀ k, Z hE (.inr (.inl k)) = 0 := fun k => by
    have h1' := (hk k 1).1
    have hθ' := (hk k θ).1
    rw [map_one, one_mul, one_mul] at h1'
    rw [← h1'] at hθ'
    have : (θ - h.bar θ) * Z hE (.inr (.inl k)) = 0 := by linear_combination hθ'
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hθ))
  have hzf : ∀ k, Z (.inr (.inl k)) hF = 0 := fun k => by
    have h1' := (hk k 1).1
    rw [map_one, one_mul, one_mul, hez] at h1'
    exact h1'.symm
  refine ⟨Z hF hF, Z hE hF, ?_⟩
  ext i j
  rcases i with i | k | i <;> rcases j with j | l | j
  · simp [Fin.eq_zero, hμ]
  · simp [Fin.eq_zero, hez]
  · simp [Fin.eq_zero]
  · simp [Fin.eq_zero, hce]
  · have := ((hk k 1).2 rfl).2 l
    rw [this, hμ]
    by_cases hlk : l = k
    · subst hlk
      simp
    · simp [hlk, Ne.symm hlk]
  · simp [Fin.eq_zero, hzf]
  · simp [Fin.eq_zero, hrf]
  · simp [Fin.eq_zero, hrf]
  · simp [Fin.eq_zero]

@[expose] def eichSub : Subgroup (hypSU h 1 ε) where
  carrier := {g | ∃ (a : Fin ε → K) (c : K),
    ((g : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) = eichM h.bar a c}
  mul_mem' := by
    rintro _ _ ⟨a, c, ha⟩ ⟨a', c', ha'⟩
    exact ⟨_, _, by rw [Subgroup.coe_mul, Units.val_mul, ha, ha', eichM_mul]⟩
  one_mem' := ⟨0, 0, by rw [eichM_zero]; rfl⟩
  inv_mem' := by
    rintro g ⟨a, c, ha⟩
    refine ⟨a, c + ∑ k, h.bar (a k) * a k, ?_⟩
    rw [coe_inv_hypSU]
    exact Units.inv_eq_of_mul_eq_one_left (by rw [ha]; exact eichM_inv_mul_eichM _ a c)

theorem eich_mem_eichSub {a : Fin ε → K} {c : K} (hc : c + h.bar c = ∑ k, h.bar (a k) * a k) :
    eich h hc ∈ eichSub h :=
  ⟨a, c, rfl⟩

theorem eichM_pow_four (a : Fin ε → K) (c : K) : eichM h.bar a c ^ 4 = 1 := by
  have h0 : a + a = 0 := funext fun k => CharTwo.add_self_eq_zero (a k)
  have hsq : eichM h.bar a c ^ 2 = eichM h.bar 0 (∑ k, h.bar (a k) * a k) := by
    rw [sq, eichM_mul, h0, CharTwo.add_self_eq_zero, zero_add]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, sq, eichM_mul, add_zero,
    CharTwo.add_self_eq_zero]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  exact eichM_zero _

theorem isPGroup_eichSub : IsPGroup 2 (eichSub (ε := ε) h) := by
  rintro ⟨g, a, c, ha⟩
  refine ⟨2, Subtype.ext (Subtype.ext (Units.ext ?_))⟩
  simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
    Units.val_one]
  rw [ha]
  exact eichM_pow_four h a c

end CFSG.ComponentClassification.RankTwoClassical.URigid
