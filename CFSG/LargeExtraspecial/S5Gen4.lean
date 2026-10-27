module

public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Module QuadraticMap CFSG.LargeExtraspecial.OrthoF2

section Singular

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem ncard_singular_le_nine (h4 : finrank (ZMod 2) V = 4) {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {a : V} (ha : a ≠ 0) (hQa : Q a = 0) :
    {v : V | v ≠ 0 ∧ Q v = 0}.ncard ≤ 9 := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype V := Fintype.ofFinite V
  let φ : V →ₗ[ZMod 2] ZMod 2 := Q.polarBilin.flip a
  have hφ : ∀ v, φ v = polar Q v a := fun v => rfl
  have hφa : φ a = 0 := by
    rw [hφ, polar_self, hQa, smul_zero]
  have hφne : ∃ b, φ b = 1 := by
    by_contra h
    push Not at h
    apply ha
    refine hQ.2 a fun v => ?_
    rw [QuadraticMap.polarBilin_apply_apply, ← hφ]
    exact (zmod2_eq_zero_or_eq_one (φ v)).resolve_right (h v)
  obtain ⟨b, hb⟩ := hφne
  have hrange : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact ⟨c • b, by rw [map_smul, hb, smul_eq_mul, mul_one]⟩
  have hker : finrank (ZMod 2) (LinearMap.ker φ) = 3 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange, finrank_top, Module.finrank_self, h4] at h1
    omega
  have hV : Fintype.card V = 16 := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2), h4,
      Nat.card_zmod]
    norm_num
  have hK : (Finset.univ.filter fun v => φ v = 0).card = 8 := by
    rw [← Fintype.card_subtype]
    have : Fintype.card {v // φ v = 0} = Nat.card (LinearMap.ker φ) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun v => LinearMap.mem_ker.symm)
    rw [this, Module.natCard_eq_pow_finrank (K := ZMod 2), hker, Nat.card_zmod]
    norm_num
  have hK1 : (Finset.univ.filter fun v => ¬ φ v = 0).card = 8 := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun v => φ v = 0
    rw [hK, Finset.card_univ, hV] at this
    omega
  have hQadd : ∀ v, Q (v + a) = Q v + φ v := by
    intro v
    rw [hφ]
    simp only [QuadraticMap.polar, hQa]
    ring
  have hφadd : ∀ v, φ (v + a) = φ v := fun v => by rw [map_add, hφa, add_zero]
  have hC : ∃ v, φ v = 0 ∧ Q v ≠ 0 := by
    by_contra h
    push Not at h
    have hle : LinearMap.ker φ ≤
        LinearMap.BilinForm.orthogonal Q.polarBilin (LinearMap.ker φ) := by
      intro v hv
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
        h _ (LinearMap.mem_ker.mp (add_mem hw hv)), h _ (LinearMap.mem_ker.mp hw),
        h _ (LinearMap.mem_ker.mp hv), sub_zero, sub_zero]
    have h1 := Submodule.finrank_mono hle
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, h4, hker] at h1
    omega
  obtain ⟨v₀, hv₀φ, hv₀Q⟩ := hC
  set S₀ := Finset.univ.filter fun v => φ v = 0 ∧ Q v = 0
  set N₀ := Finset.univ.filter fun v => φ v = 0 ∧ ¬ Q v = 0
  set S₁ := Finset.univ.filter fun v => ¬ φ v = 0 ∧ Q v = 0
  set N₁ := Finset.univ.filter fun v => ¬ φ v = 0 ∧ ¬ Q v = 0
  have h0 : S₀.card + N₀.card = 8 := by
    have := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun v => φ v = 0) fun v => Q v = 0
    rwa [Finset.filter_filter, Finset.filter_filter, hK] at this
  have h1 : S₁.card + N₁.card = 8 := by
    have := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun v => ¬ φ v = 0) fun v => Q v = 0
    rwa [Finset.filter_filter, Finset.filter_filter, hK1] at this
  have hS₁ : S₁.card ≤ N₁.card := by
    refine Finset.card_le_card_of_injOn (fun v => v + a) (fun v hv => ?_)
      (fun v _ w _ h => add_right_cancel h)
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    replace hv := hv.2
    have hv1 : φ v = 1 := (zmod2_eq_zero_or_eq_one _).resolve_left hv.1
    refine ⟨by rw [hφadd]; exact hv.1, ?_⟩
    rw [hQadd, hv.2, hv1]
    decide
  have hN₀ : 2 ≤ N₀.card := by
    have hne : v₀ ≠ v₀ + a := fun h => ha (by
      have := congrArg (fun w => w - v₀) h
      simpa using this.symm)
    have hsub : ({v₀, v₀ + a} : Finset V) ⊆ N₀ := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [N₀, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨hv₀φ, hv₀Q⟩
      · refine ⟨by rw [hφadd]; exact hv₀φ, ?_⟩
        rw [hQadd, hv₀φ, add_zero]
        exact hv₀Q
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne] at this
  have hS : (Finset.univ.filter fun v => Q v = 0).card = S₀.card + S₁.card := by
    have := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun v => Q v = 0) fun v => φ v = 0
    rw [Finset.filter_filter, Finset.filter_filter] at this
    have e₀ : (Finset.univ.filter fun v => Q v = 0 ∧ φ v = 0) = S₀ :=
      Finset.filter_congr fun _ _ => and_comm
    have e₁ : (Finset.univ.filter fun v => Q v = 0 ∧ ¬ φ v = 0) = S₁ :=
      Finset.filter_congr fun _ _ => and_comm
    rw [e₀, e₁] at this
    exact this.symm
  have hset : {v : V | v ≠ 0 ∧ Q v = 0} =
      ↑((Finset.univ.filter fun v => Q v = 0).erase 0) := by
    ext v
    simp [and_comm]
  rw [hset, Set.ncard_coe_finset, Finset.card_erase_of_mem (by simp)]
  omega

end Singular

theorem exists_sq_eq_of_odd {X : Type*} [Monoid X] {u : X} (hu : Odd (orderOf u)) :
    ∃ k : ℕ, (u ^ k) ^ 2 = u := by
  obtain ⟨k, hk⟩ := hu
  refine ⟨k + 1, ?_⟩
  rw [← pow_mul, show (k + 1) * 2 = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
    pow_orderOf_eq_one, one_mul]

theorem mem_of_sq_mem {X : Type*} [Group X] {K : Subgroup X} {w : X} (hw : Odd (orderOf w))
    (h : w ^ 2 ∈ K) : w ∈ K := by
  obtain ⟨k, hk⟩ := exists_sq_eq_of_odd hw
  rw [← hk, ← pow_mul, mul_comm, pow_mul]
  exact K.pow_mem h k

end CFSG.LargeExtraspecial.S5
