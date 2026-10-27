module

public import CFSG.LieType.SeitzGeneration.OrthCubeBlocks

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

section Reduce

theorem exists_nat_pow_of_pow_eq_one {G : Type*} [Group G] {g : G} {p : ℕ} (hp : 0 < p)
    (hg : g ^ p = 1) (i : ℤ) : ∃ a : ℕ, a < p ∧ g ^ i = g ^ a ∧ ((p : ℤ) ∣ i ↔ a = 0) := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have h0 : 0 ≤ i % (p : ℤ) := Int.emod_nonneg i hp'.ne'
  have hlt : i % (p : ℤ) < p := Int.emod_lt_of_pos i hp'
  refine ⟨(i % (p : ℤ)).toNat, by omega, ?_, ?_⟩
  · rw [zpow_eq_zpow_emod' i hg, ← zpow_natCast, Int.toNat_of_nonneg h0]
  · rw [Int.dvd_iff_emod_eq_zero]
    omega

theorem indep_of_nat {G : Type*} [Group G] {p : ℕ} (hp : 0 < p) {e₁ e₂ e₃ : G} (h₁ : e₁ ^ p = 1)
    (h₂ : e₂ ^ p = 1) (h₃ : e₃ ^ p = 1)
    (hn : ∀ a b c : ℕ, a < p → b < p → c < p → e₁ ^ a * e₂ ^ b * e₃ ^ c = 1 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    ∀ i j k : ℤ, e₁ ^ i * e₂ ^ j * e₃ ^ k = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ k := by
  intro i j k h
  obtain ⟨a, ha, hia, hpa⟩ := exists_nat_pow_of_pow_eq_one hp h₁ i
  obtain ⟨b, hb, hjb, hpb⟩ := exists_nat_pow_of_pow_eq_one hp h₂ j
  obtain ⟨c, hc, hkc, hpc⟩ := exists_nat_pow_of_pow_eq_one hp h₃ k
  rw [hia, hjb, hkc] at h
  obtain ⟨h1, h2, h3⟩ := hn a b c ha hb hc h
  exact ⟨hpa.mpr h1, hpb.mpr h2, hpc.mpr h3⟩

end Reduce

section Split

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem mem_elementaryGroup_of_odd_pow (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : orthDerived Q = elementaryGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1) :
    g ∈ elementaryGroup Q :=
  hE ▸ mem_orthDerived_of_odd_pow hQ hT (hp.odd_of_ne_two hp2) hg hgp

omit [Finite K] [FiniteDimensional K V] in
theorem hypPair_orth_symm {P P' : HypPair Q} (h : P.Orth P') : P'.Orth P where
  ee := by rw [polar_comm]; exact h.ee
  ef := by rw [polar_comm]; exact h.fe
  fe := by rw [polar_comm]; exact h.ef
  ff := by rw [polar_comm]; exact h.ff

theorem exists_stable_cube_diag (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : orthDerived Q = elementaryGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P₁ P₂ P₃ : HypPair Q} (h12 : P₁.Orth P₂) (h13 : P₁.Orth P₃) (h23 : P₂.Orth P₃) {ζ : K}
    (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) :
    ∃ E : Subgroup (elementaryGroup Q), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧
        ∀ g ∈ E, ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  have hord : orderOf ζ = p := orderOf_eq_prime hζ hζ1
  have hT1 : diagT ζ ^ p = 1 := by
    rw [diagT_pow, hζ]
    exact LinearMap.ext fun y => by simp [diagT_apply]
  let g : HypPair Q → V ≃ₗ[K] V := fun P =>
    (pairBlock P).blkEquivOf (diagT ζ) (diagT ζ⁻¹) (diagT_comp hζ0) (diagT_comp' hζ0)
  have hgO : ∀ P, g P ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun P =>
    (pairBlock P).blkEquivOf_mem_orthogonalGroup _ _ _ _ (diagT_qM hζ0 P)
  have hgp : ∀ P, g P ^ p = 1 := fun P => (pairBlock P).blkEquivOf_pow_eq_one _ _ _ _ hT1
  have hgE : ∀ P, g P ∈ elementaryGroup Q := fun P =>
    mem_elementaryGroup_of_odd_pow hQ hT hE hp hp2 (hgO P) (hgp P)
  have hpow_e : ∀ (P : HypPair Q) (a : ℕ), (g P ^ a) P.e = ζ ^ a • P.e := by
    intro P a
    have he : P.e = (pairBlock P).ι (1, 0) := by simp [pairBlock_ι]
    rw [QBlock.blkEquivOf_pow_apply, diagT_pow, he, QBlock.blk_ι]
    simp [pairBlock_ι, diagT_apply]
  have hfix_e : ∀ {P P' : HypPair Q}, P.Orth P' → ∀ a : ℕ, (g P' ^ a) P.e = P.e := by
    intro P P' h a
    rw [QBlock.blkEquivOf_pow_apply]
    refine QBlock.blk_of_m_eq_zero _ _ ?_
    have := pairBlock_m_ι_of_orth h (1, 0)
    simpa [pairBlock_ι] using this
  let G : HypPair Q → elementaryGroup Q := fun P => ⟨g P, hgE P⟩
  have hGp : ∀ P, G P ^ p = 1 := fun P => Subtype.ext (by simp [G, hgp P])
  have hcomm : ∀ {P P' : HypPair Q}, P.Orth P' → Commute (G P) (G P') := by
    intro P P' h
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    change (pairBlock P).blk (diagT ζ) ((pairBlock P').blk (diagT ζ) v) =
      (pairBlock P').blk (diagT ζ) ((pairBlock P).blk (diagT ζ) v)
    exact (pairBlock P).blk_comm (pairBlock P') (pairBlock_m_ι_of_orth (hypPair_orth_symm h))
      (pairBlock_m_ι_of_orth h) _ _ v
  have hscal : ∀ {c : K} {v : V}, v ≠ 0 → c • v = v → c = 1 := by
    intro c v hv h
    have : (c - 1) • v = 0 := by rw [sub_smul, one_smul, h, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hv)
  have hdvd : ∀ a : ℕ, a < p → ζ ^ a = 1 → a = 0 := fun a ha h =>
    Nat.eq_zero_of_dvd_of_lt (hord ▸ orderOf_dvd_of_pow_eq_one h) ha
  have hind := indep_of_nat hp.pos (hGp P₁) (hGp P₂) (hGp P₃) fun a b c ha hb hc h => by
    have hv : ∀ v : V, (((G P₁) ^ a * (G P₂) ^ b * (G P₃) ^ c : elementaryGroup Q) :
        V ≃ₗ[K] V) v = v := fun v => by rw [h]; rfl
    have e1 := hv P₁.e
    have e2 := hv P₂.e
    have e3 := hv P₃.e
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, LinearEquiv.mul_apply] at e1 e2 e3
    change (g P₁ ^ a) ((g P₂ ^ b) ((g P₃ ^ c) P₁.e)) = P₁.e at e1
    change (g P₁ ^ a) ((g P₂ ^ b) ((g P₃ ^ c) P₂.e)) = P₂.e at e2
    change (g P₁ ^ a) ((g P₂ ^ b) ((g P₃ ^ c) P₃.e)) = P₃.e at e3
    rw [hfix_e h13 c, hfix_e h12 b, hpow_e] at e1
    rw [hfix_e h23 c, hpow_e, map_smul, hfix_e (hypPair_orth_symm h12) a] at e2
    rw [hpow_e, map_smul, hfix_e (hypPair_orth_symm h23) b, map_smul,
      hfix_e (hypPair_orth_symm h13) a] at e3
    exact ⟨hdvd a ha (hscal P₁.e_ne_zero e1), hdvd b hb (hscal P₂.e_ne_zero e2),
      hdvd c hc (hscal P₃.e_ne_zero e3)⟩
  obtain ⟨E, hEab, hEcard, hEform, -⟩ := exists_cube_of_three hp (hcomm h12) (hcomm h13)
    (hcomm h23) (hGp P₁) (hGp P₂) (hGp P₃) hind
  refine ⟨E, hEab, hEcard, K ∙ P₁.e, ?_, ?_, ?_⟩
  · intro h0
    exact P₁.e_ne_zero ((Submodule.span_singleton_eq_bot).mp h0)
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [QuadraticMap.map_smul, P₁.Q_e, smul_zero]
  · intro x hx w hw
    obtain ⟨i, j, k, rfl⟩ := hEform x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨a, -, hia, -⟩ := exists_nat_pow_of_pow_eq_one hp.pos (hGp P₁) i
    obtain ⟨b, -, hjb, -⟩ := exists_nat_pow_of_pow_eq_one hp.pos (hGp P₂) j
    obtain ⟨d, -, hkd, -⟩ := exists_nat_pow_of_pow_eq_one hp.pos (hGp P₃) k
    rw [hia, hjb, hkd]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, LinearEquiv.mul_apply, map_smul]
    change c • (g P₁ ^ a) ((g P₂ ^ b) ((g P₃ ^ d) P₁.e)) ∈ K ∙ P₁.e
    rw [hfix_e h13 d, hfix_e h12 b, hpow_e, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Split

end CFSG.LieType.SeitzGeneration
