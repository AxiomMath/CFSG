module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.NMFixed

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Matrix
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

section Basic

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (Φ : QuadForm K V) (T : V →ₗ[K] V)

theorem natCast_ne_zero_of_odd {p : ℕ} (hp : Odd p) : (p : K) ≠ 0 := by
  obtain ⟨k, rfl⟩ := hp
  have h2 : (2 : K) = 0 := NM_two_eq_zero
  push_cast
  rw [h2]
  simp

omit [CharP K 2] in
theorem pow_preserves (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) (j : ℕ) (v : V) :
    Φ.Q ((T ^ j) v) = Φ.Q v := by
  induction j generalizing v with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, hTQ, ih]

omit [CharP K 2] in
theorem pow_apply_of_fixed {w : V} (hw : T w = w) (j : ℕ) : (T ^ j) w = w := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, hw]

omit [CharP K 2] in
theorem polar_pow_fixed (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {w : V} (hw : T w = w) (j : ℕ) (v : V) :
    Φ.polar.β w ((T ^ j) v) = Φ.polar.β w v := by
  have h := Φ.polar_map_of_Q (g := T ^ j) (pow_preserves Φ T hTQ j) w v
  rwa [pow_apply_of_fixed T hw j] at h

omit [CharP K 2] in
theorem sum_pow_fixed {p : ℕ} (hTp : T ^ p = 1) (v : V) :
    T (∑ j ∈ Finset.range p, (T ^ j) v) = ∑ j ∈ Finset.range p, (T ^ j) v := by
  have h1 : ∀ j, T ((T ^ j) v) = (T ^ (j + 1)) v := fun j => by
    rw [pow_succ', Module.End.mul_apply]
  rw [map_sum]
  simp only [h1]
  have h2 := Finset.sum_range_succ' (fun j => (T ^ j) v) p
  have h3 := Finset.sum_range_succ (fun j => (T ^ j) v) p
  simp only [pow_zero, hTp, Module.End.one_apply] at h2 h3
  exact add_right_cancel (h2.symm.trans h3)

theorem fixedSpace_nondegenerate {p : ℕ} (hp : Odd p) (hTp : T ^ p = 1)
    (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {W₁ : Submodule K V} (hW₁ : ∀ v, v ∈ W₁ ↔ T v = v) :
    ∀ w ∈ W₁, (∀ w' ∈ W₁, Φ.polar.β w w' = 0) → w = 0 := by
  intro w hw hperp
  have hTw : T w = w := (hW₁ w).1 hw
  apply Φ.polar.nondeg
  intro v
  have hs : (∑ j ∈ Finset.range p, (T ^ j) v) ∈ W₁ := (hW₁ _).2 (sum_pow_fixed T hTp v)
  have h0 := hperp _ hs
  have hsum : ∀ n : ℕ, Φ.polar.β w (∑ j ∈ Finset.range n, (T ^ j) v) = n * Φ.polar.β w v := by
    intro n
    induction n with
    | zero =>
      rw [Finset.sum_range_zero]
      have : Φ.polar.β w 0 = 0 := by
        have := Φ.polar.smul_right 0 w 0
        simpa using this
      simp [this]
    | succ n ih =>
      rw [Finset.sum_range_succ, Φ.polar.add_right, ih, polar_pow_fixed Φ T hTQ hTw]
      push_cast
      ring
  rw [hsum] at h0
  exact (mul_eq_zero.1 h0).resolve_left (natCast_ne_zero_of_odd hp)

end Basic

section Escape

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (Φ : QuadForm K V) (T : V →ₗ[K] V)

theorem false_of_fixed_escape [FiniteDimensional K V] (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v)
    {W₁ F : Submodule K V} (hW₁ : ∀ v, v ∈ W₁ ↔ T v = v)
    (hnd : ∀ w ∈ W₁, (∀ w' ∈ W₁, Φ.polar.β w w' = 0) → w = 0)
    (hFQ : ∀ w ∈ F, Φ.Q w = 0)
    (hE : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 →
      (∀ v, Φ.eichler x y (T v) = T (Φ.eichler x y v)) → ∀ w ∈ F, Φ.eichler x y w ∈ F)
    {a₁ : V} (ha₁F : a₁ ∈ F) (ha₁W : a₁ ∈ W₁) (ha₁0 : a₁ ≠ 0)
    (hdim : 3 ≤ Module.finrank K W₁) : False := by
  have h2K : (2 : K) = 0 := NM_two_eq_zero
  have hQa₁ := hFQ a₁ ha₁F
  have hBaa : Φ.polar.β a₁ a₁ = 0 := by rw [Φ.polar_self, hQa₁, mul_zero]
  obtain ⟨b'', hb''W, hBb''⟩ : ∃ b'' ∈ W₁, Φ.polar.β a₁ b'' = 1 := by
    obtain ⟨b', hb'W, hb'⟩ : ∃ b' ∈ W₁, Φ.polar.β a₁ b' ≠ 0 := by
      by_contra! h
      exact ha₁0 (hnd a₁ ha₁W h)
    exact ⟨(Φ.polar.β a₁ b')⁻¹ • b', W₁.smul_mem _ hb'W, by
      rw [Φ.polar.smul_right, inv_mul_cancel₀ hb']⟩
  obtain ⟨b₁, hb₁W, hBab, hQb₁⟩ :
      ∃ b₁ ∈ W₁, Φ.polar.β a₁ b₁ = 1 ∧ Φ.Q b₁ = 0 := by
    refine ⟨b'' + Φ.Q b'' • a₁, add_mem hb''W (W₁.smul_mem _ ha₁W), ?_, ?_⟩
    · rw [Φ.polar.add_right, Φ.polar.smul_right, hBaa, hBb'']
      ring
    · rw [Φ.Q_add, Φ.Q_smul, hQa₁, Φ.polar.smul_right, Φ.polar_symm b'' a₁, hBb'']
      linear_combination (Φ.Q b'') * h2K
  have hBba : Φ.polar.β b₁ a₁ = 1 := by rw [Φ.polar_symm]; exact hBab
  have hBbb : Φ.polar.β b₁ b₁ = 0 := by rw [Φ.polar_self, hQb₁, mul_zero]
  obtain ⟨c, hcW, hca, hcb, hcF⟩ :
      ∃ c ∈ W₁, Φ.polar.β a₁ c = 0 ∧ Φ.polar.β b₁ c = 0 ∧ c ∉ F := by
    by_contra! hcon
    have hproj : ∀ v ∈ W₁, v - Φ.polar.β b₁ v • a₁ - Φ.polar.β a₁ v • b₁ ∈ F ∧
        Φ.polar.β a₁ (v - Φ.polar.β b₁ v • a₁ - Φ.polar.β a₁ v • b₁) = 0 ∧
        Φ.polar.β b₁ (v - Φ.polar.β b₁ v • a₁ - Φ.polar.β a₁ v • b₁) = 0 := by
      intro v hv
      have h1 : Φ.polar.β a₁ (v - Φ.polar.β b₁ v • a₁ - Φ.polar.β a₁ v • b₁) = 0 := by
        rw [Φ.polar.β_sub_right, Φ.polar.β_sub_right, Φ.polar.smul_right, Φ.polar.smul_right,
          hBaa, hBab]
        ring
      have h2 : Φ.polar.β b₁ (v - Φ.polar.β b₁ v • a₁ - Φ.polar.β a₁ v • b₁) = 0 := by
        rw [Φ.polar.β_sub_right, Φ.polar.β_sub_right, Φ.polar.smul_right, Φ.polar.smul_right,
          hBba, hBbb]
        ring
      have hmem : v - Φ.polar.β b₁ v • a₁ - Φ.polar.β a₁ v • b₁ ∈ W₁ :=
        W₁.sub_mem (W₁.sub_mem hv (W₁.smul_mem _ ha₁W)) (W₁.smul_mem _ hb₁W)
      exact ⟨hcon _ hmem h1 h2, h1, h2⟩
    have hle : W₁ ≤ Submodule.span K {a₁, b₁} := by
      intro v hv
      obtain ⟨hcF, h1, h2⟩ := hproj v hv
      set c : V := v - Φ.polar.β b₁ v • a₁ - Φ.polar.β a₁ v • b₁ with hc
      have hc0 : c = 0 := by
        have hcW : c ∈ W₁ :=
          W₁.sub_mem (W₁.sub_mem hv (W₁.smul_mem _ ha₁W)) (W₁.smul_mem _ hb₁W)
        apply hnd c hcW
        intro w' hw'
        obtain ⟨hc'F, -, -⟩ := hproj w' hw'
        have hdec : w' = (w' - Φ.polar.β b₁ w' • a₁ - Φ.polar.β a₁ w' • b₁) +
            Φ.polar.β b₁ w' • a₁ + Φ.polar.β a₁ w' • b₁ := by abel
        have h1' : Φ.polar.β c a₁ = 0 := by rw [Φ.polar_symm]; exact h1
        have h2' : Φ.polar.β c b₁ = 0 := by rw [Φ.polar_symm]; exact h2
        rw [hdec, Φ.polar.add_right, Φ.polar.add_right, Φ.polar.smul_right, Φ.polar.smul_right,
          h1', h2', NM_B_eq_zero_of_mem Φ hFQ hcF hc'F]
        ring
      rw [Submodule.mem_span_pair]
      refine ⟨Φ.polar.β b₁ v, Φ.polar.β a₁ v, ?_⟩
      have : v = c + Φ.polar.β b₁ v • a₁ + Φ.polar.β a₁ v • b₁ := by rw [hc]; abel
      rw [hc0, zero_add] at this
      exact this.symm
    have h3 := Submodule.finrank_mono hle
    have h4 : Module.finrank K (Submodule.span K {a₁, b₁}) ≤ 2 := by
      classical
      have := finrank_span_finset_le_card (R := K) ({a₁, b₁} : Finset V)
      have e : ((({a₁, b₁} : Finset V)) : Set V) = {a₁, b₁} := by simp
      rw [e] at this
      exact this.trans Finset.card_le_two
    omega
  have hTb₁ : T b₁ = b₁ := (hW₁ _).1 hb₁W
  have hTc : T c = c := (hW₁ _).1 hcW
  have hEa := hE b₁ c hQb₁ hcb (NM_eichler_comm_fix Φ T hTQ hTb₁ hTc) a₁ ha₁F
  have hca' : Φ.polar.β c a₁ = 0 := by rw [Φ.polar_symm]; exact hca
  have hz : c - Φ.Q c • b₁ ∈ F := by
    have : Φ.eichler b₁ c a₁ - a₁ = c - Φ.Q c • b₁ := by
      rw [QuadForm.eichler_apply, hBba, hca']
      module
    rw [← this]
    exact F.sub_mem hEa ha₁F
  have hQz := hFQ _ hz
  have hcb' : Φ.polar.β c b₁ = 0 := by rw [Φ.polar_symm]; exact hcb
  have hQc : Φ.Q c = 0 := by
    have e : c - Φ.Q c • b₁ = c + (-Φ.Q c) • b₁ := by module
    rw [e, Φ.Q_add, Φ.Q_smul, hQb₁, Φ.polar.smul_right, hcb'] at hQz
    linear_combination hQz
  apply hcF
  have e : c = c - Φ.Q c • b₁ := by rw [hQc, zero_smul, sub_zero]
  rw [e]
  exact hz

theorem false_of_fixed_escape_of_pow [FiniteDimensional K V] {p : ℕ} (hp : Odd p)
    (hTp : T ^ p = 1) (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {W₁ F : Submodule K V}
    (hW₁ : ∀ v, v ∈ W₁ ↔ T v = v) (hFQ : ∀ w ∈ F, Φ.Q w = 0)
    (hE : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 →
      (∀ v, Φ.eichler x y (T v) = T (Φ.eichler x y v)) → ∀ w ∈ F, Φ.eichler x y w ∈ F)
    (hdim : 2 ≤ Module.finrank K ↥(F ⊓ W₁)) : False := by
  have hnd := fixedSpace_nondegenerate Φ T hp hTp hTQ hW₁
  obtain ⟨a₁, ha₁, ha₁0⟩ : ∃ a₁ ∈ F ⊓ W₁, a₁ ≠ 0 := by
    by_contra! h
    have : F ⊓ W₁ = ⊥ := (Submodule.eq_bot_iff _).mpr h
    rw [this] at hdim
    simp at hdim
  have hdim3 : 3 ≤ Module.finrank K W₁ := by
    by_contra hlt
    push Not at hlt
    have hle : F ⊓ W₁ = W₁ := by
      apply Submodule.eq_of_le_of_finrank_le inf_le_right
      omega
    have h0 := hnd a₁ ha₁.2 (fun w' hw' => by
      have hw'F : w' ∈ F := by
        have : w' ∈ F ⊓ W₁ := by rw [hle]; exact hw'
        exact this.1
      exact NM_B_eq_zero_of_mem Φ hFQ ha₁.1 hw'F)
    exact ha₁0 h0
  exact false_of_fixed_escape Φ T hTQ hW₁ hnd hFQ hE ha₁.1 ha₁.2 ha₁0 hdim3

end Escape

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [CharP K 2]
  (Φ : QuadForm K (ι → K)) (M : GL ι K)

omit [CharP K 2] in
theorem toLin'_pow_eq_one {n : ℕ} (hM : M ^ n = 1) :
    (Matrix.toLin' (M : Matrix ι ι K)) ^ n = 1 := by
  have h1 : (Matrix.toLin' (M : Matrix ι ι K)) ^ n =
      Matrix.toLinAlgEquiv' ((M : Matrix ι ι K) ^ n) := by
    rw [map_pow]
    rfl
  rw [h1, ← Units.val_pow_eq_pow_val, hM]
  simp

omit [CharP K 2] in
theorem eichler_stable_of_centralizer (hι : 5 ≤ Fintype.card ι) (F : Submodule K (ι → K))
    (hC : ∀ g ∈ StatedOmega Φ.Q, g * M = M * g → ∀ w ∈ F, (g : Matrix ι ι K) *ᵥ w ∈ F) :
    ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 →
      (∀ v, Φ.eichler x y (Matrix.toLin' (M : Matrix ι ι K) v) =
        Matrix.toLin' (M : Matrix ι ι K) (Φ.eichler x y v)) → ∀ w ∈ F, Φ.eichler x y w ∈ F := by
  intro x y hx hxy hcomm w hw
  obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler' Φ hι hx hxy
  have hAM : A * M = M * A := by
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_apply, Matrix.toLin'_apply,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAv, ← Matrix.toLin'_apply, hAv, hcomm,
      Matrix.toLin'_apply]
  have := hC A hA hAM w hw
  rwa [hAv] at this

theorem false_of_fixed_escape_omega (hι : 5 ≤ Fintype.card ι) {p : ℕ} (hp : Odd p)
    (hMp : M ^ p = 1) (hMQ : ∀ v, Φ.Q ((M : Matrix ι ι K) *ᵥ v) = Φ.Q v)
    {W₁ F : Submodule K (ι → K)} (hW₁ : ∀ v, v ∈ W₁ ↔ (M : Matrix ι ι K) *ᵥ v = v)
    (hFQ : ∀ w ∈ F, Φ.Q w = 0) (hdim : 2 ≤ Module.finrank K ↥(F ⊓ W₁))
    (hC : ∀ g ∈ StatedOmega Φ.Q, g * M = M * g → ∀ w ∈ F, (g : Matrix ι ι K) *ᵥ w ∈ F) :
    False := by
  refine false_of_fixed_escape_of_pow Φ (Matrix.toLin' (M : Matrix ι ι K)) hp
    (toLin'_pow_eq_one M hMp) (fun v => ?_) (fun v => ?_) hFQ
    (eichler_stable_of_centralizer Φ M hι F hC) hdim
  · rw [Matrix.toLin'_apply]; exact hMQ v
  · rw [hW₁, Matrix.toLin'_apply]

end Matrix

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
