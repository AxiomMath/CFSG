module

public import CFSG.HardMathSupport.Foote.E27.UniMonomial

public section

namespace CFSG.HardMathSupport.Foote.E27.Uni

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {E : Type} [Field E] (hU : UnitaryFieldData 2 1 E) {n : ℕ}

include hU

theorem exists_omega : ∃ ω : E, ω ^ 2 + ω + 1 = 0 ∧ ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have := hU.finite
  have hc : Nat.card Eˣ = 3 := card_units_three hU
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
  rw [hc] at hg
  have h3 : (g : E) ^ 3 = 1 := by
    have := congrArg (fun u : Eˣ => (u : E)) (unit_cube hU g)
    simpa using this
  have hne : (g : E) ≠ 1 := by
    intro h
    have : g = 1 := Units.ext h
    rw [this, orderOf_one] at hg
    omega
  refine ⟨g, ?_, h3, hne⟩
  have : ((g : E) - 1) * ((g : E) ^ 2 + g + 1) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

theorem two_eq_zero : (2 : E) = 0 := by
  have := hU.charP
  exact_mod_cast CharP.cast_eq_zero E 2

noncomputable abbrev Bf : (Fin n → E) →ₛₗ[hU.bar] (Fin n → E) →ₗ[E] E :=
  gramForm hU (1 : Matrix (Fin n) (Fin n) E)

theorem Bf_apply (x y : Fin n → E) : Bf hU x y = ∑ i, hU.bar (x i) * y i := by
  simp [Bf, gramForm_apply, dotProduct]

theorem Bf_symm (x y : Fin n → E) : hU.bar (Bf hU x y) = Bf hU y x := by
  simp only [Bf_apply, map_sum, map_mul, UnitaryFieldData.bar_bar]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem Bf_nondeg {x : Fin n → E} (h : ∀ y, Bf hU x y = 0) : x = 0 := by
  funext i
  have := h (Pi.single i 1)
  simp only [Bf_apply] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj; simp [hj]
  · simp

theorem Bf_isometry {g : Matrix (Fin n) (Fin n) E} (hg : (g.map hU.bar)ᵀ * g = 1) (x y : Fin n → E) :
    Bf hU (g *ᵥ x) (g *ᵥ y) = Bf hU x y :=
  (gramForm_isometry_iff hU 1 g).mpr (by simpa using hg) x y

theorem Bf_self_fixed (x : Fin n → E) : hU.bar (Bf hU x x) = Bf hU x x := Bf_symm hU x x

theorem Bf_self_eq_one {x : Fin n → E} (h : Bf hU x x ≠ 0) : Bf hU x x = 1 := by
  have h1 := Bf_self_fixed hU x
  rw [bar_eq hU] at h1
  have : Bf hU x x * (Bf hU x x - 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' h
  · exact sub_eq_zero.mp h'

theorem Bf_eq_zero_of_isotropic {ω : E} (hω : ω ^ 2 + ω + 1 = 0) {a b : Fin n → E}
    (ha : Bf hU a a = 0) (hb : Bf hU b b = 0) (hab : Bf hU (a + b) (a + b) = 0)
    (hab' : Bf hU (a + ω • b) (a + ω • b) = 0) : Bf hU a b = 0 := by
  have h2 := two_eq_zero hU (E := E)
  have hba := (Bf_symm hU a b).symm
  have hbar : ∀ c : E, hU.bar c = c ^ 2 := bar_eq hU
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ha, hb,
    hba] at hab hab'
  set t := Bf hU a b with ht
  have e1 : t + t ^ 2 = 0 := by
    rw [hbar] at hab
    linear_combination hab
  rw [hbar, hbar] at hab'
  simp only [RingHom.id_apply, mul_zero, add_zero, zero_add] at hab'
  linear_combination ω ^ 2 * e1 - hab' + (t + ω * t) * h2 - t * hω

def evp (g : Matrix (Fin n) (Fin n) E) (l : E) (y : Fin n → E) : Fin n → E :=
  y + l ^ 2 • (g *ᵥ y) + l • (g *ᵥ (g *ᵥ y))

omit hU in
theorem evp_eig {g : Matrix (Fin n) (Fin n) E} (hg3 : g * g * g = 1) {l : E} (hl : l ^ 3 = 1)
    (y : Fin n → E) : g *ᵥ evp g l y = l • evp g l y := by
  have h3 : g *ᵥ (g *ᵥ (g *ᵥ y)) = y := by
    rw [mulVec_mulVec, mulVec_mulVec, hg3, one_mulVec]
  simp only [evp, mulVec_add, mulVec_smul, h3, smul_add, smul_smul]
  have e1 : l * l ^ 2 = 1 := by rw [← pow_succ']; exact hl
  have e2 : l * l = l ^ 2 := (sq l).symm
  rw [e1, e2, one_smul]
  abel

theorem evp_sum {g : Matrix (Fin n) (Fin n) E} {ω : E}
    (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1) (y : Fin n → E) :
    evp g 1 y + evp g ω y + evp g (ω ^ 2) y = y := by
  have h2 := two_eq_zero hU (E := E)
  have e4 : (ω ^ 2) ^ 2 = ω := by
    calc (ω ^ 2) ^ 2 = ω ^ 3 * ω := by ring
      _ = ω := by rw [hω3, one_mul]
  have e5 : ω ^ 2 * ω ^ 2 = ω := by rw [← sq, e4]
  simp only [evp, one_pow, one_smul, e4]
  linear_combination (norm := module) h2 • y + hω • (g *ᵥ y) + hω • (g *ᵥ (g *ᵥ y))

theorem bar_mul_ne_one {l l' : E} (hl : l ^ 3 = 1) (hne : l ≠ l') : hU.bar l * l' ≠ 1 := by
  intro h
  rw [bar_eq hU] at h
  apply hne
  calc l = l ^ 3 * l' := by
        have : l ^ 3 * l' = l * (l ^ 2 * l') := by ring
        rw [this, h, mul_one]
    _ = l' := by rw [hl, one_mul]

theorem Bf_eq_zero_of_eig {g : Matrix (Fin n) (Fin n) E} (hgu : (g.map hU.bar)ᵀ * g = 1) {l l' : E}
    (hl : l ^ 3 = 1) (hne : l ≠ l') {x x' : Fin n → E} (hx : g *ᵥ x = l • x)
    (hx' : g *ᵥ x' = l' • x') : Bf hU x x' = 0 := by
  have h := Bf_isometry hU hgu x x'
  simp only [hx, hx', map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] at h
  have h' : (hU.bar l * l' - 1) * Bf hU x x' = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) (bar_mul_ne_one hU hl hne)
  · exact h1

omit hU in
theorem evp_add (g : Matrix (Fin n) (Fin n) E) (l : E) (y y' : Fin n → E) :
    evp g l (y + y') = evp g l y + evp g l y' := by
  simp only [evp, mulVec_add, smul_add]; abel

omit hU in
theorem evp_smul (g : Matrix (Fin n) (Fin n) E) (l c : E) (y : Fin n → E) :
    evp g l (c • y) = c • evp g l y := by
  simp only [evp, mulVec_smul, smul_add, smul_comm l c, smul_comm (l ^ 2) c]

theorem exists_eig_perp {g : Matrix (Fin n) (Fin n) E} (hgu : (g.map hU.bar)ᵀ * g = 1)
    (hg3 : g * g * g = 1) {ω : E} (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {k : ℕ} (b : Fin k → Fin n → E) (hb : ∀ i j, Bf hU (b i) (b j) = if i = j then 1 else 0)
    (hbe : ∀ i, ∃ l : E, l ^ 3 = 1 ∧ g *ᵥ b i = l • b i) (hk : k < n) :
    ∃ x : Fin n → E, (∀ i, Bf hU (b i) x = 0) ∧ Bf hU x x = 1 ∧
      ∃ l : E, l ^ 3 = 1 ∧ g *ᵥ x = l • x := by
  classical
  by_contra hno
  push Not at hno
  let P : (Fin n → E) →ₗ[E] (Fin n → E) := LinearMap.id - ∑ i, (Bf hU (b i)).smulRight (b i)
  have hPy : ∀ y, P y = y - ∑ i, Bf hU (b i) y • b i := by intro y; simp [P]
  have hperp : ∀ j y, Bf hU (b j) (P y) = 0 := by
    intro j y
    rw [hPy, map_sub, map_sum]
    simp only [map_smul, smul_eq_mul, hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, sub_self]
  choose l hl3 hl using hbe
  have hlbar : ∀ i, hU.bar (l i) * l i ^ 2 = l i ^ 2 * hU.bar (l i) := fun i => mul_comm _ _
  have hBg : ∀ i y, Bf hU (b i) (g *ᵥ y) = l i * Bf hU (b i) y := by
    intro i y
    have h := Bf_isometry hU hgu (b i) y
    simp only [hl i, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h
    rw [bar_eq hU] at h
    have e : l i * l i ^ 2 = 1 := by rw [← pow_succ']; exact hl3 i
    calc Bf hU (b i) (g *ᵥ y) = (l i * l i ^ 2) * Bf hU (b i) (g *ᵥ y) := by rw [e, one_mul]
      _ = l i * (l i ^ 2 * Bf hU (b i) (g *ᵥ y)) := by ring
      _ = l i * Bf hU (b i) y := by rw [h]
  have hgP : ∀ y, g *ᵥ P y = P (g *ᵥ y) := by
    intro y
    rw [hPy, hPy]
    have h1 : g *ᵥ (y - ∑ i, Bf hU (b i) y • b i) =
        g *ᵥ y - ∑ i, (l i * Bf hU (b i) y) • b i := by
      rw [mulVec_sub, mulVec_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mulVec_smul, hl i, smul_smul, mul_comm]
    rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hBg]
  let X : E → (Fin n → E) → (Fin n → E) := fun m y => P (evp g m y)
  have hXadd : ∀ (m : E) y y', X m (y + y') = X m y + X m y' := by
    intro m y y'; simp only [X, evp_add, map_add]
  have hXsmul : ∀ (m c : E) y, X m (c • y) = c • X m y := by
    intro m c y; simp only [X, evp_smul, map_smul]
  have hXeig : ∀ m : E, m ^ 3 = 1 → ∀ y, g *ᵥ X m y = m • X m y := by
    intro m hm y
    simp only [X]
    rw [hgP, evp_eig hg3 hm, map_smul]
  have hXperp : ∀ (m : E) y j, Bf hU (b j) (X m y) = 0 := fun m y j => hperp j _
  have hiso : ∀ m : E, m ^ 3 = 1 → ∀ y, Bf hU (X m y) (X m y) = 0 := by
    intro m hm y
    by_contra hne
    exact hno (X m y) (hXperp m y) (Bf_self_eq_one hU hne) m hm (hXeig m hm y)
  have hXX : ∀ m : E, m ^ 3 = 1 → ∀ y y', Bf hU (X m y) (X m y') = 0 := by
    intro m hm y y'
    refine Bf_eq_zero_of_isotropic hU hω (hiso m hm y) (hiso m hm y') ?_ ?_
    · rw [← hXadd]; exact hiso m hm _
    · rw [← hXsmul, ← hXadd]; exact hiso m hm _
  have hω0 : ω ≠ 0 := by
    intro h; rw [h] at hω3; norm_num at hω3
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hω3, h]; simp
  have hω12 : ω ≠ ω ^ 2 := by
    intro h
    apply hω1
    have : ω * (ω - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hω0
    · exact sub_eq_zero.mp h'
  have hXc : ∀ m m' : E, m ^ 3 = 1 → m ≠ m' → m' ^ 3 = 1 → ∀ y y', Bf hU (X m y) (X m' y') = 0 :=
    fun m m' hm hne hm' y y' =>
      Bf_eq_zero_of_eig hU hgu hm hne (hXeig m hm y) (hXeig m' hm' y')
  have hc1 : (1 : E) ^ 3 = 1 := one_pow 3
  have hcω : ω ^ 3 = 1 := hω3
  have hcω2 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hPsum : ∀ y, P y = X 1 y + X ω y + X (ω ^ 2) y := by
    intro y
    have := evp_sum hU hω hω3 (g := g) y
    simp only [X, ← map_add, this]
  have hPP : ∀ y y', Bf hU (P y) (P y') = 0 := by
    intro y y'
    rw [hPsum y, hPsum y']
    simp only [map_add, LinearMap.add_apply]
    rw [hXX 1 hc1, hXX ω hcω, hXX (ω ^ 2) hcω2, hXc 1 ω hc1 hω1.symm hcω,
      hXc 1 (ω ^ 2) hc1 hω2.symm hcω2, hXc ω 1 hcω hω1 hc1, hXc ω (ω ^ 2) hcω hω12 hcω2,
      hXc (ω ^ 2) 1 hcω2 hω2 hc1, hXc (ω ^ 2) ω hcω2 hω12.symm hcω]
    simp
  have hP0 : ∀ y, P y = 0 := by
    intro y
    refine Bf_nondeg hU fun y' => ?_
    have h1 : y' = P y' + ∑ i, Bf hU (b i) y' • b i := by rw [hPy]; abel
    have h2 : ∀ i, Bf hU (P y) (b i) = 0 := by
      intro i
      rw [← Bf_symm hU, hperp i y, map_zero]
    conv_lhs => rw [h1]
    rw [map_add, hPP, map_sum]
    simp only [map_smul, smul_eq_mul, h2, mul_zero, Finset.sum_const_zero, add_zero]
  have htop : Submodule.span E (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have h1 : y = P y + ∑ i, Bf hU (b i) y • b i := by rw [hPy]; abel
    rw [h1, hP0, zero_add]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hle := finrank_range_le_card (R := E) b
  rw [Set.finrank, htop, finrank_top, Fintype.card_fin, Module.finrank_fin_fun] at hle
  omega

theorem exists_eig_family {g : Matrix (Fin n) (Fin n) E} (hgu : (g.map hU.bar)ᵀ * g = 1)
    (hg3 : g * g * g = 1) {ω : E} (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∀ k ≤ n, ∃ b : Fin k → Fin n → E, (∀ i j, Bf hU (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ i, ∃ l : E, l ^ 3 = 1 ∧ g *ᵥ b i = l • b i := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro hk
    obtain ⟨b, hb, hbe⟩ := ih (by omega)
    obtain ⟨x, hxb, hxx, l, hl, hx⟩ := exists_eig_perp hU hgu hg3 hω hω3 hω1 b hb hbe (by omega)
    refine ⟨Fin.snoc b x, fun i j => ?_, fun i => ?_⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [hxx]
        | cast j =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          rw [← Bf_symm hU, hxb j, map_zero, ite_eq_right_iff.mpr (fun h => absurd h.symm
            (Fin.castSucc_lt_last j).ne)]
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          rw [hxb i, ite_eq_right_iff.mpr (fun h => absurd h (Fin.castSucc_lt_last i).ne)]
        | cast j => simp only [Fin.snoc_castSucc, hb i j, Fin.castSucc_inj]
    · induction i using Fin.lastCases with
      | last => exact ⟨l, hl, by simpa using hx⟩
      | cast i => simpa using hbe i

theorem exists_conj_diag {g : GL (Fin n) E}
    (hgu : (((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map hU.bar)ᵀ *
      (g : Matrix (Fin n) (Fin n) E) = 1)
    (hg3 : g ^ 3 = 1) :
    ∃ k : GL (Fin n) E, ((k : Matrix (Fin n) (Fin n) E).map hU.bar)ᵀ *
      (k : Matrix (Fin n) (Fin n) E) = 1 ∧ ∃ d : Fin n → Eˣ, k * g * k⁻¹ = dgHom n E d := by
  obtain ⟨ω, hω, hω3, hω1⟩ := exists_omega hU
  have hG3 : (g : Matrix (Fin n) (Fin n) E) * g * g = 1 := by
    have := congrArg (fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E)) hg3
    simpa [pow_succ] using this
  obtain ⟨b, hb, hbe⟩ := exists_eig_family hU hgu hG3 hω hω3 hω1 n le_rfl
  choose μ hμ3 hμ using hbe
  set G : Matrix (Fin n) (Fin n) E := (g : Matrix (Fin n) (Fin n) E) with hGdef
  let K : Matrix (Fin n) (Fin n) E := Matrix.of fun j i => b i j
  have hK1 : (K.map hU.bar)ᵀ * K = 1 := by
    ext i i'
    rw [Matrix.mul_apply]
    have := hb i i'
    rw [Bf_apply] at this
    simp only [Matrix.transpose_apply, Matrix.map_apply, K, Matrix.of_apply, Matrix.one_apply]
    rw [this]
  have hK2 : K * (K.map hU.bar)ᵀ = 1 := mul_eq_one_comm.mp hK1
  have hGK : G * K = K * diagonal μ := by
    ext j i
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    have := congrFun (hμ i) j
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simpa [K, mul_comm] using this
  let k : GL (Fin n) E := ⟨(K.map hU.bar)ᵀ, K, hK1, hK2⟩
  have hμ0 : ∀ i, μ i ≠ 0 := fun i h => by
    have := hμ3 i
    rw [h] at this; norm_num at this
  have hkk : (((K.map hU.bar)ᵀ).map hU.bar)ᵀ = K := by
    ext i j
    simp [UnitaryFieldData.bar_bar]
  refine ⟨k, ?_, fun i => Units.mk0 (μ i) (hμ0 i), ?_⟩
  · change (((K.map hU.bar)ᵀ).map hU.bar)ᵀ * (K.map hU.bar)ᵀ = 1
    rw [hkk]; exact hK2
  · apply Units.ext
    change (K.map hU.bar)ᵀ * G * K = diagonal fun i => μ i
    rw [Matrix.mul_assoc, hGK, ← Matrix.mul_assoc, hK1, Matrix.one_mul]

end CFSG.HardMathSupport.Foote.E27.Uni

end
