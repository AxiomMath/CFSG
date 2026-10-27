module

public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

namespace GenLocU4Aux

section Generic

variable {K : Type} [Field K]

theorem su2_entries (σ : K ≃+* K) (hinv : ∀ x, σ (σ x) = x) (a b : K) (h : σ a * a + σ b * b = 1) :
    (!![a, b; -σ b, σ a]).det = 1 ∧ conjTr σ !![a, b; -σ b, σ a] * !![a, b; -σ b, σ a] = 1 := by
  refine ⟨by rw [Matrix.det_fin_two_of]; linear_combination h, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hinv] <;>
    first | ring1 | linear_combination h


theorem blockMat4_mulVec_zero (B : Matrix (Fin 2) (Fin 2) K) (x : Fin 4 → K) :
    blockMat 4 0 B *ᵥ x = ![B 0 0 * x 0 + B 0 1 * x 1, B 1 0 * x 0 + B 1 1 * x 1, x 2, x 3] := by
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, blockMat_apply]

theorem blockMat4_mulVec_one (B : Matrix (Fin 2) (Fin 2) K) (x : Fin 4 → K) :
    blockMat 4 1 B *ᵥ x = ![x 0, B 0 0 * x 1 + B 0 1 * x 2, B 1 0 * x 1 + B 1 1 * x 2, x 3] := by
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, blockMat_apply]

theorem blockMat4_mulVec_two (B : Matrix (Fin 2) (Fin 2) K) (x : Fin 4 → K) :
    blockMat 4 2 B *ᵥ x = ![x 0, x 1, B 0 0 * x 2 + B 0 1 * x 3, B 1 0 * x 2 + B 1 1 * x 3] := by
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, blockMat_apply]


theorem axis_one_aux (σ : K ≃+* K) (x0 x1 s : K) (hs0 : s ≠ 0) (hs : σ s * s = σ x0 * x0 + σ x1 * x1) :
    σ (x1 / s) * (x1 / s) + σ (-(x0 / s)) * (-(x0 / s)) = 1 ∧
    (x1 / s) * x0 + (-(x0 / s)) * x1 = 0 ∧
    (-σ (-(x0 / s))) * x0 + σ (x1 / s) * x1 = s := by
  have hσs : σ s ≠ 0 := (map_ne_zero _).2 hs0
  simp only [map_div₀, map_neg]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination -hs
  · field_simp
    ring
  · field_simp
    linear_combination -hs

theorem axis_zero_aux (σ : K ≃+* K) (hinv : ∀ x, σ (σ x) = x) (x0 x1 t : K) (ht0 : t ≠ 0)
    (ht : σ t * t = σ x0 * x0 + σ x1 * x1) :
    σ (σ (x0 / t)) * σ (x0 / t) + σ (σ (x1 / t)) * σ (x1 / t) = 1 ∧
    σ (x0 / t) * x0 + σ (x1 / t) * x1 = t ∧
    (-σ (σ (x1 / t))) * x0 + σ (σ (x0 / t)) * x1 = 0 := by
  have hσt : σ t ≠ 0 := (map_ne_zero _).2 ht0
  simp only [map_div₀, hinv]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination -ht
  · field_simp
    linear_combination -ht
  · field_simp
    ring


variable {σ : K ≃+* K} {n : ℕ}

theorem tv_conj (hσ : ∀ c, σ (σ c) = c) (g : SUid σ n) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) :
    g * tv hσ ha hc * g⁻¹ = tv hσ (by rw [herm_smul_smul]; exact ha : herm σ (g • a) (g • a) = 0) hc := by
  apply ext_smul
  intro v
  rw [conj_smul_of_tv g _ (tv_smul hσ ha hc), tv_smul]

theorem tv_conj_mem (hσ : ∀ c, σ (σ c) = c) (Γ : Subgroup (SUid σ n)) {g : SUid σ n} (hg : g ∈ Γ)
    {v : Fin n → K} (hv : herm σ v v = 0) (hT : ∀ (c : K) (hc : c + σ c = 0), tv hσ hv hc ∈ Γ)
    {w : Fin n → K} (hw : w = g • v) (hw0 : herm σ w w = 0) (c : K) (hc : c + σ c = 0) :
    tv hσ hw0 hc ∈ Γ := by
  subst hw
  have := Γ.mul_mem (Γ.mul_mem hg (hT c hc)) (Γ.inv_mem hg)
  rwa [tv_conj hσ g hv hc] at this

theorem tv_mem_of_scalar (hσ : ∀ c, σ (σ c) = c) (Γ : Subgroup (SUid σ n)) {u a : Fin n → K} (lam : K)
    (hlam : lam ≠ 0) (hu : u = lam • a)
    (hT : ∀ (hu0 : herm σ u u = 0) (c : K) (hc : c + σ c = 0), tv hσ hu0 hc ∈ Γ)
    (ha : herm σ a a = 0) (c : K) (hc : c + σ c = 0) : tv hσ ha hc ∈ Γ := by
  have hu0 : herm σ u u = 0 := by rw [hu, herm_smul_left, herm_smul_right, ha, mul_zero, mul_zero]
  have hσl : σ lam ≠ 0 := (map_ne_zero _).2 hlam
  have hn : σ lam * lam ≠ 0 := mul_ne_zero hσl hlam
  have hfix : σ (σ lam * lam) = σ lam * lam := by rw [map_mul, hσ, mul_comm]
  have hc' : c / (σ lam * lam) + σ (c / (σ lam * lam)) = 0 := by
    rw [map_div₀, hfix, ← add_div, hc, zero_div]
  have e : tv hσ ha hc = tv hσ hu0 hc' := by
    apply ext_smul
    intro v
    rw [tv_smul, tv_smul]
    subst hu
    rw [herm_smul_left, smul_smul]
    congr 1
    congr 1
    field_simp
  rw [e]
  exact hT hu0 _ hc'


end Generic

section Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conjTr_unitaryInvolution {n : ℕ} (B : Matrix (Fin n) (Fin n) K) :
    conjTr (unitaryInvolution K p f) B = (B.map (· ^ (p ^ f)))ᵀ := by
  have : B.map (unitaryInvolution K p f) = B.map (· ^ (p ^ f)) := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply]
    exact unitaryInvolution_apply (K := K) (p := p) (f := f) _
  rw [conjTr, this]

@[expose] noncomputable def su2Mk (B : Matrix (Fin 2) (Fin 2) K) (hdet : B.det = 1)
    (hB : (B.map (· ^ (p ^ f)))ᵀ * B = 1) : Su K p f 2 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero B (by rw [hdet]; exact one_ne_zero),
    (mem_SUid (σ := unitaryInvolution K p f)).2 ⟨hdet, by rw [conjTr_unitaryInvolution]; exact hB⟩⟩

theorem coe_su2Mk (B : Matrix (Fin 2) (Fin 2) K) (hdet : B.det = 1)
    (hB : (B.map (· ^ (p ^ f)))ᵀ * B = 1) :
    (((su2Mk (p := p) (f := f) B hdet hB : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = B := rfl


@[expose] noncomputable def su2Of (hinv : ∀ x : K, unitaryInvolution K p f (unitaryInvolution K p f x) = x)
    (a b : K) (h : unitaryInvolution K p f a * a + unitaryInvolution K p f b * b = 1) : Su K p f 2 :=
  su2Mk (p := p) (f := f) !![a, b; -(unitaryInvolution K p f b), unitaryInvolution K p f a]
    (su2_entries _ hinv a b h).1
    (by rw [← conjTr_unitaryInvolution]; exact (su2_entries _ hinv a b h).2)

theorem su2Of_apply (hinv : ∀ x : K, unitaryInvolution K p f (unitaryInvolution K p f x) = x) (a b : K)
    (h : unitaryInvolution K p f a * a + unitaryInvolution K p f b * b = 1) :
    (((su2Of (p := p) (f := f) hinv a b h : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![a, b; -(unitaryInvolution K p f b), unitaryInvolution K p f a] := rfl



theorem blockEmb2_smul_zero (B : Su K p f 2) (x : Fin 4 → K) :
    (blockEmb2 K p f 3 0 B : Su K p f 4) • x =
      ![((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 * x 0 + ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 * x 1,
        ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 * x 0 + ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 * x 1,
        x 2, x 3] := by
  rw [smul_def, coe_coe_blockEmb2]
  exact blockMat4_mulVec_zero _ x

theorem blockEmb2_smul_one (B : Su K p f 2) (x : Fin 4 → K) :
    (blockEmb2 K p f 3 1 B : Su K p f 4) • x =
      ![x 0, ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 * x 1 + ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 * x 2,
        ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 * x 1 + ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 * x 2,
        x 3] := by
  rw [smul_def, coe_coe_blockEmb2]
  exact blockMat4_mulVec_one _ x

theorem blockEmb2_smul_two (B : Su K p f 2) (x : Fin 4 → K) :
    (blockEmb2 K p f 3 2 B : Su K p f 4) • x =
      ![x 0, x 1, ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 * x 2 + ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 * x 3,
        ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 * x 2 + ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 * x 3] := by
  rw [smul_def, coe_coe_blockEmb2]
  exact blockMat4_mulVec_two _ x


theorem exists_su2_axis_one (hinv : ∀ x : K, unitaryInvolution K p f (unitaryInvolution K p f x) = x)
    (x0 x1 s : K) (hs0 : s ≠ 0)
    (hs : unitaryInvolution K p f s * s =
      unitaryInvolution K p f x0 * x0 + unitaryInvolution K p f x1 * x1) :
    ∃ g : Su K p f 2, ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 * x0 +
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 * x1 = 0 ∧
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 * x0 +
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 * x1 = s := by
  obtain ⟨h, e1, e2⟩ := axis_one_aux (unitaryInvolution K p f) x0 x1 s hs0 hs
  exact ⟨su2Of hinv (x1 / s) (-(x0 / s)) h, e1, e2⟩

theorem exists_su2_axis_zero (hinv : ∀ x : K, unitaryInvolution K p f (unitaryInvolution K p f x) = x)
    (x0 x1 t : K) (ht0 : t ≠ 0)
    (ht : unitaryInvolution K p f t * t =
      unitaryInvolution K p f x0 * x0 + unitaryInvolution K p f x1 * x1) :
    ∃ g : Su K p f 2, ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 * x0 +
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 * x1 = t ∧
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 * x0 +
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 * x1 = 0 := by
  obtain ⟨h, e1, e2⟩ := axis_zero_aux (unitaryInvolution K p f) hinv x0 x1 t ht0 ht
  exact ⟨su2Of hinv (unitaryInvolution K p f (x0 / t)) (unitaryInvolution K p f (x1 / t)) h, e1, e2⟩


theorem blockEmb2_one_eq_tv (hinv : ∀ x : K, unitaryInvolution K p f (unitaryInvolution K p f x) = x)
    (g : Su K p f 2) (a : Fin 2 → K) (c : K) (hc : c + unitaryInvolution K p f c = 0)
    (hg : ∀ y : Fin 2 → K, g • y = y + (c * herm (unitaryInvolution K p f) a y) • a)
    (ha4 : herm (unitaryInvolution K p f) ![0, a 0, a 1, 0] ![0, a 0, a 1, 0] = 0) :
    blockEmb2 K p f 3 1 g = tv hinv ha4 hc := by
  apply ext_smul
  intro x
  rw [blockEmb2_smul_one, tv_smul]
  have hg0 := congrFun (hg ![x 1, x 2]) 0
  have hg1 := congrFun (hg ![x 1, x 2]) 1
  simp only [smul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hg0 hg1
  have hh : herm (unitaryInvolution K p f) ![0, a 0, a 1, 0] x =
      herm (unitaryInvolution K p f) a ![x 1, x 2] := by
    simp [herm_def, Fin.sum_univ_four, Fin.sum_univ_two]
  rw [hh]
  funext j
  fin_cases j
  · simp
  · simp [hg0]
  · simp [hg1]
  · simp


theorem block_one_le_of_tv (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (Γ : Subgroup (Su K p f 4))
    (hΓ : ∀ a : Fin 2 → K, herm (unitaryInvolution K p f) a a = 0 → ∀ (c : K)
      (hc : c + unitaryInvolution K p f c = 0)
      (ha4 : herm (unitaryInvolution K p f) ![0, a 0, a 1, 0] ![0, a 0, a 1, 0] = 0), tv hσ.invol ha4 hc ∈ Γ) :
    ∀ B : Su K p f 2, blockEmb2 K p f 3 1 B ∈ Γ := by
  have hle : tvSet (unitaryInvolution K p f) 2 ⊆ (Γ.comap (blockEmb2 K p f 3 1) : Set (Su K p f 2)) := by
    rintro g ⟨a, c, ha, hc, hg⟩
    have ha4 : herm (unitaryInvolution K p f) ![0, a 0, a 1, 0] ![0, a 0, a 1, 0] = 0 := by
      have : herm (unitaryInvolution K p f) ![0, a 0, a 1, 0] ![0, a 0, a 1, 0] =
          herm (unitaryInvolution K p f) a a := by
        simp [herm_def, Fin.sum_univ_four, Fin.sum_univ_two]
      rw [this, ha]
    show blockEmb2 K p f 3 1 g ∈ Γ
    rw [blockEmb2_one_eq_tv hσ.invol g a c hc hg ha4]
    exact hΓ a ha c hc ha4
  intro B
  have hT : T (unitaryInvolution K p f) 2 ≤ Γ.comap (blockEmb2 K p f 3 1) := (Subgroup.closure_le _).2 hle
  have hB : B ∈ T (unitaryInvolution K p f) 2 := by rw [T_two_eq_top hσ]; trivial
  exact hT hB

theorem exists_link_move (hσ : IsUnitaryInvolution (unitaryInvolution K p f))
    (v : Fin 4 → K) (hv : herm (unitaryInvolution K p f) v v = 0)
    (hv01 : unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1 ≠ 0) :
    ∃ (s t : K) (g0 g2 : Su K p f 2), s ≠ 0 ∧ t ≠ 0 ∧
      unitaryInvolution K p f s * s + unitaryInvolution K p f t * t = 0 ∧
      (blockEmb2 K p f 3 0 g0 * blockEmb2 K p f 3 2 g2 : Su K p f 4) • v = ![0, s, t, 0] := by
  have hinv := hσ.invol
  have hn12 : (unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1) +
      (unitaryInvolution K p f (v 2) * v 2 + unitaryInvolution K p f (v 3) * v 3) = 0 := by
    simp only [herm_def, Fin.sum_univ_four] at hv
    linear_combination hv
  have hfix1 : unitaryInvolution K p f (unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1) =
      unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1 := by
    rw [map_add, hσ.norm_fixed, hσ.norm_fixed]
  have hfix2 : unitaryInvolution K p f (unitaryInvolution K p f (v 2) * v 2 + unitaryInvolution K p f (v 3) * v 3) =
      unitaryInvolution K p f (v 2) * v 2 + unitaryInvolution K p f (v 3) * v 3 := by
    rw [map_add, hσ.norm_fixed, hσ.norm_fixed]
  have hn2 : unitaryInvolution K p f (v 2) * v 2 + unitaryInvolution K p f (v 3) * v 3 ≠ 0 := by
    intro h0
    apply hv01
    linear_combination hn12 - h0
  obtain ⟨s, hs⟩ := hσ.exists_norm hfix1
  obtain ⟨t, ht⟩ := hσ.exists_norm hfix2
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hv01
    rw [← hs]
    simp
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hn2
    rw [← ht]
    simp
  obtain ⟨g0, hg00, hg01⟩ := exists_su2_axis_one hinv (v 0) (v 1) s hs0 hs
  obtain ⟨g2, hg20, hg21⟩ := exists_su2_axis_zero hinv (v 2) (v 3) t ht0 ht
  refine ⟨s, t, g0, g2, hs0, ht0, by rw [hs, ht]; exact hn12, ?_⟩
  rw [mul_smul, blockEmb2_smul_two, blockEmb2_smul_zero]
  funext j
  fin_cases j
  · simpa using hg00
  · simpa using hg01
  · simpa using hg20
  · simpa using hg21

theorem torus_move (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (s t ρ : K)
    (hρ : unitaryInvolution K p f ρ * ρ = 1) :
    ∃ τ : Su K p f 2, (blockEmb2 K p f 3 2 τ : Su K p f 4) • ![0, s, t, 0] = ![0, s, ρ * t, 0] := by
  have h : unitaryInvolution K p f ρ * ρ + unitaryInvolution K p f 0 * 0 = 1 := by
    rw [map_zero]; linear_combination hρ
  refine ⟨su2Of hσ.invol ρ 0 h, ?_⟩
  rw [blockEmb2_smul_two]
  funext j
  fin_cases j
  · simp
  · simp
  · show ρ * t + 0 * 0 = ρ * t
    simp
  · show -(unitaryInvolution K p f 0) * t + unitaryInvolution K p f ρ * 0 = 0
    simp

theorem core_link (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) (Γ : Subgroup (Su K p f 4))
    (h0 : ∀ B : Su K p f 2, blockEmb2 K p f 3 0 B ∈ Γ) (h2 : ∀ B : Su K p f 2, blockEmb2 K p f 3 2 B ∈ Γ)
    (v : Fin 4 → K) (hv : herm (unitaryInvolution K p f) v v = 0)
    (hv01 : unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1 ≠ 0)
    (hT : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0),
      tv (isUnitaryInvolution_unitaryInvolution hK).invol hv hc ∈ Γ) : Γ = ⊤ := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  have hinv := hσ.invol
  obtain ⟨s, t, g0, g2, hs0, ht0, hst, hbv⟩ := exists_link_move hσ v hv hv01
  have hb : (blockEmb2 K p f 3 0 g0 * blockEmb2 K p f 3 2 g2 : Su K p f 4) ∈ Γ :=
    Γ.mul_mem (h0 g0) (h2 g2)
  have hfam : ∀ ρ : K, unitaryInvolution K p f ρ * ρ = 1 →
      ∀ (hu0 : herm (unitaryInvolution K p f) ![0, s, ρ * t, 0] ![0, s, ρ * t, 0] = 0) (c : K)
        (hc : c + unitaryInvolution K p f c = 0), tv hinv hu0 hc ∈ Γ := by
    intro ρ hρ hu0 c hc
    obtain ⟨τ, hτ⟩ := torus_move hσ s t ρ hρ
    have hg : (blockEmb2 K p f 3 2 τ * (blockEmb2 K p f 3 0 g0 * blockEmb2 K p f 3 2 g2) : Su K p f 4) ∈ Γ :=
      Γ.mul_mem (h2 τ) hb
    have hw : (![0, s, ρ * t, 0] : Fin 4 → K) =
        (blockEmb2 K p f 3 2 τ * (blockEmb2 K p f 3 0 g0 * blockEmb2 K p f 3 2 g2) : Su K p f 4) • v := by
      rw [mul_smul, hbv, hτ]
    exact tv_conj_mem hinv Γ hg hv hT hw hu0 c hc
  have hσs : unitaryInvolution K p f s ≠ 0 := (map_ne_zero _).2 hs0
  have hΓ : ∀ a : Fin 2 → K, herm (unitaryInvolution K p f) a a = 0 → ∀ (c : K)
      (hc : c + unitaryInvolution K p f c = 0)
      (ha4 : herm (unitaryInvolution K p f) ![0, a 0, a 1, 0] ![0, a 0, a 1, 0] = 0), tv hinv ha4 hc ∈ Γ := by
    intro a ha c hc ha4
    simp only [herm_def, Fin.sum_univ_two] at ha
    by_cases ha0 : a 0 = 0
    · have ha1 : a 1 = 0 := by
        rw [ha0, map_zero, zero_mul, zero_add] at ha
        rcases mul_eq_zero.1 ha with h | h
        · exact (map_eq_zero_iff _ (EquivLike.injective _)).1 h
        · exact h
      have h1 : tv hinv ha4 hc = 1 := by
        apply ext_smul
        intro x
        rw [tv_smul, one_smul]
        have hz : (![0, a 0, a 1, 0] : Fin 4 → K) = 0 := by
          funext j
          fin_cases j <;> simp [ha0, ha1]
        rw [hz]
        simp
      rw [h1]
      exact Γ.one_mem
    · have hσa0 : unitaryInvolution K p f (a 0) ≠ 0 := (map_ne_zero _).2 ha0
      have hρ : unitaryInvolution K p f (a 1 / a 0 * s / t) * (a 1 / a 0 * s / t) = 1 := by
        have hσt : unitaryInvolution K p f t ≠ 0 := (map_ne_zero _).2 ht0
        simp only [map_div₀, map_mul]
        field_simp
        linear_combination (unitaryInvolution K p f s * s) * ha - (unitaryInvolution K p f (a 0) * a 0) * hst
      have hu : (![0, s, a 1 / a 0 * s / t * t, 0] : Fin 4 → K) = (s / a 0) • ![0, a 0, a 1, 0] := by
        funext j
        fin_cases j
        · simp
        · simp
          field_simp
        · simp
          field_simp
        · simp
      exact tv_mem_of_scalar hinv Γ (s / a 0) (div_ne_zero hs0 ha0) hu
        (fun hu0 c hc => hfam _ hρ hu0 c hc) ha4 c hc
  have hone := block_one_le_of_tv hσ Γ hΓ
  have h3 := sup_range_blockEmb2_three (K := K) (p := p) (f := f) hK hq
  rw [eq_top_iff, ← h3]
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨B, rfl⟩
    exact h0 B
  · rintro _ ⟨B, rfl⟩
    exact hone B
  · rintro _ ⟨B, rfl⟩
    exact h2 B


end Unitary

end GenLocU4Aux

end CFSG.GH74.Generic.BProg.B2
