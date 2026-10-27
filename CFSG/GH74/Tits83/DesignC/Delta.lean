module

public import CFSG.GH74.Tits83.OctCoord
public import CFSG.GH74.BNPair.RootGroups

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

namespace OctCoord

variable {G : Type u} [Group G] {U : ℤ → Subgroup G}

@[expose] noncomputable def eOdd (c : OctCoord U) (j : ℤ) (hj : Odd j) : c.K ≃ U j :=
  Equiv.ofBijective (fun t => (⟨c.X j t, c.X_mem j t⟩ : U j)) (c.bij_odd j hj)

@[expose] noncomputable def eEven (c : OctCoord U) (j : ℤ) (hj : Even j) : c.K × c.K ≃ U j :=
  Equiv.ofBijective (fun p => (⟨c.X j p.1 * c.X' j p.2,
    (U j).mul_mem (c.X_mem j p.1) (c.X'_mem j p.2 hj)⟩ : U j)) (c.bij_even j hj)

@[expose] def coordMul (c : OctCoord U) (x y : c.K × c.K) : c.K × c.K :=
  (x.1 + y.1, y.1 * c.σ x.1 + x.2 + y.2)

theorem X_zero_odd (c : OctCoord U) {j : ℤ} (hj : Odd j) : c.X j 0 = 1 := by
  have h := c.X_add_odd j hj 0 0
  rw [zero_add] at h
  exact (mul_right_inj (c.X j 0)).mp (by simpa using h.symm)

theorem X'_zero (c : OctCoord U) {j : ℤ} (hj : Even j) : c.X' j 0 = 1 := by
  have h := c.X'_add j hj 0 0
  rw [zero_add] at h
  exact (mul_right_inj (c.X' j 0)).mp (by simpa using h.symm)

theorem X_zero_even (c : OctCoord U) {j : ℤ} (hj : Even j) : c.X j 0 = 1 := by
  have h := c.X_mul_even j hj 0 0
  rw [zero_add, zero_mul, c.X'_zero hj, mul_one] at h
  exact (mul_right_inj (c.X j 0)).mp (by simpa using h.symm)

theorem eOdd_apply (c : OctCoord U) {j : ℤ} (hj : Odd j) (t : c.K) :
    c.eOdd j hj t = ⟨c.X j t, c.X_mem j t⟩ := rfl

theorem eEven_apply (c : OctCoord U) {j : ℤ} (hj : Even j) (p : c.K × c.K) :
    c.eEven j hj p = ⟨c.X j p.1 * c.X' j p.2,
      (U j).mul_mem (c.X_mem j p.1) (c.X'_mem j p.2 hj)⟩ := rfl

theorem eOdd_add (c : OctCoord U) {j : ℤ} (hj : Odd j) (t u : c.K) :
    c.eOdd j hj (t + u) = c.eOdd j hj t * c.eOdd j hj u := by
  apply Subtype.ext
  exact c.X_add_odd j hj t u

theorem eOdd_zero (c : OctCoord U) {j : ℤ} (hj : Odd j) : c.eOdd j hj 0 = 1 := by
  apply Subtype.ext
  exact c.X_zero_odd hj

theorem eEven_zero (c : OctCoord U) {j : ℤ} (hj : Even j) : c.eEven j hj (0, 0) = 1 := by
  apply Subtype.ext
  simp [c.eEven_apply, c.X_zero_even hj, c.X'_zero hj]

theorem eEven_mul (c : OctCoord U) {j : ℤ} (hj : Even j) (x y : c.K × c.K) :
    c.eEven j hj x * c.eEven j hj y = c.eEven j hj (c.coordMul x y) := by
  apply Subtype.ext
  simp only [eEven_apply, coordMul, Subtype.coe_mk]
  calc
    (c.X j x.1 * c.X' j x.2) * (c.X j y.1 * c.X' j y.2)
        = c.X j x.1 * (c.X' j x.2 * c.X j y.1) * c.X' j y.2 := by group
    _ = c.X j x.1 * (c.X j y.1 * c.X' j x.2) * c.X' j y.2 := by
          rw [c.X'_comm j hj x.2 y.1]
    _ = (c.X j x.1 * c.X j y.1) * (c.X' j x.2 * c.X' j y.2) := by group
    _ = c.X j (x.1 + y.1) *
          (c.X' j (y.1 * c.σ x.1) * c.X' j (x.2 + y.2)) := by
          rw [c.X_mul_even j hj x.1 y.1, c.X'_add j hj x.2 y.2]
          group
    _ = c.X j (x.1 + y.1) *
          c.X' j (y.1 * c.σ x.1 + (x.2 + y.2)) := by
          rw [← c.X'_add j hj (y.1 * c.σ x.1) (x.2 + y.2)]
    _ = c.X j (x.1 + y.1) * c.X' j (y.1 * c.σ x.1 + x.2 + y.2) := by
          rw [add_assoc]

theorem eEven_symm_mul (c : OctCoord U) {j : ℤ} (hj : Even j) (x y : U j) :
    (c.eEven j hj).symm (x * y) =
      c.coordMul ((c.eEven j hj).symm x) ((c.eEven j hj).symm y) := by
  apply (c.eEven j hj).injective
  rw [← c.eEven_mul]
  simp

theorem eOdd_symm_mul (c : OctCoord U) {j : ℤ} (hj : Odd j) (x y : U j) :
    (c.eOdd j hj).symm (x * y) = (c.eOdd j hj).symm x + (c.eOdd j hj).symm y := by
  apply (c.eOdd j hj).injective
  rw [c.eOdd_add]
  simp

end OctCoord

section Graph

variable {G G' : Type u} [Group G] [Group G']
variable {U : ℤ → Subgroup G} {U' : ℤ → Subgroup G'}
variable (c : OctCoord U) (c' : OctCoord U') (θ : c.K ≃+* c'.K)
variable (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))

@[expose] def thetaPair (p : c.K × c.K) : c'.K × c'.K := (θ p.1, θ p.2)

theorem thetaPair_zero : thetaPair c c' θ (0, 0) = (0, 0) := by
  simp [thetaPair]

theorem thetaPair_coordMul (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) (p q : c.K × c.K) :
    thetaPair c c' θ (c.coordMul p q) =
      c'.coordMul (thetaPair c c' θ p) (thetaPair c c' θ q) := by
  ext
  · simp [thetaPair, OctCoord.coordMul, map_add]
  · simp only [thetaPair, OctCoord.coordMul, map_add, map_mul]
    rw [hθ]

@[expose] noncomputable def gOdd (j : ℤ) (hj : Odd j) : U j →* U' j where
  toFun x := c'.eOdd j hj (θ ((c.eOdd j hj).symm x))
  map_one' := by
    have h0 : (c.eOdd j hj).symm 1 = 0 := by
      rw [← c.eOdd_zero hj, Equiv.symm_apply_apply]
    rw [h0, map_zero, c'.eOdd_zero hj]
  map_mul' := by
    intro x y
    rw [c.eOdd_symm_mul hj x y, map_add, c'.eOdd_add]

@[expose] noncomputable def gEven (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    (j : ℤ) (hj : Even j) : U j →* U' j where
  toFun x := c'.eEven j hj (thetaPair c c' θ ((c.eEven j hj).symm x))
  map_one' := by
    have h0 : (c.eEven j hj).symm 1 = (0, 0) := by
      rw [← c.eEven_zero hj, Equiv.symm_apply_apply]
    rw [h0, thetaPair_zero, c'.eEven_zero hj]
  map_mul' := by
    intro x y
    rw [c.eEven_symm_mul hj x y, thetaPair_coordMul c c' θ hθ, ← c'.eEven_mul]

@[expose] noncomputable def g (j : ℤ) : U j →* U' j :=
  if hj : Even j then gEven c c' θ hθ j hj
  else gOdd c c' θ j (Int.not_even_iff_odd.mp hj)

theorem g_of_even {j : ℤ} (hj : Even j) :
    g c c' θ hθ j = gEven c c' θ hθ j hj := by
  rw [g, dif_pos hj]

theorem g_of_odd {j : ℤ} (hj : Odd j) :
    g c c' θ hθ j = gOdd c c' θ j hj := by
  rw [g, dif_neg (Int.not_even_iff_odd.mpr hj)]

theorem g_eOdd (j : ℤ) (hj : Odd j) (t : c.K) :
    g c c' θ hθ j (c.eOdd j hj t) = c'.eOdd j hj (θ t) := by
  rw [g_of_odd c c' θ hθ hj]
  change c'.eOdd j hj (θ ((c.eOdd j hj).symm (c.eOdd j hj t))) = c'.eOdd j hj (θ t)
  rw [Equiv.symm_apply_apply]

theorem g_eEven (j : ℤ) (hj : Even j) (p : c.K × c.K) :
    g c c' θ hθ j (c.eEven j hj p) = c'.eEven j hj (thetaPair c c' θ p) := by
  rw [g_of_even c c' θ hθ hj]
  change c'.eEven j hj (thetaPair c c' θ ((c.eEven j hj).symm (c.eEven j hj p))) =
    c'.eEven j hj (thetaPair c c' θ p)
  rw [Equiv.symm_apply_apply]

theorem g_even_X (j : ℤ) (hj : Even j) (t : c.K) :
    g c c' θ hθ j (c.eEven j hj (t, 0)) =
      ⟨c'.X j (θ t), c'.X_mem j (θ t)⟩ := by
  rw [g_eEven]
  apply Subtype.ext
  simp [thetaPair, c'.eEven_apply, c'.X'_zero hj]

theorem g_even_X' (j : ℤ) (hj : Even j) (t : c.K) :
    g c c' θ hθ j (c.eEven j hj (0, t)) =
      ⟨c'.X' j (θ t), c'.X'_mem j (θ t) hj⟩ := by
  rw [g_eEven]
  apply Subtype.ext
  simp [thetaPair, c'.eEven_apply, c'.X_zero_even hj]

@[expose] noncomputable def psi (j : ℤ) : U j →* G × G' where
  toFun x := ((x : G), (g c c' θ hθ j x : G'))
  map_one' := by
    ext <;> simp
  map_mul' := by
    intro x y
    ext <;> simp

@[expose] def gpX (j : ℤ) (t : c.K) : G × G' := (c.X j t, c'.X j (θ t))

@[expose] def gpX' (j : ℤ) (t : c.K) : G × G' := (c.X' j t, c'.X' j (θ t))

@[expose] def Gen (j : ℤ) : Set (G × G') :=
  {x | (∃ t : c.K, x = gpX c c' θ j t) ∨
    (Even j ∧ ∃ t : c.K, x = gpX' c c' θ j t)}

@[expose] def Delta (j : ℤ) : Subgroup (G × G') := Subgroup.closure (Gen c c' θ j)

theorem gpX_mem_Delta (j : ℤ) (t : c.K) : gpX c c' θ j t ∈ Delta c c' θ j :=
  Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)

theorem gpX'_mem_Delta (j : ℤ) (hj : Even j) (t : c.K) :
    gpX' c c' θ j t ∈ Delta c c' θ j :=
  Subgroup.subset_closure (Or.inr ⟨hj, t, rfl⟩)

theorem gpX_mem_range_psi (j : ℤ) (t : c.K) :
    gpX c c' θ j t ∈ (psi c c' θ hθ j).range := by
  by_cases hj : Even j
  · refine ⟨c.eEven j hj (t, 0), ?_⟩
    ext
    · simp [psi, gpX, c.eEven_apply, c.X'_zero hj]
    · simp [psi, gpX, g_even_X c c' θ hθ j hj t]
  · have ho : Odd j := Int.not_even_iff_odd.mp hj
    refine ⟨c.eOdd j ho t, ?_⟩
    ext
    · simp [psi, gpX, c.eOdd_apply]
    · simp [psi, gpX, g_eOdd c c' θ hθ j ho t, c'.eOdd_apply]

theorem gpX'_mem_range_psi (j : ℤ) (hj : Even j) (t : c.K) :
    gpX' c c' θ j t ∈ (psi c c' θ hθ j).range := by
  refine ⟨c.eEven j hj (0, t), ?_⟩
  ext
  · simp [psi, gpX', c.eEven_apply, c.X_zero_even hj]
  · simp [psi, gpX', g_even_X' c c' θ hθ j hj t]

theorem Gen_subset_range_psi (j : ℤ) : Gen c c' θ j ⊆ (psi c c' θ hθ j).range := by
  intro x hx
  simp only [Gen, Set.mem_setOf_eq] at hx
  rcases hx with ⟨t, rfl⟩ | ⟨hj, t, rfl⟩
  · exact gpX_mem_range_psi c c' θ hθ j t
  · exact gpX'_mem_range_psi c c' θ hθ j hj t

theorem Delta_le_range_psi (j : ℤ) : Delta c c' θ j ≤ (psi c c' θ hθ j).range := by
  rw [Delta]
  exact (Subgroup.closure_le (psi c c' θ hθ j).range).2 (Gen_subset_range_psi c c' θ hθ j)

theorem Delta_eq_psi {j : ℤ} {f : G × G'} (hf : f ∈ Delta c c' θ j) :
    ∃ x : U j, f = psi c c' θ hθ j x := by
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 (Delta_le_range_psi c c' θ hθ j hf)
  exact ⟨x, rfl⟩

@[expose] def DeltaWin (i j : ℤ) : Subgroup (G × G') :=
  ⨆ k ∈ intList (i + 1) (j - 1), Delta c c' θ k

theorem mem_DeltaWin_of_mem_Delta {i j k : ℤ} (hik : i < k) (hkj : k < j)
    {x : G × G'} (hx : x ∈ Delta c c' θ k) : x ∈ DeltaWin c c' θ i j := by
  rw [DeltaWin]
  exact (le_iSup₂_of_le (f := fun k (_ : k ∈ intList (i + 1) (j - 1)) =>
    Delta c c' θ k) k (mem_intList_iff.2 ⟨by omega, by omega⟩) le_rfl) hx

theorem gpX_mem_DeltaWin {i j k : ℤ} (hik : i < k) (hkj : k < j) (t : c.K) :
    gpX c c' θ k t ∈ DeltaWin c c' θ i j :=
  mem_DeltaWin_of_mem_Delta c c' θ hik hkj (gpX_mem_Delta c c' θ k t)

theorem gpX'_mem_DeltaWin {i j k : ℤ} (hik : i < k) (hkj : k < j)
    (hk : Even k) (t : c.K) :
    gpX' c c' θ k t ∈ DeltaWin c c' θ i j :=
  mem_DeltaWin_of_mem_Delta c c' θ hik hkj (gpX'_mem_Delta c c' θ k hk t)

end Graph

end CFSG.GH74.Tits83
