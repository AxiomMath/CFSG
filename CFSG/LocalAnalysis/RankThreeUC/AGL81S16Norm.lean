module

public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.ClassicalGroups.Unitary.Transitivity
public import CFSG.Open.StatedDefs
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.ClassicalGroups.Unitary CFSG.Open
open CFSG.LieType.Universal.Unitary (SUid conjTr)

section Rot

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem su2_smul_single_one (hσ : ∀ c, σ (σ c) = c) {α β : F} (h : σ α * α + σ β * β = 1) :
    su2 hσ h • (Pi.single 1 1 : Fin 2 → F) = ![-σ β, σ α] := by
  rw [su2, mkSU_smul]
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_rot (hσ : IsUnitaryInvolution σ) {n : ℕ} {x z : Fin n → F}
    (hx : herm σ x x = 1) (hz : herm σ z z = 1) (hxz : herm σ x z = 0) {α β : F}
    (h : σ α * α + σ β * β = 1) :
    ∃ g : SUid σ n, g • x = α • x + β • z ∧ g • z = (-σ β) • x + σ α • z ∧
      ∀ v, herm σ x v = 0 → herm σ z v = 0 → g • v = v := by
  have hzx : herm σ z x = 0 := herm_eq_zero_comm σ hσ.invol hxz
  have hφ : ∀ c d : Fin 2 → F, herm σ (pairL x z c) (pairL x z d) = herm σ c d := by
    intro c d
    simp only [pairL, LinearMap.coe_mk, AddHom.coe_mk, herm_add_left, herm_add_right,
      herm_smul_left, herm_smul_right, hx, hz, hxz, hzx, herm_fin_two]
    ring
  have hA : su2 hσ.invol h ∈ T σ 2 := by
    rw [T_two_eq_top hσ]
    exact Subgroup.mem_top _
  obtain ⟨g, hg, hgφ, hperp⟩ := transport hσ.invol (pairL x z) hφ hA
  refine ⟨g, ?_, ?_, ?_⟩
  · have hx' : pairL x z (Pi.single 0 1) = x := by simp [pairL]
    rw [← hx', hgφ, su2_smul_single]
    simp [pairL]
  · have hz' : pairL x z (Pi.single 1 1) = z := by simp [pairL]
    rw [← hz', hgφ, su2_smul_single_one hσ.invol]
    simp [pairL]
  · intro v hxv hzv
    apply hperp
    intro u
    simp only [pairL, LinearMap.coe_mk, AddHom.coe_mk, herm_add_left, herm_smul_left, hxv, hzv]
    ring

theorem exists_rot_std (hσ : IsUnitaryInvolution σ) {i j : Fin 4} (hij : i ≠ j) {α β : F}
    (h : σ α * α + σ β * β = 1) :
    ∃ g : SUid σ 4, g • (Pi.single i 1 : Fin 4 → F) = α • Pi.single i 1 + β • Pi.single j 1 ∧
      g • (Pi.single j 1 : Fin 4 → F) = (-σ β) • Pi.single i 1 + σ α • Pi.single j 1 ∧
      ∀ v : Fin 4 → F, v i = 0 → v j = 0 → g • v = v := by
  have hii : herm σ (Pi.single i 1 : Fin 4 → F) (Pi.single i 1) = 1 := by
    simp [herm_single_left]
  have hjj : herm σ (Pi.single j 1 : Fin 4 → F) (Pi.single j 1) = 1 := by
    simp [herm_single_left]
  have hij' : herm σ (Pi.single i 1 : Fin 4 → F) (Pi.single j 1) = 0 := by
    simp [herm_single_left, Pi.single_apply, hij.symm]
  obtain ⟨g, h1, h2, h3⟩ := exists_rot hσ hii hjj hij' h
  refine ⟨g, h1, h2, fun v hi hj => h3 v ?_ ?_⟩
  · simp [herm_single_left, hi]
  · simp [herm_single_left, hj]

end Rot

section Commutant

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem rot_smul_apply {g : SUid σ 4} {i j : Fin 4} (hij : i ≠ j) {α β : F}
    (h1 : g • (Pi.single i 1 : Fin 4 → F) = α • Pi.single i 1 + β • Pi.single j 1)
    (h2 : g • (Pi.single j 1 : Fin 4 → F) = (-σ β) • Pi.single i 1 + σ α • Pi.single j 1)
    (h3 : ∀ v : Fin 4 → F, v i = 0 → v j = 0 → g • v = v) (w : Fin 4 → F) :
    (g • w) i = α * w i + (-σ β) * w j ∧ (g • w) j = β * w i + σ α * w j := by
  set w' : Fin 4 → F := w - w i • Pi.single i 1 - w j • Pi.single j 1 with hw'
  have hw'i : w' i = 0 := by simp [hw', Pi.single_apply, hij.symm]
  have hw'j : w' j = 0 := by simp [hw', Pi.single_apply, hij]
  have hdec : w = w i • (Pi.single i 1 : Fin 4 → F) + w j • (Pi.single j 1 : Fin 4 → F) + w' := by
    rw [hw']
    abel
  have hgw : g • w = w i • (g • (Pi.single i 1 : Fin 4 → F)) +
      w j • (g • (Pi.single j 1 : Fin 4 → F)) + w' := by
    conv_lhs => rw [hdec]
    rw [smul_add, smul_add, smul_comm g (w i), smul_comm g (w j), h3 w' hw'i hw'j]
  rw [hgw, h1, h2]
  constructor
  · simp [Pi.single_apply, hij.symm, hij, hw'i]
    ring
  · simp [Pi.single_apply, hij.symm, hij, hw'j]
    ring

theorem commutant_offdiag (hσ : IsUnitaryInvolution σ) (β : (Fin 4 → F) →+ (Fin 4 → F))
    (hβ : ∀ (g : SUid σ 4) (x : Fin 4 → F), β (g • x) = g • β x) (k i : Fin 4) (hik : i ≠ k)
    (y : F) : (β (y • (Pi.single k 1 : Fin 4 → F))) i = 0 := by
  obtain ⟨j, hji, hjk⟩ : ∃ j : Fin 4, j ≠ i ∧ j ≠ k := by
    have : ∀ k i : Fin 4, ∃ j : Fin 4, j ≠ i ∧ j ≠ k := by decide
    exact this k i
  obtain ⟨ω, hω1, hω⟩ := hσ.exists_norm_one_ne_one
  obtain ⟨g, h1, h2, h3⟩ := exists_rot_std hσ (i := i) (j := j) hji.symm (α := ω) (β := 0)
    (by rw [map_zero, mul_zero, add_zero]; exact hω1)
  have hyk : ∀ m : Fin 4, m ≠ k → (y • (Pi.single k 1 : Fin 4 → F)) m = 0 := fun m hm => by
    simp [Pi.single_apply, hm]
  have hfix : g • β (y • (Pi.single k 1 : Fin 4 → F)) = β (y • (Pi.single k 1 : Fin 4 → F)) := by
    rw [← hβ g, h3 _ (hyk i hik) (hyk j hjk)]
  have h4 := (rot_smul_apply hji.symm h1 h2 h3 (β (y • (Pi.single k 1 : Fin 4 → F)))).1
  rw [hfix] at h4
  simp only [map_zero, neg_zero, zero_mul, add_zero] at h4
  have h5 : (ω - 1) * (β (y • (Pi.single k 1 : Fin 4 → F))) i = 0 := by linear_combination -h4
  rcases mul_eq_zero.mp h5 with h | h
  · exact absurd (sub_eq_zero.mp h) hω
  · exact h

theorem commutant_diag (hσ : IsUnitaryInvolution σ) (β : (Fin 4 → F) →+ (Fin 4 → F))
    (hβ : ∀ (g : SUid σ 4) (x : Fin 4 → F), β (g • x) = g • β x) (k : Fin 4) (y : F) :
    β (y • (Pi.single k 1 : Fin 4 → F)) =
      (β (y • (Pi.single k 1 : Fin 4 → F))) k • (Pi.single k 1 : Fin 4 → F) := by
  funext i
  by_cases hik : i = k
  · subst hik
    simp
  · simp [Pi.single_apply, hik, commutant_offdiag hσ β hβ k i hik y]

theorem commutant_suid (hσ : IsUnitaryInvolution σ) (β : (Fin 4 → F) →+ (Fin 4 → F))
    (hβ : ∀ (g : SUid σ 4) (x : Fin 4 → F), β (g • x) = g • β x) :
    ∃ μ : F, ∀ x, β x = μ • x := by
  obtain ⟨gk, hgk⟩ : ∃ gk : Fin 4 → F → F, ∀ k y,
      β (y • (Pi.single k 1 : Fin 4 → F)) = gk k y • (Pi.single k 1 : Fin 4 → F) :=
    ⟨fun k y => (β (y • (Pi.single k 1 : Fin 4 → F))) k, fun k y => commutant_diag hσ β hβ k y⟩
  have step : ∀ {i j : Fin 4}, i ≠ j → ∀ {α b : F}, σ α * α + σ b * b = 1 → ∀ y : F,
      gk i (y * α) = gk i y * α ∧ gk j (y * b) = gk i y * b := by
    intro i j hij α b h y
    obtain ⟨g, h1, h2, h3⟩ := exists_rot_std hσ hij h
    have hL : β (g • (y • (Pi.single i 1 : Fin 4 → F))) =
        gk i (y * α) • (Pi.single i 1 : Fin 4 → F) + gk j (y * b) • (Pi.single j 1 : Fin 4 → F) := by
      rw [smul_comm g y, h1, smul_add, smul_smul, smul_smul, map_add, hgk i, hgk j]
    have hR : g • β (y • (Pi.single i 1 : Fin 4 → F)) =
        (gk i y * α) • (Pi.single i 1 : Fin 4 → F) + (gk i y * b) • (Pi.single j 1 : Fin 4 → F) := by
      rw [hgk i y, smul_comm g, h1, smul_add, smul_smul, smul_smul]
    have h6 := hβ g (y • (Pi.single i 1 : Fin 4 → F))
    rw [hL, hR] at h6
    have h7 := congrFun h6 i
    have h8 := congrFun h6 j
    simp [Pi.single_apply, hij, hij.symm] at h7 h8
    exact ⟨h7, h8⟩
  have hmul : ∀ i : Fin 4, ∀ y : F, gk i y = gk i 1 * y := by
    intro i y
    obtain ⟨j, hj⟩ : ∃ j : Fin 4, i ≠ j := by
      have : ∀ i : Fin 4, ∃ j : Fin 4, i ≠ j := by decide
      exact this i
    obtain ⟨b, hb⟩ := hσ.exists_norm (d := 1 - σ y * y) (by
      rw [map_sub, map_one, map_mul, hσ.invol]
      ring)
    have := (step hj (α := y) (b := b) (by linear_combination hb) 1).1
    simpa using this
  have heq : ∀ i j : Fin 4, i ≠ j → gk j 1 = gk i 1 := by
    intro i j hij
    have := (step hij (α := 0) (b := 1) (by simp) 1).2
    simpa using this
  refine ⟨gk 0 1, fun x => ?_⟩
  have hk : ∀ k : Fin 4, gk k 1 = gk 0 1 := by
    intro k
    by_cases hk0 : k = 0
    · rw [hk0]
    · exact heq 0 k (Ne.symm hk0)
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin 4 → F) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  funext i
  simp only [Finset.sum_apply, hgk, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hmul i (x i), hk i]

end Commutant

section Normalizer

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem exists_semilinear (hσ : IsUnitaryInvolution σ) (α : (Fin 4 → F) ≃+ (Fin 4 → F))
    (h2 : ∀ g : SUid σ 4, ∃ g' : SUid σ 4, ∀ x, α.symm (g • x) = g' • α.symm x) :
    ∃ θ : F →+* F, ∀ (c : F) (x : Fin 4 → F), α (c • x) = θ c • α x := by
  have hβ : ∀ c : F, ∃ μ : F, ∀ x, α (c • α.symm x) = μ • x := by
    intro c
    refine commutant_suid hσ ((α.toAddMonoidHom).comp
      ((AddMonoidHom.mk' (fun x : Fin 4 → F => c • x) (fun a b => smul_add c a b)).comp
        α.symm.toAddMonoidHom)) ?_
    intro g x
    obtain ⟨g', hg'⟩ := h2 g
    have h3 : ∀ y, α (g' • y) = g • α y := by
      intro y
      have := hg' (α y)
      rw [AddEquiv.symm_apply_apply] at this
      rw [← this, AddEquiv.apply_symm_apply]
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddMonoidHom.mk'_apply]
    rw [hg' x, ← smul_comm g' c, h3]
  choose μ hμ using hβ
  have hsm : ∀ c y, α (c • y) = μ c • α y := by
    intro c y
    have := hμ c (α y)
    rwa [AddEquiv.symm_apply_apply] at this
  have key : ∀ a b : F, (∀ y, a • α y = b • α y) → a = b := by
    intro a b h
    have := congrFun (h (α.symm (Pi.single 0 1))) 0
    simpa using this
  refine ⟨{ toFun := μ
            map_one' := key _ _ (fun y => by rw [← hsm, one_smul, one_smul])
            map_zero' := key _ _ (fun y => by rw [← hsm, zero_smul, zero_smul, map_zero])
            map_mul' := fun c d => key _ _ (fun y => by
              rw [← hsm, mul_smul, hsm, hsm, mul_smul])
            map_add' := fun c d => key _ _ (fun y => by
              rw [← hsm, add_smul, map_add, hsm, hsm, add_smul]) }, hsm⟩

theorem herm_inv_smul_left (g : SUid σ 4) (u v : Fin 4 → F) :
    herm σ (g⁻¹ • u) v = herm σ u (g • v) := by
  rw [← herm_smul_smul σ g (g⁻¹ • u) v, smul_inv_smul]

theorem exists_su_of_normalizes (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (A : Matrix (Fin 4) (Fin 4) F) (hAA : A * A = 1)
    (hN : ∀ g : SUid σ 4, ∃ g' : SUid σ 4, ∀ x, A *ᵥ (g • x) = g' • (A *ᵥ x)) :
    ∃ g : SUid σ 4, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = A := by
  have hcomm : ∀ (g : SUid σ 4) (y : Fin 4 → F),
      (conjTr σ A * A) *ᵥ (g • y) = g • ((conjTr σ A * A) *ᵥ y) := by
    intro g y
    obtain ⟨g', hg'⟩ := hN g
    have hinv : ∀ x, A *ᵥ (g⁻¹ • x) = g'⁻¹ • (A *ᵥ x) := by
      intro x
      have := hg' (g⁻¹ • x)
      rw [smul_inv_smul] at this
      rw [this, inv_smul_smul]
    have hx : ∀ x, herm σ x ((conjTr σ A * A) *ᵥ (g • y) - g • ((conjTr σ A * A) *ᵥ y)) = 0 := by
      intro x
      rw [herm_sub_right]
      have e1 : herm σ x ((conjTr σ A * A) *ᵥ (g • y)) = herm σ (A *ᵥ x) (A *ᵥ (g • y)) := by
        rw [herm_mulVec]
      have e2 : herm σ x (g • ((conjTr σ A * A) *ᵥ y)) =
          herm σ (g⁻¹ • x) ((conjTr σ A * A) *ᵥ y) := by
        rw [herm_inv_smul_left]
      have e3 : herm σ (g⁻¹ • x) ((conjTr σ A * A) *ᵥ y) =
          herm σ (A *ᵥ (g⁻¹ • x)) (A *ᵥ y) := by
        rw [herm_mulVec]
      rw [e1, e2, e3, hg' y, hinv x, herm_inv_smul_left, sub_self]
    have h0 : (conjTr σ A * A) *ᵥ (g • y) - g • ((conjTr σ A * A) *ᵥ y) = 0 := by
      apply eq_zero_of_herm σ
      intro x
      rw [herm_conj σ hσ.invol, hx x, map_zero]
    exact sub_eq_zero.mp h0
  obtain ⟨μ, hμ⟩ := commutant_suid hσ (Matrix.mulVecLin (conjTr σ A * A)).toAddMonoidHom
    (fun g x => hcomm g x)
  have hμ' : ∀ x, (conjTr σ A * A) *ᵥ x = μ • x := hμ
  have hform : ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = μ * herm σ x y := by
    intro x y
    rw [herm_mulVec, hμ', herm_smul_right]
  have hμ1 : μ = 1 := by
    obtain ⟨y, hy⟩ := exists_herm_eq_one σ (x := (Pi.single 0 1 : Fin 4 → F)) (by
      intro h
      have := congrFun h 0
      simp at this)
    have h1 := hform (A *ᵥ Pi.single 0 1) (A *ᵥ y)
    rw [mulVec_mulVec, mulVec_mulVec, hAA, one_mulVec, one_mulVec, hform, hy] at h1
    have h3 : (μ - 1) ^ 2 = 0 := by linear_combination (-1 : F) * h1 + (1 - μ) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  have hiso : ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y := fun x y => by
    rw [hform, hμ1, one_mul]
  have hdet : A.det = 1 := by
    have h4 : A.det * A.det = 1 := by rw [← det_mul, hAA, det_one]
    have h5 : (A.det - 1) ^ 2 = 0 := by linear_combination h4 + (1 - A.det) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  exact ⟨mkSU σ A hdet hiso, rfl⟩

end Normalizer

section Stated

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem statedSU_data (hF : Nat.card F = (2 ^ n) ^ 2) :
    ∃ σ : F ≃+* F, IsUnitaryInvolution σ ∧ (2 : F) = 0 ∧
      SUid σ 4 = StatedSU 4 (2 ^ n) F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_sq (p := 2) (f := n) hF
  refine ⟨CFSG.LieType.BorelTits.unitaryInvolution F 2 n, isUnitaryInvolution_unitaryInvolution hF,
    CharP.cast_eq_zero F 2, CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4⟩

theorem commutant_statedSU (hF : Nat.card F = (2 ^ n) ^ 2) (β : (Fin 4 → F) →+ (Fin 4 → F))
    (hβ : ∀ g ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      β (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ β x) :
    ∃ μ : F, ∀ x, β x = μ • x := by
  obtain ⟨σ, hσ, -, hS⟩ := statedSU_data hF
  refine commutant_suid hσ β (fun g x => ?_)
  exact hβ g (hS ▸ g.2) x

theorem exists_semilinear_statedSU (hF : Nat.card F = (2 ^ n) ^ 2)
    (α : (Fin 4 → F) ≃+ (Fin 4 → F))
    (h : ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      α.symm (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ α.symm x) :
    ∃ θ : F →+* F, ∀ (c : F) (x : Fin 4 → F), α (c • x) = θ c • α x := by
  obtain ⟨σ, hσ, -, hS⟩ := statedSU_data hF
  refine exists_semilinear hσ α (fun g => ?_)
  obtain ⟨g', hg', hg'x⟩ := h g (hS ▸ g.2)
  exact ⟨⟨g', hS.symm ▸ hg'⟩, hg'x⟩

theorem exists_mem_statedSU_of_normalizes (hF : Nat.card F = (2 ^ n) ^ 2)
    (A : Matrix (Fin 4) (Fin 4) F) (hAA : A * A = 1)
    (h : ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      A *ᵥ (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (A *ᵥ x)) :
    ∃ g ∈ StatedSU 4 (2 ^ n) F, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = A := by
  obtain ⟨σ, hσ, h2, hS⟩ := statedSU_data hF
  obtain ⟨g, hg⟩ := exists_su_of_normalizes hσ h2 A hAA (fun g => by
    obtain ⟨g', hg', hg'x⟩ := h g (hS ▸ g.2)
    exact ⟨⟨g', hS.symm ▸ hg'⟩, hg'x⟩)
  exact ⟨g, hS ▸ g.2, hg⟩

end Stated

end CFSG.LocalAnalysis.RankThreeUC
