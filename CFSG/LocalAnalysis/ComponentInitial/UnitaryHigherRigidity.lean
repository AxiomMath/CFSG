module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherOpposite

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Module Submodule
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

variable (r ε) in
@[expose] def hypZEmb : (Fin ε → K) →ₗ[K] (HypIndex r ε → K) where
  toFun t := Sum.elim 0 (Sum.elim t 0)
  map_add' x y := funext fun c => by rcases c with i | k | i <;> simp
  map_smul' s x := funext fun c => by rcases c with i | k | i <;> simp

theorem hypSplit (v : HypIndex r ε → K) :
    v = hypXEmb r ε (fun i => v (Sum.inl i)) + hypZEmb r ε (fun k => v (Sum.inr (Sum.inl k))) +
      hypYEmb r ε (fun i => v (Sum.inr (Sum.inr i))) := by
  funext c
  rcases c with i | k | i <;> simp [hypXEmb, hypYEmb, hypZEmb]

noncomputable abbrev hdot (h : UnitaryFieldData p f K) {n : Type} [Fintype n] (a b : n → K) : K :=
  (fun i => h.bar (a i)) ⬝ᵥ b

section Hdot

variable (h : UnitaryFieldData p f K) {n : Type} [Fintype n]

theorem hdot_comm (a b : n → K) : hdot h b a = h.bar (hdot h a b) := by
  simp only [hdot, dotProduct, map_sum, map_mul, h.bar_bar]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hdot_smul_right (c : K) (a b : n → K) : hdot h a (c • b) = c * hdot h a b := by
  rw [hdot, dotProduct_smul, smul_eq_mul]

theorem hdot_smul_left (c : K) (a b : n → K) : hdot h (c • a) b = h.bar c * hdot h a b := by
  rw [hdot, hdot, ← smul_eq_mul, ← smul_dotProduct]
  congr 1
  funext i
  simp

theorem hdot_zero_right (a : n → K) : hdot h a 0 = 0 :=
  dotProduct_zero _

theorem hdot_zero_left (b : n → K) : hdot h 0 b = 0 := by
  simp [hdot]

theorem hdot_add_right (a b b' : n → K) : hdot h a (b + b') = hdot h a b + hdot h a b' :=
  dotProduct_add _ _ _

theorem hdot_add_left (a a' b : n → K) : hdot h (a + a') b = hdot h a b + hdot h a' b := by
  simp only [hdot, Pi.add_apply, map_add]
  exact add_dotProduct _ _ _

theorem hdot_sub_right (a b b' : n → K) : hdot h a (b - b') = hdot h a b - hdot h a b' :=
  dotProduct_sub _ _ _

variable [DecidableEq n]

theorem hdot_single_right (a : n → K) (j : n) : hdot h a (Pi.single j 1) = h.bar (a j) := by
  rw [hdot, dotProduct_single, mul_one]

theorem hdot_single_left (j : n) (b : n → K) : hdot h (Pi.single j 1) b = b j := by
  have : (fun i => h.bar ((Pi.single j (1 : K) : n → K) i)) = Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [hi]
  rw [hdot, this, single_dotProduct, one_mul]

end Hdot

theorem eq_zero_of_hdot_self (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {t : Fin ε → K}
    (ht : hdot h t t = 0) : t = 0 := by
  obtain rfl | rfl : ε = 0 ∨ ε = 1 := by omega
  · exact funext fun k => k.elim0
  · funext k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [hdot, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton] at ht
    rcases mul_eq_zero.mp ht with h0 | h0
    · exact (UnitaryFieldData.bar_eq_zero_iff h).mp h0
    · exact h0

theorem hypForm_split (h : UnitaryFieldData p f K) (a b a' b' : Fin r → K) (t t' : Fin ε → K) :
    hypForm h r ε (hypXEmb r ε a + hypZEmb r ε t + hypYEmb r ε b)
        (hypXEmb r ε a' + hypZEmb r ε t' + hypYEmb r ε b') =
      hdot h a b' + hdot h t t' + hdot h b a' := by
  rw [hypForm_eq_dotProduct]
  simp [hypXEmb, hypYEmb, hypZEmb]

theorem hypForm_xy (h : UnitaryFieldData p f K) (a b a' b' : Fin r → K) :
    hypForm h r ε (hypXEmb r ε a + hypYEmb r ε b) (hypXEmb r ε a' + hypYEmb r ε b') =
      hdot h a b' + hdot h b a' := by
  have := hypForm_split h a b a' b' (0 : Fin ε → K) 0
  rwa [map_zero, add_zero, add_zero, hdot_zero_right, add_zero] at this

theorem hypForm_xzy_xy (h : UnitaryFieldData p f K) (a b a' b' : Fin r → K) (t : Fin ε → K) :
    hypForm h r ε (hypXEmb r ε a + hypZEmb r ε t + hypYEmb r ε b)
        (hypXEmb r ε a' + hypYEmb r ε b') = hdot h a b' + hdot h b a' := by
  have := hypForm_split h a b a' b' t 0
  rwa [map_zero, add_zero, hdot_zero_right, add_zero] at this

theorem hypXEmb_add_hypYEmb_ne_zero {a : Fin r → K} (ha : a ≠ 0) (b : Fin r → K) :
    hypXEmb r ε a + hypYEmb r ε b ≠ 0 := by
  intro h0
  apply ha
  funext i
  have := congrFun h0 (Sum.inl i)
  simpa [hypXEmb, hypYEmb] using this

theorem hypForm_self_of_span (h : UnitaryFieldData p f K) (L : hypIsotropicLines h r ε)
    {w : HypIndex r ε → K} (hL : (L : Submodule K (HypIndex r ε → K)) = K ∙ w) :
    hypForm h r ε w w = 0 :=
  (mem_hypIsotropicLines.mp L.2).2 w (by rw [hL]; exact mem_span_singleton_self w)

section Rigid

variable (h : UnitaryFieldData p f K) {ψ : Equiv.Perm (hypIsotropicLines h r ε)}
  (hψ : ∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔ LineOrth h (ψ L) (ψ M))

include hψ in
theorem rigid_pair {L M : hypIsotropicLines h r ε} {v w v' w' : HypIndex r ε → K}
    (hL : (L : Submodule K (HypIndex r ε → K)) = K ∙ v)
    (hM : (M : Submodule K (HypIndex r ε → K)) = K ∙ w)
    (hL' : (ψ L : Submodule K (HypIndex r ε → K)) = K ∙ v')
    (hM' : (ψ M : Submodule K (HypIndex r ε → K)) = K ∙ w') :
    hypForm h r ε v w = 0 ↔ hypForm h r ε v' w' = 0 := by
  have h1 : SubOrtho (hypForm h r ε) (L : Submodule K (HypIndex r ε → K)) M ↔
      SubOrtho (hypForm h r ε) (ψ L : Submodule K (HypIndex r ε → K)) (ψ M) := hψ L M
  rw [hL, hM, hL', hM'] at h1
  unfold SubOrtho at h1
  rwa [orth_span_iff, orth_span_iff] at h1

include hψ in
theorem rigid_coeff {L M : hypIsotropicLines h r ε} {a b a₂ b₂ : Fin r → K} {s c' : K}
    {t : Fin ε → K}
    (hL : (L : Submodule K (HypIndex r ε → K)) = K ∙ (hypXEmb r ε a + hypYEmb r ε b))
    (hL' : (ψ L : Submodule K (HypIndex r ε → K)) =
      K ∙ (hypXEmb r ε a + hypZEmb r ε t + hypYEmb r ε (s • b)))
    (hM : (M : Submodule K (HypIndex r ε → K)) = K ∙ (hypXEmb r ε a₂ + hypYEmb r ε b₂))
    (hM' : (ψ M : Submodule K (HypIndex r ε → K)) =
      K ∙ (hypXEmb r ε a₂ + hypYEmb r ε (c' • b₂)))
    (hsum : hdot h a b₂ + hdot h b a₂ = 0) (hne : hdot h b a₂ ≠ 0) : h.bar s = c' := by
  have h1 := (rigid_pair h hψ hL hM hL' hM').mp (by rw [hypForm_xy, hsum])
  rw [hypForm_xzy_xy, hdot_smul_right, hdot_smul_left] at h1
  have h2 : (h.bar s - c') * hdot h b a₂ = 0 := by linear_combination h1 - c' * hsum
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hne)

variable (hX : ∀ L : hypIsotropicLines h r ε,
    (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε → ψ L = L)
  (hY : ∀ L : hypIsotropicLines h r ε,
    (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε → ψ L = L)

include hψ hX hY in
theorem rigid_shape (L : hypIsotropicLines h r ε) {a b : Fin r → K} (ha : a ≠ 0)
    (hL : (L : Submodule K (HypIndex r ε → K)) = K ∙ (hypXEmb r ε a + hypYEmb r ε b)) :
    ∃ (s : K) (t : Fin ε → K), (b ≠ 0 → s ≠ 0) ∧
      (ψ L : Submodule K (HypIndex r ε → K)) =
        K ∙ (hypXEmb r ε a + hypZEmb r ε t + hypYEmb r ε (s • b)) := by
  obtain ⟨v', hv'0, -, hψv'⟩ := exists_eq_span_of_mem_hypIsotropicLines h (ψ L).2
  set x' : Fin r → K := fun i => v' (Sum.inl i) with hx'def
  set t' : Fin ε → K := fun k => v' (Sum.inr (Sum.inl k)) with ht'def
  set y' : Fin r → K := fun i => v' (Sum.inr (Sum.inr i)) with hy'def
  have hv' : v' = hypXEmb r ε x' + hypZEmb r ε t' + hypYEmb r ε y' := hypSplit v'
  have hkeyY : ∀ u : Fin r → K, hdot h u b = 0 ↔ hdot h u y' = 0 := by
    intro u
    by_cases hu : u = 0
    · simp [hu, hdot_zero_left]
    have hx0 : hypXEmb r ε u ≠ 0 := fun h0 =>
      hu (hypXEmb_injective (h0.trans (map_zero _).symm))
    let P : hypIsotropicLines h r ε := ⟨K ∙ hypXEmb r ε u,
      span_mem_hypIsotropicLines h hx0 (hypX_isotropic h _ ⟨u, rfl⟩ _ ⟨u, rfl⟩)⟩
    have hPX : (P : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε :=
      (span_singleton_le_iff_mem _ _).mpr ⟨u, rfl⟩
    have hPP : (ψ P : Submodule K (HypIndex r ε → K)) = K ∙ hypXEmb r ε u := by
      rw [hX P hPX]
    have h1 := rigid_pair h hψ (L := P) (M := L) rfl hL hPP hψv'
    have e1 : hypForm h r ε (hypXEmb r ε u) (hypXEmb r ε a + hypYEmb r ε b) = hdot h u b := by
      rw [hypForm_hypXEmb]
      simp [hypXEmb, hypYEmb, dotProduct]
    have e2 : hypForm h r ε (hypXEmb r ε u) v' = hdot h u y' := by
      rw [hypForm_hypXEmb]
      rfl
    rwa [e1, e2] at h1
  have hkeyX : ∀ u : Fin r → K, hdot h u a = 0 ↔ hdot h u x' = 0 := by
    intro u
    by_cases hu : u = 0
    · simp [hu, hdot_zero_left]
    have hy0 : hypYEmb r ε u ≠ 0 := fun h0 =>
      hu (hypYEmb_injective (h0.trans (map_zero _).symm))
    let P : hypIsotropicLines h r ε := ⟨K ∙ hypYEmb r ε u,
      span_mem_hypIsotropicLines h hy0 (hypY_isotropic h _ ⟨u, rfl⟩ _ ⟨u, rfl⟩)⟩
    have hPY : (P : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε :=
      (span_singleton_le_iff_mem _ _).mpr ⟨u, rfl⟩
    have hPP : (ψ P : Submodule K (HypIndex r ε → K)) = K ∙ hypYEmb r ε u := by
      rw [hY P hPY]
    have h1 := rigid_pair h hψ (L := P) (M := L) rfl hL hPP hψv'
    have e1 : hypForm h r ε (hypYEmb r ε u) (hypXEmb r ε a + hypYEmb r ε b) = hdot h u a := by
      rw [hypForm_hypYEmb]
      simp [hypXEmb, hypYEmb, dotProduct]
    have e2 : hypForm h r ε (hypYEmb r ε u) v' = hdot h u x' := by
      rw [hypForm_hypYEmb]
      rfl
    rwa [e1, e2] at h1
  have hbar : ∀ {w w' : Fin r → K}, (∀ u, hdot h u w = 0 ↔ hdot h u w' = 0) →
      ∀ u : Fin r → K, u ⬝ᵥ w = 0 ↔ u ⬝ᵥ w' = 0 := fun hww u => by
    have := hww (fun i => h.bar (u i))
    simpa only [hdot, h.bar_bar] using this
  obtain ⟨α, hα, hx'⟩ := eq_smul_of_dotProduct_iff ha (hbar hkeyX)
  have hα' : IsUnit α⁻¹ := IsUnit.mk0 _ (inv_ne_zero hα)
  by_cases hb : b = 0
  · have hy' : y' = 0 := funext fun i => by
      have := (hbar hkeyY (Pi.single i 1)).mp (by rw [hb, dotProduct_zero])
      rwa [single_dotProduct, one_mul] at this
    refine ⟨0, α⁻¹ • t', fun h0 => absurd hb h0, ?_⟩
    rw [hψv', ← span_singleton_smul_eq hα' v', hv', hx', hy', hb]
    congr 1
    rw [smul_add, smul_add, ← map_smul, smul_smul, inv_mul_cancel₀ hα, one_smul, ← map_smul,
      map_zero, smul_zero, smul_zero, map_zero]
  · obtain ⟨β, hβ, hy'⟩ := eq_smul_of_dotProduct_iff hb (hbar hkeyY)
    refine ⟨α⁻¹ * β, α⁻¹ • t', fun _ => mul_ne_zero (inv_ne_zero hα) hβ, ?_⟩
    rw [hψv', ← span_singleton_smul_eq hα' v', hv', hx', hy']
    congr 1
    rw [smul_add, smul_add, ← map_smul, smul_smul, inv_mul_cancel₀ hα, one_smul, ← map_smul,
      ← map_smul, smul_smul]

end Rigid

section Diag

@[expose] def diagFun (c d : K) (v : HypIndex r ε → K) : HypIndex r ε → K :=
  Sum.elim (fun i => v (Sum.inl i))
    (Sum.elim (fun k => d * v (Sum.inr (Sum.inl k))) (fun i => c * v (Sum.inr (Sum.inr i))))

theorem diagFun_diagFun (c d c' d' : K) (v : HypIndex r ε → K) :
    diagFun c d (diagFun c' d' v) = diagFun (c * c') (d * d') v := by
  funext x
  rcases x with i | k | i <;> simp [diagFun, mul_assoc]

theorem diagFun_one (v : HypIndex r ε → K) : diagFun 1 1 v = v := by
  funext x
  rcases x with i | k | i <;> simp [diagFun]

@[expose] noncomputable def hypDiagEquiv {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) :
    (HypIndex r ε → K) ≃ₗ[K] (HypIndex r ε → K) where
  toFun := diagFun c d
  invFun := diagFun c⁻¹ d⁻¹
  map_add' v w := by
    funext x
    rcases x with i | k | i <;> simp [diagFun, mul_add]
  map_smul' t v := by
    funext x
    rcases x with i | k | i <;> simp [diagFun, mul_left_comm]
  left_inv v := by
    rw [diagFun_diagFun, inv_mul_cancel₀ hc, inv_mul_cancel₀ hd, diagFun_one]
  right_inv v := by
    rw [diagFun_diagFun, mul_inv_cancel₀ hc, mul_inv_cancel₀ hd, diagFun_one]

theorem hypDiagEquiv_apply {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) (v : HypIndex r ε → K) :
    hypDiagEquiv hc hd v = diagFun c d v :=
  rfl

theorem diagFun_xy (c d : K) (a b : Fin r → K) :
    diagFun (ε := ε) c d (hypXEmb r ε a + hypYEmb r ε b) = hypXEmb r ε a + hypYEmb r ε (c • b) := by
  funext x
  rcases x with i | k | i <;> simp [diagFun, hypXEmb, hypYEmb]

theorem hypDiag_similitude (h : UnitaryFieldData p f K) {c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (hcF : h.bar c = c) (hN : h.norm d = c) :
    (((glOfLinearEquiv (hypDiagEquiv (r := r) (ε := ε) hc hd) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      ((glOfLinearEquiv (hypDiagEquiv (r := r) (ε := ε) hc hd) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = c • hypGram r ε K := by
  refine gramForm_injective h fun u v => ?_
  rw [← gramForm_mulVec, glOfLinearEquiv_mulVec, glOfLinearEquiv_mulVec, gramForm_smul_gram,
    hypDiagEquiv_apply, hypDiagEquiv_apply]
  change hypForm h r ε (diagFun c d u) (diagFun c d v) = c * hypForm h r ε u v
  rw [hypForm_eq_dotProduct, hypForm_eq_dotProduct]
  have hd' : ∀ x y : K, h.bar d * h.bar x * (d * y) = c * (h.bar x * y) := fun x y => by
    rw [← hN, UnitaryFieldData.norm]
    ring
  simp only [diagFun, Sum.elim_inl, Sum.elim_inr, dotProduct, map_mul, hcF, Finset.mul_sum,
    mul_add]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun k _ => hd' _ _
  · exact Finset.sum_congr rfl fun i _ => by ring

end Diag


theorem exists_ne_ne (hr : 3 ≤ r) (i j : Fin r) : ∃ l : Fin r, l ≠ i ∧ l ≠ j := by
  have hcard : ({i, j} : Finset (Fin r)).card < (Finset.univ : Finset (Fin r)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  exact ⟨l, hl.1, hl.2⟩

section Points

variable (h : UnitaryFieldData p f K)

@[expose] def MapsSpan (ψ : Equiv.Perm (hypIsotropicLines h r ε)) (v w : HypIndex r ε → K) :
    Prop :=
  ∀ L : hypIsotropicLines h r ε, (L : Submodule K (HypIndex r ε → K)) = K ∙ v →
    (ψ L : Submodule K (HypIndex r ε → K)) = K ∙ w

theorem exists_pt {a b : Fin r → K} (ha : a ≠ 0) (hab : hdot h a b + hdot h b a = 0) :
    ∃ L : hypIsotropicLines h r ε,
      (L : Submodule K (HypIndex r ε → K)) = K ∙ (hypXEmb r ε a + hypYEmb r ε b) :=
  ⟨⟨_, span_mem_hypIsotropicLines h (hypXEmb_add_hypYEmb_ne_zero ha b)
    (by rw [hypForm_xy, hab])⟩, rfl⟩

theorem pt_iso (L : hypIsotropicLines h r ε) {a b : Fin r → K}
    (hL : (L : Submodule K (HypIndex r ε → K)) = K ∙ (hypXEmb r ε a + hypYEmb r ε b)) :
    hdot h a b + hdot h b a = 0 := by
  rw [← hypForm_xy]
  exact hypForm_self_of_span h L hL

theorem pt_mid (hε : ε ≤ 1) (L L' : hypIsotropicLines h r ε) {a b : Fin r → K} {s : K}
    {t : Fin ε → K}
    (hL : (L : Submodule K (HypIndex r ε → K)) = K ∙ (hypXEmb r ε a + hypYEmb r ε b))
    (hL' : (L' : Submodule K (HypIndex r ε → K)) =
      K ∙ (hypXEmb r ε a + hypZEmb r ε t + hypYEmb r ε (s • b)))
    (hs : hdot h a b = 0 ∨ h.bar s = s) : t = 0 := by
  have h1 := hypForm_self_of_span h L' hL'
  have h2 := pt_iso h L hL
  rw [hypForm_split, hdot_smul_right, hdot_smul_left] at h1
  refine eq_zero_of_hdot_self h hε ?_
  rcases hs with hs | hs
  · have hba : hdot h b a = 0 := by rw [hdot_comm h a b, hs, map_zero]
    rw [hs, hba, mul_zero, mul_zero, zero_add, add_zero] at h1
    exact h1
  · rw [hs] at h1
    linear_combination h1 - s * h2

theorem hdot_single_smul_single {i j : Fin r} (hij : i ≠ j) (α : K) :
    hdot h (Pi.single j (1 : K)) (α • Pi.single i 1) = 0 := by
  rw [hdot_smul_right, hdot_single_left, Pi.single_eq_of_ne (Ne.symm hij), mul_zero]

theorem single_ne_zero (j : Fin r) : (Pi.single j (1 : K) : Fin r → K) ≠ 0 := fun h0 => by
  simpa using congrFun h0 j

theorem pt_single_iso {i j : Fin r} (hij : i ≠ j) (α : K) :
    hdot h (Pi.single j (1 : K)) (α • Pi.single i 1) +
      hdot h (α • Pi.single i 1) (Pi.single j (1 : K)) = 0 := by
  rw [hdot_comm h (Pi.single j (1 : K)), hdot_single_smul_single h hij, map_zero, add_zero]

theorem pt_x_iso {i : Fin r} {x : Fin r → K} (hxi : x i = 0) (b : K) :
    hdot h x (b • Pi.single i 1) + hdot h (b • Pi.single i 1) x = 0 := by
  have h0 : hdot h x (b • Pi.single i 1) = 0 := by
    rw [hdot_smul_right, hdot_single_right, hxi, map_zero, mul_zero]
  rw [hdot_comm h x, h0, map_zero, add_zero]

end Points

section Coefficients

variable (h : UnitaryFieldData p f K) {ψ : Equiv.Perm (hypIsotropicLines h r ε)}
  (hψ : ∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔ LineOrth h (ψ L) (ψ M))
  (hX : ∀ L : hypIsotropicLines h r ε,
    (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε → ψ L = L)
  (hY : ∀ L : hypIsotropicLines h r ε,
    (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε → ψ L = L)

include hψ hX hY in
theorem exists_mapsSpan_of_hdot (hε : ε ≤ 1) {a b : Fin r → K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : hdot h a b = 0) : ∃ s : K, s ≠ 0 ∧
      MapsSpan h ψ (hypXEmb r ε a + hypYEmb r ε b) (hypXEmb r ε a + hypYEmb r ε (s • b)) := by
  have hab' : hdot h a b + hdot h b a = 0 := by rw [hdot_comm h a b, hab, map_zero, add_zero]
  obtain ⟨L₀, hL₀⟩ := exists_pt h ha hab'
  obtain ⟨s, t, hs, hL₀'⟩ := rigid_shape h hψ hX hY L₀ ha hL₀
  have ht := pt_mid h hε L₀ (ψ L₀) hL₀ hL₀' (Or.inl hab)
  refine ⟨s, hs hb, fun L hL => ?_⟩
  have hLL : L = L₀ := Subtype.ext (hL.trans hL₀.symm)
  rw [hLL, hL₀', ht, map_zero, add_zero]

variable (S : Fin r → Fin r → K → K)
  (hS : ∀ i j α, i ≠ j → α ≠ 0 → S i j α ≠ 0 ∧
    MapsSpan h ψ (hypXEmb r ε (Pi.single j 1) + hypYEmb r ε (α • Pi.single i 1))
      (hypXEmb r ε (Pi.single j 1) + hypYEmb r ε (S i j α • α • Pi.single i 1)))

include hψ hS in
theorem rigid_rel (i : Fin r) (x : Fin r → K) (b s : K) (hxi : x i = 0) (hx0 : x ≠ 0)
    (hb : b ≠ 0)
    (hs : MapsSpan h ψ (hypXEmb r ε x + hypYEmb r ε (b • Pi.single i 1))
      (hypXEmb r ε x + hypYEmb r ε (s • b • Pi.single i 1)))
    (j : Fin r) (hji : j ≠ i) (hxj : x j ≠ 0) :
    h.bar s = S j i (-h.bar b / h.bar (x j)) := by
  obtain ⟨L, hL⟩ := exists_pt h hx0 (pt_x_iso h hxi b)
  set a' := -h.bar b / h.bar (x j) with ha'
  have hbxj : h.bar (x j) ≠ 0 := (map_ne_zero h.bar).mpr hxj
  have ha'0 : a' ≠ 0 := div_ne_zero (neg_ne_zero.mpr ((map_ne_zero h.bar).mpr hb)) hbxj
  obtain ⟨M, hM⟩ := exists_pt h (single_ne_zero i) (pt_single_iso h hji a')
  have hM' := (hS j i a' hji ha'0).2 M hM
  have hL'' : (ψ L : Submodule K (HypIndex r ε → K)) =
      K ∙ (hypXEmb r ε x + hypZEmb r ε 0 + hypYEmb r ε (s • (b • Pi.single i 1))) := by
    rw [hs L hL, map_zero, add_zero]
  refine rigid_coeff h hψ hL hL'' hM hM' ?_ ?_
  · rw [hdot_smul_right, hdot_single_right, hdot_smul_left, hdot_single_left,
      Pi.single_eq_same, mul_one, ha', div_mul_cancel₀ _ hbxj, neg_add_cancel]
  · rw [hdot_smul_left, hdot_single_left, Pi.single_eq_same, mul_one]
    exact (map_ne_zero h.bar).mpr hb

include hψ hX hY hS in
theorem rigid_const₀ (hε : ε ≤ 1) (i j k : Fin r) (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≠ k)
    (A B : K) (hA : A ≠ 0) (hB : B ≠ 0) : S j i A = S k i B := by
  set lam : K := h.bar (A / B) with hlam
  set b : K := -h.bar A with hb
  have hb0 : b ≠ 0 := neg_ne_zero.mpr ((map_ne_zero h.bar).mpr hA)
  have hlam0 : lam ≠ 0 := (map_ne_zero h.bar).mpr (div_ne_zero hA hB)
  set x : Fin r → K := Pi.single j 1 + lam • Pi.single k 1 with hx
  have hxi : x i = 0 := by
    rw [hx, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hji),
      Pi.single_eq_of_ne (Ne.symm hki), smul_zero, add_zero]
  have hxj : x j = 1 := by
    rw [hx, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjk, smul_zero,
      add_zero]
  have hxk : x k = lam := by
    rw [hx, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hjk),
      smul_eq_mul, mul_one, zero_add]
  have hx0 : x ≠ 0 := fun h0 => by
    have := congrFun h0 j
    rw [hxj] at this
    exact one_ne_zero this
  have hxb : hdot h x (b • Pi.single i 1) = 0 := by
    rw [hdot_smul_right, hdot_single_right, hxi, map_zero, mul_zero]
  have hbi : b • Pi.single i (1 : K) ≠ 0 := fun h0 => by
    have := congrFun h0 i
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at this
    exact hb0 this
  obtain ⟨s, -, hs⟩ := exists_mapsSpan_of_hdot h hψ hX hY hε hx0 hbi hxb
  have hs' : MapsSpan h ψ (hypXEmb r ε x + hypYEmb r ε (b • Pi.single i 1))
      (hypXEmb r ε x + hypYEmb r ε (s • b • Pi.single i 1)) := hs
  have h1 := rigid_rel h hψ S hS i x b s hxi hx0 hb0 hs' j hji (by rw [hxj]; exact one_ne_zero)
  have h2 := rigid_rel h hψ S hS i x b s hxi hx0 hb0 hs' k hki (by rw [hxk]; exact hlam0)
  rw [hxj, map_one, div_one, hb, map_neg, neg_neg, h.bar_bar] at h1
  rw [hxk, hlam, h.bar_bar, hb, map_neg, neg_neg, h.bar_bar, div_div_cancel₀ hA] at h2
  rw [← h1, h2]

include hψ hX hY hS in
theorem rigid_const (hr : 3 ≤ r) (hε : ε ≤ 1) (i j k : Fin r) (hji : j ≠ i) (hki : k ≠ i)
    (A B : K) (hA : A ≠ 0) (hB : B ≠ 0) : S j i A = S k i B := by
  by_cases hjk : j = k
  · subst hjk
    obtain ⟨l, hli, hlj⟩ := exists_ne_ne hr i j
    rw [rigid_const₀ h hψ hX hY S hS hε i j l hji hli (Ne.symm hlj) A 1 hA one_ne_zero,
      rigid_const₀ h hψ hX hY S hS hε i l j hli hji hlj 1 B one_ne_zero hB]
  · exact rigid_const₀ h hψ hX hY S hS hε i j k hji hki hjk A B hA hB

include hψ hS in
theorem rigid_swap (i j : Fin r) (hij : i ≠ j) (b : K) (hb : b ≠ 0) :
    h.bar (S i j b) = S j i (-h.bar b) := by
  have hxi : (Pi.single j (1 : K) : Fin r → K) i = 0 := Pi.single_eq_of_ne hij _
  have := rigid_rel h hψ S hS i (Pi.single j 1) b (S i j b) hxi (single_ne_zero j) hb
    (hS i j b hij hb).2 j (Ne.symm hij) (by rw [Pi.single_eq_same]; exact one_ne_zero)
  rwa [Pi.single_eq_same, map_one, div_one] at this

include hψ hX hY hS in
theorem rigid_all (hr : 3 ≤ r) (hε : ε ≤ 1) (i j i' j' : Fin r) (hij : i ≠ j) (hij' : i' ≠ j')
    (α α' : K) (hα : α ≠ 0) (hα' : α' ≠ 0) : S i' j' α' = S i j α := by
  have hQ : ∀ i j i' j' : Fin r, i ≠ j → i' ≠ j' → j ≠ j' → ∀ α α' : K, α ≠ 0 → α' ≠ 0 →
      S i' j' α' = h.bar (S i j α) := by
    intro i j i' j' hij hij' hjj' α α' hα hα'
    have h1 := rigid_swap h hψ S hS j' j (Ne.symm hjj') 1 one_ne_zero
    have hn : -h.bar (1 : K) ≠ 0 := by rw [map_one]; exact neg_ne_zero.mpr one_ne_zero
    rw [rigid_const h hψ hX hY S hS hr hε j' i' j hij' hjj' α' (-h.bar 1) hα' hn, ← h1,
      rigid_const h hψ hX hY S hS hr hε j j' i (Ne.symm hjj') hij 1 α one_ne_zero hα]
  by_cases hjj' : j = j'
  · subst hjj'
    exact rigid_const h hψ hX hY S hS hr hε j i' i hij' hij α' α hα' hα
  · obtain ⟨j'', hj''j, hj''j'⟩ := exists_ne_ne hr j j'
    rw [hQ j j'' i' j' (Ne.symm hj''j) hij' hj''j' 1 α' one_ne_zero hα',
      hQ i j j j'' hij (Ne.symm hj''j) (Ne.symm hj''j) α 1 hα one_ne_zero, h.bar_bar]

variable {c : K} (hcF : h.bar c = c)
  (hSc : ∀ i j : Fin r, i ≠ j → ∀ α : K, α ≠ 0 → S i j α = c)

include hψ hX hY hS hcF hSc in
theorem rigid_mix (hε : ε ≤ 1) (L : hypIsotropicLines h r ε) {a b : Fin r → K} (i j : Fin r)
    (hij : i ≠ j) (hai : a i ≠ 0) (hbj : b j ≠ 0)
    (hL : (L : Submodule K (HypIndex r ε → K)) = K ∙ (hypXEmb r ε a + hypYEmb r ε b)) :
    (ψ L : Submodule K (HypIndex r ε → K)) = K ∙ (hypXEmb r ε a + hypYEmb r ε (c • b)) := by
  have ha : a ≠ 0 := fun h0 => hai (by rw [h0, Pi.zero_apply])
  obtain ⟨s, t, -, hL'⟩ := rigid_shape h hψ hX hY L ha hL
  set α := -h.bar (b j) / h.bar (a i) with hα
  have hbai : h.bar (a i) ≠ 0 := (map_ne_zero h.bar).mpr hai
  have hα0 : α ≠ 0 := div_ne_zero (neg_ne_zero.mpr ((map_ne_zero h.bar).mpr hbj)) hbai
  obtain ⟨M, hM⟩ := exists_pt h (single_ne_zero j) (pt_single_iso h hij α)
  have hM' := (hS i j α hij hα0).2 M hM
  rw [hSc i j hij α hα0] at hM'
  have hs : h.bar s = c := by
    refine rigid_coeff h hψ hL hL' hM hM' ?_ ?_
    · rw [hdot_smul_right, hdot_single_right, hdot_single_right, hα, div_mul_cancel₀ _ hbai,
        neg_add_cancel]
    · rw [hdot_single_right]
      exact (map_ne_zero h.bar).mpr hbj
  have hs' : s = c := by rw [← h.bar_bar s, hs, hcF]
  rw [hs'] at hL'
  have ht := pt_mid h hε L (ψ L) hL hL' (Or.inr hcF)
  rw [hL', ht, map_zero, add_zero]

include hψ hX hY hS hcF hSc in
theorem rigid_gen (hr : 2 ≤ r) (hε : ε ≤ 1) (L : hypIsotropicLines h r ε) {a b : Fin r → K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hL : (L : Submodule K (HypIndex r ε → K)) = K ∙ (hypXEmb r ε a + hypYEmb r ε b)) :
    (ψ L : Submodule K (HypIndex r ε → K)) = K ∙ (hypXEmb r ε a + hypYEmb r ε (c • b)) := by
  classical
  by_cases hm : ∃ i j : Fin r, i ≠ j ∧ a i ≠ 0 ∧ b j ≠ 0
  · obtain ⟨i, j, hij, hai, hbj⟩ := hm
    exact rigid_mix h hψ hX hY S hS hcF hSc hε L i j hij hai hbj hL
  push Not at hm
  obtain ⟨i, hai⟩ := Function.ne_iff.mp ha
  obtain ⟨j₁, hbj₁⟩ := Function.ne_iff.mp hb
  have hij₁ : i = j₁ := by
    by_contra hne
    exact hbj₁ (hm i j₁ hne hai)
  subst hij₁
  have hak : ∀ k, k ≠ i → a k = 0 := fun k hk => by
    by_contra hak
    exact hbj₁ (hm k i hk hak)
  have hbk : ∀ k, k ≠ i → b k = 0 := fun k hk => hm i k (Ne.symm hk) hai
  have hae : a = a i • Pi.single i 1 := funext fun k => by
    by_cases hk : k = i
    · subst hk
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero, hak k hk]
  have hbe : b = b i • Pi.single i 1 := funext fun k => by
    by_cases hk : k = i
    · subst hk
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero, hbk k hk]
  obtain ⟨s, t, -, hL'⟩ := rigid_shape h hψ hX hY L ha hL
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  obtain ⟨j, hji⟩ := exists_ne i
  set u := -h.bar (b i) / h.bar (a i) with hu
  have hbai : h.bar (a i) ≠ 0 := (map_ne_zero h.bar).mpr hai
  have hu0 : u ≠ 0 := div_ne_zero (neg_ne_zero.mpr ((map_ne_zero h.bar).mpr hbj₁)) hbai
  set aw : Fin r → K := Pi.single i 1 + Pi.single j 1 with haw
  set bw : Fin r → K := u • (Pi.single i 1 - Pi.single j 1) with hbw
  have hawi : aw i = 1 := by
    rw [haw, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hji), add_zero]
  have hawj : aw j = 1 := by
    rw [haw, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hji, zero_add]
  have hbwi : bw i = u := by
    rw [hbw, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hji),
      sub_zero, smul_eq_mul, mul_one]
  have hbwj : bw j = -u := by
    rw [hbw, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hji, zero_sub,
      smul_eq_mul, mul_neg, mul_one]
  have hdw : hdot h aw bw = 0 := by
    rw [haw, hdot_add_left, hdot_single_left, hdot_single_left, hbwi, hbwj, add_neg_cancel]
  have haw0 : aw ≠ 0 := fun h0 => by
    have := congrFun h0 i
    rw [hawi] at this
    exact one_ne_zero this
  obtain ⟨M, hM⟩ := exists_pt (b := bw) h haw0 (by
    rw [hdot_comm h aw bw, hdw, map_zero, add_zero])
  have hM' := rigid_mix h hψ hX hY S hS hcF hSc hε M i j (Ne.symm hji)
    (by rw [hawi]; exact one_ne_zero) (by rw [hbwj]; exact neg_ne_zero.mpr hu0) hM
  have hs : h.bar s = c := by
    refine rigid_coeff h hψ hL hL' hM hM' ?_ ?_
    · rw [hae, hbe, hdot_smul_left, hdot_single_left, hdot_smul_left, hdot_single_left, hbwi,
        hawi, mul_one, hu]
      field_simp
      ring
    · rw [hbe, hdot_smul_left, hdot_single_left, hawi, mul_one]
      exact (map_ne_zero h.bar).mpr hbj₁
  have hs' : s = c := by rw [← h.bar_bar s, hs, hcF]
  rw [hs'] at hL'
  have ht := pt_mid h hε L (ψ L) hL hL' (Or.inr hcF)
  rw [hL', ht, map_zero, add_zero]

end Coefficients

theorem unitary_hyperbolic_point_rigidity (h : UnitaryFieldData p f K) (hr : 3 ≤ r)
    (hε : ε ≤ 1) (φ : Equiv.Perm (hypIsotropicLines h r ε))
    (hφ : ∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔ LineOrth h (φ L) (φ M))
    (hX : ∀ L : hypIsotropicLines h r ε,
      (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε → φ L = L)
    (hY : ∀ L : hypIsotropicLines h r ε,
      (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε → φ L = L) :
    ∃ (c d : K) (hc : c ≠ 0) (hd : d ≠ 0), h.bar c = c ∧ h.norm d = c ∧
      ∃ hD : (⟨glOfLinearEquiv (hypDiagEquiv (r := r) (ε := ε) hc hd), 1⟩ :
          SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε,
        ∀ L : hypIsotropicLines h r ε,
          (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε ⊔ hypY K r ε →
          φ L = semilinearPointAction h r ε ⟨_, hD⟩ L := by
  have hSex : ∀ (i j : Fin r) (α : K), ∃ s : K, i ≠ j → α ≠ 0 → s ≠ 0 ∧
      MapsSpan h φ (hypXEmb r ε (Pi.single j 1) + hypYEmb r ε (α • Pi.single i 1))
        (hypXEmb r ε (Pi.single j 1) + hypYEmb r ε (s • α • Pi.single i 1)) := by
    intro i j α
    by_cases hij : i = j
    · exact ⟨0, fun h0 => absurd hij h0⟩
    by_cases hα : α = 0
    · exact ⟨0, fun _ h0 => absurd hα h0⟩
    have hαi : α • Pi.single i (1 : K) ≠ 0 := fun h0 => by
      have := congrFun h0 i
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at this
      exact hα this
    obtain ⟨s, hs, hmaps⟩ := exists_mapsSpan_of_hdot h hφ hX hY hε (single_ne_zero j) hαi
      (hdot_single_smul_single h hij α)
    exact ⟨s, fun _ _ => ⟨hs, hmaps⟩⟩
  choose S hS using hSex
  have hS' : ∀ i j α, i ≠ j → α ≠ 0 → S i j α ≠ 0 ∧
      MapsSpan h φ (hypXEmb r ε (Pi.single j 1) + hypYEmb r ε (α • Pi.single i 1))
        (hypXEmb r ε (Pi.single j 1) + hypYEmb r ε (S i j α • α • Pi.single i 1)) := hS
  set i₀ : Fin r := ⟨0, by omega⟩ with hi₀
  set j₀ : Fin r := ⟨1, by omega⟩ with hj₀
  have hi₀j₀ : i₀ ≠ j₀ := fun h0 => absurd (congrArg Fin.val h0) (by simp [hi₀, hj₀])
  set c := S i₀ j₀ 1 with hcdef
  have hc0 : c ≠ 0 := (hS' i₀ j₀ 1 hi₀j₀ one_ne_zero).1
  have hSc : ∀ i j : Fin r, i ≠ j → ∀ α : K, α ≠ 0 → S i j α = c := fun i j hij α hα =>
    rigid_all h hφ hX hY S hS' hr hε i₀ j₀ i j hi₀j₀ hij 1 α one_ne_zero hα
  have hcF : h.bar c = c := by
    have h1 := rigid_swap h hφ S hS' i₀ j₀ hi₀j₀ 1 one_ne_zero
    rw [hSc j₀ i₀ (Ne.symm hi₀j₀) _ (by rw [map_one]; exact neg_ne_zero.mpr one_ne_zero)] at h1
    exact h1
  obtain ⟨d, hd⟩ := h.normHom_surjective ⟨c, (UnitaryFieldData.mem_fixedField h).mpr hcF⟩
  have hN : h.norm d = c := by
    have := congrArg Subtype.val hd
    rwa [UnitaryFieldData.coe_normHom] at this
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hN
    exact hc0 hN.symm
  have hDmem : (⟨glOfLinearEquiv (hypDiagEquiv (r := r) (ε := ε) hc0 hd0), 1⟩ :
      SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε :=
    ⟨c, hc0, hcF, hypDiag_similitude h hc0 hd0 hcF hN⟩
  refine ⟨c, d, hc0, hd0, hcF, hN, hDmem, fun L hL => ?_⟩
  obtain ⟨v, -, -, hLv⟩ := exists_eq_span_of_mem_hypIsotropicLines h L.2
  have hvH : v ∈ hypX K r ε ⊔ hypY K r ε := hL (by rw [hLv]; exact mem_span_singleton_self v)
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hvH
  rw [← hab] at hLv
  have hDL : (semilinearPointAction h r ε ⟨_, hDmem⟩ L : Submodule K (HypIndex r ε → K)) =
      K ∙ (hypXEmb r ε a + hypYEmb r ε (c • b)) := by
    change (⟨glOfLinearEquiv (hypDiagEquiv (r := r) (ε := ε) hc0 hd0), 1⟩ :
      SemiGL (HypIndex r ε) K) • (L : Submodule K (HypIndex r ε → K)) = _
    rw [hLv, semiGL_smul_eq_map, Submodule.map_span, Set.image_singleton, semiLin_apply]
    congr 2
    change ((glOfLinearEquiv (hypDiagEquiv (r := r) (ε := ε) hc0 hd0) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (hypXEmb r ε a + hypYEmb r ε b) = _
    rw [glOfLinearEquiv_mulVec, hypDiagEquiv_apply, diagFun_xy]
  apply Subtype.ext
  rw [hDL]
  by_cases ha : a = 0
  · have hLY : (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε := by
      rw [hLv, ha, map_zero, zero_add, span_singleton_le_iff_mem]
      exact ⟨b, rfl⟩
    rw [hY L hLY, hLv, ha, map_zero, zero_add, zero_add, map_smul,
      span_singleton_smul_eq (IsUnit.mk0 _ hc0)]
  by_cases hb : b = 0
  · have hLX : (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε := by
      rw [hLv, hb, map_zero, add_zero, span_singleton_le_iff_mem]
      exact ⟨a, rfl⟩
    rw [hX L hLX, hLv, hb, smul_zero]
  exact rigid_gen h hφ hX hY S hS' hcF hSc (by omega) hε L ha hb hLv

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
