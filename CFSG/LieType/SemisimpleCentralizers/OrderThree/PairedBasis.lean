module

public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Adjoint
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type*} [Field K]

theorem gramForm_mulVec_self_eq_zero (h : UnitaryFieldData p f K) {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) K} (hM' : (M.map h.bar)ᵀ = M') (hzero : M' * M = 0)
    (x y : Fin d → K) : gramForm h 1 (M *ᵥ x) (M *ᵥ y) = 0 := by
  rw [gramForm_mulVec, hM', Matrix.mul_one, hzero]
  simp [gramForm_apply]

theorem gramForm_sum_smul (h : UnitaryFieldData p f K) {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → K) (b : ι → Fin d → K) (w : Fin d → K) :
    gramForm h 1 (∑ i, c i • b i) w = ∑ i, h.bar (c i) * gramForm h 1 (b i) w := by
  rw [map_sum, LinearMap.sum_apply Finset.univ (fun i => (gramForm h 1) (c i • b i)) w]
  exact Finset.sum_congr rfl fun i _ => by
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

theorem gramForm_eq_zero_of_forall_basis (h : UnitaryFieldData p f K) {d : ℕ}
    {M : Matrix (Fin d) (Fin d) K} {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K (LinearMap.range (Matrix.toLin' M))) {w : Fin d → K}
    (hb : ∀ i, gramForm h 1 (b i : Fin d → K) w = 0) :
    ∀ v : LinearMap.range (Matrix.toLin' M), gramForm h 1 (v : Fin d → K) w = 0 := by
  intro v
  have hsum : ∑ i, (b.repr v i) • (b i : Fin d → K) = (v : Fin d → K) := by
    have h := congrArg Subtype.val (b.sum_repr v)
    rw [Submodule.coe_sum] at h
    simpa using h
  rw [← hsum, gramForm_sum_smul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hb i, mul_zero]

theorem eq_zero_of_mem_range_adjoint_of_orthogonal (h : UnitaryFieldData p f K) {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) K} (hM : M * M = M) (hMM' : M * M' = 0)
    (hM'M : M' * M = 0) (hM' : (M.map h.bar)ᵀ = M')
    {w : Fin d → K} (hw : w ∈ LinearMap.range (Matrix.toLin' M'))
    (horth : ∀ v : LinearMap.range (Matrix.toLin' M), gramForm h 1 (v : Fin d → K) w = 0) :
    w = 0 := by
  have hsymm : (gramForm h 1).IsSymm :=
    gramForm_isSymm h (G := (1 : Matrix (Fin d) (Fin d) K))
      (by rw [Matrix.map_one h.bar (map_zero h.bar) (map_one h.bar), Matrix.transpose_one])
  have hsep : (gramForm h 1).SeparatingLeft :=
    gramForm_separatingLeft h (G := (1 : Matrix (Fin d) (Fin d) K)) (by simp)
  refine hsep w fun u => ?_
  obtain ⟨y, hy⟩ := hw
  have h1 : gramForm h 1 w (M *ᵥ u) = 0 := by
    rw [← hsymm.eq (M *ᵥ u) w, horth ⟨M *ᵥ u, ⟨u, rfl⟩⟩, map_zero]
  have h2 : gramForm h 1 w (M' *ᵥ u) = 0 := by
    rw [← hy]
    exact gramForm_mulVec_self_eq_zero h ((map_transpose_eq_iff h).1 hM') hMM' y u
  have h3 : gramForm h 1 w (u - M *ᵥ u - M' *ᵥ u) = 0 := by
    rw [← hy, Matrix.toLin'_apply, gramForm_one_mulVec_left h M' y,
      (map_transpose_eq_iff h).1 hM']
    have hz : M *ᵥ (u - M *ᵥ u - M' *ᵥ u) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        hM, hMM', Matrix.zero_mulVec]
      abel
    rw [hz, map_zero]
  have hdecomp : u = M *ᵥ u + M' *ᵥ u + (u - M *ᵥ u - M' *ᵥ u) := by abel
  rw [hdecomp, map_add, map_add, h1, h2, h3, add_zero, add_zero]

theorem conjTranspose_mul_apply (h : UnitaryFieldData p f K) {d n : ℕ}
    (M N : Matrix (Fin d) (Fin n) K) (i j : Fin n) :
    ((M.map h.bar)ᵀ * N) i j = gramForm h 1 (M.col i) (N.col j) := by
  rw [gramForm_apply, Matrix.one_mulVec]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    dotProduct]

theorem conjTranspose_mulVec_apply (h : UnitaryFieldData p f K) {d n : ℕ}
    (M : Matrix (Fin d) (Fin n) K) (v : Fin d → K) (i : Fin n) :
    ((M.map h.bar)ᵀ *ᵥ v) i = gramForm h 1 (M.col i) v := by
  rw [gramForm_apply, Matrix.one_mulVec]
  simp only [Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    dotProduct]

theorem exists_paired_cols {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {d : ℕ}
    {P P' : Matrix (Fin d) (Fin d) K} (hP : P * P = P) (hPP' : P * P' = 0) (hP'P : P' * P = 0)
    (hPa : (P.map h.bar)ᵀ = P') :
    ∃ (a : ℕ) (E F : Matrix (Fin d) (Fin a) K), (E.map h.bar)ᵀ * E = 0 ∧ (F.map h.bar)ᵀ * F = 0 ∧
      (E.map h.bar)ᵀ * F = 1 ∧ E * (F.map h.bar)ᵀ = P := by
  classical
  have hP' : P' * P' = P' := by
    rw [← hPa, ← Matrix.transpose_mul, ← Matrix.map_mul, hP]
  have hP'a : (P'.map h.bar)ᵀ = P := (map_transpose_eq_iff h).1 hPa
  let W : Submodule K (Fin d → K) := LinearMap.range (Matrix.toLin' P)
  let W' : Submodule K (Fin d → K) := LinearMap.range (Matrix.toLin' P')
  have hisoW : ∀ u v : W, gramForm h 1 (u : Fin d → K) (v : Fin d → K) = 0 := by
    intro u v
    obtain ⟨x, hx⟩ := u.2
    obtain ⟨y, hy⟩ := v.2
    rw [← hx, ← hy]
    exact gramForm_mulVec_self_eq_zero h hPa hP'P x y
  have hisoW' : ∀ u v : W', gramForm h 1 (u : Fin d → K) (v : Fin d → K) = 0 := by
    intro u v
    obtain ⟨x, hx⟩ := u.2
    obtain ⟨y, hy⟩ := v.2
    rw [← hx, ← hy]
    exact gramForm_mulVec_self_eq_zero h hP'a hPP' x y
  set a : ℕ := Module.finrank K W with ha
  set b : Module.Basis (Fin a) K W := Module.finBasis K W with hb
  set Λ : W' →ₗ[K] (Fin a → K) :=
    LinearMap.pi fun i => (gramForm h 1 (b i : Fin d → K)).comp W'.subtype with hΛdef
  have hΛ : ∀ (w : W') i, Λ w i = gramForm h 1 (b i : Fin d → K) (w : Fin d → K) :=
    fun _ _ => rfl
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (eq_zero_of_mem_range_adjoint_of_orthogonal (M := P) (M' := P')
      h hP hPP' hP'P hPa w.2
      (gramForm_eq_zero_of_forall_basis (M := P) h b fun i => by
        rw [← hΛ w i]
        exact congrFun hw i))
  have hdim_le : Module.finrank K W' ≤ a := by
    simpa only [Module.finrank_fin_fun] using
      (LinearMap.finrank_le_finrank_of_injective (f := Λ) hinj)
  set b' : Module.Basis (Fin (Module.finrank K W')) K W' := Module.finBasis K W' with hb'
  set Λ' : W →ₗ[K] (Fin (Module.finrank K W') → K) :=
    LinearMap.pi fun i => (gramForm h 1 (b' i : Fin d → K)).comp W.subtype with hΛ'def
  have hΛ' : ∀ (v : W) i, Λ' v i = gramForm h 1 (b' i : Fin d → K) (v : Fin d → K) :=
    fun _ _ => rfl
  have hinj' : Function.Injective Λ' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext (eq_zero_of_mem_range_adjoint_of_orthogonal (M := P') (M' := P)
      h hP' hP'P hPP' hP'a v.2
      (gramForm_eq_zero_of_forall_basis (M := P') h b' fun i => by
        rw [← hΛ' v i]
        exact congrFun hv i))
  have hdim_ge : a ≤ Module.finrank K W' := by
    have h := LinearMap.finrank_le_finrank_of_injective (f := Λ') hinj'
    rw [Module.finrank_fin_fun] at h
    simpa only [ha] using h
  have hdim : a = Module.finrank K W' := le_antisymm hdim_ge hdim_le
  have hsurj : Function.Surjective Λ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun, hdim])).mp hinj
  choose g hg using fun j : Fin a => hsurj (Pi.single j 1)
  set E : Matrix (Fin d) (Fin a) K := Matrix.of fun i j => (b j : Fin d → K) i with hE
  set F : Matrix (Fin d) (Fin a) K := Matrix.of fun i j => (g j : Fin d → K) i with hF
  have hEcol : ∀ i, E.col i = (b i : Fin d → K) := by
    intro i
    rw [hE]
    funext k
    rfl
  have hFcol : ∀ i, F.col i = (g i : Fin d → K) := by
    intro i
    rw [hF]
    funext k
    rfl
  have hEE : (E.map h.bar)ᵀ * E = 0 := by
    ext i j
    rw [conjTranspose_mul_apply h E E i j, hEcol i, hEcol j]
    exact hisoW (b i) (b j)
  have hFF : (F.map h.bar)ᵀ * F = 0 := by
    ext i j
    rw [conjTranspose_mul_apply h F F i j, hFcol i, hFcol j]
    exact hisoW' (g i) (g j)
  have hEF : (E.map h.bar)ᵀ * F = 1 := by
    ext i j
    rw [conjTranspose_mul_apply h E F i j, hEcol i, hFcol j, ← hΛ (g j) i, hg j,
      Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Pi.single_eq_of_ne' (Ne.symm hij), if_neg hij]
  have hFstarE : (F.map h.bar)ᵀ * E = 1 := by
    have h1 := congrArg (fun M : Matrix (Fin a) (Fin a) K => M.map h.bar) hEF
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)] at h1
    have h2 : ((E.map h.bar)ᵀ).map h.bar = Eᵀ := by
      rw [Matrix.transpose_map, Matrix.map_map,
        show h.bar ∘ h.bar = id from funext (h.bar_bar), Matrix.map_id]
    rw [h2] at h1
    have h3 := congrArg Matrix.transpose h1
    simpa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using h3
  have hFstarP : (F.map h.bar)ᵀ * P = (F.map h.bar)ᵀ := by
    have hlin : Matrix.toLin' ((F.map h.bar)ᵀ * P) = Matrix.toLin' ((F.map h.bar)ᵀ) := by
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      have hz : (F.map h.bar)ᵀ *ᵥ (v - P *ᵥ v) = 0 := by
        have h1 : (F.map h.bar)ᵀ *ᵥ (P' *ᵥ v) = 0 := by
          ext i
          rw [Pi.zero_apply, conjTranspose_mulVec_apply h F (P' *ᵥ v) i, hFcol i]
          exact hisoW' (g i) ⟨P' *ᵥ v, ⟨v, rfl⟩⟩
        have h2 : (F.map h.bar)ᵀ *ᵥ (v - P *ᵥ v - P' *ᵥ v) = 0 := by
          ext i
          rw [Pi.zero_apply, conjTranspose_mulVec_apply h F (v - P *ᵥ v - P' *ᵥ v) i,
            hFcol i]
          obtain ⟨y, hy⟩ := (g i).2
          rw [← hy, Matrix.toLin'_apply, gramForm_one_mulVec_left h P' y, hP'a]
          have hz' : P *ᵥ (v - P *ᵥ v - P' *ᵥ v) = 0 := by
            rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
              Matrix.mulVec_mulVec, hP, hPP', Matrix.zero_mulVec]
            abel
          rw [hz', map_zero]
        have hsplit : v - P *ᵥ v = P' *ᵥ v + (v - P *ᵥ v - P' *ᵥ v) := by abel
        rw [hsplit, Matrix.mulVec_add, h1, h2, add_zero]
      have hz' : (F.map h.bar)ᵀ *ᵥ (P *ᵥ v - v) = 0 := by
        have hneg : P *ᵥ v - v = -(v - P *ᵥ v) := by abel
        rw [hneg, mulVec_neg, hz, neg_zero]
      rw [Matrix.mulVec_sub] at hz'
      exact sub_eq_zero.mp hz'
    exact Matrix.toLin'.injective hlin
  have hEFP : E * (F.map h.bar)ᵀ = P := by
    have hlin : Matrix.toLin' (E * (F.map h.bar)ᵀ) = Matrix.toLin' P := by
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      have hFP : (F.map h.bar)ᵀ *ᵥ (P *ᵥ v) = (F.map h.bar)ᵀ *ᵥ v := by
        rw [Matrix.mulVec_mulVec, hFstarP]
      rw [← hFP]
      have hmem : P *ᵥ v ∈ W := ⟨v, rfl⟩
      have hEc : E *ᵥ (fun i => b.repr ⟨P *ᵥ v, hmem⟩ i) = P *ᵥ v := by
        have hsum : ∑ i, (b.repr ⟨P *ᵥ v, hmem⟩ i) • (b i : Fin d → K) = P *ᵥ v := by
          have h := congrArg Subtype.val (b.sum_repr ⟨P *ᵥ v, hmem⟩)
          rw [Submodule.coe_sum] at h
          simpa using h
        have hEc' : E *ᵥ (fun i => b.repr ⟨P *ᵥ v, hmem⟩ i) =
            ∑ i, (b.repr ⟨P *ᵥ v, hmem⟩ i) • (b i : Fin d → K) := by
          ext k
          rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_apply]
          simp only [Pi.smul_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hkj : E k j = (b j : Fin d → K) k :=
            (Matrix.col_apply E j k).symm.trans (congrFun (hEcol j) k)
          rw [hkj, mul_comm]
        rw [hEc', hsum]
      have hc : (F.map h.bar)ᵀ *ᵥ (E *ᵥ (fun i => b.repr ⟨P *ᵥ v, hmem⟩ i)) =
          fun i => b.repr ⟨P *ᵥ v, hmem⟩ i := by
        rw [Matrix.mulVec_mulVec, hFstarE, Matrix.one_mulVec]
      rw [← hEc, hc]
    exact Matrix.toLin'.injective hlin
  exact ⟨a, E, F, hEE, hFF, hEF, hEFP⟩

end CFSG.LieType.SemisimpleCentralizers.OrderThree
