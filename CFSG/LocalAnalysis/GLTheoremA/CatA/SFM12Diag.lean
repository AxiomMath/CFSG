module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Herm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM12

open Matrix

variable {F : Type} [Field F] [CharP F 2]

@[expose] def OrthoEigen (g : Matrix (Fin 6) (Fin 6) F) (ζ : F) {m : ℕ} (f : Fin m → Fin 6 → F) : Prop :=
  (∀ i, ∃ j : ℕ, g *ᵥ f i = (ζ ^ j) • f i) ∧ (∀ i k, herm (f i) (f k) = if i = k then 1 else 0)

theorem exists_next {g : Matrix (Fin 6) (Fin 6) F} (hU : (g.map (fun x : F => x ^ 4))ᵀ * g = 1)
    (hx16 : ∀ x : F, x ^ 16 = x) {ζ : F} (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) (hg5 : g ^ 5 = 1)
    {m : ℕ} (f : Fin m → Fin 6 → F) (hf : OrthoEigen g ζ f) (hm : m < 6) :
    ∃ e : Fin 6 → F, (∃ j : ℕ, g *ᵥ e = (ζ ^ j) • e) ∧ herm e e = 1 ∧ ∀ i, herm (f i) e = 0 := by
  classical
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0] at hζ5
    norm_num at hζ5
  obtain ⟨w, hw0, hwK⟩ : ∃ w : Fin 6 → F, w ≠ 0 ∧ ∀ i, herm (f i) w = 0 := by
    let T : (Fin 6 → F) →ₗ[F] (Fin m → F) :=
      { toFun := fun x i => herm (f i) x
        map_add' := fun x y => funext fun i => herm_add_right _ _ _
        map_smul' := fun c x => funext fun i => by simp [herm_smul_right] }
    have hker : LinearMap.ker T ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by simp [Module.finrank_fin_fun]; omega)
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    refine ⟨w, hw0, fun i => ?_⟩
    have := congrFun (LinearMap.mem_ker.1 hw) i
    simpa [T] using this
  have hKg : ∀ x : Fin 6 → F, (∀ i, herm (f i) x = 0) → ∀ i, herm (f i) (g *ᵥ x) = 0 := by
    intro x hx i
    obtain ⟨j, hj⟩ := hf.1 i
    have h1 := herm_unitary hU (f i) x
    rw [hj, herm_smul_left, hx i] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (pow_ne_zero _ hζ0))
  have hKpow : ∀ k : ℕ, ∀ x : Fin 6 → F, (∀ i, herm (f i) x = 0) →
      ∀ i, herm (f i) ((g ^ k) *ᵥ x) = 0 := by
    intro k
    induction k with
    | zero =>
      intro x hx
      simpa using hx
    | succ k ih =>
      intro x hx i
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact hKg _ (ih x hx) i
  have hKpr : ∀ j : ℕ, ∀ x : Fin 6 → F, (∀ i, herm (f i) x = 0) →
      ∀ i, herm (f i) (pr g ζ j x) = 0 := by
    intro j x hx i
    unfold pr
    rw [herm_sum_right]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [herm_smul_right, hKpow k x hx i, mul_zero]
  obtain ⟨j0, hj05, hj0⟩ : ∃ j : ℕ, j < 5 ∧ pr g ζ j w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hw0
    rw [← pr_sum g hζ5 hζ1 w]
    exact Finset.sum_eq_zero fun j hj => hcon j (Finset.mem_range.1 hj)
  have he0eig : g *ᵥ pr g ζ j0 w = (ζ ^ j0) • pr g ζ j0 w := pr_eigen g hζ5 hg5 j0 w
  have he0K : ∀ i, herm (f i) (pr g ζ j0 w) = 0 := hKpr j0 w hwK
  obtain ⟨e1, he1eig, he1K, he1ne⟩ : ∃ e : Fin 6 → F, g *ᵥ e = (ζ ^ j0) • e ∧
      (∀ i, herm (f i) e = 0) ∧ herm e e ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hpol : ∀ x y : Fin 6 → F, g *ᵥ x = (ζ ^ j0) • x → (∀ i, herm (f i) x = 0) →
        g *ᵥ y = (ζ ^ j0) • y → (∀ i, herm (f i) y = 0) → herm x y = 0 := by
      intro x y hx hxK hy hyK
      apply herm_zero_of_isotropic hx16 hζ5 hζ1 (hcon x hx hxK) (hcon y hy hyK)
      intro a
      apply hcon (x + a • y)
      · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hy, smul_add, smul_comm a (ζ ^ j0) y]
      · intro i
        rw [herm_add_right, herm_smul_right, hxK i, hyK i]
        simp
    set e0 := pr g ζ j0 w with he0def
    have hef : ∀ i, herm e0 (f i) = 0 := fun i => by
      rw [herm_symm hx16, he0K i, zero_pow (by norm_num)]
    have hzero : ∀ z : Fin 6 → F, herm e0 z = 0 := by
      intro z
      set c : Fin m → F := fun i => herm (f i) z with hc
      set r : Fin 6 → F := z + ∑ i, (-c i) • f i with hr
      have hrK : ∀ k, herm (f k) r = 0 := by
        intro k
        rw [hr, herm_add_right, herm_sum_right]
        have hs : ∑ i, herm (f k) ((-c i) • f i) = -c k := by
          have hterm : ∀ i, herm (f k) ((-c i) • f i) = -c i * (if k = i then 1 else 0) := fun i => by
            rw [herm_smul_right, hf.2 k i]
          simp only [hterm, mul_ite, mul_one, mul_zero]
          simp
        rw [hs, hc]
        simp
      have hdec : z = r + ∑ i, c i • f i := by
        rw [hr, add_assoc, ← Finset.sum_add_distrib]
        simp
      rw [hdec, herm_add_right, herm_sum_right]
      have h1 : ∑ i, herm e0 (c i • f i) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [herm_smul_right, hef i, mul_zero]
      rw [h1, add_zero]
      have h2 : herm e0 r = ∑ m ∈ Finset.range 5, herm e0 (pr g ζ m r) := by
        conv_lhs => rw [← pr_sum g hζ5 hζ1 r]
        rw [herm_sum_right]
      rw [h2]
      refine Finset.sum_eq_zero fun m hm => ?_
      have hm5 : m < 5 := Finset.mem_range.1 hm
      by_cases hmj : m = j0
      · rw [hmj]
        exact hpol _ _ he0eig he0K (pr_eigen g hζ5 hg5 j0 r) (hKpr j0 r hrK)
      · exact herm_eigen_zeta hU hζ5 hζ1 (by omega) he0eig (pr_eigen g hζ5 hg5 m r)
    obtain ⟨k, hk⟩ : ∃ k, e0 k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hj0 (funext h)
    have hval : herm e0 (Pi.single k 1) = (e0 k) ^ 4 := by
      unfold herm
      simp [Pi.single_apply]
    have := hzero (Pi.single k 1)
    rw [hval] at this
    exact hk (pow_eq_zero_iff (by norm_num) |>.1 this)
  have hβ4 : herm e1 e1 ^ 4 = herm e1 e1 := (herm_symm hx16 e1 e1).symm
  have hβ0 : herm e1 e1 ≠ 0 := he1ne
  have hβ3 : herm e1 e1 ^ 3 = 1 := by
    have h' : herm e1 e1 * herm e1 e1 ^ 3 = herm e1 e1 * 1 := by
      rw [mul_one, ← pow_succ']
      exact hβ4
    exact mul_left_cancel₀ hβ0 h'
  refine ⟨(herm e1 e1) • e1, ⟨j0, ?_⟩, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, he1eig]
    exact smul_comm _ _ _
  · rw [herm_smul_left, herm_smul_right]
    have : herm e1 e1 ^ 4 * (herm e1 e1 * herm e1 e1) = (herm e1 e1 ^ 3) ^ 2 := by ring
    rw [this, hβ3, one_pow]
  · intro i
    rw [herm_smul_right, he1K i, mul_zero]

theorem exists_OrthoEigen {g : Matrix (Fin 6) (Fin 6) F} (hU : (g.map (fun x : F => x ^ 4))ᵀ * g = 1)
    (hx16 : ∀ x : F, x ^ 16 = x) {ζ : F} (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) (hg5 : g ^ 5 = 1) :
    ∀ m : ℕ, m ≤ 6 → ∃ f : Fin m → Fin 6 → F, OrthoEigen g ζ f := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨f, hf⟩ := ih (by omega)
    obtain ⟨e, ⟨j, hj⟩, hee, hoe⟩ := exists_next hU hx16 hζ5 hζ1 hg5 f hf (by omega)
    refine ⟨Fin.snoc f e, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => exact ⟨j, by simpa using hj⟩
      | cast i =>
        obtain ⟨j', hj'⟩ := hf.1 i
        exact ⟨j', by simpa using hj'⟩
    · intro i k
      induction i using Fin.lastCases with
      | last =>
        induction k using Fin.lastCases with
        | last => simpa using hee
        | cast k =>
          simp [herm_symm hx16 (f k) e, hoe k, (Fin.castSucc_lt_last k).ne']
      | cast i =>
        induction k using Fin.lastCases with
        | last => simp [hoe i, (Fin.castSucc_lt_last i).ne]
        | cast k => simpa using hf.2 i k

end CFSG.LocalAnalysis.GLTheoremA.SFM12
