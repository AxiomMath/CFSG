module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighUnitaryGU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

open Matrix CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.SeitzGeneration.Centers
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux

section ToolsC

variable {ℓ f n m : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem mul_comm_of_mulVec {A B : Matrix (Fin n) (Fin n) K}
    (hAB : ∀ v, A *ᵥ (B *ᵥ v) = B *ᵥ (A *ᵥ v)) : A * B = B * A :=
  Matrix.ext_of_mulVec_single fun i => by rw [← mulVec_mulVec, ← mulVec_mulVec, hAB]

variable (h : UnitaryFieldData ℓ f K)

theorem siegel_comm_of_eigen_gu {ι : Type*} [Fintype ι] {S : SUid σ₀ n}
    {B : primeFormUnitary h (idGram K n)} {u : ι → Fin n → K}
    {c : K} (hS : ∀ v, S • v = v + ∑ k, (c * herm σ₀ (u k) v) • u k) {lam : ι → K}
    (hB : ∀ k, B • u k = lam k • u k) (hl : ∀ k, σ₀ (lam k) * lam k = 1) :
    ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  refine (mul_comm_of_mulVec fun v => ?_).symm
  rw [← smul_def σ₀ S, ← smul_def σ₀ S, ← smul_def_gu h B, ← smul_def_gu h B, hS, hS, smul_add,
    Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hl0 : lam k ≠ 0 := by
    rintro h0
    have := hl k
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hσl : σ₀ (lam k)⁻¹ = lam k := by
    rw [map_inv₀]
    exact inv_eq_of_mul_eq_one_right (hl k)
  have hBu : u k = B • ((lam k)⁻¹ • u k) := by
    rw [smul_comm, hB, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have h1 : herm σ₀ (u k) (B • v) = lam k * herm σ₀ (u k) v := by
    conv_lhs => rw [hBu]
    rw [herm_smul_smul_gu, herm_smul_left, hσl]
  rw [smul_comm, hB, h1, smul_smul]
  congr 1
  ring

theorem exists_siegel_orbit_gu {p : ℕ} [NeZero p] {X : primeFormUnitary h (idGram K n)} {β : K}
    (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1) (hβ : σ₀ β * β = 1)
    {w : Fin n → K} (horth : ∀ k l : Fin p, herm σ₀ ((X ^ (k : ℕ)) • w) ((X ^ (l : ℕ)) • w) = 0)
    {c : K} (hc : c + σ₀ c = 0) :
    ∃ S : SUid σ₀ n, (∀ v, S • v = v + ∑ k : Fin p,
      (c * herm σ₀ ((X ^ (k : ℕ)) • w) v) • ((X ^ (k : ℕ)) • w)) ∧
      ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hσi : ∀ c, σ₀ (σ₀ c) = c := (Nonsplit.isUnitaryInvolution h).invol
  obtain ⟨S, hS⟩ := exists_siegel hσi (fun k : Fin p => (X ^ (k : ℕ)) • w) horth hc
  refine ⟨S, hS, (mul_comm_of_mulVec fun v => ?_).symm⟩
  rw [← smul_def σ₀ S, ← smul_def σ₀ S, ← smul_def_gu h X, ← smul_def_gu h X, hS, hS, smul_add,
    Finset.smul_sum]
  congr 1
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := NeZero.pos p; omega⟩
  rw [← Equiv.sum_comp (finRotate (q + 1)) (fun k : Fin (q + 1) =>
    (c * herm σ₀ ((X ^ (k : ℕ)) • w) (X • v)) • ((X ^ (k : ℕ)) • w))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hXpw : (X ^ (q + 1)) • w = β • w := by
    rw [smul_def_gu, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hXp, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  by_cases hk : k = Fin.last q
  · subst hk
    rw [finRotate_last, Fin.val_zero, pow_zero, one_smul, Fin.val_last, smul_comm X,
      ← mul_smul X (X ^ q) w, ← pow_succ', hXpw, smul_smul]
    have h1 : herm σ₀ ((X ^ q) • w) v = σ₀ β * herm σ₀ w (X • v) := by
      rw [← herm_smul_smul_gu h X, ← mul_smul, ← pow_succ', hXpw, herm_smul_left]
    rw [h1]
    congr 1
    linear_combination (c * herm σ₀ w (X • v)) * hβ
  · rw [coe_finRotate_of_ne_last hk, pow_succ', mul_smul X (X ^ (k : ℕ)) w, herm_smul_smul_gu]
    exact smul_comm X _ _

theorem exists_nonscalar_comm_gu {xs : Fin m → Fin n → K}
    (hxs : ONExt.IsON σ₀ xs) {s : primeFormUnitary h (idGram K n)}
    (hsU : ∀ c, ∃ d, s • orthoEmb xs c = orthoEmb xs d)
    (hsU' : ∀ c, ∃ d, s⁻¹ • orthoEmb xs c = orthoEmb xs d) {e₁ e₂ : Fin m → K}
    (h11 : herm σ₀ e₁ e₁ = 1) (h22 : herm σ₀ e₂ e₂ = 1) (h12 : herm σ₀ e₁ e₂ = 0)
    {l₁ l₂ : K} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0) (hs₁ : s • orthoEmb xs e₁ = l₁ • orthoEmb xs e₁)
    (hs₂ : s • orthoEmb xs e₂ = l₂ • orthoEmb xs e₂) {d : K} (hd : σ₀ d * d = 1)
    (hdd : d ≠ d⁻¹) :
    ∃ g : SUid σ₀ m, (∀ c : K, ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ≠ c • 1) ∧
      ((ONExt.ext (Nonsplit.isUnitaryInvolution h).invol hxs g : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((ONExt.ext (Nonsplit.isUnitaryInvolution h).invol hxs g : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσi := hσ.invol
  set y : Fin 2 → Fin m → K := ![e₁, e₂] with hy
  have h21 : herm σ₀ e₂ e₁ = 0 := herm_eq_zero_comm σ₀ hσi h12
  have hyON : ONExt.IsON σ₀ y := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hy, h11, h22, h12, h21]
  set g : SUid σ₀ m := ONExt.ext hσi hyON (diagTwo σ₀ hd) with hg
  have hy0 : orthoEmb y (Pi.single 0 1) = e₁ := by rw [ONExt.orthoEmb_single]; rfl
  have hy1 : orthoEmb y (Pi.single 1 1) = e₂ := by rw [ONExt.orthoEmb_single]; rfl
  have hge₁ : g • e₁ = d • e₁ := by
    rw [← hy0, hg, ONExt.ext_smul_orthoEmb, (diagTwo_smul_single σ₀ hd).1, map_smul]
  have hge₂ : g • e₂ = d⁻¹ • e₂ := by
    rw [← hy1, hg, ONExt.ext_smul_orthoEmb, (diagTwo_smul_single σ₀ hd).2, map_smul]
  refine ⟨g, fun c hc => ?_, ?_⟩
  ·
    have he₁ : e₁ ≠ 0 := by rintro rfl; rw [herm_zero_left] at h11; exact zero_ne_one h11
    have he₂ : e₂ ≠ 0 := by rintro rfl; rw [herm_zero_left] at h22; exact zero_ne_one h22
    have h1 : c • e₁ = d • e₁ := by
      rw [← hge₁, smul_def, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 : c • e₂ = d⁻¹ • e₂ := by
      rw [← hge₂, smul_def, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hcd : c = d := by
      have h3 : (c - d) • e₁ = 0 := by rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.1 h3 with h4 | h4
      · exact sub_eq_zero.1 h4
      · exact absurd h4 he₁
    have hcd' : c = d⁻¹ := by
      have h3 : (c - d⁻¹) • e₂ = 0 := by rw [sub_smul, h2, sub_self]
      rcases smul_eq_zero.1 h3 with h4 | h4
      · exact sub_eq_zero.1 h4
      · exact absurd h4 he₂
    exact hdd (hcd.symm.trans hcd')
  ·
    refine commute_ext_of_resMat_gu h hσi hxs hsU hsU' ?_
    set M : GL (Fin m) K := resGL_gu h hxs s hsU hsU' with hM
    have hMe : ∀ (e : Fin m → K) (l : K), s • orthoEmb xs e = l • orthoEmb xs e →
        (M : Matrix (Fin m) (Fin m) K) *ᵥ e = l • e := by
      intro e l he
      rw [hM, coe_resGL_gu]
      exact resMat_mulVec_of_eq hxs (by rw [← smul_def_gu h, he, ← map_smul])
    have hMe₁ := hMe e₁ l₁ hs₁
    have hMe₂ := hMe e₂ l₂ hs₂
    have hsinv : ∀ (e : Fin m → K) (l : K), l ≠ 0 → s • orthoEmb xs e = l • orthoEmb xs e →
        s⁻¹ • orthoEmb xs e = l⁻¹ • orthoEmb xs e := by
      intro e l hl he
      rw [inv_smul_eq_iff, smul_comm, he, smul_smul, inv_mul_cancel₀ hl, one_smul]
    have hMinv : ∀ (e : Fin m → K) (l : K), l ≠ 0 → s • orthoEmb xs e = l • orthoEmb xs e →
        ((M⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ e = l⁻¹ • e := by
      intro e l hl he
      show ONExt.resMat σ₀ xs (((s⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ e = l⁻¹ • e
      exact resMat_mulVec_of_eq hxs (by rw [← smul_def_gu h, hsinv e l hl he, ← map_smul])
    have hspan : ∀ (N : Matrix (Fin m) (Fin m) K) (a b : K), N *ᵥ e₁ = a • e₁ →
        N *ᵥ e₂ = b • e₂ → ∀ c, ∃ c', N *ᵥ orthoEmb y c = orthoEmb y c' := by
      intro N a b ha hb c
      refine ⟨![a * c 0, b * c 1], ?_⟩
      simp only [Centers.orthoEmb_apply, Fin.sum_univ_two, hy, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, mulVec_add, mulVec_smul, ha, hb, smul_smul]
      ring_nf
    have hres : ONExt.resMat σ₀ y (M : Matrix (Fin m) (Fin m) K) =
        Matrix.diagonal ![l₁, l₂] := by
      refine Matrix.ext_of_mulVec_single fun j => ?_
      have hj : (M : Matrix (Fin m) (Fin m) K) *ᵥ orthoEmb y (Pi.single j 1) =
          orthoEmb y (![l₁, l₂] j • Pi.single j 1) := by
        rw [ONExt.orthoEmb_single, map_smul, ONExt.orthoEmb_single]
        fin_cases j
        · simpa [hy] using hMe₁
        · simpa [hy] using hMe₂
      rw [resMat_mulVec_of_eq hyON hj]
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    have hcomm := commute_extMat_of_GL hσi hyON (M := M)
      (fun u v => by rw [hM, coe_resGL_gu]; exact herm_resMat_gu h hxs hsU u v)
      (hspan _ l₁ l₂ hMe₁ hMe₂)
      (hspan _ l₁⁻¹ l₂⁻¹ (hMinv e₁ l₁ hl₁ hs₁) (hMinv e₂ l₂ hl₂ hs₂))
      (g := ((diagTwo σ₀ hd : SUid σ₀ 2) : GL (Fin 2) K)) (by
        rw [hres]
        show Matrix.diagonal ![d, d⁻¹] * Matrix.diagonal ![l₁, l₂] =
          Matrix.diagonal ![l₁, l₂] * Matrix.diagonal ![d, d⁻¹]
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        exact mul_comm _ _)
    rw [hM, coe_resGL_gu] at hcomm
    exact hcomm.symm

end ToolsC

section BlockC

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

variable (h : UnitaryFieldData ℓ f K)

theorem mulVec_pow_smul_of_qcomm_gu {X B : primeFormUnitary h (idGram K n)} {ζ : K}
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) {μ : K} :
    ∀ (k a : ℕ) (v : Fin n → K),
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (μ * ζ ^ a) • v →
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((X ^ k) • v) =
        (μ * ζ ^ (a + k)) • ((X ^ k) • v) := by
  intro k
  induction k with
  | zero => intro a v hv; simpa using hv
  | succ k ih =>
    intro a v hv
    rw [pow_succ', mul_smul, smul_def_gu h X, mulVec_mulVec, hBX, Matrix.smul_mulVec,
      ← mulVec_mulVec, ih a v hv, mulVec_smul, smul_smul]
    congr 1
    ring

theorem eq_smul_of_eigen_le_gu {X B r : primeFormUnitary h (idGram K n)} {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : (p : K) ≠ 0) (hrX : r * X = X * r)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {μ : K} (hμ : μ ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1) (hp : p.Prime)
    (l : Fin p) {lam : K}
    (hle : Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (μ * ζ ^ (l : ℕ)) ≤
      Module.End.eigenspace (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) lam) :
    ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = lam • 1 := by
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (a : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) a ↔ M *ᵥ v = a • v := fun M a v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hBT : (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p =
      algebraMap K (Module.End K (Fin n → K)) (μ ^ p) := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hBp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hsup := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hμ hBT
  have hVle : ∀ i : Fin p,
      Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (μ * ζ ^ (i : ℕ)) ≤
      Module.End.eigenspace (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        lam := by
    intro i v hv
    rw [hmemE] at hv ⊢
    set k := (l : ℕ) + p - i with hk
    have hXkv := mulVec_pow_smul_of_qcomm_gu h hBX k i v hv
    have hik : (i : ℕ) + k = l + p := by have := i.2; omega
    rw [hik, pow_add, hζ.pow_eq_one, mul_one] at hXkv
    have h1 := (hmemE _ _ _).1 (hle ((hmemE _ _ _).2 hXkv))
    have h2 : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((X ^ k) • v) =
        (X ^ k) • (((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
      rw [smul_def_gu, smul_def_gu, mulVec_mulVec, mulVec_mulVec,
        coe_comm_gu h (Commute.pow_right hrX k).eq]
    rw [h2, ← smul_comm] at h1
    exact smul_left_cancel _ h1
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have hv : (Pi.single i 1 : Fin n → K) ∈ (⊤ : Submodule K (Fin n → K)) := Submodule.mem_top
  rw [← hsup] at hv
  rw [(hmemE _ _ _).1 ((iSup_le hVle) hv), Matrix.smul_mulVec, Matrix.one_mulVec]

theorem exists_two_eigen_gu {X B r : primeFormUnitary h (idGram K n)} {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (hpK : (p : K) ≠ 0) (hp : p.Prime) (hrX : r * X = X * r) (hrB : r * B = B * r)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {μ ρ : K} (hμ : μ ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1) (hρ : ρ ≠ 0)
    (hrp : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ρ ^ p) • 1)
    (hrs : ∀ c : K, ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1) (l : Fin p)
    (hU0 : Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (μ * ζ ^ (l : ℕ)) ≠ ⊥) :
    ∃ c₁ c₂ : Fin p, c₁ ≠ c₂ ∧
      Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (μ * ζ ^ (l : ℕ)) ⊓
        Module.End.eigenspace (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (ρ * ζ ^ (c₁ : ℕ)) ≠ ⊥ ∧
      Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (μ * ζ ^ (l : ℕ)) ⊓
        Module.End.eigenspace (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (ρ * ζ ^ (c₂ : ℕ)) ≠ ⊥ := by
  classical
  set U := Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (μ * ζ ^ (l : ℕ)) with hU
  have hrT : (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p =
      algebraMap K (Module.End K (Fin n → K)) (ρ ^ p) := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hrp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hBr_lin : Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, mulVec_mulVec, coe_comm_gu h hrB]
  have hdecU := eigenspace_le_iSup_inf hp hpK hζ hBr_lin hρ hrT (μ * ζ ^ (l : ℕ))
  by_contra hcon
  push Not at hcon
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Fin p, U ≤ Module.End.eigenspace
      (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (ρ * ζ ^ (c₀ : ℕ)) := by
    by_cases hex : ∃ c₀ : Fin p, U ⊓ Module.End.eigenspace
        (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (ρ * ζ ^ (c₀ : ℕ)) ≠ ⊥
    · obtain ⟨c₀, hne⟩ := hex
      refine ⟨c₀, hdecU.trans (iSup_le fun c => ?_)⟩
      by_cases hc : c = c₀
      · rw [hc]
        exact inf_le_right
      · rw [hcon c₀ c (Ne.symm hc) hne]
        exact bot_le
    · push Not at hex
      exfalso
      apply hU0
      rw [eq_bot_iff]
      refine hdecU.trans (iSup_le fun c => ?_)
      rw [hex c]
  exact hrs _ (eq_smul_of_eigen_le_gu h hζ hpK hrX hBX hμ hBp hp l hc₀)

theorem finrank_eigen_le_gu {X B : primeFormUnitary h (idGram K n)} {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) (μ : K) (a b : Fin p) :
    Module.finrank K (Module.End.eigenspace
        (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (a : ℕ))) ≤
      Module.finrank K (Module.End.eigenspace
        (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (b : ℕ))) := by
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) c ↔ M *ᵥ v = c • v := fun M c v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  set k := (b : ℕ) + p - a with hk
  have hmaps : ∀ v ∈ Module.End.eigenspace
      (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (a : ℕ)),
      Matrix.toLin' (((X ^ k : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) v ∈
        Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (μ * ζ ^ (b : ℕ)) := by
    intro v hv
    rw [hmemE] at hv ⊢
    rw [Matrix.toLin'_apply, ← smul_def_gu]
    have h1 := mulVec_pow_smul_of_qcomm_gu h hBX k a v hv
    have hak : (a : ℕ) + k = b + p := by have := a.2; omega
    rwa [hak, pow_add, hζ.pow_eq_one, mul_one] at h1
  refine LinearMap.finrank_le_finrank_of_injective
    (f := (Matrix.toLin' (((X ^ k : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)).restrict hmaps) ?_
  intro v w hvw
  apply Subtype.ext
  have := congrArg Subtype.val hvw
  simp only [LinearMap.restrict_coe_apply, Matrix.toLin'_apply] at this
  rw [← smul_def_gu, ← smul_def_gu] at this
  exact smul_left_cancel _ this

theorem card_mul_finrank_eigen_gu (hp : p.Prime) {X B : primeFormUnitary h (idGram K n)} {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {μ : K} (hμ : μ ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1) (l : Fin p) :
    p * Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (l : ℕ))) = n := by
  classical
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  have hBT : (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p =
      algebraMap K (Module.End K (Fin n → K)) (μ ^ p) := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hBp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  set W : Fin p → Submodule K (Fin n → K) := fun l => Module.End.eigenspace
    (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (l : ℕ)) with hW
  have heq : ∀ l', Module.finrank K (W l') = Module.finrank K (W l) := fun l' =>
    le_antisymm (finrank_eigen_le_gu h hζ hBX μ l' l) (finrank_eigen_le_gu h hζ hBX μ l l')
  have hsum : ∑ l', Module.finrank K (W l') = p * Module.finrank K (W l) := by
    rw [Finset.sum_congr rfl fun l' _ => heq l', Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hle : ∑ l', Module.finrank K (W l') ≤ n := by
    have := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryRestAux.sum_finrank_le
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryRestAux.iSupIndep_eigen
        (Y := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hμ hζ)
    rwa [Module.finrank_fin_fun] at this
  have hsup : (⨆ l', W l') = ⊤ := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hμ hBT
  have hge : n ≤ ∑ l', Module.finrank K (W l') := by
    have := finrank_iSup_le_sum (K := K) W
    rwa [hsup, finrank_top, Module.finrank_fin_fun] at this
  show p * Module.finrank K (W l) = n
  omega

theorem allCenters_eigen_nonab_gu (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) {Γ : Type*} [Group Γ]
    (κ : primeFormUnitary h (idGram K n) →* Γ)
    (hker' : ∀ g : primeFormUnitary h (idGram K n),
      (∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) → κ g = 1)
    {E : Subgroup Γ} {H : Subgroup (SUid σ₀ n)} (hH : HyperLift h κ E H)
    {X B r : primeFormUnitary h (idGram K n)} (hXE : κ X ∈ E) (hBE : κ B ∈ E) (hrE : κ r ∈ E)
    (hr1 : κ r ≠ 1)
    (hB1 : κ B ≠ 1) (hBr : κ B ∉ Subgroup.zpowers (κ r)) (hXB : κ X ∉ Subgroup.zpowers (κ B))
    (hrX : r * X = X * r) (hrB : r * B = B * r)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {β μ ρ : K} (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1)
    (hμ : μ ≠ 0) (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1)
    (hρ : ρ ≠ 0) (hrp : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ρ ^ p) • 1)
    (l : Fin p)
    (hdim : 3 ≤ Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (l : ℕ)))) :
    AllCenters H (Module.End.eigenspace
      (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (l : ℕ))) := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσi := hσ.invol
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set Bm : Matrix (Fin n) (Fin n) K := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hBm
  set Xm : Matrix (Fin n) (Fin n) K := ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hXm
  set rm : Matrix (Fin n) (Fin n) K := ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hrm
  set U := Module.End.eigenspace (Matrix.toLin' Bm) (μ * ζ ^ (l : ℕ)) with hU
  have hU0 : U ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hdim
    omega
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact absurd (Subsingleton.elim v₀ 0) hv₀0
    · exact h0
  have hμN := bar_mul_eq_one_of_gu_pow h hp hp2 hpq hn hμ hBp
  have hρN := bar_mul_eq_one_of_gu_pow h hp hp2 hpq hn hρ hrp
  have hβN := bar_mul_eq_one_of_gu_scalar h hn hXp
  have hpowT : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K), M ^ p = c • 1 →
      (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    intro M c hM
    have h2 := congrArg Matrix.toLinAlgEquiv' hM
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (a : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) a ↔ M *ᵥ v = a • v := fun M a v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hlamN : ∀ (c : K), h.bar c * c = 1 → ∀ k : ℕ, h.bar (c * ζ ^ k) * (c * ζ ^ k) = 1 := by
    intro c hc k
    rw [map_mul, map_pow]
    calc h.bar c * h.bar ζ ^ k * (c * ζ ^ k) = (h.bar c * c) * (h.bar ζ * ζ) ^ k := by ring
      _ = 1 := by rw [hc, hζN, one_pow, one_mul]
  have horthE : ∀ (s : primeFormUnitary h (idGram K n)) (c : K), c ≠ 0 → h.bar c * c = 1 →
      ∀ a b : ℕ, a % p ≠ b % p →
      ∀ u v, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = (c * ζ ^ a) • u →
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (c * ζ ^ b) • v →
        herm σ₀ u v = 0 := by
    intro s c hc0 hcN a b hab u v hu hv
    rw [pow_eq_pow_mod hζ a] at hu
    rw [pow_eq_pow_mod hζ b] at hv
    exact herm_eq_zero_of_eigen_gu h hu hv (bar_mul_ne_one h hc0 hcN hζ hζN
      (i := ⟨a % p, Nat.mod_lt _ hp.pos⟩) (i' := ⟨b % p, Nat.mod_lt _ hp.pos⟩)
      (fun he => hab (congrArg Fin.val he)))
  have hmodne : ∀ a b : ℕ, a < p → b < p → a ≠ b → a % p ≠ b % p := by
    intro a b ha hb hab
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have hshiftk : ∀ (k a : ℕ) (v : Fin n → K), Bm *ᵥ v = (μ * ζ ^ a) • v →
      Bm *ᵥ ((X ^ k) • v) = (μ * ζ ^ (a + k)) • ((X ^ k) • v) :=
    mulVec_pow_smul_of_qcomm_gu h hBX
  have hsup : ⨆ i : Fin p, Module.End.eigenspace (Matrix.toLin' Bm) (μ * ζ ^ (i : ℕ)) = ⊤ :=
    NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hμ (hpowT _ _ hBp)
  have hnd : ((idForm h n).domRestrict₁₂ U U).SeparatingLeft := by
    refine NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n)
      (fun i : Fin p => Module.End.eigenspace (Matrix.toLin' Bm) (μ * ζ ^ (i : ℕ)))
      (fun i i' hii u hu v hv => ?_) hsup l
    rw [Nonsplit.idForm_eq_herm h]
    exact horthE B μ hμ hμN i i' (hmodne _ _ i.2 i'.2 (fun he => hii (Fin.ext he))) u v
      ((hmemE _ _ u).1 hu) ((hmemE _ _ v).1 hv)
  have hON : HasONBasis σ₀ U := by
    refine Nonsplit.hasONBasis_of_separatingLeft h U hnd ?_
    obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
    exact Or.inr ⟨hdim, s, hs0, by rw [hσb]; exact hs1⟩
  obtain ⟨m, xs, hxs, hspan, hm⟩ := hON
  have hxsON : ONExt.IsON σ₀ xs := hxs
  have hm3 : 3 ≤ m := by rcases hm with h4 | ⟨h3, -⟩ <;> omega
  have h3m : m = 3 → ∃ s : K, s ≠ 0 ∧ σ₀ s * s ≠ 1 := fun _ => by
    obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
    exact ⟨s, hs0, by rw [hσb]; exact hs1⟩
  have hstab : ∀ t : primeFormUnitary h (idGram K n), t * B = B * t → ∀ v ∈ U, t • v ∈ U := by
    intro t ht v hv
    rw [hU, hmemE] at hv ⊢
    rw [smul_def_gu, mulVec_mulVec, ← coe_comm_gu h ht, ← mulVec_mulVec, hv, mulVec_smul]
  have hsU : ∀ t : primeFormUnitary h (idGram K n), t * B = B * t →
      ∀ c, ∃ d, t • orthoEmb xs c = orthoEmb xs d :=
    fun t ht => exists_orthoEmb_of_stable_gu h hspan (hstab t ht)
  have hsU' : ∀ t : primeFormUnitary h (idGram K n), t * B = B * t →
      ∀ c, ∃ d, t⁻¹ • orthoEmb xs c = orthoEmb xs d :=
    fun t ht => exists_orthoEmb_of_stable_gu h hspan (hstab t⁻¹ (Commute.inv_left ht).eq)
  have hBlam : ∀ c, B • orthoEmb xs c = (μ * ζ ^ (l : ℕ)) • orthoEmb xs c := fun c => by
    have hc : orthoEmb xs c ∈ U := hspan ▸ orthoEmb_mem_span xs c
    exact (hmemE _ _ _).1 hc
  have hBres : ONExt.resMat σ₀ xs Bm = (μ * ζ ^ (l : ℕ)) • 1 :=
    resMat_eq_smul_of_eigen_gu h hxsON hBlam
  have hBB : B * B = B * B := rfl
  set ε := ONExt.ext hσi hxsON with hε
  set HU := H.comap ε with hHU
  have hnorm : ∀ g ∈ HU, ∀ t : SUid σ₀ m, t * g * t⁻¹ ∈ HU := by
    refine conj_mem_of_tv hσ (by omega) h3m ?_
    intro a ha c hc g hg
    set w := orthoEmb xs a with hw
    have hwU : w ∈ U := hspan ▸ orthoEmb_mem_span xs a
    have hwB : Bm *ᵥ w = (μ * ζ ^ (l : ℕ)) • w := (hmemE _ _ w).1 hwU
    have hXkB : ∀ k : ℕ, Bm *ᵥ ((X ^ k) • w) = (μ * ζ ^ ((l : ℕ) + k)) • ((X ^ k) • w) :=
      fun k => hshiftk k _ w hwB
    have horthS : ∀ k k' : Fin p, herm σ₀ ((X ^ (k : ℕ)) • w) ((X ^ (k' : ℕ)) • w) = 0 := by
      intro k k'
      by_cases hkk : k = k'
      · subst hkk
        rw [herm_smul_smul_gu, hw, herm_orthoEmb hxs, ha]
      · refine horthE B μ hμ hμN ((l : ℕ) + k) ((l : ℕ) + k') ?_ _ _ (hXkB k) (hXkB k')
        intro he
        apply hkk
        have h1 := Nat.ModEq.add_left_cancel' (l : ℕ) he
        exact Fin.ext (by rwa [Nat.ModEq, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2] at h1)
    obtain ⟨S, hS, hXS⟩ :=
      exists_siegel_orbit_gu h (p := p) hXp (by rw [hσb]; exact hβN) horthS hc
    have hBS := siegel_comm_of_eigen_gu h hS (B := B)
      (lam := fun k : Fin p => μ * ζ ^ ((l : ℕ) + k)) (fun k => by rw [smul_def_gu]; exact hXkB k)
      (fun k => by rw [hσb]; exact hlamN μ hμN _)
    have hSH : S ∈ H := hH S B X hBE hXE hB1 hXB hBS hXS
    have hSU : ∀ c', S • orthoEmb xs c' = ε (tv hσi ha hc) • orthoEmb xs c' := by
      intro c'
      have hc'U : orthoEmb xs c' ∈ U := hspan ▸ orthoEmb_mem_span xs c'
      rw [hS, ONExt.ext_tv_smul hσi hxsON ha hc, ← hw]
      congr 1
      rw [Finset.sum_eq_single (0 : Fin p)]
      · simp
      · intro k _ hk0
        have h0 : herm σ₀ ((X ^ (k : ℕ)) • w) (orthoEmb xs c') = 0 := by
          refine horthE B μ hμ hμN ((l : ℕ) + k) l ?_ _ _ (hXkB k) ((hmemE _ _ _).1 hc'U)
          intro he
          apply hk0
          have h1 : (l : ℕ) + k ≡ (l : ℕ) + 0 [MOD p] := by rw [add_zero]; exact he
          have h2 := Nat.ModEq.add_left_cancel' (l : ℕ) h1
          exact Fin.ext (by rwa [Nat.ModEq, Nat.mod_eq_of_lt k.2, Nat.zero_mod] at h2)
        rw [h0, mul_zero, zero_smul]
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    set T := (ε (tv hσi ha hc))⁻¹ * S with hT
    have hTU : ∀ c', T • orthoEmb xs c' = orthoEmb xs c' := by
      intro c'
      rw [hT, mul_smul, hSU, inv_smul_smul]
    have hTU' : ∀ c', T⁻¹ • orthoEmb xs c' = orthoEmb xs c' := by
      intro c'
      rw [inv_smul_eq_iff, hTU]
    have hTres : ONExt.resMat σ₀ xs ((T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [resMat_eq_smul_of_eigen hxsON (lam := 1) (fun c' => by rw [hTU, one_smul]), one_smul]
    have hTg : T * ε g = ε g * T :=
      commute_ext_of_resMat hσi hxsON (fun c' => ⟨c', hTU c'⟩) (fun c' => ⟨c', hTU' c'⟩)
        (by rw [hTres, Matrix.mul_one, Matrix.one_mul])
    have hS' : S = ε (tv hσi ha hc) * T := by rw [hT, mul_inv_cancel_left]
    have hconj : T * ε g * T⁻¹ = ε g := by rw [hTg, mul_inv_cancel_right]
    have key : ε (tv hσi ha hc * g * (tv hσi ha hc)⁻¹) = S * ε g * S⁻¹ := by
      calc ε (tv hσi ha hc * g * (tv hσi ha hc)⁻¹)
          = ε (tv hσi ha hc) * ε g * (ε (tv hσi ha hc))⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = ε (tv hσi ha hc) * (T * ε g * T⁻¹) * (ε (tv hσi ha hc))⁻¹ := by rw [hconj]
        _ = (ε (tv hσi ha hc) * T) * ε g * (ε (tv hσi ha hc) * T)⁻¹ := by group
        _ = S * ε g * S⁻¹ := by rw [← hS']
    show ε (tv hσi ha hc * g * (tv hσi ha hc)⁻¹) ∈ H
    rw [key]
    exact H.mul_mem (H.mul_mem hSH hg) (H.inv_mem hSH)
  have hBr_lin : Matrix.toLin' Bm * Matrix.toLin' rm = Matrix.toLin' rm * Matrix.toLin' Bm := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, mulVec_mulVec, coe_comm_gu h hrB]
  obtain ⟨c₁, c₂, hc12, hJ₁, hJ₂⟩ := exists_two_eigen_gu h hζ hpK hp hrX hrB hBX hμ hBp hρ hrp
    (fun c hc => hr1 (hker' r ⟨c, hc⟩)) l hU0
  set J : Fin p × Fin p → Submodule K (Fin n → K) := fun ij =>
    Module.End.eigenspace (Matrix.toLin' Bm) (μ * ζ ^ (ij.1 : ℕ)) ⊓
      Module.End.eigenspace (Matrix.toLin' rm) (ρ * ζ ^ (ij.2 : ℕ)) with hJ
  have hJtop : ⨆ ij, J ij = ⊤ :=
    iSup_inf_eigenspace_eq_top hp hpK hζ hBr_lin hμ hρ (hpowT _ _ hBp) (hpowT _ _ hrp)
  have hJorth : ∀ ij ij' : Fin p × Fin p, ij ≠ ij' → ∀ u ∈ J ij, ∀ v ∈ J ij',
      herm σ₀ u v = 0 := by
    intro ij ij' hne u hu v hv
    by_cases h1 : ij.1 = ij'.1
    · have h2 : ij.2 ≠ ij'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact horthE r ρ hρ hρN ij.2 ij'.2 (hmodne _ _ ij.2.2 ij'.2.2 (fun he => h2 (Fin.ext he)))
        u v ((hmemE _ _ u).1 hu.2) ((hmemE _ _ v).1 hv.2)
    · exact horthE B μ hμ hμN ij.1 ij'.1 (hmodne _ _ ij.1.2 ij'.1.2 (fun he => h1 (Fin.ext he)))
        u v ((hmemE _ _ u).1 hu.1) ((hmemE _ _ v).1 hv.1)
  have hJsep : ∀ ij, ((idForm h n).domRestrict₁₂ (J ij) (J ij)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) J
      (fun ij ij' hne u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]; exact hJorth ij ij' hne u hu v hv) hJtop
  obtain ⟨e₁, he₁J, he₁⟩ := exists_unit_of_separatingLeft h hJ₁ (hJsep (l, c₁))
  obtain ⟨e₂, he₂J, he₂⟩ := exists_unit_of_separatingLeft h hJ₂ (hJsep (l, c₂))
  have he₁₂ : herm σ₀ e₁ e₂ = 0 := hJorth (l, c₁) (l, c₂) (fun he => hc12 (congrArg Prod.snd he))
    e₁ he₁J e₂ he₂J
  obtain ⟨d₁, hd₁⟩ := (mem_span_range_iff xs e₁).1 (hspan ▸ he₁J.1)
  obtain ⟨d₂, hd₂⟩ := (mem_span_range_iff xs e₂).1 (hspan ▸ he₂J.1)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζζ : ζ ≠ ζ⁻¹ := by
    intro he
    have h1 : ζ ^ 2 = 1 := by
      rw [sq]
      calc ζ * ζ = ζ * ζ⁻¹ := by rw [← he]
        _ = 1 := mul_inv_cancel₀ hζ0
    have := Nat.le_of_dvd (by norm_num) (hζ.dvd_of_pow_eq_one 2 h1)
    have := hp.two_le
    omega
  have hρζ : ∀ c : ℕ, ρ * ζ ^ c ≠ 0 := fun c => mul_ne_zero hρ (pow_ne_zero _ hζ0)
  obtain ⟨g₀, hg₀s, hg₀r⟩ := exists_nonscalar_comm_gu h hxsON (hsU r hrB) (hsU' r hrB)
    (by rw [← herm_orthoEmb hxs, hd₁, he₁]) (by rw [← herm_orthoEmb hxs, hd₂, he₂])
    (by rw [← herm_orthoEmb hxs, hd₁, hd₂, he₁₂]) (hρζ c₁) (hρζ c₂)
    (by rw [hd₁, smul_def_gu]; exact (hmemE _ _ _).1 he₁J.2)
    (by rw [hd₂, smul_def_gu]; exact (hmemE _ _ _).1 he₂J.2) (d := ζ) (by rw [hσb]; exact hζN)
    hζζ
  have hg₀B := commute_ext_of_resMat_gu h hσi hxsON (hsU B hBB) (hsU' B hBB) (g := g₀)
      (by rw [hBres, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul])
  have hg₀HU : g₀ ∈ HU := by
    show ε g₀ ∈ H
    exact hH (ε g₀) r B hrE hBE hr1 hBr hg₀r hg₀B
  have htop : HU = ⊤ := eq_top_of_normal_of_nonscalar hσ hm3 h3m hnorm hg₀HU hg₀s
  rw [← hspan]
  exact ONExt.allCenters_of_forall_ext_mem hσi hxsON fun g => by
    have : g ∈ HU := by rw [htop]; exact Subgroup.mem_top g
    exact this

theorem hyperGen_of_nonab_pth_gu (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) (hn : 2 * p < n) {Γ : Type*} [Group Γ]
    (κ : primeFormUnitary h (idGram K n) →* Γ)
    (hker' : ∀ g : primeFormUnitary h (idGram K n),
      (∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) → κ g = 1)
    {E : Subgroup Γ} {H : Subgroup (SUid σ₀ n)} (hH : HyperLift h κ E H)
    {X Y r : primeFormUnitary h (idGram K n)} (hXE : κ X ∈ E) (hYE : κ Y ∈ E) (hrE : κ r ∈ E)
    (hr1 : κ r ≠ 1)
    (hYr : κ Y ∉ Subgroup.zpowers (κ r))
    (hXcl : κ X ∉ Subgroup.closure ({κ r, κ Y} : Set Γ))
    (hrX : r * X = X * r) (hrY : r * Y = Y * r)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hYX : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {β ν ρ : K} (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1)
    (hν : ν ≠ 0) (hYp : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1)
    (hρ : ρ ≠ 0) (hrp : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ρ ^ p) • 1) :
    H = ⊤ := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσi := hσ.invol
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hn0 : 0 < n := by omega
  have hrs : ∀ c : K, ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 :=
    fun c hc => hr1 (hker' r ⟨c, hc⟩)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set Xm : Matrix (Fin n) (Fin n) K := ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hXm
  set Ym : Matrix (Fin n) (Fin n) K := ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hYm
  set rm : Matrix (Fin n) (Fin n) K := ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hrm
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (a : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) a ↔ M *ᵥ v = a • v := fun M a v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hpowT : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K), M ^ p = c • 1 →
      (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    intro M c hM
    have h2 := congrArg Matrix.toLinAlgEquiv' hM
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hνN := bar_mul_eq_one_of_gu_pow h hp hp2 hpq hn0 hν hYp
  have hρN := bar_mul_eq_one_of_gu_pow h hp hp2 hpq hn0 hρ hrp
  have hrcl : κ r ∈ Subgroup.closure ({κ r, κ Y} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hYcl : κ Y ∈ Subgroup.closure ({κ r, κ Y} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hYr' : Y * r = r * Y := hrY.symm
  have hBm : ∀ t : ℕ, (((Y * r ^ t : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Ym * rm ^ t := fun t => by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val, hYm,
      hrm]
  have hBE : ∀ t : ℕ, κ (Y * r ^ t) ∈ E := fun t => by
    rw [map_mul, map_pow]
    exact E.mul_mem hYE (E.pow_mem hrE t)
  have hBX : ∀ t : ℕ, (((Y * r ^ t : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * Xm =
      ζ • (Xm * (((Y * r ^ t : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) := by
    intro t
    have hc : Commute rm Xm := coe_comm_gu h hrX
    rw [hBm, Matrix.mul_assoc, (hc.pow_left t).eq, ← Matrix.mul_assoc, hYX, Matrix.smul_mul,
      Matrix.mul_assoc]
  have hrB : ∀ t : ℕ, r * (Y * r ^ t) = (Y * r ^ t) * r := fun t => by
    rw [← mul_assoc, hrY, mul_assoc, mul_assoc, (Commute.self_pow r t).eq]
  have hBp : ∀ t : ℕ, (((Y * r ^ t : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) ^ p = ((ν * ρ ^ t) ^ p) • 1 := by
    intro t
    have := pow_word_of_comm_gu h hYr' hYp hrp 1 t
    rw [pow_one] at this
    rw [this]
    congr 1
    rw [pow_one, mul_pow, ← pow_mul, ← pow_mul, mul_comm t p]
  have hμ : ∀ t : ℕ, ν * ρ ^ t ≠ 0 := fun t => mul_ne_zero hν (pow_ne_zero _ hρ)
  have hBr : ∀ t : ℕ, κ (Y * r ^ t) ∉ Subgroup.zpowers (κ r) := by
    intro t hmem
    apply hYr
    have : κ Y = κ (Y * r ^ t) * ((κ r) ^ t)⁻¹ := by
      rw [map_mul, map_pow, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _))
  have hB1 : ∀ t : ℕ, κ (Y * r ^ t) ≠ 1 := fun t h1 => hBr t (h1 ▸ Subgroup.one_mem _)
  have hXB : ∀ t : ℕ, κ X ∉ Subgroup.zpowers (κ (Y * r ^ t)) := by
    intro t hmem
    apply hXcl
    refine (Subgroup.zpowers_le.2 ?_) hmem
    rw [map_mul, map_pow]
    exact Subgroup.mul_mem _ hYcl (Subgroup.pow_mem _ hrcl t)
  have hdim : ∀ (t : ℕ) (l : Fin p), 3 ≤ Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' (((Y * r ^ t : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) ((ν * ρ ^ t) * ζ ^ (l : ℕ))) := by
    intro t l
    by_contra hlt
    push Not at hlt
    have hsup := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ (hμ t) (hpowT _ _ (hBp t))
    have h1 := finrank_iSup_le_sum (K := K) (fun l' : Fin p => Module.End.eigenspace
      (Matrix.toLin' (((Y * r ^ t : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) ((ν * ρ ^ t) * ζ ^ (l' : ℕ)))
    rw [hsup, finrank_top, Module.finrank_fin_fun] at h1
    have h2 : ∀ l' : Fin p, Module.finrank K (Module.End.eigenspace
        (Matrix.toLin' (((Y * r ^ t : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) ((ν * ρ ^ t) * ζ ^ (l' : ℕ))) ≤ 2 := fun l' =>
      (finrank_eigen_le_gu h hζ (hBX t) _ l' l).trans (by omega)
    have h3 := Finset.sum_le_sum (s := Finset.univ) fun l' _ => h2 l'
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
    omega
  have hAll : ∀ (t : ℕ) (l : Fin p), AllCenters H (Module.End.eigenspace
      (Matrix.toLin' (((Y * r ^ t : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) ((ν * ρ ^ t) * ζ ^ (l : ℕ))) := fun t l =>
    allCenters_eigen_nonab_gu h hp hp2 hpq hq2 κ hker' hH hXE (hBE t) hrE hr1 (hB1 t) (hBr t)
      (hXB t) hrX (hrB t) hζ hζN (hBX t) hXp (hμ t) (hBp t) hρ hrp l (hdim t l)
  have hY0 : (((Y * r ^ 0 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Ym := by
    rw [hBm, pow_zero, Matrix.mul_one]
  set W : Fin p → Submodule K (Fin n → K) :=
    fun l => Module.End.eigenspace (Matrix.toLin' Ym) (ν * ζ ^ (l : ℕ)) with hW
  have hWeq : ∀ l : Fin p, W l = Module.End.eigenspace
      (Matrix.toLin' (((Y * r ^ 0 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) ((ν * ρ ^ 0) * ζ ^ (l : ℕ)) := fun l => by
    rw [hY0, pow_zero, mul_one]
  have hWtop : ⨆ l, W l = ⊤ := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hν (hpowT _ _ hYp)
  have horthE : ∀ (s : primeFormUnitary h (idGram K n)) (c : K), c ≠ 0 → h.bar c * c = 1 →
      ∀ a b : Fin p, a ≠ b →
      ∀ u v, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = (c * ζ ^ (a : ℕ)) • u →
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (c * ζ ^ (b : ℕ)) • v →
        herm σ₀ u v = 0 := fun s c hc0 hcN a b hab u v hu hv =>
    herm_eq_zero_of_eigen_gu h hu hv (bar_mul_ne_one h hc0 hcN hζ hζN hab)
  have hWorth : ∀ l l' : Fin p, l ≠ l' → ∀ u ∈ W l, ∀ v ∈ W l', herm σ₀ u v = 0 :=
    fun l l' hll u hu v hv => horthE Y ν hν hνN l l' hll u v ((hmemE _ _ u).1 hu)
      ((hmemE _ _ v).1 hv)
  have hWsep : ∀ l, ((idForm h n).domRestrict₁₂ (W l) (W l)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) W
      (fun l l' hne u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]; exact hWorth l l' hne u hu v hv) hWtop
  have hWON : ∀ l, HasONBasis σ₀ (W l) := by
    intro l
    refine Nonsplit.hasONBasis_of_separatingLeft h (W l) (hWsep l) ?_
    obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
    exact Or.inr ⟨by rw [hWeq]; exact hdim 0 l, s, hs0, by rw [hσb]; exact hs1⟩
  have hWAll : ∀ l, AllCenters H (W l) := fun l => by rw [hWeq]; exact hAll 0 l
  have hW0 : ∀ l, W l ≠ ⊥ := by
    intro l h0
    have := hdim 0 l
    rw [← hWeq, h0, finrank_bot] at this
    omega
  have hYr_lin : Matrix.toLin' Ym * Matrix.toLin' rm = Matrix.toLin' rm * Matrix.toLin' Ym := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, mulVec_mulVec, coe_comm_gu h hrY]
  set J : Fin p × Fin p → Submodule K (Fin n → K) := fun ij =>
    W ij.1 ⊓ Module.End.eigenspace (Matrix.toLin' rm) (ρ * ζ ^ (ij.2 : ℕ)) with hJ
  have hJtop : ⨆ ij, J ij = ⊤ :=
    iSup_inf_eigenspace_eq_top hp hpK hζ hYr_lin hν hρ (hpowT _ _ hYp) (hpowT _ _ hrp)
  have hJorth : ∀ ij ij' : Fin p × Fin p, ij ≠ ij' → ∀ u ∈ J ij, ∀ v ∈ J ij',
      herm σ₀ u v = 0 := by
    intro ij ij' hne u hu v hv
    by_cases h1 : ij.1 = ij'.1
    · have h2 : ij.2 ≠ ij'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact horthE r ρ hρ hρN ij.2 ij'.2 h2 u v ((hmemE _ _ u).1 hu.2) ((hmemE _ _ v).1 hv.2)
    · exact hWorth ij.1 ij'.1 h1 u hu.1 v hv.1
  have hJsep : ∀ ij, ((idForm h n).domRestrict₁₂ (J ij) (J ij)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) J
      (fun ij ij' hne u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]; exact hJorth ij ij' hne u hu v hv) hJtop
  have hJshift : ∀ (l l' c : Fin p), J (l, c) ≠ ⊥ → J (l', c) ≠ ⊥ := by
    intro l l' c hne h0
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set k := (l' : ℕ) + p - l with hk
    have h1 := mulVec_pow_smul_of_qcomm_gu h hYX k l v ((hmemE _ _ v).1 hv.1)
    have hlk : (l : ℕ) + k = l' + p := by have := l.2; omega
    rw [hlk, pow_add, hζ.pow_eq_one, mul_one] at h1
    have h2 : rm *ᵥ ((X ^ k) • v) = (ρ * ζ ^ (c : ℕ)) • ((X ^ k) • v) := by
      rw [smul_def_gu, mulVec_mulVec, coe_comm_gu h (Commute.pow_right hrX k).eq,
        ← mulVec_mulVec, (hmemE _ _ v).1 hv.2, mulVec_smul]
    have hmem : (X ^ k) • v ∈ J (l', c) := ⟨(hmemE _ _ _).2 h1, (hmemE _ _ _).2 h2⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hv0 (by simpa using congrArg (fun w => (X ^ k)⁻¹ • w) hmem)
  have hmix : ∀ l l' : Fin p, l ≠ l' →
      ∃ w₁ ∈ W l, ∃ w₂ ∈ W l', w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ IsCenter H (w₁ + w₂) := by
    intro l l' hll
    obtain ⟨c₁, c₂, hc12, hJ₁, hJ₂⟩ :=
      exists_two_eigen_gu h hζ hpK hp hrX hrY hYX hν hYp hρ hrp hrs l (hW0 l)
    have hJ₂' : J (l', c₂) ≠ ⊥ := hJshift l l' c₂ hJ₂
    obtain ⟨e₁, he₁J, he₁⟩ := exists_unit_of_separatingLeft h hJ₁ (hJsep (l, c₁))
    obtain ⟨e₂, he₂J, he₂⟩ := exists_unit_of_separatingLeft h hJ₂' (hJsep (l', c₂))
    obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
    have hcz : ((c₁ : ℕ) : ZMod p) - ((c₂ : ℕ) : ZMod p) ≠ 0 := by
      intro h0
      apply hc12
      rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt c₁.2,
        Nat.mod_eq_of_lt c₂.2] at h0
      exact Fin.ext h0
    set t : ℕ := ((((l' : ℕ) : ZMod p) - ((l : ℕ) : ZMod p)) *
      (((c₁ : ℕ) : ZMod p) - ((c₂ : ℕ) : ZMod p))⁻¹).val with ht
    have htZ : (t : ZMod p) = (((l' : ℕ) : ZMod p) - ((l : ℕ) : ZMod p)) *
        (((c₁ : ℕ) : ZMod p) - ((c₂ : ℕ) : ZMod p))⁻¹ := ZMod.natCast_zmod_val _
    have hcong : ((l : ℕ) + c₁ * t) % p = ((l' : ℕ) + c₂ * t) % p := by
      rw [← ZMod.natCast_eq_natCast_iff']
      push_cast
      have key : ((c₁ : ℕ) : ZMod p) * t - ((c₂ : ℕ) : ZMod p) * t =
          ((l' : ℕ) : ZMod p) - ((l : ℕ) : ZMod p) := by
        rw [← sub_mul, htZ, mul_comm, mul_assoc, inv_mul_cancel₀ hcz, mul_one]
      linear_combination key
    set kk : Fin p := ⟨((l : ℕ) + c₁ * t) % p, Nat.mod_lt _ hp.pos⟩ with hkk
    have hBv : ∀ (a c : Fin p) (v : Fin n → K), v ∈ J (a, c) →
        (((Y * r ^ t : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ v =
          ((ν * ρ ^ t) * ζ ^ (((a : ℕ) + c * t) % p)) • v := by
      intro a c v hv
      rw [hBm, ← mulVec_mulVec, pow_mulVec_of_eigen ((hmemE _ _ v).1 hv.2), mulVec_smul,
        (hmemE _ _ v).1 hv.1, smul_smul, ← pow_eq_pow_mod hζ]
      congr 1
      rw [pow_add, mul_pow, ← pow_mul]
      ring
    have he₁B := hBv l c₁ e₁ he₁J
    have he₂B := hBv l' c₂ e₂ he₂J
    rw [← hcong] at he₂B
    have hw₂ : u • e₂ ∈ W l' := (W l').smul_mem u he₂J.1
    have he₁0 : e₁ ≠ 0 := by rintro rfl; rw [herm_zero_left] at he₁; exact zero_ne_one he₁
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hu
      exact (neg_ne_zero.mpr one_ne_zero) hu.symm
    have he₂0 : u • e₂ ≠ 0 := by
      rintro h0
      rcases smul_eq_zero.1 h0 with h1 | h1
      · exact hu0 h1
      · rw [h1, herm_zero_left] at he₂; exact zero_ne_one he₂
    refine ⟨e₁, he₁J.1, u • e₂, hw₂, he₁0, he₂0, hAll t kk _ ?_ ?_⟩
    · rw [hmemE, mulVec_add, mulVec_smul, he₁B, he₂B, smul_add, smul_comm u]
    · have h12 := hWorth l l' hll e₁ he₁J.1 (u • e₂) hw₂
      have h21 := hWorth l' l (Ne.symm hll) (u • e₂) hw₂ e₁ he₁J.1
      rw [herm_add_left, herm_add_right, herm_add_right, h12, h21, he₁, herm_smul_left,
        herm_smul_right, he₂, mul_one, hu]
      ring
  have hn4 : 4 ≤ n := by have := hp.two_le; omega
  have : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
  exact Centers.eq_top_of_blocks hσ hn4 W hWON hWorth hWAll hmix hWtop

end BlockC

section ChoiceC

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

variable (h : UnitaryFieldData ℓ f K)

theorem exists_comm_scalar_gu (hn : 0 < n) {Γ : Type*} [Group Γ]
    (κ : primeFormUnitary h (idGram K n) →* Γ)
    (hker : ∀ g ∈ κ.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {E : Subgroup Γ} (hE : IsElemAbelian p E) {a b : primeFormUnitary h (idGram K n)}
    (ha : κ a ∈ E) (hb : κ b ∈ E) :
    ∃ c : K, ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • (((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧ c ^ p = 1 := by
  have hcommE : κ b * κ a = κ a * κ b :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨κ b, hb⟩ ⟨κ a, ha⟩)
  have h1 : κ (b * a * b⁻¹ * a⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommE]
    group
  obtain ⟨c, hc⟩ := hker _ h1
  have hrel : ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • (((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have e : b * a = (b * a * b⁻¹ * a⁻¹) * (a * b) := by group
    have := congrArg (fun g : primeFormUnitary h (idGram K n) =>
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) e
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rw [this]
    have hc' : ((((b * a * b⁻¹ * a⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) = c • 1 := hc
    simp only [Subgroup.coe_mul, Units.val_mul] at hc'
    rw [hc', Matrix.smul_mul, Matrix.one_mul]
  refine ⟨c, hrel, ?_⟩
  have hap : κ (a ^ p) = 1 := by rw [map_pow]; exact hE.2 _ ha
  obtain ⟨α, hα⟩ := hker _ hap
  have hα' : (((a : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1 := by
    rw [← hα, Subgroup.coe_pow]
  have hα0 : α ≠ 0 := scalar_ne_zero_of_matPow hn (by rw [← Units.val_pow_eq_pow_val]; exact hα')
  exact pow_eq_one_of_smul_comm_p hn hα0 hα' hrel

theorem comm_of_scalar_gu {z : primeFormUnitary h (idGram K n)} {c : K}
    (hz : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    (s : primeFormUnitary h (idGram K n)) : z * s = s * z := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hz, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem eq_mul_scalar_gu {Γ : Type*} [Group Γ] (κ : primeFormUnitary h (idGram K n) →* Γ)
    (hker : ∀ g ∈ κ.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {s w : primeFormUnitary h (idGram K n)} (hsw : κ w = κ s) :
    ∃ z : primeFormUnitary h (idGram K n),
      (∃ c : K, ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) ∧ s = w * z :=
  ⟨w⁻¹ * s, hker _ (by rw [MonoidHom.mem_ker, map_mul, map_inv, hsw, inv_mul_cancel]),
    by rw [mul_inv_cancel_left]⟩

theorem exists_radical_gu (hp : p.Prime) (hn : 0 < n) {Γ : Type*} [Group Γ] [Finite Γ]
    (κ : primeFormUnitary h (idGram K n) →* Γ) {E : Subgroup Γ}
    (hEκ : ∀ e ∈ E, ∃ a : primeFormUnitary h (idGram K n), κ a = e)
    (hker : ∀ g ∈ κ.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {a b : primeFormUnitary h (idGram K n)} (ha : κ a ∈ E) (hb : κ b ∈ E) (hab : a * b ≠ b * a) :
    κ a ≠ 1 ∧ κ b ∉ Subgroup.zpowers (κ a) ∧
    ∃ r : primeFormUnitary h (idGram K n), κ r ∈ E ∧
      κ r ∉ Subgroup.closure ({κ a, κ b} : Set Γ) ∧
      r * a = a * r ∧ r * b = b * r ∧
      ∀ s : primeFormUnitary h (idGram K n), κ s ∈ E → r * s = s * r := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have ha1 : κ a ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := hker a h1
    exact hab (comm_of_scalar_gu h hc b)
  have hba : κ b ∉ Subgroup.zpowers (κ a) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    obtain ⟨z, hz, hbz⟩ := eq_mul_scalar_gu h κ hker (s := b) (w := a ^ k) (by rw [map_zpow, hk])
    apply hab
    obtain ⟨c, hc⟩ := hz
    have hza : z * a = a * z := comm_of_scalar_gu h hc a
    rw [hbz]
    calc a * (a ^ k * z) = a ^ (1 + k) * z := by rw [← mul_assoc, ← _root_.zpow_one_add]
      _ = a ^ (k + 1) * z := by rw [add_comm]
      _ = a ^ k * a * z := by rw [_root_.zpow_add_one]
      _ = a ^ k * z * a := by rw [mul_assoc, ← hza, ← mul_assoc]
  obtain ⟨c, hcba, hcp⟩ := exists_comm_scalar_gu h hn κ hker hE ha hb
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hab
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hcba, one_smul]
  have hζc : IsPrimitiveRoot c p := by
    rw [← orderOf_eq_prime hcp hc1]
    exact IsPrimitiveRoot.orderOf c
  have hc0 : c ≠ 0 := hζc.ne_zero hp.ne_zero
  have hc2 : Nat.card (Subgroup.closure ({κ a, κ b} : Set Γ)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE ha hb ha1 hba
  obtain ⟨e₀, he₀E, he₀⟩ := exists_not_mem_of_card hp hcard (k := 2) (by norm_num) hc2
  obtain ⟨e, rfl⟩ := hEκ e₀ he₀E
  obtain ⟨d₁, hd₁, hd₁p⟩ := exists_comm_scalar_gu h hn κ hker hE he₀E ha
  obtain ⟨d₂, hd₂, hd₂p⟩ := exists_comm_scalar_gu h hn κ hker hE he₀E hb
  obtain ⟨s₁, hs₁, hcs₁⟩ := hζc.eq_pow_of_pow_eq_one hd₁p
  obtain ⟨s₂, hs₂, hcs₂⟩ := hζc.eq_pow_of_pow_eq_one hd₂p
  set am : Matrix (Fin n) (Fin n) K := ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with ham
  set bm : Matrix (Fin n) (Fin n) K := ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hbm
  set em : Matrix (Fin n) (Fin n) K := ((e : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hem
  set i := p - s₂ with hi
  set j := s₁ with hj
  set r := e * a ^ i * b ^ j with hr
  have hrm : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = em * am ^ i * bm ^ j := by
    simp only [hr, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      hem, ham, hbm]
  have hbaj : bm ^ j * am = c ^ j • (am * bm ^ j) := qcommMat_pow_left hcba j
  have hbai : bm * am ^ i = c ^ i • (am ^ i * bm) := by
    have := qcommMat_pow_pow hcba i 1
    simpa only [pow_one, mul_one] using this
  have hra : r * a = a * r := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hrm]
    calc em * am ^ i * bm ^ j * am = em * am ^ i * (bm ^ j * am) := by
          simp only [Matrix.mul_assoc]
      _ = c ^ j • (em * (am ^ i * am) * bm ^ j) := by
          rw [hbaj, Matrix.mul_smul]
          simp only [Matrix.mul_assoc]
      _ = c ^ j • (em * am * am ^ i * bm ^ j) := by
          rw [← pow_succ, pow_succ']
          simp only [Matrix.mul_assoc]
      _ = (d₁ • (em * am)) * am ^ i * bm ^ j := by
          rw [hcs₁, Matrix.smul_mul, Matrix.smul_mul]
      _ = am * (em * am ^ i * bm ^ j) := by
          rw [← hd₁]
          simp only [Matrix.mul_assoc]
  have hrb : r * b = b * r := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hrm]
    have hci : d₂ * c ^ i = 1 := by
      rw [← hcs₂, hi, ← pow_add, Nat.add_sub_cancel' hs₂.le, hcp]
    symm
    calc bm * (em * am ^ i * bm ^ j) = (bm * em) * am ^ i * bm ^ j := by
          simp only [Matrix.mul_assoc]
      _ = d₂ • (em * (bm * am ^ i) * bm ^ j) := by
          rw [hd₂, Matrix.smul_mul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
      _ = (d₂ * c ^ i) • (em * am ^ i * (bm * bm ^ j)) := by
          rw [hbai, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
          simp only [Matrix.mul_assoc]
      _ = em * am ^ i * bm ^ j * bm := by
          rw [hci, one_smul, ← pow_succ', pow_succ]
          simp only [Matrix.mul_assoc]
  have hacl : κ a ∈ Subgroup.closure ({κ a, κ b} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbcl : κ b ∈ Subgroup.closure ({κ a, κ b} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hrE : κ r ∈ E := by
    rw [hr, map_mul, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.mul_mem he₀E (E.pow_mem ha _)) (E.pow_mem hb _)
  have hrcl : κ r ∉ Subgroup.closure ({κ a, κ b} : Set Γ) := by
    intro hmem
    apply he₀
    have : κ e = κ r * ((κ a) ^ i * (κ b) ^ j)⁻¹ := by
      rw [hr, map_mul, map_mul, map_pow, map_pow]
      group
    rw [this]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hacl _) (Subgroup.pow_mem _ hbcl _)))
  refine ⟨ha1, hba, r, hrE, hrcl, hra, hrb, fun s hs => ?_⟩
  have hcl3 := closure_triple_eq hp hE hcard ha hb hrE ha1 hba hrcl
  have hsmem : κ s ∈ (Subgroup.closure ({a, b, r} : Set (primeFormUnitary h (idGram K n)))).map κ := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      hcl3]
    exact hs
  obtain ⟨w, hw, hws⟩ := hsmem
  have hwr : Subgroup.closure ({a, b, r} : Set (primeFormUnitary h (idGram K n))) ≤
      Subgroup.centralizer {r} := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl | rfl
    · exact hra.symm
    · exact hrb.symm
    · rfl
  have hrw : r * w = w * r := (Subgroup.mem_centralizer_singleton_iff.1 (hwr hw)).symm
  obtain ⟨z, ⟨cz, hcz⟩, rfl⟩ := eq_mul_scalar_gu h κ hker hws
  rw [← mul_assoc, hrw, mul_assoc, ← comm_of_scalar_gu h hcz r, mul_assoc]

theorem exists_heis_pair_gu (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hn : 0 < n) {Γ : Type*} [Group Γ] [Finite Γ]
    (κ : primeFormUnitary h (idGram K n) →* Γ)
    (hker : ∀ g ∈ κ.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {E : Subgroup Γ} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {a b r : primeFormUnitary h (idGram K n)} (ha : κ a ∈ E) (hb : κ b ∈ E) (hab : a * b ≠ b * a)
    (ha1 : κ a ≠ 1)
    (hba : κ b ∉ Subgroup.zpowers (κ a)) (hrE : κ r ∈ E)
    (hrcl : κ r ∉ Subgroup.closure ({κ a, κ b} : Set Γ)) (hra : r * a = a * r)
    (hrb : r * b = b * r) :
    ∃ (X Y : primeFormUnitary h (idGram K n)) (ζ ν : K), κ X ∈ E ∧ κ Y ∈ E ∧
      κ Y ∉ Subgroup.zpowers (κ r) ∧
      κ X ∉ Subgroup.closure ({κ r, κ Y} : Set Γ) ∧ r * X = X * r ∧ r * Y = Y * r ∧
      IsPrimitiveRoot ζ p ∧ h.bar ζ * ζ = 1 ∧
      ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧
      ν ≠ 0 ∧ ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1 := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hexp : ∀ e ∈ E, e ^ p = 1 := hE.2
  obtain ⟨c, hcba, hcp⟩ := exists_comm_scalar_gu h hn κ hker hE ha hb
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hab
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hcba, one_smul]
  have hζc : IsPrimitiveRoot c p := by
    rw [← orderOf_eq_prime hcp hc1]
    exact IsPrimitiveRoot.orderOf c
  have hc0 : c ≠ 0 := hζc.ne_zero hp.ne_zero
  set am : Matrix (Fin n) (Fin n) K := ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with ham
  set bm : Matrix (Fin n) (Fin n) K := ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hbm
  have hap : κ (a ^ p) = 1 := by rw [map_pow]; exact hexp _ ha
  have hbp : κ (b ^ p) = 1 := by rw [map_pow]; exact hexp _ hb
  obtain ⟨α, hα⟩ := hker _ hap
  obtain ⟨β, hβ⟩ := hker _ hbp
  have hα' : am ^ p = α • 1 := by rw [← hα, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hβ' : bm ^ p = β • 1 := by rw [← hβ, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hα0 : α ≠ 0 := scalar_ne_zero_of_matPow hn hα'
  have hβ0 : β ≠ 0 := scalar_ne_zero_of_matPow hn hβ'
  obtain ⟨i, j, hij, ν, hν⟩ :=
    exists_pth_power_word hp (dvd_card_sub_one_of_unitary h hpq) hα0 hβ0
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hν
    exact mul_ne_zero (pow_ne_zero _ hα0) (pow_ne_zero _ hβ0) hν.symm
  set Y := a ^ i * b ^ j with hY
  have hYm : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = am ^ i * bm ^ j := by
    simp only [hY, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      ham, hbm]
  have hYp : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1 := by
    rw [hYm, pow_word_p hp hp2 hα' hβ' hcba hcp i j, hν]
  have hYE : κ Y ∈ E := by
    rw [hY, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem ha _) (E.pow_mem hb _)
  have hrY : r * Y = Y * r := ((Commute.pow_right hra i).mul_right (Commute.pow_right hrb j)).eq
  have hacl : κ a ∈ Subgroup.closure ({κ a, κ b} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbcl : κ b ∈ Subgroup.closure ({κ a, κ b} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hYcl : κ Y ∈ Subgroup.closure ({κ a, κ b} : Set Γ) := by
    rw [hY, map_mul, map_pow, map_pow]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hacl _) (Subgroup.pow_mem _ hbcl _)
  have hY1 : κ Y ≠ 1 := by
    intro h1
    rw [hY, map_mul, map_pow, map_pow] at h1
    exact hij (dvd_of_pow_mul_pow_eq_one hp (hexp _ ha) (hexp _ hb) ha1 hba h1)
  have hr1 : κ r ≠ 1 := fun h1 => hrcl (h1 ▸ Subgroup.one_mem _)
  have hYr : κ Y ∉ Subgroup.zpowers (κ r) := by
    intro hmem
    apply hrcl
    have hle : Subgroup.zpowers (κ Y) ≤ Subgroup.zpowers (κ r) := Subgroup.zpowers_le.2 hmem
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hexp _ hrE) hr1,
        orderOf_eq_prime (hexp _ hYE) hY1])
    have : κ r ∈ Subgroup.zpowers (κ Y) := heq ▸ Subgroup.mem_zpowers (κ r)
    exact Subgroup.zpowers_le.2 hYcl this
  obtain ⟨X, ζ, hXab, hζ, hYX⟩ : ∃ (X : primeFormUnitary h (idGram K n)) (ζ : K), (X = a ∨ X = b) ∧
      IsPrimitiveRoot ζ p ∧
      ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    by_cases hj : p ∣ j
    · have hi : ¬ p ∣ i := fun hi => hij ⟨hi, hj⟩
      refine ⟨b, (c ^ i)⁻¹, Or.inr rfl,
        (hζc.pow_of_coprime i (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hi))).inv,
        ?_⟩
      rw [hYm]
      exact planeW_comm_caseII hcba hc0 i j
    · refine ⟨a, c ^ j, Or.inl rfl,
        hζc.pow_of_coprime j (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hj)), ?_⟩
      rw [hYm]
      exact planeW_comm_caseI hcba i j
  have hXE : κ X ∈ E := by rcases hXab with rfl | rfl <;> assumption
  have hXcl' : κ X ∈ Subgroup.closure ({κ a, κ b} : Set Γ) := by
    rcases hXab with rfl | rfl <;> assumption
  have hrX : r * X = X * r := by rcases hXab with rfl | rfl <;> assumption
  have hζN : h.bar ζ * ζ = 1 := by
    rw [h.bar_apply, ← pow_succ]
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨X, Y, ζ, ν, hXE, hYE, hYr, ?_, hrX, hrY, hζ, hζN, hYX, hν0, hYp⟩
  have hXY : κ X ∉ Subgroup.zpowers (κ Y) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    obtain ⟨z, ⟨cz, hcz⟩, hXz⟩ := eq_mul_scalar_gu h κ hker (s := X) (w := Y ^ k)
      (by rw [map_zpow, hk])
    have hcomm : X * Y = Y * X := by
      rw [hXz, mul_assoc, comm_of_scalar_gu h hcz Y, ← mul_assoc, ← (Commute.self_zpow Y k).eq,
        mul_assoc]
    have hM := coe_comm_gu h hcomm
    rw [← hM] at hYX
    have h1 : (1 - ζ) • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 0 := by
      rw [sub_smul, one_smul, ← hYX, sub_self]
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact hζ.ne_one hp.one_lt (sub_eq_zero.1 h2).symm
    · have h3 : (((X * Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = 0 := by
        simp only [Subgroup.coe_mul, Units.val_mul]
        exact h2
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact Units.ne_zero _ h3
  intro hmem
  have hcXY : Nat.card (Subgroup.closure ({κ Y, κ X} : Set Γ)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hYE hXE hY1 hXY
  have hcab : Nat.card (Subgroup.closure ({κ a, κ b} : Set Γ)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE ha hb ha1 hba
  have hcrY : Nat.card (Subgroup.closure ({κ r, κ Y} : Set Γ)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hrE hYE hr1 (fun hm => hYr hm)
  have hle1 : Subgroup.closure ({κ Y, κ X} : Set Γ) ≤ Subgroup.closure ({κ a, κ b} : Set Γ) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hYcl, Set.singleton_subset_iff.2 hXcl'⟩)
  have hle2 : Subgroup.closure ({κ Y, κ X} : Set Γ) ≤ Subgroup.closure ({κ r, κ Y} : Set Γ) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2
      ⟨Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), Set.singleton_subset_iff.2 hmem⟩)
  have heq1 := Subgroup.eq_of_le_of_card_ge hle1 (by rw [hcXY, hcab])
  have heq2 := Subgroup.eq_of_le_of_card_ge hle2 (by rw [hcXY, hcrY])
  apply hrcl
  rw [← heq1, heq2]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

end ChoiceC

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

end
