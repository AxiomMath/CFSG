module

public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

open Module Module.End Matrix Polynomial

namespace CFSG.GH74.Generic.S1

variable {Ω : Type*} [Field Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kl3cl_pow_mulVec_of_eig (A : Matrix ι ι Ω) {μ : Ω} {v : ι → Ω} (h : A *ᵥ v = μ • v) (k : ℕ) :
    A ^ k *ᵥ v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, ← pow_succ]

theorem kl3cl_exists_eig_ne_one [IsAlgClosed Ω] {n : ℕ} (hn : (n : Ω) ≠ 0) (A : Matrix ι ι Ω)
    (hA : A ^ n = 1) (hne : A ≠ 1) :
    ∃ μ : Ω, μ ≠ 1 ∧ μ ^ n = 1 ∧ ∃ v : ι → Ω, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  classical
  set f : Module.End Ω (ι → Ω) := Matrix.toLinAlgEquiv' A with hf
  have hfn : f ^ n = 1 := by
    rw [hf, ← map_pow, hA, map_one]
  have hsq : Squarefree ((X : Ω[X]) ^ n - 1) := by
    have := (separable_X_pow_sub_C (1 : Ω) hn one_ne_zero).squarefree
    simpa using this
  have haeval : Polynomial.aeval f ((X : Ω[X]) ^ n - 1) = 0 := by
    simp [hfn]
  have hss : f.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq haeval
  have htop := hss.iSup_eigenspace_eq_top
  by_contra hcon
  push Not at hcon
  have hbot : ∀ μ : Ω, μ ≠ 1 → f.eigenspace μ = ⊥ := by
    intro μ hμ
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    have hAv : A *ᵥ v = μ • v := by
      have := Module.End.mem_eigenspace_iff.1 hv
      simpa [hf, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply] using this
    have hpow : A ^ n *ᵥ v = μ ^ n • v := kl3cl_pow_mulVec_of_eig A hAv n
    have hμn : μ ^ n = 1 := by
      rw [hA, Matrix.one_mulVec] at hpow
      have h1 : (μ ^ n - 1) • v = 0 := by rw [sub_smul, ← hpow, one_smul, sub_self]
      have := (smul_eq_zero.1 h1).resolve_right hv0
      exact sub_eq_zero.1 this
    exact hcon μ hμ hμn v hv0 hAv
  have h1top : f.eigenspace 1 = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ = 1
    · rw [hμ]
    · rw [hbot μ hμ]; exact bot_le
  apply hne
  have hall : ∀ v : ι → Ω, A *ᵥ v = v := by
    intro v
    have hv : v ∈ f.eigenspace 1 := by rw [h1top]; trivial
    have := Module.End.mem_eigenspace_iff.1 hv
    simpa [hf, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply] using this
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this


theorem kl3cl_frobenius_dim [IsAlgClosed Ω] (h13 : ((13 : ℕ) : Ω) ≠ 0) (A B : Matrix ι ι Ω)
    (hA : A ^ 13 = 1) (hAne : A ≠ 1) (hBinj : ∀ v, B *ᵥ v = 0 → v = 0)
    (hBA : B * A = A ^ 3 * B) (r : ℕ) (hr : r % 13 = 1 ∨ r % 13 = 3 ∨ r % 13 = 9)
    (hdual : ∀ μ : Ω, μ ^ 13 = 1 → (∃ v, v ≠ 0 ∧ A *ᵥ v = μ • v) →
      ∃ v, v ≠ 0 ∧ A *ᵥ v = (μ⁻¹) ^ r • v) :
    6 ≤ Fintype.card ι := by
  classical
  obtain ⟨μ, hμ1, hμ13, v₀, hv₀, hAv₀⟩ := kl3cl_exists_eig_ne_one h13 A hA hAne
  have hFact : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hord : orderOf μ = 13 := orderOf_eq_prime hμ13 hμ1
  let Ev : Ω → Prop := fun c => ∃ v : ι → Ω, v ≠ 0 ∧ A *ᵥ v = c • v
  have hA27 : A ^ 27 = A := by
    calc A ^ 27 = (A ^ 13) ^ 2 * A := by rw [← pow_mul, ← pow_succ]
      _ = A := by rw [hA]; simp
  have hEv9 : ∀ c, Ev c → Ev (c ^ 9) := by
    rintro c ⟨v, hv, hAv⟩
    refine ⟨B *ᵥ v, fun h => hv (hBinj v h), ?_⟩
    have h1 : A ^ 3 *ᵥ (B *ᵥ v) = c • (B *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← hBA, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul]
    have h2 : (A ^ 3) ^ 9 *ᵥ (B *ᵥ v) = c ^ 9 • (B *ᵥ v) := kl3cl_pow_mulVec_of_eig (A ^ 3) h1 9
    rwa [← pow_mul, show 3 * 9 = 27 by norm_num, hA27] at h2
  have hmod : ∀ k : ℕ, μ ^ k = μ ^ (k % 13) := fun k => pow_eq_pow_mod k hμ13
  have hEvk : ∀ k : ℕ, Ev (μ ^ k) → Ev (μ ^ ((9 * k) % 13)) := by
    intro k hk
    have := hEv9 _ hk
    rwa [← pow_mul, mul_comm, hmod] at this
  have hEv0 : Ev μ := ⟨v₀, hv₀, hAv₀⟩
  have hEvdual : Ev (μ ^ ((12 * r) % 13)) := by
    obtain ⟨v, hv, hAv⟩ := hdual μ hμ13 ⟨v₀, hv₀, hAv₀⟩
    refine ⟨v, hv, ?_⟩
    have hinv : μ⁻¹ = μ ^ 12 := by
      have : μ * μ ^ 12 = 1 := by rw [← pow_succ']; exact hμ13
      exact inv_eq_of_mul_eq_one_right this
    rw [hinv, ← pow_mul, hmod (12 * r)] at hAv
    exact hAv
  have e1 : Ev (μ ^ ((9 * 1) % 13)) := hEvk 1 (by simpa using hEv0)
  have e2 : Ev (μ ^ ((9 * 9) % 13)) := hEvk 9 (by
    have := hEvk 1 (by simpa using hEv0); simpa using this)
  have hclass : Ev (μ ^ 12) ∧ Ev (μ ^ 4) ∧ Ev (μ ^ 10) := by
    rcases hr with hr | hr | hr
    · have h12 : Ev (μ ^ 12) := by
        have : (12 * r) % 13 = 12 := by omega
        rwa [this] at hEvdual
      have h4 : Ev (μ ^ 4) := by have := hEvk 12 h12; simpa using this
      have h10 : Ev (μ ^ 10) := by have := hEvk 4 h4; simpa using this
      exact ⟨h12, h4, h10⟩
    · have h10 : Ev (μ ^ 10) := by
        have : (12 * r) % 13 = 10 := by omega
        rwa [this] at hEvdual
      have h12 : Ev (μ ^ 12) := by have := hEvk 10 h10; simpa using this
      have h4 : Ev (μ ^ 4) := by have := hEvk 12 h12; simpa using this
      exact ⟨h12, h4, h10⟩
    · have h4 : Ev (μ ^ 4) := by
        have : (12 * r) % 13 = 4 := by omega
        rwa [this] at hEvdual
      have h10 : Ev (μ ^ 10) := by have := hEvk 4 h4; simpa using this
      have h12 : Ev (μ ^ 12) := by have := hEvk 10 h10; simpa using this
      exact ⟨h12, h4, h10⟩
  have h9 : Ev (μ ^ 9) := by simpa using e1
  have h3 : Ev (μ ^ 3) := by simpa using e2
  have h1 : Ev (μ ^ 1) := by simpa using hEv0
  let exps : Fin 6 → ℕ := ![1, 9, 3, 12, 4, 10]
  have hall : ∀ i : Fin 6, Ev (μ ^ exps i) := by
    intro i
    fin_cases i
    · exact h1
    · exact h9
    · exact h3
    · exact hclass.1
    · exact hclass.2.1
    · exact hclass.2.2
  choose vec hvec using hall
  have hinj : Function.Injective fun i : Fin 6 => μ ^ exps i := by
    intro i j hij
    have hprim : IsPrimitiveRoot μ 13 := hord ▸ IsPrimitiveRoot.orderOf μ
    have hlt : ∀ k : Fin 6, exps k < 13 := by decide
    have hexps : ∀ i j : Fin 6, exps i = exps j → i = j := by decide
    exact hexps i j (hprim.pow_inj (hlt i) (hlt j) hij)
  have hli : LinearIndependent Ω vec := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) (fun i => μ ^ exps i) hinj
      vec ?_
    intro i
    refine ⟨?_, (hvec i).1⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact (hvec i).2
  have := hli.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this


theorem kl3cl_heisenberg_dim [IsAlgClosed Ω] (h3 : ((3 : ℕ) : Ω) ≠ 0) (A B T S : Matrix ι ι Ω)
    (hT3 : T ^ 3 = 1) (hTne : T ≠ 1) (hTA : T * A = A * T) (hTB : T * B = B * T)
    (hAB : A * B = T * B * A) (hAinj : ∀ v, A *ᵥ v = 0 → v = 0) (hBinj : ∀ v, B *ᵥ v = 0 → v = 0)
    (hSinj : ∀ v, S *ᵥ v = 0 → v = 0) (hST : S * T = T ^ 2 * S) :
    6 ≤ Fintype.card ι := by
  classical
  obtain ⟨μ, hμ1, hμ3, v₀, hv₀, hTv₀⟩ := kl3cl_exists_eig_ne_one h3 T hT3 hTne
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ3; simp at hμ3
  have hμ2 : μ ^ 2 ≠ 1 := fun h => hμ1 (by
    calc μ = μ ^ 2 * μ := by rw [h, one_mul]
      _ = μ ^ 3 := (pow_succ μ 2).symm
      _ = 1 := hμ3)
  let fT : Module.End Ω (ι → Ω) := Matrix.toLin' T
  have hfT : ∀ (κ : Ω) (v : ι → Ω), v ∈ fT.eigenspace κ ↔ T *ᵥ v = κ • v := fun κ v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hdim3 : ∀ κ : Ω, κ ≠ 1 → κ ^ 2 ≠ 1 → κ ≠ 0 → (∃ w : ι → Ω, w ≠ 0 ∧ T *ᵥ w = κ • w) →
      3 ≤ Module.finrank Ω ↥(fT.eigenspace κ) := by
    intro κ hκ1 hκ2 hκ0 ⟨w, hw0, hTw⟩
    set N := fT.eigenspace κ with hN
    have hpres : ∀ X : Matrix ι ι Ω, T * X = X * T → ∀ x : ι → Ω, T *ᵥ x = κ • x →
        T *ᵥ (X *ᵥ x) = κ • (X *ᵥ x) := by
      intro X hX x hx
      rw [Matrix.mulVec_mulVec, hX, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    have hAN : ∀ x ∈ N, Matrix.toLin' A x ∈ N := by
      intro x hx
      rw [hN, hfT] at hx ⊢
      rw [Matrix.toLin'_apply]
      exact hpres A hTA x hx
    have hnontriv : Nontrivial N := ⟨⟨⟨w, (hfT κ w).2 hTw⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
    let fA : Module.End Ω N := LinearMap.restrict (Matrix.toLin' A) hAN
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue fA
    obtain ⟨x, hx⟩ := hlam.exists_hasEigenvector
    have hxN : T *ᵥ (x : ι → Ω) = κ • (x : ι → Ω) := (hfT κ x).1 x.2
    have hxne : (x : ι → Ω) ≠ 0 := fun h => hx.2 (Subtype.ext h)
    have hAx : A *ᵥ (x : ι → Ω) = lam • (x : ι → Ω) := by
      have := Module.End.mem_eigenspace_iff.1 hx.1
      have h2 := congrArg Subtype.val this
      simpa [fA, LinearMap.coe_restrict_apply, Matrix.toLin'_apply] using h2
    have hlam0 : lam ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hAx
      exact hxne (hAinj _ hAx)
    set v₁ : ι → Ω := (x : ι → Ω) with hv₁
    set v₂ : ι → Ω := B *ᵥ v₁ with hv₂
    set v₃ : ι → Ω := B *ᵥ v₂ with hv₃
    have hv₂T : T *ᵥ v₂ = κ • v₂ := hpres B hTB v₁ hxN
    have hv₃T : T *ᵥ v₃ = κ • v₃ := hpres B hTB v₂ hv₂T
    have hAv₂ : A *ᵥ v₂ = (lam * κ) • v₂ := by
      calc A *ᵥ v₂ = (A * B) *ᵥ v₁ := by rw [hv₂, Matrix.mulVec_mulVec]
        _ = T *ᵥ (B *ᵥ (A *ᵥ v₁)) := by
          rw [hAB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        _ = (lam * κ) • v₂ := by
          rw [hAx, Matrix.mulVec_smul, Matrix.mulVec_smul, ← hv₂, hv₂T, smul_smul]
    have hAv₃ : A *ᵥ v₃ = (lam * κ * κ) • v₃ := by
      calc A *ᵥ v₃ = (A * B) *ᵥ v₂ := by rw [hv₃, Matrix.mulVec_mulVec]
        _ = T *ᵥ (B *ᵥ (A *ᵥ v₂)) := by
          rw [hAB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        _ = (lam * κ * κ) • v₃ := by
          rw [hAv₂, Matrix.mulVec_smul, Matrix.mulVec_smul, ← hv₃, hv₃T, smul_smul]
    have hne₂ : v₂ ≠ 0 := fun h => hxne (hBinj _ h)
    have hne₃ : v₃ ≠ 0 := fun h => hne₂ (hBinj _ h)
    let vv : Fin 3 → (ι → Ω) := ![v₁, v₂, v₃]
    let ev : Fin 3 → Ω := ![lam, lam * κ, lam * κ * κ]
    have hκκ : κ * κ ≠ 1 := by rwa [← sq]
    have h01 : lam ≠ lam * κ := fun h =>
      hκ1 (mul_left_cancel₀ hlam0 (h.symm.trans (mul_one lam).symm))
    have h02 : lam ≠ lam * κ * κ := fun h => by
      rw [mul_assoc] at h
      exact hκκ (mul_left_cancel₀ hlam0 (h.symm.trans (mul_one lam).symm))
    have h12 : lam * κ ≠ lam * κ * κ := fun h =>
      hκ1 (mul_left_cancel₀ (mul_ne_zero hlam0 hκ0) (h.symm.trans (mul_one (lam * κ)).symm))
    have hevinj : Function.Injective ev := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd (show lam = lam * κ from hij) h01
      · exact absurd (show lam = lam * κ * κ from hij) h02
      · exact absurd (show lam * κ = lam from hij) (Ne.symm h01)
      · rfl
      · exact absurd (show lam * κ = lam * κ * κ from hij) h12
      · exact absurd (show lam * κ * κ = lam from hij) (Ne.symm h02)
      · exact absurd (show lam * κ * κ = lam * κ from hij) (Ne.symm h12)
      · rfl
    have hli : LinearIndependent Ω vv := by
      refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) ev hevinj vv ?_
      intro i
      refine ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        fin_cases i
        · exact hAx
        · exact hAv₂
        · exact hAv₃
      · fin_cases i
        · exact hxne
        · exact hne₂
        · exact hne₃
    have hmem : ∀ i : Fin 3, vv i ∈ N := by
      intro i
      rw [hN, hfT]
      fin_cases i
      · exact hxN
      · exact hv₂T
      · exact hv₃T
    let ww : Fin 3 → N := fun i => ⟨vv i, hmem i⟩
    have hww : LinearIndependent Ω ww := LinearIndependent.of_comp N.subtype hli
    have := hww.fintype_card_le_finrank
    simpa using this
  have hV1 := hdim3 μ hμ1 hμ2 hμ0 ⟨v₀, hv₀, hTv₀⟩
  have hTS : T *ᵥ (S *ᵥ v₀) = (μ ^ 2) • (S *ᵥ v₀) := by
    have h1 : T ^ 2 *ᵥ (S *ᵥ v₀) = μ • (S *ᵥ v₀) := by
      rw [Matrix.mulVec_mulVec, ← hST, ← Matrix.mulVec_mulVec, hTv₀, Matrix.mulVec_smul]
    have h2 : S *ᵥ v₀ = μ • (T *ᵥ (S *ᵥ v₀)) := by
      calc S *ᵥ v₀ = T ^ 3 *ᵥ (S *ᵥ v₀) := by rw [hT3, Matrix.one_mulVec]
        _ = T *ᵥ (T ^ 2 *ᵥ (S *ᵥ v₀)) := by rw [Matrix.mulVec_mulVec _ T (T ^ 2), ← pow_succ']
        _ = μ • (T *ᵥ (S *ᵥ v₀)) := by rw [h1, Matrix.mulVec_smul]
    calc T *ᵥ (S *ᵥ v₀) = (μ ^ 2 * μ) • (T *ᵥ (S *ᵥ v₀)) := by
          rw [← pow_succ, hμ3, one_smul]
      _ = (μ ^ 2) • (S *ᵥ v₀) := by rw [mul_smul, ← h2]
  have hμ4 : (μ ^ 2) ^ 2 ≠ 1 := by
    have h : (μ ^ 2) ^ 2 = μ := by
      calc (μ ^ 2) ^ 2 = μ ^ 3 * μ := by ring
        _ = μ := by rw [hμ3, one_mul]
    rw [h]; exact hμ1
  have hS0 : S *ᵥ v₀ ≠ 0 := fun h => hv₀ (hSinj _ h)
  have hV2 := hdim3 (μ ^ 2) hμ2 hμ4 (pow_ne_zero 2 hμ0) ⟨S *ᵥ v₀, hS0, hTS⟩
  have hne : μ ≠ μ ^ 2 := by
    intro h
    apply hμ1
    have : μ * 1 = μ * μ := by rw [mul_one, ← sq]; exact h
    exact (mul_left_cancel₀ hμ0 this).symm
  have hdisj : Disjoint (fT.eigenspace μ) (fT.eigenspace (μ ^ 2)) :=
    (Module.End.eigenspaces_iSupIndep fT).pairwiseDisjoint hne
  have hinf : fT.eigenspace μ ⊓ fT.eigenspace (μ ^ 2) = ⊥ := disjoint_iff.1 hdisj
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (fT.eigenspace μ) (fT.eigenspace (μ ^ 2))
  rw [hinf, finrank_bot, add_zero] at hsum
  have hle := Submodule.finrank_le (fT.eigenspace μ ⊔ fT.eigenspace (μ ^ 2))
  rw [Module.finrank_fintype_fun_eq_card] at hle
  omega

end CFSG.GH74.Generic.S1
