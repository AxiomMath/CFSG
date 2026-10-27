module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding.LeviBlock
open scoped Pointwise

section Flag

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ} {h : UnitaryFieldData p f K}

theorem gl_mul_smul {ι : Type} [Fintype ι] [DecidableEq ι] (a b : GL ι K)
    (W : Submodule K (ι → K)) : (a * b) • W = a • (b • W) :=
  mul_smul a b W

theorem coordImage_hypFlag (hε : ε ≤ 1) (σ : K ≃+* K) {c : ℕ} (hc : c ≤ 2 * r + ε) :
    coordImage σ (hypFlag h r ε c) = hypFlag h r ε c := by
  rw [hypFlag_eq_posFlag h hε hc]
  ext v
  rw [mem_coordImage, mem_posFlag, mem_posFlag]
  refine forall_congr' fun a => forall_congr' fun _ => ?_
  rw [map_eq_zero_iff _ σ.symm.injective]

theorem glAut_smul_hypFlag (hε : ε ≤ 1) (σ : K ≃+* K) {c : ℕ} (hc : c ≤ 2 * r + ε)
    (q : GL (HypIndex r ε) K) (hq : q • hypFlag h r ε c = hypFlag h r ε c) :
    glAut σ q • hypFlag h r ε c = hypFlag h r ε c := by
  have h1 := coordImage_smul σ q (hypFlag h r ε c)
  erw [hq, coordImage_hypFlag hε σ hc] at h1
  exact h1.symm

variable (h) in
theorem exists_mul_of_mem_flag (hr : 1 ≤ r) (hε : ε ≤ 1) {I : Finset ℕ}
    (γ : semilinearSimilitudes h r ε)
    (hγ : (projFlag h r ε I).map (semilinearAutHom h hr hε γ).toMonoidHom =
      projFlag h r ε I) {g : hypSU h r ε} (hg : g ∈ flagStabilizer h r ε ↑I) :
    ∃ q ∈ flagStabilizer h r ε ↑I, ∃ z ∈ hypScalars h r ε,
      (g : GL (HypIndex r ε) K) =
        (γ : SemiGL (HypIndex r ε) K).left * glAut (γ : SemiGL (HypIndex r ε) K).right
          (q : GL (HypIndex r ε) K) * (γ : SemiGL (HypIndex r ε) K).left⁻¹ * (z : GL _ K) := by
  have hmem : hypProj h r ε g ∈
      (projFlag h r ε I).map (semilinearAutHom h hr hε γ).toMonoidHom := by
    rw [hγ]
    exact Subgroup.mem_map_of_mem _ hg
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
  refine ⟨q, hq, (⟨_, conj_mem_hypSU γ.2 q⟩ : hypSU h r ε)⁻¹ * g, ?_, ?_⟩
  · rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    have h2 := semilinearAutHom_apply h hr hε γ q
    change semilinearAutHom h hr hε γ (hypProj h r ε q) = hypProj h r ε g at hyg
    rw [h2] at hyg
    exact hyg
  · simp [mul_assoc]

theorem finrank_hypFlag (hε : ε ≤ 1) {i : ℕ} (hi : i ≤ 2 * r + ε) :
    finrank K ↥(hypFlag h r ε i) = i := by
  rw [hypFlag_eq_posFlag h hε hi]
  exact finrank_posFlag' hi

variable (h) in
theorem smul_hypFlag_eq_of_map_projFlag (hr : 1 ≤ r) (hε : ε ≤ 1) {I : Finset ℕ}
    (hIr : ∀ c ∈ I, 1 ≤ c ∧ c ≤ r) (γ : semilinearSimilitudes h r ε)
    (hγ : (projFlag h r ε I).map (semilinearAutHom h hr hε γ).toMonoidHom =
      projFlag h r ε I) :
    ∀ c ∈ I, ((γ : SemiGL (HypIndex r ε) K).left : GL (HypIndex r ε) K) • hypFlag h r ε c =
      hypFlag h r ε c := by
  obtain ⟨c₀, hc₀, hc₀0⟩ := exists_mem_traceZero_ne_zero' h
  have hIset : (↑I : Set ℕ) ⊆ Set.Icc 1 r := fun c hc => hIr c hc
  obtain ⟨-, -, hinv⟩ := unitary_subflag_generation h hr hε hc₀ hc₀0 hIset
  intro c hc
  set M := (γ : SemiGL (HypIndex r ε) K).left with hM
  set σ := (γ : SemiGL (HypIndex r ε) K).right with hσ
  have hcn : c ≤ 2 * r + ε := by
    have := (hIr c hc).2
    omega
  obtain ⟨hFiso, -⟩ := (hinv (hypFlag h r ε c)).mpr (Or.inr ⟨c, hc, rfl⟩)
  obtain ⟨μ, hμ0, -, hsim⟩ := γ.2
  have hiso : ∀ x ∈ M • hypFlag h r ε c, ∀ y ∈ M • hypFlag h r ε c, hypForm h r ε x y = 0 := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x M _).mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y M _).mp hy
    change gramForm h (hypGram r ε K) ((M : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x₀)
      ((M : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y₀) = 0
    rw [gramForm_mulVec, hsim, gramForm_smul_gram, hFiso x₀ hx₀ y₀ hy₀, mul_zero]
  have hdim : finrank K ↥(M • hypFlag h r ε c) = c := by
    refine (LinearEquiv.finrank_map_eq
      (DistribMulAction.toLinearEquiv K (HypIndex r ε → K) M) (hypFlag h r ε c)).trans ?_
    exact finrank_hypFlag (h := h) hε hcn
  have hinvQ : ∀ g ∈ flagStabilizer h r ε ↑I,
      g • (M • hypFlag h r ε c) = M • hypFlag h r ε c := by
    intro g hg
    obtain ⟨q, hq, z, hz, hgq⟩ := exists_mul_of_mem_flag h hr hε γ hγ hg
    have hqF := (mem_flagStabilizer.mp hq) c hc
    have hqF' : (q : GL (HypIndex r ε) K) • hypFlag h r ε c = hypFlag h r ε c := hqF
    have hzF : (z : GL (HypIndex r ε) K) • (M • hypFlag h r ε c) = M • hypFlag h r ε c :=
      smul_submodule_of_mem_normOneScalars hz (M • hypFlag h r ε c)
    change (g : GL (HypIndex r ε) K) • (M • hypFlag h r ε c) = M • hypFlag h r ε c
    rw [hgq, gl_mul_smul, hzF, ← gl_mul_smul, inv_mul_cancel_right, gl_mul_smul,
      glAut_smul_hypFlag hε σ hcn _ hqF']
  obtain h0 | ⟨i, hi, hWi⟩ := (hinv (M • hypFlag h r ε c)).mp ⟨hiso, hinvQ⟩
  · have h1 := hdim
    rw [h0, finrank_hypFlag (h := h) hε (Nat.zero_le _)] at h1
    have := (hIr c hc).1
    omega
  · have h1 := hdim
    have hin : i ≤ 2 * r + ε := by
      have := (hIr i hi).2
      omega
    rw [hWi, finrank_hypFlag (h := h) hε hin] at h1
    rw [hWi, h1]

end Flag

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
