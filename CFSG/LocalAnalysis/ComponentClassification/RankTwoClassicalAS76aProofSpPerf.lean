module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpPerfFrame
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitCTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsLift
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSplitA

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open CFSG.Quasithin (perfectCore)
open scoped Matrix commutatorElement

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

theorem sub_cTwoX_of_alt {N : Matrix ι ι K} (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) {x y : ι → K}
    (hxy : Q.polarBilin x (N *ᵥ y) = 1) {N' : Matrix ι ι K}
    (hN' : N' = N - cTwoX Q (N *ᵥ y) (N *ᵥ x)) :
    N' * N' = 0 ∧ (∀ a b, Q.polarBilin (N' *ᵥ a) b = Q.polarBilin a (N' *ᵥ b)) ∧
      (∀ v, Q.polarBilin v (N' *ᵥ v) = 0) ∧ N' *ᵥ x = 0 ∧ N' *ᵥ y = 0 ∧
      N'.rank = N.rank - 2 := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hNN : ∀ a b, Q.polarBilin (N *ᵥ a) (N *ᵥ b) = 0 := fun a b => by
    rw [hadj, mulVec_mulVec, hN, zero_mulVec, map_zero]
  have hyx : Q.polarBilin y (N *ᵥ x) = 1 := by rw [← hadj, hBs, hxy]
  have hxx : Q.polarBilin x (N *ᵥ x) = 0 := halt x
  have hyy : Q.polarBilin y (N *ᵥ y) = 0 := halt y
  obtain ⟨E, hE⟩ : ∃ E, E = cTwoX Q (N *ᵥ y) (N *ᵥ x) := ⟨_, rfl⟩
  rw [← hE] at hN'
  have hEv : ∀ v, E *ᵥ v = Q.polarBilin v (N *ᵥ y) • (N *ᵥ x) +
      Q.polarBilin v (N *ᵥ x) • (N *ᵥ y) := fun v => by rw [hE, cTwoX_mulVec]
  have hN'v : ∀ v, N' *ᵥ v = N *ᵥ v - E *ᵥ v := fun v => by rw [hN', sub_mulVec]
  have hN'x : N' *ᵥ x = 0 := by
    rw [hN'v, hEv, hxy, hxx, one_smul, zero_smul, add_zero, sub_self]
  have hN'y : N' *ᵥ y = 0 := by
    rw [hN'v, hEv, hyy, hyx, one_smul, zero_smul, zero_add, sub_self]
  have hEadj : ∀ a b, Q.polarBilin (E *ᵥ a) b = Q.polarBilin a (E *ᵥ b) := fun a b => by
    rw [hEv, hEv]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hBs (N *ᵥ x) b, hBs (N *ᵥ y) b]
    ring
  have hN'adj : ∀ a b, Q.polarBilin (N' *ᵥ a) b = Q.polarBilin a (N' *ᵥ b) := fun a b => by
    rw [hN'v, hN'v, map_sub, map_sub, LinearMap.sub_apply, hadj, hEadj]
  have hEN : E * N = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hEv, hNN, hNN, zero_smul, zero_smul, add_zero, zero_mulVec]
  have hNE : N * E = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hEv, mulVec_add, mulVec_smul, mulVec_smul]
    simp only [mulVec_mulVec, hN, zero_mulVec, smul_zero, add_zero]
  have hEE : E * E = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hEv v, mulVec_add, mulVec_smul, mulVec_smul, hEv, hEv]
    simp [hNN]
  have hN'N' : N' * N' = 0 := by
    rw [hN', sub_mul, mul_sub, mul_sub, hN, hNE, hEN, hEE]
    simp
  have hN'alt : ∀ v, Q.polarBilin v (N' *ᵥ v) = 0 := fun v => by
    rw [hN'v, map_sub, halt, hEv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      mul_comm, CharTwo.add_self_eq_zero, sub_zero]
  have hNx0 : N *ᵥ x ≠ 0 := fun h => by
    rw [h, map_zero] at hyx
    exact zero_ne_one hyx
  have hrE : E.rank = 2 := by
    rw [hE]
    exact rank_cTwoX hNx0 hxy hxx hyy hyx
  have hker : ∀ v, N *ᵥ v = 0 → N' *ᵥ v = 0 := fun v hv => by
    have h1 : Q.polarBilin v (N *ᵥ y) = 0 := by rw [← hadj, hv, map_zero, LinearMap.zero_apply]
    have h2 : Q.polarBilin v (N *ᵥ x) = 0 := by rw [← hadj, hv, map_zero, LinearMap.zero_apply]
    rw [hN'v, hv, hEv, h1, h2, zero_smul, zero_smul, add_zero, sub_zero]
  have hpair : ∀ a b : K, a • (N *ᵥ x) + b • (N *ᵥ y) = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 := congrArg (Q.polarBilin x) hab
    have h2 := congrArg (Q.polarBilin y) hab
    simp only [map_add, map_smul, smul_eq_mul, hxx, hxy, hyx, hyy, map_zero, mul_zero, mul_one,
      zero_add, add_zero] at h1 h2
    exact ⟨h2, h1⟩
  exact ⟨hN'N', hN'adj, hN'alt, hN'x, hN'y,
    rank_eq_sub_two_of_split (by rw [hN', add_sub_cancel]) hrE hker hN'x hN'y hpair⟩

theorem exists_blocks_of_alt (hQ : Q.polarBilin.Nondegenerate) :
    ∀ (r : ℕ) (N : Matrix ι ι K), N.rank = r → N * N = 0 →
      (∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) →
      (∀ v, Q.polarBilin v (N *ᵥ v) = 0) →
      ∃ L : List ((ι → K) × (ι → K)), (∀ p ∈ L, Q.polarBilin p.1 (N *ᵥ p.2) = 1) ∧
        N = (L.map fun p => cTwoX Q (N *ᵥ p.2) (N *ᵥ p.1)).sum := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih => ?_
  intro N hr hN hadj halt
  by_cases hN0 : N = 0
  · exact ⟨[], by simp, by simp [hN0]⟩
  obtain ⟨y, hy⟩ : ∃ y, N *ᵥ y ≠ 0 := by
    by_contra! h
    exact hN0 (Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, zero_mulVec])
  obtain ⟨x, hxy⟩ : ∃ x, Q.polarBilin x (N *ᵥ y) = 1 := by
    obtain ⟨x, hx⟩ : ∃ x, Q.polarBilin x (N *ᵥ y) ≠ 0 := by
      by_contra! h
      exact hy (hQ.2 _ h)
    exact ⟨(Q.polarBilin x (N *ᵥ y))⁻¹ • x, by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx]⟩
  obtain ⟨N', hN'⟩ : ∃ N', N' = N - cTwoX Q (N *ᵥ y) (N *ᵥ x) := ⟨_, rfl⟩
  obtain ⟨hN'N', hN'adj, hN'alt, hN'x, hN'y, hrN'⟩ := sub_cTwoX_of_alt hN hadj halt hxy hN'
  rw [hr] at hrN'
  have hr0 : 0 < r := by
    rw [← hr]
    by_contra h
    exact hN0 (eq_zero_of_rank_eq_zero (by omega))
  obtain ⟨R, hR⟩ : ∃ R : (ι → K) → ι → K,
      R = fun v => v - (Q.polarBilin v (N *ᵥ y) • x + Q.polarBilin v (N *ᵥ x) • y) := ⟨_, rfl⟩
  have hNR : ∀ v, N *ᵥ R v = N' *ᵥ v := fun v => by
    rw [hR, hN', sub_mulVec, cTwoX_mulVec, mulVec_sub, mulVec_add, mulVec_smul, mulVec_smul]
  obtain ⟨L', hL'1, hL'2⟩ := ih (r - 2) (by omega) N' hrN' hN'N' hN'adj hN'alt
  have hRB : ∀ a w, Q.polarBilin (R a) (N' *ᵥ w) = Q.polarBilin a (N' *ᵥ w) := fun a w => by
    have h1 : Q.polarBilin x (N' *ᵥ w) = 0 := by
      rw [← hN'adj, hN'x, map_zero, LinearMap.zero_apply]
    have h2 : Q.polarBilin y (N' *ᵥ w) = 0 := by
      rw [← hN'adj, hN'y, map_zero, LinearMap.zero_apply]
    rw [hR]
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, h1, h2, mul_zero, add_zero, sub_zero]
  refine ⟨(x, y) :: L'.map (fun p => (R p.1, R p.2)), fun p hp => ?_, ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact hxy
    · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
      show Q.polarBilin (R p'.1) (N *ᵥ R p'.2) = 1
      rw [hNR, hRB]
      exact hL'1 p' hp'
  · rw [List.map_cons, List.sum_cons, List.map_map]
    have h1 : L'.map ((fun p : (ι → K) × (ι → K) => cTwoX Q (N *ᵥ p.2) (N *ᵥ p.1)) ∘
        fun p => (R p.1, R p.2)) = L'.map fun p => cTwoX Q (N' *ᵥ p.2) (N' *ᵥ p.1) :=
      List.map_congr_left fun p _ => by simp only [Function.comp, hNR]
    rw [h1, ← hL'2]
    dsimp only
    rw [hN']
    abel

omit [CharP K 2] in
theorem frR_sub (u : Fin 2 → ι → K) (T T' : Matrix (Fin 2) (Fin 2) K) :
    frR Q u (T - T') = frR Q u T - frR Q u T' := by
  rw [frR, frR, frR, Matrix.mul_sub, Matrix.sub_mul]

omit [CharP K 2] in
theorem SpFrame.frD_mul_of_kill {u u'' : Fin 2 → ι → K} {X : Matrix ι ι K}
    (hXu : ∀ k, X *ᵥ u k = 0) (hXu'' : ∀ k, X *ᵥ u'' k = 0)
    (hXadj : ∀ v w, Q.polarBilin (X *ᵥ v) w = Q.polarBilin v (X *ᵥ w))
    (a b : Matrix (Fin 2) (Fin 2) K) :
    frD Q u u'' a b * X = X ∧ X * frD Q u u'' a b = X := by
  have h1 : ∀ w : Fin 2 → ι → K, (∀ k, X *ᵥ w k = 0) → X * frCol w = 0 := fun w hw =>
    Matrix.ext_iff_mulVec.mpr fun c => by
      rw [← mulVec_mulVec, frCol_mulVec, mulVec_sum, zero_mulVec]
      simp [mulVec_smul, hw]
  have h2 : ∀ w : Fin 2 → ι → K, (∀ k, X *ᵥ w k = 0) → frRow Q w * X = 0 := fun w hw =>
    Matrix.ext_iff_mulVec.mpr fun v => by
      rw [← mulVec_mulVec, frRow_mulVec, zero_mulVec]
      ext i
      simp only [hXadj, hw, map_zero, Pi.zero_apply]
  refine ⟨?_, ?_⟩
  · rw [frD, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, frP, frQ, Matrix.mul_assoc _ _ X,
      Matrix.mul_assoc _ _ X, h2 u'' hXu'', h2 u hXu, Matrix.mul_zero, Matrix.mul_zero, add_zero,
      add_zero]
  · rw [frD, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, frP, frQ, ← Matrix.mul_assoc X,
      ← Matrix.mul_assoc X, ← Matrix.mul_assoc X, ← Matrix.mul_assoc X, h1 u hXu, h1 u'' hXu'',
      Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul, add_zero, add_zero]

section Perfect

variable {H : Subgroup (GL ι K)}
  (hH : ∀ X : GL ι K, (∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v)
    ((X : Matrix ι ι K) *ᵥ w) = Q.polarBilin v w) → X ∈ H)
include hH

theorem sqZeroGL_mem_of_adj {E : Matrix ι ι K} (hE : E * E = 0)
    (hadj : ∀ v w, Q.polarBilin (E *ᵥ v) w = Q.polarBilin v (E *ᵥ w)) : sqZeroGL E hE ∈ H := by
  refine hH _ fun v w => ?_
  rw [coe_sqZeroGL, add_mulVec, add_mulVec, one_mulVec, one_mulVec]
  have hEE : Q.polarBilin (E *ᵥ v) (E *ᵥ w) = 0 := by
    rw [hadj, mulVec_mulVec, hE, zero_mulVec, map_zero]
  simp only [map_add, LinearMap.add_apply, hEE, hadj v w, add_zero]
  linear_combination Q.polarBilin v (E *ᵥ w) * CharTwo.two_eq_zero (R := K)

theorem mem_perfectCore_block (hK : ∃ s : Finset K, s.card = 4) {M : GL ι K}
    {N : Matrix ι ι K} (hMN : (M : Matrix ι ι K) = 1 + N) (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) {x y : ι → K}
    (hxy : Q.polarBilin x (N *ᵥ y) = 1) {X : GL ι K}
    (hX : (X : Matrix ι ι K) = 1 + cTwoX Q (N *ᵥ y) (N *ᵥ x)) :
    X ∈ perfectCore (H ⊓ centralizer ({M} : Set (GL ι K))) := by
  classical
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hB0 : ∀ a, Q.polarBilin a a = 0 := fun a => TypeCData.pol_self a
  have hNN : ∀ a b, Q.polarBilin (N *ᵥ a) (N *ᵥ b) = 0 := fun a b => by
    rw [hadj, mulVec_mulVec, hN, zero_mulVec, map_zero]
  have hyx : Q.polarBilin y (N *ᵥ x) = 1 := by rw [← hadj, hBs, hxy]
  have hxx : Q.polarBilin x (N *ᵥ x) = 0 := halt x
  have hyy : Q.polarBilin y (N *ᵥ y) = 0 := halt y
  have hNNv : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  obtain ⟨x', hx'⟩ : ∃ x', x' = x + Q.polarBilin y x • (N *ᵥ x) := ⟨_, rfl⟩
  have hyx' : Q.polarBilin y x' = 0 := by
    rw [hx', map_add, map_smul, smul_eq_mul, hyx, mul_one, CharTwo.add_self_eq_zero]
  have hNxx' : Q.polarBilin (N *ᵥ x) x' = 0 := by
    rw [hx', map_add, map_smul, smul_eq_mul, hNN, mul_zero, add_zero, hadj, hxx]
  have hNyx' : Q.polarBilin (N *ᵥ y) x' = 1 := by
    rw [hx', map_add, map_smul, smul_eq_mul, hNN, mul_zero, add_zero, hadj, hyx]
  have hNxy : Q.polarBilin (N *ᵥ x) y = 1 := by rw [hadj, hxy]
  have hNyy : Q.polarBilin (N *ᵥ y) y = 0 := by rw [hadj, hyy]
  obtain ⟨u, hu⟩ : ∃ u : Fin 2 → ι → K, u = ![N *ᵥ x, N *ᵥ y] := ⟨_, rfl⟩
  obtain ⟨u'', hu''⟩ : ∃ u'' : Fin 2 → ι → K, u'' = ![y, x'] := ⟨_, rfl⟩
  have hF : SpFrame Q u u'' := by
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [hu]
      fin_cases i <;> fin_cases j <;> simp [hNN]
    · rw [hu'']
      fin_cases i <;> fin_cases j <;> simp [hB0, hyx', hBs x' y]
    · rw [hu, hu'']
      fin_cases i <;> fin_cases j <;> simp [hNxy, hNxx', hNyy, hNyx']
  have hER : frR Q u (frH K) = cTwoX Q (N *ᵥ y) (N *ᵥ x) :=
    Matrix.ext_iff_mulVec.mpr fun v => by
      rw [frR, ← mulVec_mulVec, ← mulVec_mulVec, frRow_mulVec, frCol_mulVec, cTwoX_mulVec, hu]
      simp [frH, mulVec, dotProduct, Fin.sum_univ_two]
  obtain ⟨Nr, hNr⟩ : ∃ Nr, Nr = N - frR Q u (frH K) := ⟨_, rfl⟩
  have hNrv : ∀ v, Nr *ᵥ v = N *ᵥ v - (Q.polarBilin v (N *ᵥ y) • (N *ᵥ x) +
      Q.polarBilin v (N *ᵥ x) • (N *ᵥ y)) := fun v => by
    rw [hNr, sub_mulVec, hER, cTwoX_mulVec]
  have hNx' : N *ᵥ x' = N *ᵥ x := by
    rw [hx', mulVec_add, mulVec_smul, hNNv, smul_zero, add_zero]
  have hx'Ny : Q.polarBilin x' (N *ᵥ y) = 1 := by
    rw [hx', map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hNN,
      mul_zero, add_zero, hxy]
  have hx'Nx : Q.polarBilin x' (N *ᵥ x) = 0 := by
    rw [hx', map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hNN,
      mul_zero, add_zero, hxx]
  have hNrNx : Nr *ᵥ (N *ᵥ x) = 0 := by
    rw [hNrv, hNNv, hNN, hNN, zero_smul, zero_smul, add_zero, sub_self]
  have hNrNy : Nr *ᵥ (N *ᵥ y) = 0 := by
    rw [hNrv, hNNv, hNN, hNN, zero_smul, zero_smul, add_zero, sub_self]
  have hNry : Nr *ᵥ y = 0 := by
    rw [hNrv, hyy, hyx, zero_smul, one_smul, zero_add, sub_self]
  have hNrx' : Nr *ᵥ x' = 0 := by
    rw [hNrv, hNx', hx'Ny, hx'Nx, one_smul, zero_smul, add_zero, sub_self]
  have hNru : ∀ k, Nr *ᵥ u k = 0 := fun k => by
    rw [hu]
    fin_cases k
    exacts [hNrNx, hNrNy]
  have hNru'' : ∀ k, Nr *ᵥ u'' k = 0 := fun k => by
    rw [hu'']
    fin_cases k
    exacts [hNry, hNrx']
  have hNradj : ∀ a b, Q.polarBilin (Nr *ᵥ a) b = Q.polarBilin a (Nr *ᵥ b) := fun a b => by
    rw [hNrv, hNrv]
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hadj, hBs (N *ᵥ x) b, hBs (N *ᵥ y) b]
    ring
  have hMN' : (M : Matrix ι ι K) = 1 + frR Q u (frH K) + Nr := by
    rw [hMN, hNr]
    abel
  have hDM : ∀ g, hF.frLevi g * M = M * hF.frLevi g := fun g => by
    apply Units.ext
    obtain ⟨h1, h2⟩ := SpFrame.frD_mul_of_kill (Q := Q) (u := u) (u'' := u'') hNru hNru''
      hNradj ((g : Matrix (Fin 2) (Fin 2) K) - 1)
      (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ - 1)
    rw [Units.val_mul, Units.val_mul, hMN', Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hF.frLevi_mul_frR_frH, SpFrame.coe_frLevi,
      frLeviMat, h1, h2]
  have hLC : hF.frLevi.range ≤ H ⊓ centralizer ({M} : Set (GL ι K)) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨hH _ (hF.polarBilin_frLevi_mulVec g), mem_centralizer_singleton_iff.mpr (hDM g)⟩
  have hLperf : ⁅hF.frLevi.range, hF.frLevi.range⁆ = hF.frLevi.range := by
    have hperf := CFSG.LinearGroups.special_linear_dimension_two_perfect hK
    have htop : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
      hperf.commutator_eq_top
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  have hLcore : hF.frLevi.range ≤ perfectCore (H ⊓ centralizer ({M} : Set (GL ι K))) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hLC hLperf
  have hNU : N * frCol u = 0 := Matrix.ext_iff_mulVec.mpr fun c => by
    rw [← mulVec_mulVec, frCol_mulVec, mulVec_sum, zero_mulVec, hu]
    simp [mulVec_smul, hNNv]
  have hUN : frRow Q u * N = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, frRow_mulVec, zero_mulVec, hu]
    ext i
    fin_cases i <;> simp [hNN]
  have hzC : ∀ T : Matrix (Fin 2) (Fin 2) K, Tᵀ = T →
      sqZeroGL (frR Q u T) (hF.frR_mul_frR T T) ∈ H ⊓ centralizer ({M} : Set (GL ι K)) := by
    intro T hT
    refine ⟨sqZeroGL_mem_of_adj hH _ fun v w => by rw [polarBilin_frR_mulVec, hT],
      mem_centralizer_singleton_iff.mpr ?_⟩
    apply Units.ext
    have h1 : N * frR Q u T = 0 := by rw [frR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hNU,
      Matrix.zero_mul, Matrix.zero_mul]
    have h2 : frR Q u T * N = 0 := by rw [frR, Matrix.mul_assoc, hUN, Matrix.mul_zero]
    rw [Units.val_mul, Units.val_mul, coe_sqZeroGL, hMN]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2, add_zero]
    abel
  have hcomm : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (T : Matrix (Fin 2) (Fin 2) K),
      ⁅hF.frLevi g, sqZeroGL (frR Q u T) (hF.frR_mul_frR T T)⁆ =
        sqZeroGL (frR Q u ((g : Matrix (Fin 2) (Fin 2) K) * T * (g : Matrix (Fin 2) (Fin 2) K)ᵀ
          - T)) (hF.frR_mul_frR _ _) := by
    intro g T
    apply Units.ext
    have e1 : (hF.frLevi g : Matrix ι ι K) * ((hF.frLevi g)⁻¹ : GL ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e2 := hF.frLevi_mul_frR_mul_frLevi_inv g T
    have e3 : ((sqZeroGL (frR Q u T) (hF.frR_mul_frR T T))⁻¹ : GL ι K) =
        (1 - frR Q u T : Matrix ι ι K) := rfl
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, coe_sqZeroGL, e3,
      coe_sqZeroGL, frR_sub]
    calc (hF.frLevi g : Matrix ι ι K) * (1 + frR Q u T) * ((hF.frLevi g)⁻¹ : GL ι K) *
          (1 - frR Q u T) =
        ((hF.frLevi g : Matrix ι ι K) * ((hF.frLevi g)⁻¹ : GL ι K) +
          (hF.frLevi g : Matrix ι ι K) * frR Q u T * ((hF.frLevi g)⁻¹ : GL ι K)) *
          (1 - frR Q u T) := by noncomm_ring
      _ = 1 + (frR Q u ((g : Matrix (Fin 2) (Fin 2) K) * T * (g : Matrix (Fin 2) (Fin 2) K)ᵀ) -
          frR Q u T) := by
        rw [e1, e2, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
          hF.frR_mul_frR]
        abel
  obtain ⟨l, hl0, hl1⟩ : ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
    obtain ⟨s, hs⟩ := hK
    by_contra! h
    have hsub : s ⊆ {0, 1} := fun a _ => by
      by_cases ha : a = 0
      · simp [ha]
      · simp [h a ha]
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (0 : K) {1}
    rw [Finset.card_singleton] at h2
    omega
  have hl2 : l ^ 2 + 1 ≠ 0 := fun h0 => hl1 (by
    have h1 : (l + 1) ^ 2 = 0 := by rw [CharTwo.add_sq, one_pow, h0]
    have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h2
    exact h2)
  let g₂ : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  let g₁ : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![l, 0; 0, l⁻¹], by
    simp [det_fin_two, hl0]⟩
  let T₂ : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, 1]
  let T₁ : Matrix (Fin 2) (Fin 2) K := !![(l ^ 2 + 1)⁻¹, 0; 0, 0]
  have hT₂ : T₂ᵀ = T₂ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hT₁ : T₁ᵀ = T₁ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hg₂ : (g₂ : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := rfl
  have hg₂t : (g₂ : Matrix (Fin 2) (Fin 2) K)ᵀ = !![1, 0; 1, 1] := by
    rw [hg₂]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) = !![l, 0; 0, l⁻¹] := rfl
  have hg₁t : (g₁ : Matrix (Fin 2) (Fin 2) K)ᵀ = !![l, 0; 0, l⁻¹] := by
    rw [hg₁]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hsum : ((g₂ : Matrix (Fin 2) (Fin 2) K) * T₂ * (g₂ : Matrix (Fin 2) (Fin 2) K)ᵀ - T₂) +
      ((g₁ : Matrix (Fin 2) (Fin 2) K) * T₁ * (g₁ : Matrix (Fin 2) (Fin 2) K)ᵀ - T₁) = frH K := by
    rw [hg₂t, hg₁t, hg₂, hg₁]
    simp only [T₂, T₁, frH, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (mul_inv_cancel₀ hl2) + (1 - (l ^ 2 + 1)⁻¹) * CharTwo.two_eq_zero (R := K)
  have hc₂ := commutatorElement_mem_perfectCore' (hzC T₂ hT₂) (hLcore ⟨g₂, rfl⟩)
  have hc₁ := commutatorElement_mem_perfectCore' (hzC T₁ hT₁) (hLcore ⟨g₁, rfl⟩)
  rw [hcomm] at hc₂ hc₁
  have hprod := mul_mem hc₂ hc₁
  rw [sqZeroGL_mul _ _ (hF.frR_mul_frR _ _) (by rw [← frR_add]; exact hF.frR_mul_frR _ _)]
    at hprod
  convert hprod using 1
  apply Units.ext
  rw [hX, coe_sqZeroGL, ← frR_add, hsum, hER]

theorem mem_perfectCore_of_typeA (hQ : Q.polarBilin.Nondegenerate)
    (hK : ∃ s : Finset K, s.card = 4) {M : GL ι K}
    (hMB : ∀ v w, Q.polarBilin ((M : Matrix ι ι K) *ᵥ v) ((M : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w) (hM2 : orderOf M = 2)
    (halt : ∀ v, Q.polarBilin v (((M : Matrix ι ι K) - 1) *ᵥ v) = 0) :
    M ∈ perfectCore (H ⊓ centralizer ({M} : Set (GL ι K))) := by
  have hN := sub_one_mul_self_eq_zero hM2
  have hadj := polarBilin_sub_one_adj hMB hM2
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hadj halt
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hNN : ∀ a b, Q.polarBilin (N *ᵥ a) (N *ᵥ b) = 0 := fun a b => by
    rw [hadj, mulVec_mulVec, hN, zero_mulVec, map_zero]
  obtain ⟨L, hL1, hL2⟩ := exists_blocks_of_alt hQ _ N rfl hN hadj halt
  have hblk : ∀ p : (ι → K) × (ι → K), cTwoX Q (N *ᵥ p.2) (N *ᵥ p.1) * N = 0 ∧
      ∀ v, ∃ w, cTwoX Q (N *ᵥ p.2) (N *ᵥ p.1) *ᵥ v = N *ᵥ w := fun p => by
    refine ⟨Matrix.ext_iff_mulVec.mpr fun v => ?_, fun v => ⟨Q.polarBilin v (N *ᵥ p.2) • p.1 +
      Q.polarBilin v (N *ᵥ p.1) • p.2, ?_⟩⟩
    · rw [← mulVec_mulVec, cTwoX_mulVec, hNN, hNN, zero_smul, zero_smul, add_zero, zero_mulVec]
    · rw [cTwoX_mulVec, mulVec_add, mulVec_smul, mulVec_smul]
  have key : ∀ L' : List ((ι → K) × (ι → K)), (∀ p ∈ L', Q.polarBilin p.1 (N *ᵥ p.2) = 1) →
      ((L'.map fun p => cTwoX Q (N *ᵥ p.2) (N *ᵥ p.1)).sum * N = 0 ∧
        ∀ v, ∃ w, (L'.map fun p => cTwoX Q (N *ᵥ p.2) (N *ᵥ p.1)).sum *ᵥ v = N *ᵥ w) ∧
      ∀ X : GL ι K, (X : Matrix ι ι K) = 1 + (L'.map fun p => cTwoX Q (N *ᵥ p.2)
        (N *ᵥ p.1)).sum → X ∈ perfectCore (H ⊓ centralizer ({M} : Set (GL ι K))) := by
    intro L'
    induction L' with
    | nil =>
      intro _
      refine ⟨⟨by simp, fun v => ⟨0, by simp⟩⟩, fun X hX => ?_⟩
      have hX1 : X = 1 := Units.ext (by rw [hX]; simp)
      rw [hX1]
      exact one_mem _
    | cons p L' ih =>
      intro hp
      obtain ⟨⟨hSN, hSV⟩, hS⟩ := ih fun q hq => hp q (List.mem_cons_of_mem p hq)
      obtain ⟨hPN, hPV⟩ := hblk p
      set S := (L'.map fun p => cTwoX Q (N *ᵥ p.2) (N *ᵥ p.1)).sum with hSdef
      set P := cTwoX Q (N *ᵥ p.2) (N *ᵥ p.1) with hPdef
      have hzero : ∀ Y Y' : Matrix ι ι K, Y * N = 0 → (∀ v, ∃ w, Y' *ᵥ v = N *ᵥ w) →
          Y * Y' = 0 := fun Y Y' hY hY' => Matrix.ext_iff_mulVec.mpr fun v => by
        obtain ⟨w, hw⟩ := hY' v
        rw [← mulVec_mulVec, hw, mulVec_mulVec, hY, zero_mulVec, zero_mulVec]
      have hPP : P * P = 0 := hzero P P hPN hPV
      have hSS : S * S = 0 := hzero S S hSN hSV
      have hPS : P * S = 0 := hzero P S hPN hSV
      have hPSPS : (P + S) * (P + S) = 0 := by
        rw [add_mul, mul_add, mul_add, hPP, hSS, hPS, hzero S P hSN hPV]
        simp
      rw [List.map_cons, List.sum_cons]
      refine ⟨⟨by rw [add_mul, hPN, hSN, add_zero], fun v => ?_⟩, fun X hX => ?_⟩
      · obtain ⟨w, hw⟩ := hPV v
        obtain ⟨w', hw'⟩ := hSV v
        exact ⟨w + w', by rw [add_mulVec, hw, hw', mulVec_add]⟩
      · have hXe : X = sqZeroGL P hPP * sqZeroGL S hSS := by
          rw [sqZeroGL_mul hPP hSS hPS hPSPS]
          exact Units.ext (by rw [hX, coe_sqZeroGL])
        rw [hXe]
        refine mul_mem ?_ (hS _ (coe_sqZeroGL _ _))
        exact mem_perfectCore_block hH hK hMN hN hadj halt (hp p (List.mem_cons_self ..))
          (coe_sqZeroGL _ _)
  exact (key L hL1).2 M (by rw [hMN, ← hL2])

end Perfect

theorem mem_perfectCore_of_typeA_sp {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : ∃ s : Finset K, s.card = 4) {M : GL (Fin n ⊕ Fin n) K} (hM : M ∈ StatedSp n K)
    (hM2 : orderOf M = 2)
    (h0 : ∀ v, sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = 0) :
    M ∈ perfectCore (StatedSp n K ⊓ centralizer ({M} : Set (GL (Fin n ⊕ Fin n) K))) :=
  mem_perfectCore_of_typeA (Q := quadPlus n K) (fun _ hX => mem_statedSp_of_polarBilin hX)
    (nondegenerate_polarBilin_quadPlus n K) hK (polarBilin_mulVec_of_mem_statedSp hM) hM2
    fun v => by rw [polarBilin_quadPlus, sympForm_sub_one_mulVec]; exact h0 v

theorem symplecticTypeAPerfect : SymplecticTypeAPerfect := by
  intro G _ _ A D hD _ hZ hq x ℓ hx
  cases D with
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨hx2, M, hxM, hM2, -, -, h0⟩ := hx
    have hK4 : ∃ s : Finset K, s.card = 4 := by
      have : Fintype K := Fintype.ofFinite K
      have h4 : 4 ≤ (Finset.univ : Finset K).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
        exact hq
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4
      exact ⟨t, ht⟩
    have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
    exact mem_perfectCore_of_represents e hZ hx2' hxM
      (mem_perfectCore_of_typeA_sp hK4 hxM.2.1 hM2 h0)
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
