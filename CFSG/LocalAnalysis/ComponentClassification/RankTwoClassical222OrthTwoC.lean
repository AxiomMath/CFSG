module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthTwoA

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Linear

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

omit [DecidableEq ι] in
theorem exists_pair_indep_mod {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) {z y₀ : ι → K}
    (hy₀ : N *ᵥ y₀ = z) (hz0 : z ≠ 0) (hrk : 4 ≤ N.rank) :
    ∃ x y : ι → K, Q.polarBilin x z = 0 ∧ Q.polarBilin y z = 0 ∧
      ∀ a b d : K, a • (N *ᵥ x) + b • (N *ᵥ y) + d • z = 0 → a = 0 ∧ b = 0 := by
  have hperp : ∀ h, h ∈ LinearMap.range N.mulVecLin →
      Q.polarBilin h y₀ = 0 → ∃ x, N *ᵥ x = h ∧ Q.polarBilin x z = 0 :=
    fun h ⟨x, hx⟩ hhy => ⟨x, hx, by rw [← hy₀, ← hadj]; rw [← hx] at hhy; exact hhy⟩
  obtain ⟨hx', hxr, hxy₀, hxT⟩ := exists_mem_range_perp_not_mem (Q := Q) N y₀
    (T := K ∙ z) (by rw [finrank_span_singleton hz0]; omega)
  obtain ⟨x, hx, hxz⟩ := hperp hx' hxr hxy₀
  set T := Submodule.span K (Set.range ![z, N *ᵥ x]) with hT
  have hT2 : finrank K T ≤ 2 := by
    have h := finrank_range_le_card (R := K) ![z, N *ᵥ x]
    rw [Fintype.card_fin] at h
    exact h
  obtain ⟨hy', hyr, hyy₀, hyT⟩ := exists_mem_range_perp_not_mem (Q := Q) N y₀
    (T := T) (by omega)
  obtain ⟨y, hy, hyz⟩ := hperp hy' hyr hyy₀
  refine ⟨x, y, hxz, hyz, fun a b d h => ?_⟩
  have hb : b = 0 := by
    by_contra hb
    apply hyT
    have h1 : hy' = (-(b⁻¹ * d)) • z + (-(b⁻¹ * a)) • (N *ᵥ x) := by
      rw [← hy]
      have h2 : b⁻¹ • (a • (N *ᵥ x) + b • (N *ᵥ y) + d • z) = 0 := by rw [h, smul_zero]
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, inv_mul_cancel₀ hb,
        one_smul] at h2
      rw [neg_smul, neg_smul]
      linear_combination (norm := module) h2
    rw [h1]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  refine ⟨?_, hb⟩
  by_contra ha
  apply hxT
  rw [hb, zero_smul, add_zero] at h
  refine Submodule.mem_span_singleton.mpr ⟨-(a⁻¹ * d), ?_⟩
  have h2 : a⁻¹ • (a • (N *ᵥ x) + d • z) = 0 := by rw [h, smul_zero]
  rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
  rw [← hx, neg_smul]
  linear_combination (norm := module) -h2

variable [CharP K 2]

theorem commutant_typeC_of_mem [Finite K] (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    {z : ι → K} (hz : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v)) (hz0 : z ≠ 0)
    {x y : ι → K} (hxz : Q.polarBilin x z = 0) (hyz : Q.polarBilin y z = 0)
    (hli : ∀ a b d : K, a • (N *ᵥ x) + b • (N *ᵥ y) + d • z = 0 → a = 0 ∧ b = 0) {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w)
    (hXN : (X : Matrix ι ι K) * N = N * X)
    (hmem : ∀ w, Q.polarBilin w z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) →
      ∃ c : K, ((X : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w)) :
    ∃ s t : K, (X : Matrix ι ι K) = 1 + s • N + t • polMat Q z z := by
  set L := (X : Matrix ι ι K) - 1 with hL
  have hgood : ∀ w v : ι → K, (∀ a b d : K, a • (N *ᵥ w) + b • (N *ᵥ v) + d • z = 0 →
      a = 0 ∧ b = 0) → ∀ c : K, N *ᵥ w ≠ c • z := fun w v h c hc => by
    have h1 := h 1 0 (-c) (by rw [hc, zero_smul, add_zero, one_smul, neg_smul, add_neg_cancel])
    exact one_ne_zero h1.1
  have hswap : ∀ w v : ι → K, (∀ a b d : K, a • (N *ᵥ w) + b • (N *ᵥ v) + d • z = 0 →
      a = 0 ∧ b = 0) → ∀ a b d : K, a • (N *ᵥ v) + b • (N *ᵥ w) + d • z = 0 → a = 0 ∧ b = 0 :=
    fun w v h a b d hab => by
      have h1 := h b a d (by rw [← hab]; abel)
      exact ⟨h1.2, h1.1⟩
  obtain ⟨s, hs⟩ := hmem x hxz (hgood x y hli)
  have hshift : ∀ w v, Q.polarBilin w z = 0 → Q.polarBilin v z = 0 →
      (∀ a b d : K, a • (N *ᵥ w) + b • (N *ᵥ v) + d • z = 0 → a = 0 ∧ b = 0) →
      L *ᵥ v = s • (N *ᵥ v) → L *ᵥ w = s • (N *ᵥ w) := by
    intro w v hwz hvz hind hv
    obtain ⟨cw, hcw⟩ := hmem w hwz (hgood w v hind)
    obtain ⟨c, hc⟩ := hmem (w + v) (by rw [map_add, LinearMap.add_apply, hwz, hvz, add_zero])
      fun c h => by
        have h1 := hind 1 1 (-c) (by
          rw [one_smul, one_smul, ← mulVec_add, h, neg_smul, add_neg_cancel])
        exact one_ne_zero h1.1
    rw [mulVec_add, hcw, hv, mulVec_add] at hc
    have h1 : (c - cw) • (N *ᵥ w) + (c - s) • (N *ᵥ v) + (0 : K) • z = 0 := by
      linear_combination (norm := module) -hc
    obtain ⟨h2, h3⟩ := hind _ _ _ h1
    rw [hcw, show cw = s by linear_combination h3 - h2]
  have hys : L *ᵥ y = s • (N *ᵥ y) := hshift y x hyz hxz (hswap x y hli) hs
  have hA : ∀ w, Q.polarBilin w z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) →
      L *ᵥ w = s • (N *ᵥ w) := by
    intro w hwz hwg
    by_cases hdep : ∀ a b d : K, a • (N *ᵥ w) + b • (N *ᵥ x) + d • z = 0 → a = 0 ∧ b = 0
    · exact hshift w x hwz hxz hdep hs
    push Not at hdep
    obtain ⟨a, b, d, habd, hab⟩ := hdep
    have ha : a ≠ 0 := fun ha => by
      rw [ha, zero_smul, zero_add] at habd
      exact hab ha (hli b 0 d (by rw [zero_smul, add_zero]; exact habd)).1
    refine hshift w y hwz hyz (fun a' b' d' h => ?_) hys
    have h1 := hli (-(a' * b)) (a * b') (a * d' - a' * d) (by
      linear_combination (norm := module) a • h - a' • habd)
    have hb' : b' = 0 := (mul_eq_zero.mp h1.2).resolve_left ha
    refine ⟨?_, hb'⟩
    by_contra ha'
    have hb : b = 0 := (mul_eq_zero.mp (neg_eq_zero.mp h1.1)).resolve_left ha'
    apply hwg (-(a⁻¹ * d))
    rw [hb, zero_smul, add_zero] at habd
    have h2 : a⁻¹ • (a • (N *ᵥ w) + d • z) = 0 := by rw [habd, smul_zero]
    rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h2
  have hxg := hgood x y hli
  have hB' : ∀ w, Q.polarBilin w z = 0 → L *ᵥ w = s • (N *ᵥ w) := by
    intro w hwz
    by_cases hwg : ∀ c : K, N *ᵥ w ≠ c • z
    · exact hA w hwz hwg
    push Not at hwg
    obtain ⟨μ, hμ⟩ := hwg
    have h1 := hA (w + x) (by
      rw [map_add, LinearMap.add_apply, hwz, hxz, add_zero]) fun c h => hxg (c - μ) (by
        rw [mulVec_add, hμ] at h
        rw [sub_smul, ← h]
        abel)
    rw [mulVec_add, mulVec_add, hs, smul_add] at h1
    exact add_right_cancel h1
  refine eq_of_fix_of_mem hQ hN hadj hz hz0 hXB hXN (fun k hk => ?_) fun w hwz => ⟨s, hB' w hwz⟩
  have hkz : Q.polarBilin k z = 0 := by
    have h1 := hz k
    rwa [hk, map_zero, pow_eq_zero_iff two_ne_zero] at h1
  have h1 := hB' k hkz
  rwa [hk, smul_zero, hL, sub_mulVec, one_mulVec, sub_eq_zero] at h1

end Linear

section Groups

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [Finite K] [CharP K 2]

theorem noPairOrbit_typeC_orth_two (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K)
    (hq : ⇑Q = q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : Nat.card K = 2) {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)}
    (hZ : Odd (Nat.card (center ↥A))) {p : G} (hp2 : orderOf p = 2) {M : GL ι K}
    (hpM : Represents e p M) (hM2 : orderOf M = 2)
    (hnz : ∃ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) ≠ 0) (hℓ : 4 ≤ commRank M) :
    NoPairOrbit A p := by
  subst hq
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hMQ := statedOmega_isometry hpM.2.1
  have hN : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0 := sub_one_mul_self hM2'
  have hiso : ∀ v, Q (v + ((M : Matrix ι ι K) - 1) *ᵥ v) = Q v := fun v => by
    rw [sub_mulVec, one_mulVec, add_sub_cancel]
    exact hMQ v
  obtain ⟨z, hz⟩ := exists_sqrt_vector Q hQ hN hiso
  have hrk : 4 ≤ ((M : Matrix ι ι K) - 1).rank := hℓ
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hiso hz hnz hrk
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hadj := polar_mulVec_adj Q hN hiso
  have hzB : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v) := fun v => by
    rw [polar_self_mulVec Q hiso]
    exact hz v
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hNz : N *ᵥ z = 0 := mulVec_sqrt_vector_of_adj hQ hN hadj hzB
  have hz0 : z ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hnz
    exact hv (by rw [← hz v, map_zero, zero_pow two_ne_zero])
  have hcomm : ∀ X : GL ι K, X * M = M * X → (X : Matrix ι ι K) * N = N * X := fun X hXM => by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hXM
    simp only [Units.val_mul] at h1
    rw [hNdef, Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]
  have hPz : ∀ X : GL ι K, (∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) → X * M = M * X →
      (X : Matrix ι ι K) * polMat Q z z = polMat Q z z * X := fun X hXQ hXM => by
    have hXB := polarBilin_mulVec_of_isometry Q hXQ
    have hXz := mulVec_sqrt_vector_of_commute_adj hQ hzB hXB (hcomm X hXM)
    have h1 := conj_polMat_self_of_polar hXB z
    rw [hXz] at h1
    calc (X : Matrix ι ι K) * polMat Q z z =
        X * polMat Q z z * ((X⁻¹ : GL ι K) : Matrix ι ι K) * X := by
          rw [Matrix.mul_assoc _ (((X⁻¹ : GL ι K) : Matrix ι ι K)), Units.inv_mul, Matrix.mul_one]
      _ = polMat Q z z * X := by rw [h1]
  obtain ⟨y₀, hy₀⟩ := exists_mulVec_eq_of_sqrt_vector hQ hN hiso hz
  obtain ⟨x, y, hxz, hyz, hli⟩ := exists_pair_indep_mod hadj hy₀ hz0 hrk
  have hxg : ∀ c : K, N *ᵥ x ≠ c • z := fun c hc => by
    have h1 := hli 1 0 (-c) (by rw [hc, zero_smul, add_zero, one_smul, neg_smul, add_neg_cancel])
    exact one_ne_zero h1.1
  have hlift : ∀ w, (∀ c : K, N *ᵥ w ≠ c • z) →
      ∃ y₁, Q.polarBilin y₁ z = 0 ∧ Q (w + N *ᵥ y₁) = 0 := by
    intro w hwg
    have hli2 : LinearIndependent K ![N *ᵥ w, z] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      by_cases ha : a = 0
      · rw [ha, zero_smul, zero_add] at hab
        exact ⟨ha, (smul_eq_zero.mp hab).resolve_right hz0⟩
      · exfalso
        apply hwg (-(a⁻¹ * b))
        have h1 : a⁻¹ • (a • (N *ᵥ w) + b • z) = 0 := by rw [hab, smul_zero]
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul] at h1
        rw [neg_smul, eq_neg_iff_add_eq_zero]
        exact h1
    obtain ⟨x', hx'⟩ := exists_polar_dual Q hQ ![N *ᵥ w, z] hli2
    have hwx : Q.polarBilin w (N *ᵥ x' 0) = 1 := by rw [← hadj]; simpa using hx' 0 0
    have hxz' : Q.polarBilin (x' 0) z = 0 := by rw [hBs]; simpa using hx' 1 0
    have hQNx : Q (N *ᵥ x' 0) = 0 := by rw [← hz, hxz', zero_pow two_ne_zero]
    refine ⟨Q w • x' 0, by rw [map_smul, LinearMap.smul_apply, hxz', smul_zero], ?_⟩
    rw [mulVec_smul, quad_add, QuadraticMap.map_smul, hQNx, map_smul, smul_eq_mul, smul_eq_mul,
      hwx, mul_zero, add_zero, mul_one, CharTwo.add_self_eq_zero]
  have hperp : ∀ w y₁, Q.polarBilin w z = 0 → Q.polarBilin (w + N *ᵥ y₁) z = 0 := fun w y₁ hwz => by
    rw [map_add, LinearMap.add_apply, hwz, hadj, hNz, map_zero, add_zero]
  have hNb : ∀ w y₁, N *ᵥ (w + N *ᵥ y₁) = N *ᵥ w := fun w y₁ => by
    rw [mulVec_add, hNN, add_zero]
  intro u hu hu2 horb
  have hu2' : u * u = 1 := by rw [← _root_.sq]; exact hu2
  obtain ⟨U, hU⟩ := exists_represents e (mem_inf.mp hu).1
  have hUM : U * M = M * U := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hU.mul_comm_of_commute hpM hM2' (mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2))
  have hUB := polarBilin_mulVec_of_isometry Q (statedOmega_isometry hU.2.1)
  have key : ∀ b, Q b = 0 → Q.polarBilin b z = 0 → N *ᵥ b ≠ 0 →
      (U : Matrix ι ι K) * cTwoX Q (N *ᵥ b) b = cTwoX Q (N *ᵥ b) b * U := by
    intro b hb hbz hNb0
    have hQNb : Q (N *ᵥ b) = 0 := by rw [← hz, hbz, zero_pow two_ne_zero]
    have hab : Q.polarBilin (N *ᵥ b) b = 0 := by rw [hBs, ← hzB, hbz, zero_pow two_ne_zero]
    have hE : cTwoX Q (N *ᵥ b) b * cTwoX Q (N *ᵥ b) b = 0 := cTwoX_mul_self hab
    set S := unipGL (cTwoX Q (N *ᵥ b) b) hE 1 with hS
    have hSv : (S : Matrix ι ι K) = 1 + cTwoX Q (N *ᵥ b) b := by
      rw [hS, coe_unipGL, one_smul]
    have hSH : S ∈ StatedOmega ⇑Q := mem_statedOmega_of Q hQ hT
      (fun v => by rw [hS, coe_unipGL]; exact cTwoX_isometry hQNb hb hab 1 v)
      (by rw [hS, commRank_unipGL hE one_ne_zero]; exact even_rank_cTwoX hQ _ _)
    have hSM : S * M = M * S := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hSv, hMN]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        cTwoX_commute_typeA hN hadj b]
      abel)
    obtain ⟨g, hg⟩ := exists_represents_of_mem (e := e) hSH
    have hgp : g * p = p * g := commute_of_represents hZ hg hpM hp2' hSM
    have hgC : g ∈ A ⊓ centralizer ({p} : Set G) :=
      mem_inf.mpr ⟨hg.1, mem_centralizer_singleton_iff.mpr hgp⟩
    have hrkS : ∀ c : Kˣ, commRank (M * S * Matrix.GeneralLinearGroup.scalar ι c) ≠
        commRank S := by
      intro c
      rw [eq_one_of_units_of_card_eq_two hK c, map_one, mul_one]
      have h1 : commRank S ≤ 2 := by
        rw [hS, commRank_unipGL hE one_ne_zero]
        exact rank_cTwoX_le _ _
      have h2 : N.rank ≤ commRank (M * S) + 1 := by
        have h3 := rank_le_rank_add_mul_cTwoX hQ hN hNb0
        have e : ((M * S : GL ι K) : Matrix ι ι K) - 1 =
            N + (1 + N) * cTwoX Q (N *ᵥ b) b := by
          rw [Units.val_mul, hSv, hMN]
          noncomm_ring
        unfold commRank
        rwa [e]
      omega
    have hfix := hpM.fix_of_commRank_ne hU hg hu2' hrkS (horb g hgC)
    have hgu : g * u = u * g := by rw [← mul_inv_eq_iff_eq_mul.mp hfix]
    have hUS := hU.mul_comm_of_commute hg (unipGL_sq hE 1) hgu.symm
    rw [hSv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at hUS
    exact add_left_cancel hUS
  have hmemU : ∀ b, Q b = 0 → Q.polarBilin b z = 0 → N *ᵥ b ≠ 0 →
      ∃ c : K, ((U : Matrix ι ι K) - 1) *ᵥ b = c • (N *ᵥ b) := fun b hb hbz hNb0 =>
    exists_sub_one_mulVec_of_commute hQ hN hUB (hcomm U hUM) hNb0 (key b hb hbz hNb0)
  have hLN : ∀ v, ((U : Matrix ι ι K) - 1) *ᵥ (N *ᵥ v) =
      N *ᵥ (((U : Matrix ι ι K) - 1) *ᵥ v) := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.sub_mul, Matrix.mul_sub, hcomm U hUM,
      Matrix.one_mul, Matrix.mul_one]
  have hfixN : ∀ w, Q.polarBilin w z = 0 → ((U : Matrix ι ι K) - 1) *ᵥ (N *ᵥ w) = 0 := by
    have hgood : ∀ w, Q.polarBilin w z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) →
        ((U : Matrix ι ι K) - 1) *ᵥ (N *ᵥ w) = 0 := by
      intro w hwz hwg
      obtain ⟨y₁, -, hy₁⟩ := hlift w hwg
      obtain ⟨c, hc⟩ := hmemU (w + N *ᵥ y₁) hy₁ (hperp w y₁ hwz)
        (by rw [hNb]; exact fun h => hwg 0 (by rw [h, zero_smul]))
      rw [← hNb w y₁, hLN, hc, mulVec_smul, hNN, smul_zero]
    intro w hwz
    by_cases hwg : ∀ c : K, N *ᵥ w ≠ c • z
    · exact hgood w hwz hwg
    push Not at hwg
    obtain ⟨μ, hμ⟩ := hwg
    have h1 := hgood (w + x) (by rw [map_add, LinearMap.add_apply, hwz, hxz, add_zero])
      fun c h => hxg (c - μ) (by
        rw [mulVec_add, hμ] at h
        rw [sub_smul, ← h]
        abel)
    rw [mulVec_add, mulVec_add, hgood x hxz hxg, add_zero] at h1
    exact h1
  have hmem : ∀ w, Q.polarBilin w z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) →
      ∃ c : K, ((U : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w) := by
    intro w hwz hwg
    obtain ⟨y₁, hy₁z, hy₁⟩ := hlift w hwg
    obtain ⟨c, hc⟩ := hmemU (w + N *ᵥ y₁) hy₁ (hperp w y₁ hwz)
      (by rw [hNb]; exact fun h => hwg 0 (by rw [h, zero_smul]))
    rw [hNb, mulVec_add, hfixN y₁ hy₁z, add_zero] at hc
    exact ⟨c, hc⟩
  obtain ⟨s, t, hst⟩ := commutant_typeC_of_mem hQ hN hadj hzB hz0 hxz hyz hli hUB
    (hcomm U hUM) hmem
  refine central_of_commute_all hZ hpM hM2' hu2 hU fun X hX hXM => Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hst, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, hcomm X hXM, hPz X (statedOmega_isometry hX) hXM]

end Groups

end CFSG.ComponentClassification.RankTwoClassical
