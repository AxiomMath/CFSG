module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthPairC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Aut

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Linear

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

omit [CharP K 2] in
theorem betaT_eq_polMat (N : Matrix ι ι K) (z : ι → K) (d : K) :
    betaT Q.polarBilin N z d = d • N + (d ^ 2 + d) • polMat Q z z := rfl

theorem conj_one_add_of_alt {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) {w : ι → K}
    (hw : Q.polarBilin w (N *ᵥ w) = 0) :
    (1 + polMat Q w w) * (1 + N) * (1 + polMat Q w w) = 1 + N + cTwoX Q (N *ᵥ w) w := by
  have hsq : (1 + polMat Q w w) * (1 + polMat Q w w) = 1 := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, polMat_self_mul_self,
      add_zero, add_assoc, matrix_add_self, add_zero]
  calc (1 + polMat Q w w) * (1 + N) * (1 + polMat Q w w)
      = (1 + polMat Q w w) * (1 + polMat Q w w) +
        (1 + polMat Q w w) * N * (1 + polMat Q w w) := by noncomm_ring
    _ = 1 + N + cTwoX Q (N *ᵥ w) w := by
      rw [hsq, conj_transvection_of_alt hadj hw, add_assoc]

omit [DecidableEq ι] [CharP K 2] in
theorem exists_good_pair_span {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) {z y₀ : ι → K}
    (hy₀ : N *ᵥ y₀ = z) (hz0 : z ≠ 0) (hrk : 4 ≤ N.rank) :
    ∃ x y : ι → K, Q.polarBilin x z = 0 ∧ Q.polarBilin y z = 0 ∧ (∀ c : K, N *ᵥ x ≠ c • z) ∧
      ∀ a b : K, N *ᵥ y ≠ a • z + b • (N *ᵥ x) := by
  have hperp : ∀ h, h ∈ LinearMap.range N.mulVecLin →
      Q.polarBilin h y₀ = 0 → ∃ x, N *ᵥ x = h ∧ Q.polarBilin x z = 0 :=
    fun h ⟨x, hx⟩ hhy => ⟨x, hx, by rw [← hy₀, ← hadj]; rw [← hx] at hhy; exact hhy⟩
  obtain ⟨hx', hxr, hxy₀, hxT⟩ := exists_mem_range_perp_not_mem (Q := Q) N y₀
    (T := K ∙ z) (by rw [finrank_span_singleton hz0]; omega)
  obtain ⟨x, hx, hxz⟩ := hperp hx' hxr hxy₀
  obtain ⟨hy', hyr, hyy₀, hyT⟩ := exists_mem_range_perp_not_mem (Q := Q) N y₀
    (T := Submodule.span K (Set.range ![z, N *ᵥ x])) (by
      have h := finrank_range_le_card (R := K) ![z, N *ᵥ x]
      rw [Fintype.card_fin] at h
      change finrank K (Submodule.span K (Set.range ![z, N *ᵥ x])) ≤ 2 at h
      omega)
  obtain ⟨y, hy, hyz⟩ := hperp hy' hyr hyy₀
  refine ⟨x, y, hxz, hyz, fun c h => hxT (Submodule.mem_span_singleton.mpr ⟨c, by rw [← hx, h]⟩),
    fun a b h => hyT ?_⟩
  rw [← hy, h]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

theorem commutant_of_good_mem [Finite K] (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    {z : ι → K} (hz : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v)) (hz0 : z ≠ 0)
    {x y : ι → K} (hxz : Q.polarBilin x z = 0) (hyz : Q.polarBilin y z = 0)
    (hxg : ∀ c : K, N *ᵥ x ≠ c • z) (hyg : ∀ a b : K, N *ᵥ y ≠ a • z + b • (N *ᵥ x))
    {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w)
    (hXN : (X : Matrix ι ι K) * N = N * X)
    (hmem : ∀ w, Q.polarBilin w z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) →
      ∃ c : K, ((X : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w)) :
    ∃ s t : K, (X : Matrix ι ι K) = 1 + s • N + t • polMat Q z z := by
  set L := (X : Matrix ι ι K) - 1 with hL
  have hpair : ∀ w u, Q.polarBilin w z = 0 → Q.polarBilin u z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) →
      (∀ a b : K, N *ᵥ u ≠ a • z + b • (N *ᵥ w)) → ∀ cw cu : K, L *ᵥ w = cw • (N *ᵥ w) →
      L *ᵥ u = cu • (N *ᵥ u) → cw = cu := by
    intro w u hwz huz hwg hug cw cu hw hu
    have hw0 : N *ᵥ w ≠ 0 := fun h => hwg 0 (by rw [h, zero_smul])
    obtain ⟨c, hc⟩ := hmem (w + u) (by rw [map_add, LinearMap.add_apply, hwz, huz, add_zero])
      fun c h => hug c (-1) (by
        rw [mulVec_add] at h
        rw [neg_one_smul, ← h]
        abel)
    rw [mulVec_add, hw, hu, mulVec_add, smul_add] at hc
    have hcu : cu = c := by
      by_contra hne
      apply hug 0 ((c - cu)⁻¹ * (cw - c))
      have h1 : (c - cu) • (N *ᵥ u) = (cw - c) • (N *ᵥ w) := by
        linear_combination (norm := module) -hc
      rw [zero_smul, zero_add, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr
        (Ne.symm hne)), one_smul]
    rw [hcu] at hc ⊢
    have h1 : (cw - c) • (N *ᵥ w) = 0 := by linear_combination (norm := module) hc
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hw0)
  obtain ⟨s, hs⟩ := hmem x hxz hxg
  have hyg' : ∀ c : K, N *ᵥ y ≠ c • z := fun c h => hyg c 0 (by rw [h, zero_smul, add_zero])
  have hys : L *ᵥ y = s • (N *ᵥ y) := by
    obtain ⟨cy, hcy⟩ := hmem y hyz hyg'
    rw [hcy, ← hpair x y hxz hyz hxg hyg s cy hs hcy]
  have hA : ∀ w, Q.polarBilin w z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) → L *ᵥ w = s • (N *ᵥ w) := by
    intro w hwz hwg
    obtain ⟨cw, hcw⟩ := hmem w hwz hwg
    by_cases hxw : ∀ a b : K, N *ᵥ x ≠ a • z + b • (N *ᵥ w)
    · rw [hcw, hpair w x hwz hxz hwg hxw cw s hcw hs]
    push Not at hxw
    obtain ⟨a, b, hab⟩ := hxw
    have hb : b ≠ 0 := fun hb => hxg a (by rw [hab, hb, zero_smul, add_zero])
    have hyw : ∀ a' b' : K, N *ᵥ y ≠ a' • z + b' • (N *ᵥ w) := fun a' b' h => by
      apply hyg (a' - b' * b⁻¹ * a) (b' * b⁻¹)
      rw [h, hab, smul_add, smul_smul, smul_smul, mul_assoc b' b⁻¹ b, inv_mul_cancel₀ hb,
        mul_one]
      module
    rw [hcw, hpair w y hwz hyz hwg hyw cw s hcw hys]
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

theorem commutant_typeC_orth [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hι : 8 ≤ Fintype.card ι) {M X : GL ι K}
    (hMQ : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v) (hM2 : orderOf M = 2)
    (hev : Even (commRank M)) {z : ι → K}
    (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (((M : Matrix ι ι K) - 1) *ᵥ v)) (hz0 : z ≠ 0)
    (hXQ : ∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) (hXM : X * M = M * X)
    (hXg : ∀ g ∈ StatedOmega ⇑Q, g * M * g⁻¹ * M = M * (g * M * g⁻¹) →
      X * (g * M * g⁻¹) = g * M * g⁻¹ * X) :
    ∃ d : K, (X : Matrix ι ι K) = 1 + betaT Q.polarBilin ((M : Matrix ι ι K) - 1) z d := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hN : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0 := sub_one_mul_self hMsq
  have hiso : ∀ v, Q (v + ((M : Matrix ι ι K) - 1) *ᵥ v) = Q v := fun v => by
    rw [sub_mulVec, one_mulVec, add_sub_cancel]
    exact hMQ v
  have hQz : Q z = 0 := quad_eq_zero_of_sqrt_vector hQ hMQ hN hev hz
  have hXN' : (X : Matrix ι ι K) * ((M : Matrix ι ι K) - 1) =
      ((M : Matrix ι ι K) - 1) * X := by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hXM
    simp only [Units.val_mul] at h1
    rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]
  have hev' : Even ((M : Matrix ι ι K) - 1).rank := hev
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hiso hz hXN' hev' ⊢
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hadj := polar_mulVec_adj Q hN hiso
  have hzB : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v) := fun v => by
    rw [polar_self_mulVec Q hiso]
    exact hz v
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hNz : N *ᵥ z = 0 := mulVec_sqrt_vector_of_adj hQ hN hadj hzB
  have hXB := polarBilin_mulVec_of_isometry Q hXQ
  have hXz : (X : Matrix ι ι K) *ᵥ z = z := mulVec_sqrt_vector_of_commute_adj hQ hzB hXB hXN'
  have hconj : ∀ g ∈ StatedOmega ⇑Q, ∀ E : Matrix ι ι K,
      ((g * M * g⁻¹ : GL ι K) : Matrix ι ι K) = 1 + N + E → E * N = N * E →
      (X : Matrix ι ι K) * E = E * X := by
    intro g hg E hgE hEN
    have hcomm := hXg g hg (Units.ext (by
      rw [Units.val_mul (g * M * g⁻¹) M, Units.val_mul M (g * M * g⁻¹), hgE, hMN]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hN, hEN]
      abel))
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hcomm
    rw [Units.val_mul X (g * M * g⁻¹), Units.val_mul (g * M * g⁻¹) X, hgE] at h1
    calc (X : Matrix ι ι K) * E = X * (1 + N + E) - (X + X * N) := by
          simp only [Matrix.mul_add, Matrix.mul_one]
          abel
      _ = (1 + N + E) * X - (X + N * X) := by rw [h1, hXN']
      _ = E * X := by
          simp only [Matrix.add_mul, Matrix.one_mul]
          abel
  obtain ⟨x₁, hx₁⟩ := exists_polarBilin_eq_one hQ hz0
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = N *ᵥ x₁ := ⟨_, rfl⟩
  have hQy₁ : Q y₁ = 1 := by rw [hy₁, ← hz, hx₁, one_pow]
  have hy₁z : Q.polarBilin y₁ z = 0 := by rw [hy₁, hadj, hNz, map_zero]
  have hNy₁ : N *ᵥ y₁ = 0 := by rw [hy₁]; exact hNN x₁
  have hx₁y₁ : Q.polarBilin x₁ y₁ = 1 := by rw [hy₁, polar_self_mulVec Q hiso, ← hz, hx₁, one_pow]
  have hinv : ∀ w : ι → K, (((sqZeroGL (polMat Q w w) (polMat_self_mul_self w))⁻¹ : GL ι K) :
      Matrix ι ι K) = 1 + polMat Q w w := fun w => by
    show 1 - polMat Q w w = 1 + polMat Q w w
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (matrix_add_self _)]
  have hF1 : ∀ a, Q.polarBilin a z = 0 → Q a = 1 →
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ a) a = cTwoX Q (N *ᵥ a) a * X := by
    intro a haz ha
    set S := sqZeroGL (polMat Q a a) (polMat_self_mul_self a) *
      sqZeroGL (polMat Q y₁ y₁) (polMat_self_mul_self y₁) with hS
    have hτ : (1 + polMat Q y₁ y₁) * (1 + N) * (1 + polMat Q y₁ y₁) = 1 + N := by
      rw [conj_one_add_of_alt hadj (by rw [hNy₁, map_zero]), hNy₁, cTwoX_zero_left, add_zero]
    have hg : ((S * M * S⁻¹ : GL ι K) : Matrix ι ι K) = 1 + N + cTwoX Q (N *ᵥ a) a := by
      rw [hS, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
        hinv, hinv, coe_sqZeroGL, coe_sqZeroGL, hMN]
      calc (1 + polMat Q a a) * (1 + polMat Q y₁ y₁) * (1 + N) *
            ((1 + polMat Q y₁ y₁) * (1 + polMat Q a a))
          = (1 + polMat Q a a) * ((1 + polMat Q y₁ y₁) * (1 + N) * (1 + polMat Q y₁ y₁)) *
            (1 + polMat Q a a) := by simp only [Matrix.mul_assoc]
        _ = 1 + N + cTwoX Q (N *ᵥ a) a := by
          rw [hτ, conj_one_add_of_alt hadj (by rw [← hzB, haz, zero_pow two_ne_zero])]
    exact hconj S (transvection_mul_mem_statedOmega hQ hT ha hQy₁) _ hg
      (cTwoX_commute_typeA hN hadj a)
  have hsing : ∀ k, N *ᵥ k = 0 → Q k = 0 → (X : Matrix ι ι K) *ᵥ k = k := by
    intro k hk hQk
    have hkz0 : Q.polarBilin k z = 0 := by
      have h1 := hz k
      rwa [hk, QuadraticMap.map_zero, pow_eq_zero_iff two_ne_zero] at h1
    by_cases hkz : ∃ c : K, k = c • z
    · obtain ⟨c, rfl⟩ := hkz
      rw [mulVec_smul, hXz]
    push Not at hkz
    have hli : LinearIndependent K ![k, z] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      by_cases ha : a = 0
      · rw [ha, zero_smul, zero_add] at hab
        exact ⟨ha, (smul_eq_zero.mp hab).resolve_right hz0⟩
      · exfalso
        apply hkz (-(a⁻¹ * b))
        have h1 : a⁻¹ • (a • k + b • z) = 0 := by rw [hab, smul_zero]
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul] at h1
        rw [neg_smul, eq_neg_iff_add_eq_zero]
        exact h1
    obtain ⟨w', hw'⟩ := exists_polar_dual Q hQ ![k, z] hli
    have hkw : Q.polarBilin k (w' 1) = 0 := by simpa using hw' 0 1
    have hzw : Q.polarBilin z (w' 1) = 1 := by simpa using hw' 1 1
    obtain ⟨w, hw⟩ : ∃ w, w = w' 1 + Q (w' 1) • z := ⟨_, rfl⟩
    have hQw : Q w = 0 := by
      rw [hw, quad_add, QuadraticMap.map_smul, hQz, smul_zero, add_zero, map_smul, smul_eq_mul,
        hBs (w' 1) z, hzw, mul_one, CharTwo.add_self_eq_zero]
    have hwz : Q.polarBilin w z = 1 := by
      rw [hw, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hBs (w' 1) z, hzw,
        TypeCData.pol_self z, smul_zero, add_zero]
    have hwk : Q.polarBilin w k = 0 := by
      rw [hw, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hBs (w' 1) k, hkw,
        hBs z k, hkz0, smul_zero, add_zero]
    have hwNw : Q.polarBilin w (N *ᵥ w) = 1 := by rw [← hzB, hwz, one_pow]
    have hXX := cTwoX_mul_self (Q := Q) hwk
    set S := sqZeroGL (cTwoX Q w k) hXX with hS
    have hSH : S ∈ StatedOmega ⇑Q := by
      refine mem_statedOmega_of Q hQ hT (fun v => ?_) ?_
      · rw [hS, coe_sqZeroGL]
        have h1 := cTwoX_isometry hQw hQk hwk 1 v
        rwa [one_smul] at h1
      · rw [commRank_sqZeroGL]
        exact even_rank_cTwoX hQ w k
    have hSi : ((S⁻¹ : GL ι K) : Matrix ι ι K) = 1 + cTwoX Q w k := by
      show 1 - cTwoX Q w k = 1 + cTwoX Q w k
      rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (matrix_add_self _)]
    have hg : ((S * M * S⁻¹ : GL ι K) : Matrix ι ι K) = 1 + N +
        (cTwoX Q (N *ᵥ w) k + Q.polarBilin w (N *ᵥ w) • polMat Q k k) := by
      rw [Units.val_mul, Units.val_mul, hSi, hS, coe_sqZeroGL, hMN]
      have hsq : (1 + cTwoX Q w k) * (1 + cTwoX Q w k) = 1 := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hXX, add_zero,
          add_assoc, matrix_add_self, add_zero]
      calc (1 + cTwoX Q w k) * (1 + N) * (1 + cTwoX Q w k)
          = (1 + cTwoX Q w k) * (1 + cTwoX Q w k) +
            (1 + cTwoX Q w k) * N * (1 + cTwoX Q w k) := by noncomm_ring
        _ = 1 + N + (cTwoX Q (N *ᵥ w) k + Q.polarBilin w (N *ᵥ w) • polMat Q k k) := by
          rw [hsq, conj_siegel_of_ker hadj hk]
          abel
    obtain ⟨hNE, hEN⟩ := mul_cTwoX_ker hN hadj hk w (Q.polarBilin w (N *ᵥ w))
    have hXE := hconj S hSH _ hg (by rw [hEN, hNE])
    rw [hwNw, one_smul] at hXE
    refine mulVec_sqrt_vector_of_commute_adj hQ (fun v => ?_) hXB hXE
    rw [add_mulVec, cTwoX_mulVec, polMat_mulVec, map_add, map_add, map_smul, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    linear_combination (-(Q.polarBilin v (N *ᵥ w) * Q.polarBilin v k)) *
      CharTwo.two_eq_zero (R := K)
  have hrk : N.rank = 2 ∨ 4 ≤ N.rank := by
    have hr0 : N.rank ≠ 0 := fun h => by
      have h1 : N *ᵥ x₁ ∈ LinearMap.range N.mulVecLin := ⟨x₁, rfl⟩
      rw [Submodule.finrank_eq_zero.mp h] at h1
      rw [hy₁, (Submodule.mem_bot K).mp h1, QuadraticMap.map_zero] at hQy₁
      exact zero_ne_one hQy₁
    obtain ⟨r, hr⟩ := hev'
    omega
  obtain ⟨s, t, hst⟩ : ∃ s t : K, (X : Matrix ι ι K) = 1 + s • N + t • polMat Q z z := by
    rcases hrk with hrk | hrk
    · exact commutant_c2_of_fix hQ hι hN hiso hrk hz hz0 hQz hXQ hXN' (c₀ := 1)
        (fun w hw hwz => hF1 w hwz hw) hsing
    obtain ⟨y₀, hy₀⟩ := exists_mulVec_eq_of_sqrt_vector hQ hN hiso hz
    obtain ⟨x, y, hxz, hyz, hxg, hyg⟩ := exists_good_pair_span hadj hy₀ hz0 hrk
    refine commutant_of_good_mem hQ hN hadj hzB hz0 hxz hyz hxg hyg hXB hXN' fun w hwz hwg => ?_
    have hw0 : N *ᵥ w ≠ 0 := fun h => hwg 0 (by rw [h, zero_smul])
    have hli : LinearIndependent K ![N *ᵥ w, z] := by
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
    obtain ⟨x', hx'⟩ := exists_polar_dual Q hQ ![N *ᵥ w, z] hli
    have hwx : Q.polarBilin w (N *ᵥ x' 0) = 1 := by rw [← hadj]; simpa using hx' 0 0
    have hxz' : Q.polarBilin (x' 0) z = 0 := by rw [hBs]; simpa using hx' 1 0
    have hk₀ : N *ᵥ (N *ᵥ x' 0) = 0 := hNN _
    have hQk₀ : Q (N *ᵥ x' 0) = 0 := by rw [← hz, hxz', zero_pow two_ne_zero]
    have hQw' : Q (w + (1 + Q w) • (N *ᵥ x' 0)) = 1 := by
      rw [quad_add, QuadraticMap.map_smul, hQk₀, smul_zero, add_zero, map_smul, smul_eq_mul, hwx,
        mul_one]
      linear_combination Q w * CharTwo.two_eq_zero (R := K)
    have hw'z : Q.polarBilin (w + (1 + Q w) • (N *ᵥ x' 0)) z = 0 := by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hwz, hadj, hNz, map_zero,
        smul_zero, add_zero]
    have hNw' : N *ᵥ (w + (1 + Q w) • (N *ᵥ x' 0)) = N *ᵥ w := by
      rw [mulVec_add, mulVec_smul, hk₀, smul_zero, add_zero]
    obtain ⟨c, hc⟩ := exists_sub_one_mulVec_of_commute hQ hN hXB hXN' (by rw [hNw']; exact hw0)
      (hF1 _ hw'z hQw')
    have hk₀' : ((X : Matrix ι ι K) - 1) *ᵥ (N *ᵥ x' 0) = 0 := by
      rw [sub_mulVec, one_mulVec, hsing _ hk₀ hQk₀, sub_self]
    refine ⟨c, ?_⟩
    rw [hNw', mulVec_add, mulVec_smul, hk₀', smul_zero, add_zero] at hc
    exact hc
  have h1 := hXQ x₁
  rw [hst, add_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec, ← hy₁, polMat_mulVec,
    hx₁, one_smul] at h1
  have h2 : Q (x₁ + s • y₁ + t • z) = Q x₁ + (s ^ 2 + s + t) := by
    rw [quad_add, quad_add, QuadraticMap.map_smul, QuadraticMap.map_smul, hQy₁, hQz]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hx₁y₁, hx₁, hy₁z]
    ring
  have ht : t = s ^ 2 + s := by
    linear_combination h2.symm.trans h1 - (s ^ 2 + s) * CharTwo.two_eq_zero (R := K)
  exact ⟨s, by rw [hst, ht, betaT_eq_polMat, add_assoc]⟩

theorem conj_betaT_of_conj [Finite K] (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) {z : ι → K}
    (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (N *ᵥ v)) (hQz : Q z = 0) {X : GL ι K}
    (hXQ : ∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) {s : K}
    (hX : (X : Matrix ι ι K) * N * ((X⁻¹ : GL ι K) : Matrix ι ι K) = betaT Q.polarBilin N z s)
    (t : K) :
    (X : Matrix ι ι K) * betaT Q.polarBilin N z t * ((X⁻¹ : GL ι K) : Matrix ι ι K) =
      betaT Q.polarBilin N z (s * t) := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hadj := polar_mulVec_adj Q hN hiso
  have hNz : N *ᵥ z = 0 := mulVec_sqrt_vector hQ hN hiso hz
  have hXB := polarBilin_mulVec_of_isometry Q hXQ
  have hXX : ∀ v, (X : Matrix ι ι K) *ᵥ (((X⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  have hXX' : ∀ v, ((X⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((X : Matrix ι ι K) *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have hQT : ∀ v, Q (betaT Q.polarBilin N z s *ᵥ v) = (s * Q.polarBilin v z) ^ 2 := fun v => by
    have hNvz : Q.polarBilin (N *ᵥ v) z = 0 := by rw [hadj, hNz, map_zero]
    rw [betaT_mulVec, quad_add, QuadraticMap.map_smul, QuadraticMap.map_smul, ← hz, hQz,
      smul_zero, add_zero]
    simp only [map_smul, LinearMap.smul_apply, hNvz, smul_eq_mul]
    ring
  have hfrob : Function.Injective fun c : K => c ^ 2 := by
    intro a b hab
    simp only at hab
    have h : (a + b) ^ 2 = 0 := by rw [CharTwo.add_sq, hab, CharTwo.add_self_eq_zero]
    have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [← CharTwo.sub_eq_add] at h'
    exact sub_eq_zero.mp h'
  have h1 : ∀ u, Q.polarBilin u z = s * Q.polarBilin ((X : Matrix ι ι K) *ᵥ u) z := fun u => by
    apply hfrob
    simp only
    rw [hz, ← hXQ (N *ᵥ u), ← hQT, ← hX]
    simp only [← mulVec_mulVec, hXX']
  have hXz : (X : Matrix ι ι K) *ᵥ z = s • z := by
    rw [← sub_eq_zero]
    refine hQ.2 _ fun w => ?_
    have h2 := h1 (((X⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w)
    rw [hXX] at h2
    have h3 := hXB (((X⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) z
    rw [hXX] at h3
    rw [map_sub, map_smul, smul_eq_mul, h3, h2, sub_self]
  have hXP : (X : Matrix ι ι K) * polMat Q z z * ((X⁻¹ : GL ι K) : Matrix ι ι K) =
      (s * s) • polMat Q z z := by
    rw [conj_polMat_self_of_polar hXB z, hXz, polMat_smul_left, polMat_smul_right, smul_smul]
  rw [betaT_eq_polMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, hX, hXP, betaT_eq_polMat, betaT_eq_polMat]
  linear_combination (norm := module) CharTwo.two_eq_zero (R := K) • ((t * s ^ 2) • polMat Q z z)

omit [CharP K 2] in
theorem conj_cTwoT_of_fix {y z : ι → K} {D : GL ι K}
    (hDQ : ∀ v, Q ((D : Matrix ι ι K) *ᵥ v) = Q v) (hDz : (D : Matrix ι ι K) *ᵥ z = z)
    (hDy : (D : Matrix ι ι K) *ᵥ y = y) (d : K) :
    ((D⁻¹ : GL ι K) : Matrix ι ι K) * cTwoT Q y z d * D = cTwoT Q y z d := by
  have hinv : ∀ v, (D : Matrix ι ι K) *ᵥ v = v → ((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v = v :=
    fun v hv => by
      conv_lhs => rw [← hv]
      rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  rw [cTwoT, cTwoX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, conj_polMat Q hDQ,
    conj_polMat Q hDQ, conj_polMat Q hDQ, hinv z hDz, hinv y hDy]

theorem exists_conj_eq_betaT [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {N : Matrix ι ι K}
    (hN : N * N = 0) (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) {z z' y' : ι → K}
    (hd : TypeCData Q N z z' y') {l : K} (hl : l ≠ 0) :
    ∃ d ∈ StatedOmega ⇑Q,
      (d : Matrix ι ι K) * N * ((d⁻¹ : GL ι K) : Matrix ι ι K) = betaT Q.polarBilin N z l := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hNE : N = TypeCData.e₁ Q N z y' + cTwoT Q (N *ᵥ y') z 1 := by
    rw [TypeCData.e₁, add_assoc, matrix_add_self, add_zero]
  have hTl : betaT Q.polarBilin N z l = l • TypeCData.e₁ Q N z y' + cTwoT Q (N *ᵥ y') z l := by
    have h1 := hd.factor hN hiso l
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      hd.e₁_mul_cTwoT hN hiso, smul_zero, add_zero] at h1
    calc betaT Q.polarBilin N z l = (1 + betaT Q.polarBilin N z l) - 1 := by abel
      _ = l • TypeCData.e₁ Q N z y' + cTwoT Q (N *ᵥ y') z l := by rw [← h1]; abel
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) l
  have hμ0 : μ ≠ 0 := fun h => hl (by rw [hμ, h, mul_zero])
  have hEy : TypeCData.e₁ Q N z y' *ᵥ (N *ᵥ y') = 0 := by
    rw [TypeCData.e₁_mulVec, mulVec_mulVec, hN, zero_mulVec, TypeCData.pol_self,
      hd.pol_y_z hN]
    simp only [add_zero, zero_smul]
  have hli : LinearIndependent K ![z, N *ᵥ y'] :=
    LinearIndependent.pair_iff.mpr (hd.pair_indep hN hiso)
  have hdisj : Disjoint (LinearMap.range (TypeCData.e₁ Q N z y').mulVecLin)
      (Submodule.span K (Set.range ![z, N *ᵥ y'])) := by
    rw [Submodule.disjoint_def]
    rintro x ⟨v, rfl⟩ hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    rw [Fin.sum_univ_two] at hc
    change c 0 • z + c 1 • (N *ᵥ y') = TypeCData.e₁ Q N z y' *ᵥ v at hc
    have e1 : Q.polarBilin (TypeCData.e₁ Q N z y' *ᵥ v) y' = 0 := by
      rw [TypeCData.adj_e₁ hN hiso, hd.e₁_mulVec_y' hiso, map_zero]
    have e2 : Q.polarBilin (TypeCData.e₁ Q N z y' *ᵥ v) z' = 0 := by
      rw [TypeCData.adj_e₁ hN hiso, hd.e₁_mulVec_z' hN hiso, map_zero]
    rw [← hc] at e1 e2
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hBs z y', hd.pol_y'z, hBs (N *ᵥ y') y', hd.pol_y'_y hiso, hBs z z', hd.pol_z'_z hiso,
      hBs (N *ᵥ y') z', hd.pol_z'_y hN hiso, mul_one, mul_zero, zero_add] at e1 e2
    change TypeCData.e₁ Q N z y' *ᵥ v = 0
    rw [← hc, e2, zero_smul, add_zero]
    rw [e2, add_zero] at e1
    rw [e1, zero_smul]
  obtain ⟨D, hDQ, hDfix, hDE⟩ := exists_torus Q hQ (hd.e₁_mul_self hN hiso)
    (TypeCData.adj_e₁ hN hiso) (hd.quad_e₁ hN hiso) ![z, N *ᵥ y']
    (fun j => by fin_cases j; exacts [hd.e₁_mulVec_z hN hiso, hEy]) hli hdisj hμ0
  have hDz : (D : Matrix ι ι K) *ᵥ z = z := hDfix 0
  have hDy : (D : Matrix ι ι K) *ᵥ (N *ᵥ y') = N *ᵥ y' := hDfix 1
  set Dc := hypGL (hd.pol_z_f hiso) (inv_ne_zero hl) with hDc
  have hDcH : Dc ∈ StatedOmega ⇑Q := by
    refine mem_statedOmega_of Q hQ hT (fun v => ?_) ?_
    · rw [hDc, coe_hypGL]
      exact hypMat_isometry (hd.pol_z_f hiso) hd.quad_z (hd.quad_f hiso) (inv_ne_zero hl) v
    · exact hypGL_even_commRank (hd.pol_z_f hiso) (inv_ne_zero hl)
  have hDcE : ((Dc⁻¹ : GL ι K) : Matrix ι ι K) * TypeCData.e₁ Q N z y' * Dc =
      TypeCData.e₁ Q N z y' := by
    have hcomm : TypeCData.e₁ Q N z y' * (Dc : Matrix ι ι K) =
        (Dc : Matrix ι ι K) * TypeCData.e₁ Q N z y' := by
      rw [hDc, coe_hypGL]
      exact hd.e₁_mul_hypMat hN hiso _
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hDcT : ((Dc⁻¹ : GL ι K) : Matrix ι ι K) * cTwoT Q (N *ᵥ y') z 1 * Dc =
      cTwoT Q (N *ᵥ y') z l := by
    rw [hDc, hd.conj_cTwoT hN hiso hl 1, mul_one]
  refine ⟨(D ^ 2 * Dc)⁻¹, inv_mem (mul_mem (sq_mem_statedOmega Q hQ hT hDQ) hDcH), ?_⟩
  have hDE2 : ((D⁻¹ : GL ι K) : Matrix ι ι K) * ((D⁻¹ : GL ι K) : Matrix ι ι K) *
      TypeCData.e₁ Q N z y' * ((D : Matrix ι ι K) * D) = l • TypeCData.e₁ Q N z y' := by
    calc ((D⁻¹ : GL ι K) : Matrix ι ι K) * ((D⁻¹ : GL ι K) : Matrix ι ι K) *
          TypeCData.e₁ Q N z y' * ((D : Matrix ι ι K) * D)
        = ((D⁻¹ : GL ι K) : Matrix ι ι K) * (((D⁻¹ : GL ι K) : Matrix ι ι K) *
          TypeCData.e₁ Q N z y' * D) * D := by simp only [Matrix.mul_assoc]
      _ = l • TypeCData.e₁ Q N z y' := by
          rw [hDE, Matrix.mul_smul, Matrix.smul_mul, hDE, smul_smul, ← hμ]
  have hDT2 : ((D⁻¹ : GL ι K) : Matrix ι ι K) * ((D⁻¹ : GL ι K) : Matrix ι ι K) *
      cTwoT Q (N *ᵥ y') z 1 * ((D : Matrix ι ι K) * D) = cTwoT Q (N *ᵥ y') z 1 := by
    calc ((D⁻¹ : GL ι K) : Matrix ι ι K) * ((D⁻¹ : GL ι K) : Matrix ι ι K) *
          cTwoT Q (N *ᵥ y') z 1 * ((D : Matrix ι ι K) * D)
        = ((D⁻¹ : GL ι K) : Matrix ι ι K) * (((D⁻¹ : GL ι K) : Matrix ι ι K) *
          cTwoT Q (N *ᵥ y') z 1 * D) * D := by simp only [Matrix.mul_assoc]
      _ = cTwoT Q (N *ᵥ y') z 1 := by
          rw [conj_cTwoT_of_fix hDQ hDz hDy, conj_cTwoT_of_fix hDQ hDz hDy]
  rw [inv_inv, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, pow_two, _root_.mul_inv_rev,
    Units.val_mul, Units.val_mul, hTl]
  calc ((Dc⁻¹ : GL ι K) : Matrix ι ι K) *
        (((D⁻¹ : GL ι K) : Matrix ι ι K) * ((D⁻¹ : GL ι K) : Matrix ι ι K)) * N *
        ((D : Matrix ι ι K) * D * Dc)
      = ((Dc⁻¹ : GL ι K) : Matrix ι ι K) * (((D⁻¹ : GL ι K) : Matrix ι ι K) *
          ((D⁻¹ : GL ι K) : Matrix ι ι K) * N * ((D : Matrix ι ι K) * D)) * Dc := by
        simp only [Matrix.mul_assoc]
    _ = l • TypeCData.e₁ Q N z y' + cTwoT Q (N *ᵥ y') z l := by
        conv_lhs => rw [hNE]
        rw [Matrix.mul_add, Matrix.add_mul, hDE2, hDT2, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_smul, Matrix.smul_mul, hDcE, hDcT]

end Linear

end CFSG.ComponentClassification.RankTwoClassical
