module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Orth
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222SpBC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Two

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Commutant

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

theorem commutant_typeA_of_quad_eq_one (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) (hsing : ∀ v, Q (N *ᵥ v) = 0) (hN0 : N ≠ 0)
    {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w) (hXN : (X : Matrix ι ι K) * N = N * X)
    (hone : ∀ w, Q w = 1 →
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X) :
    ∃ c : K, (X : Matrix ι ι K) = 1 + c • N := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hXNv : ∀ v, (X : Matrix ι ι K) *ᵥ (N *ᵥ v) = N *ᵥ ((X : Matrix ι ι K) *ᵥ v) := fun v => by
    rw [mulVec_mulVec, hXN, ← mulVec_mulVec]
  have hfix : ∀ y, (X : Matrix ι ι K) *ᵥ (N *ᵥ y) = N *ᵥ y := fun y => by
    by_cases hy : N *ᵥ y = 0
    · rw [hy, mulVec_zero]
    obtain ⟨w, hw, hwy⟩ := exists_quad_eq_one_mulVec hQ hN hadj hsing hy
    rw [← hwy] at hy ⊢
    obtain ⟨c, hc⟩ := exists_sub_one_mulVec_of_commute hQ hN hXB hXN hy (hone w hw)
    rw [sub_mulVec, one_mulVec] at hc
    have h1 := congrArg (N *ᵥ ·) hc
    simp only [mulVec_sub, mulVec_smul, hNN, smul_zero] at h1
    rw [hXNv]
    exact sub_eq_zero.mp h1
  have hmem : ∀ w, N *ᵥ w ≠ 0 → ∃ c : K, ((X : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w) := by
    intro w hw
    obtain ⟨y, hy⟩ := exists_polarBilin_eq_one hQ hw
    have hQw : Q (w + N *ᵥ ((1 + Q w) • y)) = 1 := by
      rw [quad_add, hsing, add_zero, ← hadj, map_smul, smul_eq_mul, hBs (N *ᵥ w), hy, mul_one,
        add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    have hNw : N *ᵥ (w + N *ᵥ ((1 + Q w) • y)) = N *ᵥ w := by rw [mulVec_add, hNN, add_zero]
    obtain ⟨c, hc⟩ := exists_sub_one_mulVec_of_commute hQ hN hXB hXN (by rwa [hNw]) (hone _ hQw)
    have h0 : ((X : Matrix ι ι K) - 1) *ᵥ (N *ᵥ ((1 + Q w) • y)) = 0 := by
      rw [sub_mulVec, one_mulVec, hfix, sub_self]
    rw [hNw, mulVec_add, h0, add_zero] at hc
    exact ⟨c, hc⟩
  obtain ⟨y, hy⟩ : ∃ y, N *ᵥ y ≠ 0 := by
    by_contra! h
    exact hN0 (Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, zero_mulVec])
  obtain ⟨x, hxy⟩ := exists_polarBilin_eq_one hQ hy
  have hyx : Q.polarBilin y (N *ᵥ x) = 1 := by rw [← hadj, hBs, hxy]
  have hli : ∀ a b : K, a • (N *ᵥ x) + b • (N *ᵥ y) = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 := congrArg (Q.polarBilin x) hab
    have h2 := congrArg (Q.polarBilin y) hab
    simp only [map_add, map_smul, smul_eq_mul, halt, hxy, hyx, map_zero, mul_zero, mul_one,
      zero_add, add_zero] at h1 h2
    exact ⟨h2, h1⟩
  obtain ⟨c, hc⟩ := exists_eq_smul_of_mulVec_mem hli hmem
  exact ⟨c, by rw [← hc, add_sub_cancel]⟩

theorem commute_cTwoX_of_four_le_rank [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {M X : GL ι K}
    {N : Matrix ι ι K} (hMN : (M : Matrix ι ι K) = 1 + N) (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) (hsing : ∀ v, Q (N *ᵥ v) = 0)
    (hrk : 4 ≤ N.rank)
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w)
    (hXN : (X : Matrix ι ι K) * N = N * X)
    (hXg : ∀ g ∈ StatedOmega ⇑Q, g * M * g⁻¹ * M = M * (g * M * g⁻¹) →
      X * (g * M * g⁻¹) = g * M * g⁻¹ * X)
    {w : ι → K} (hw : Q w = 1) :
    (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X := by
  have hBs : ∀ x y, Q.polarBilin x y = Q.polarBilin y x := polarBilin_comm Q
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hXNv : ∀ v, (X : Matrix ι ι K) *ᵥ (N *ᵥ v) = N *ᵥ ((X : Matrix ι ι K) *ᵥ v) := fun v => by
    rw [mulVec_mulVec, hXN, ← mulVec_mulVec]
  have hrange : ∀ {h : ι → K}, h ∈ LinearMap.range N.mulVecLin → ∃ y, N *ᵥ y = h :=
    fun ⟨y, hy⟩ => ⟨y, hy⟩
  have hXu : ∀ {w y : ι → K}, Q w = 1 → Q.polarBilin (N *ᵥ y) w = 0 →
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) (N *ᵥ y) = cTwoX Q (N *ᵥ w) (N *ᵥ y) * X := by
    intro w y hw huw
    have hQ₂ : Q (w + N *ᵥ y) = 1 := by
      rw [quad_add, hw, hsing, hBs, huw, add_zero, add_zero]
    have hN₂ : N *ᵥ (w + N *ᵥ y) = N *ᵥ w := by rw [mulVec_add, hNN, add_zero]
    have h21 : cTwoX Q (N *ᵥ (w + N *ᵥ y)) (w + N *ᵥ y) *ᵥ w = 0 := by
      rw [hN₂, cTwoX_mulVec, halt, zero_smul, zero_add, map_add, TypeCData.pol_self, zero_add,
        hBs w (N *ᵥ y), huw, zero_smul]
    have h := commute_cTwoX_pair hQ hT hMN hN hadj halt hXN hXg hw hQ₂ h21
    have hsum : cTwoX Q (N *ᵥ w) w + cTwoX Q (N *ᵥ w) (w + N *ᵥ y) =
        cTwoX Q (N *ᵥ w) (N *ᵥ y) := by
      rw [show w + N *ᵥ y = w + (1 : K) • N *ᵥ y by rw [one_smul], cTwoX_add_smul_right,
        one_smul, ← add_assoc, matrix_add_self, zero_add]
    rwa [hN₂, hsum] at h
  have heig : ∀ y, ∃ c : K, (X : Matrix ι ι K) *ᵥ (N *ᵥ y) = c • (N *ᵥ y) := by
    intro y
    by_cases hy : N *ᵥ y = 0
    · exact ⟨0, by rw [hy, mulVec_zero, smul_zero]⟩
    obtain ⟨w, hw, hwy⟩ := exists_quad_eq_one_mulVec hQ hN hadj hsing hy
    rw [← hwy] at hy ⊢
    obtain ⟨u, hu, huw, hua⟩ := exists_mem_range_perp_not_mem (Q := Q) N w
      (T := Submodule.span K (Set.range ![N *ᵥ w])) (by
        have h := finrank_range_le_card (R := K) ![N *ᵥ w]
        rw [Fintype.card_fin] at h
        change finrank K (Submodule.span K (Set.range ![N *ᵥ w])) ≤ 1 at h
        omega)
    obtain ⟨u', hu', hu'w, hu'T⟩ := exists_mem_range_perp_not_mem (Q := Q) N w
      (T := Submodule.span K (Set.range ![u, N *ᵥ w])) (by
        have h := finrank_range_le_card (R := K) ![u, N *ᵥ w]
        rw [Fintype.card_fin] at h
        change finrank K (Submodule.span K (Set.range ![u, N *ᵥ w])) ≤ 2 at h
        omega)
    have hli1 : LinearIndependent K ![N *ᵥ w] :=
      linearIndependent_unique_iff.mpr (by simpa using hy)
    have hli2 : LinearIndependent K ![u, N *ᵥ w] := linearIndependent_finCons.mpr ⟨hli1, hua⟩
    have hli3 : LinearIndependent K ![u', u, N *ᵥ w] :=
      linearIndependent_finCons.mpr ⟨hli2, hu'T⟩
    obtain ⟨yu, rfl⟩ := hrange hu
    obtain ⟨yu', rfl⟩ := hrange hu'
    exact exists_mulVec_eq_smul_of_commute_cTwoX hQ hli3 (hXu hw huw) (hXu hw hu'w)
  have hfix := mulVec_eq_self_of_eigen hQ hadj halt hXB hXNv heig
  have hXab : ∀ y y', (X : Matrix ι ι K) * cTwoX Q (N *ᵥ y) (N *ᵥ y') =
      cTwoX Q (N *ᵥ y) (N *ᵥ y') * X := by
    intro y y'
    have h := conj_cTwoX_of_polar hXB (N *ᵥ y) (N *ᵥ y')
    rw [hfix, hfix] at h
    calc (X : Matrix ι ι K) * cTwoX Q (N *ᵥ y) (N *ᵥ y') =
        X * cTwoX Q (N *ᵥ y) (N *ᵥ y') * ((X⁻¹ : GL ι K) : Matrix ι ι K) * X := by
          rw [Matrix.mul_assoc _ (((X⁻¹ : GL ι K) : Matrix ι ι K)), Units.inv_mul, Matrix.mul_one]
      _ = cTwoX Q (N *ᵥ y) (N *ᵥ y') * X := by rw [h]
  have hDk : ∀ a y, (X : Matrix ι ι K) * cTwoX Q (N *ᵥ (a + N *ᵥ y)) (a + N *ᵥ y) -
      cTwoX Q (N *ᵥ (a + N *ᵥ y)) (a + N *ᵥ y) * X =
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ a) a - cTwoX Q (N *ᵥ a) a * X := by
    intro a y
    have h1 : cTwoX Q (N *ᵥ (a + N *ᵥ y)) (a + N *ᵥ y) =
        cTwoX Q (N *ᵥ a) a + cTwoX Q (N *ᵥ a) (N *ᵥ y) := by
      rw [mulVec_add, hNN, add_zero, show a + N *ᵥ y = a + (1 : K) • N *ᵥ y by rw [one_smul],
        cTwoX_add_smul_right, one_smul]
    rw [h1, Matrix.mul_add, Matrix.add_mul, hXab a y]
    abel
  have hpair : ∀ u, Q u = 1 → Q.polarBilin w u = 0 → Q.polarBilin w (N *ᵥ u) = 0 →
      ((X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w - cTwoX Q (N *ᵥ w) w * X) +
        ((X : Matrix ι ι K) * cTwoX Q (N *ᵥ u) u - cTwoX Q (N *ᵥ u) u * X) = 0 := by
    intro u hu hwu hwNu
    have h := commute_cTwoX_pair hQ hT hMN hN hadj halt hXN hXg hw hu (by
      rw [cTwoX_mulVec, hwNu, hwu, zero_smul, zero_smul, add_zero])
    rw [Matrix.mul_add, Matrix.add_mul] at h
    rw [sub_add_sub_comm, h, sub_self]
  have hexp : ∀ a b : ι → K, cTwoX Q (N *ᵥ (a + b)) (a + b) = cTwoX Q (N *ᵥ a) a +
      cTwoX Q (N *ᵥ b) b + (cTwoX Q (N *ᵥ a) b + cTwoX Q (N *ᵥ b) a) := fun a b =>
    Matrix.ext_iff_mulVec.mpr fun x => by
      simp only [mulVec_add, add_mulVec, cTwoX_mulVec, map_add]
      module
  by_cases hw0 : N *ᵥ w = 0
  · rw [hw0, cTwoX_zero_left, Matrix.mul_zero, Matrix.zero_mul]
  have hli1 : LinearIndependent K ![N *ᵥ w] :=
    linearIndependent_unique_iff.mpr (by simpa using hw0)
  have key : ∀ v, N *ᵥ v ∉ Submodule.span K (Set.range ![N *ᵥ w]) →
      Q.polarBilin (N *ᵥ v) w = 0 →
      ((X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w - cTwoX Q (N *ᵥ w) w * X) +
        ((X : Matrix ι ι K) * (cTwoX Q (N *ᵥ w) v + cTwoX Q (N *ᵥ v) w) -
          (cTwoX Q (N *ᵥ w) v + cTwoX Q (N *ᵥ v) w) * X) = 0 := by
    intro v hvT hvw
    have hli : LinearIndependent K ![N *ᵥ v, N *ᵥ w] := linearIndependent_finCons.mpr ⟨hli1, hvT⟩
    obtain ⟨z, hz⟩ := exists_polar_dual Q hQ ![N *ᵥ v, N *ᵥ w] hli
    have h00 : Q.polarBilin (N *ᵥ v) (z 0) = 1 := by simpa using hz 0 0
    have h10 : Q.polarBilin (N *ᵥ w) (z 0) = 0 := by simpa using hz 1 0
    have h01 : Q.polarBilin (N *ᵥ v) (z 1) = 0 := by simpa using hz 0 1
    have h11 : Q.polarBilin (N *ᵥ w) (z 1) = 1 := by simpa using hz 1 1
    set y₁ := (1 + Q v) • z 0 + Q.polarBilin v w • z 1 with hy₁
    have hBv : Q.polarBilin v (N *ᵥ y₁) = 1 + Q v := by
      rw [← hadj, hy₁, map_add, map_smul, map_smul, h00, h01, smul_eq_mul, smul_eq_mul, mul_one,
        mul_zero, add_zero]
    have hBw : Q.polarBilin w (N *ᵥ y₁) = Q.polarBilin v w := by
      rw [← hadj, hy₁, map_add, map_smul, map_smul, h10, h11, smul_eq_mul, smul_eq_mul, mul_one,
        mul_zero, zero_add]
    have hv₁Q : Q (v + N *ᵥ y₁) = 1 := by
      rw [quad_add, hsing, add_zero, hBv, add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    have hwv₁ : Q.polarBilin w (v + N *ᵥ y₁) = 0 := by
      rw [map_add, hBw, hBs w v, CharTwo.add_self_eq_zero]
    have hwNv₁ : Q.polarBilin w (N *ᵥ (v + N *ᵥ y₁)) = 0 := by
      rw [mulVec_add, hNN, add_zero, hBs, hvw]
    have P1 := hpair _ hv₁Q hwv₁ hwNv₁
    rw [hDk v y₁] at P1
    set y₂ := y₁ + z 0 with hy₂
    have hBw₂ : Q.polarBilin w (N *ᵥ y₂) = Q.polarBilin v w := by
      rw [hy₂, mulVec_add, map_add, hBw, ← hadj w (z 0), h10, add_zero]
    have hBv₂ : Q.polarBilin v (N *ᵥ y₂) = Q v := by
      rw [hy₂, mulVec_add, map_add, hBv, ← hadj v (z 0), h00]
      linear_combination CharTwo.two_eq_zero (R := K)
    have huQ : Q (w + v + N *ᵥ y₂) = 1 := by
      rw [quad_add, quad_add, hw, hsing, map_add, LinearMap.add_apply, hBw₂, hBv₂, hBs w v]
      linear_combination (Q v + Q.polarBilin v w) * CharTwo.two_eq_zero (R := K)
    have hwu : Q.polarBilin w (w + v + N *ᵥ y₂) = 0 := by
      rw [map_add, map_add, TypeCData.pol_self, hBw₂, zero_add, hBs w v,
        CharTwo.add_self_eq_zero]
    have hwNu : Q.polarBilin w (N *ᵥ (w + v + N *ᵥ y₂)) = 0 := by
      rw [mulVec_add, mulVec_add, hNN, add_zero, map_add, halt, zero_add, hBs, hvw]
    have P2 := hpair _ huQ hwu hwNu
    rw [hDk (w + v) y₂, hexp w v] at P2
    simp only [Matrix.mul_add, Matrix.add_mul] at P1 P2 ⊢
    linear_combination (norm := module) P2 - P1
  obtain ⟨h₁, hh₁, hh₁w, hh₁T⟩ := exists_mem_range_perp_not_mem (Q := Q) N w
    (T := Submodule.span K (Set.range ![N *ᵥ w])) (by
      have h := finrank_range_le_card (R := K) ![N *ᵥ w]
      rw [Fintype.card_fin] at h
      change finrank K (Submodule.span K (Set.range ![N *ᵥ w])) ≤ 1 at h
      omega)
  obtain ⟨h₂, hh₂, hh₂w, hh₂T⟩ := exists_mem_range_perp_not_mem (Q := Q) N w
    (T := Submodule.span K (Set.range ![h₁, N *ᵥ w])) (by
      have h := finrank_range_le_card (R := K) ![h₁, N *ᵥ w]
      rw [Fintype.card_fin] at h
      change finrank K (Submodule.span K (Set.range ![h₁, N *ᵥ w])) ≤ 2 at h
      omega)
  obtain ⟨v, rfl⟩ := hrange hh₁
  obtain ⟨v', rfl⟩ := hrange hh₂
  have hle : Submodule.span K (Set.range ![N *ᵥ w]) ≤
      Submodule.span K (Set.range ![N *ᵥ v, N *ᵥ w]) :=
    Submodule.span_mono (Set.range_subset_iff.mpr fun i => ⟨1, by fin_cases i; rfl⟩)
  have hv'T : N *ᵥ v' ∉ Submodule.span K (Set.range ![N *ᵥ w]) := fun h => hh₂T (hle h)
  have hvv'T : N *ᵥ (v + v') ∉ Submodule.span K (Set.range ![N *ᵥ w]) := fun h => hh₂T (by
    have h1 := Submodule.sub_mem _ (hle h)
      (Submodule.subset_span ⟨0, rfl⟩ : N *ᵥ v ∈ Submodule.span K (Set.range ![N *ᵥ v, N *ᵥ w]))
    rwa [mulVec_add, add_sub_cancel_left] at h1)
  have k1 := key v hh₁T hh₁w
  have k2 := key v' hv'T hh₂w
  have k3 := key (v + v') hvv'T (by rw [mulVec_add, map_add, LinearMap.add_apply, hh₁w, hh₂w,
    add_zero])
  have hG : cTwoX Q (N *ᵥ w) (v + v') + cTwoX Q (N *ᵥ (v + v')) w =
      (cTwoX Q (N *ᵥ w) v + cTwoX Q (N *ᵥ v) w) + (cTwoX Q (N *ᵥ w) v' + cTwoX Q (N *ᵥ v') w) :=
    Matrix.ext_iff_mulVec.mpr fun x => by
      simp only [mulVec_add, add_mulVec, cTwoX_mulVec, map_add]
      module
  rw [hG] at k3
  simp only [Matrix.mul_add, Matrix.add_mul] at k1 k2 k3
  rw [← sub_eq_zero]
  linear_combination (norm := module) k1 + k2 - k3

variable [Finite K]

theorem commutant_typeA_orth_of_eight_le_card (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hι : 8 ≤ Fintype.card ι) {M X : GL ι K}
    (hMQ : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v) (hM2 : orderOf M = 2)
    (hsing : ∀ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0)
    (hXQ : ∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) (hXM : X * M = M * X)
    (hXg : ∀ g ∈ StatedOmega ⇑Q, g * M * g⁻¹ * M = M * (g * M * g⁻¹) →
      X * (g * M * g⁻¹) = g * M * g⁻¹ * X) :
    ∃ c : K, (X : Matrix ι ι K) = 1 + c • ((M : Matrix ι ι K) - 1) := by
  have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hadj := polarBilin_sub_one_adj (polarBilin_mulVec_of_isometry Q hMQ) hM2
  have hXN : (X : Matrix ι ι K) * ((M : Matrix ι ι K) - 1) = ((M : Matrix ι ι K) - 1) * X := by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hXM
    simp only [Units.val_mul] at h1
    rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]
  have hN0 : (M : Matrix ι ι K) - 1 ≠ 0 := sub_one_ne_zero fun h => by
    rw [h, orderOf_one] at hM2
    omega
  have hN : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0 := sub_one_mul_self hMsq
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hadj hsing hXN hN0 hN ⊢
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0 := fun v => by
    have h1 := hMQ v
    rw [hMN, add_mulVec, one_mulVec, quad_add, hsing, add_zero] at h1
    exact add_eq_left.mp h1
  have hXB := polarBilin_mulVec_of_isometry Q hXQ
  refine commutant_typeA_of_quad_eq_one hQ hN hadj halt hsing hN0 hXB hXN fun w hw => ?_
  by_cases hA : ∃ h, N *ᵥ h = 0 ∧ Q h ≠ 0
  · obtain ⟨h, hh, hQh⟩ := hA
    exact commute_cTwoX_of_ker hQ hT hMN hN hadj halt hXN hXg hh hQh hw
  · push Not at hA
    have hrk : 4 ≤ N.rank := by
      have h1 := two_mul_finrank_le_of_forall_eq_zero hQ (U := LinearMap.ker N.mulVecLin)
        fun x hx => hA x (by simpa using hx)
      have h2 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
      rw [Module.finrank_fintype_fun_eq_card] at h1 h2
      show 4 ≤ finrank K (LinearMap.range N.mulVecLin)
      omega
    exact commute_cTwoX_of_four_le_rank hQ hT hMN hN hadj halt hsing hrk hXB hXN hXg hw

end Commutant

section Families

theorem deltaCentral_of_typeA_orth_of_eight_le_card {G : Type} [Group G] {A : Subgroup G}
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K) (hq : ⇑Q = q)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hι : 8 ≤ Fintype.card ι) {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)}
    (hZ : Odd (Nat.card (center ↥A))) {p : G} {ℓ : ℕ}
    (hp : HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) p .a ℓ) :
    DeltaCentral A p (alphaGroup e p) := by
  subst hq
  obtain ⟨hp2, M, hpM, hM2, -, -, hsing⟩ := hp
  replace hsing : ∀ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0 := hsing
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  refine deltaCentral_alpha_of hZ hp2' hpM hM2 fun X hXH hXM hXg => ⟨X, hXH,
    ⟨1, by rw [map_one, mul_one]⟩, ?_⟩
  obtain ⟨c, hc⟩ := commutant_typeA_orth_of_eight_le_card hQ hT hι
    (statedOmega_isometry hpM.2.1) hM2 hsing (statedOmega_isometry hXH) hXM hXg
  exact ⟨c, by rw [hc, add_sub_cancel_left]⟩

theorem deltaAlphaTwo_orthPlus : DeltaAlphaTwo .orthPlus := by
  intro G _ _ A D hD _ hZ _ p hp
  cases D with
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨ℓ, hpℓ⟩ := hp
    show DeltaCentral A p (alphaGroup e p)
    exact deltaCentral_of_typeA_orth_of_eight_le_card (quadPlus n K) (StatedQuadPlus n K)
      (coe_quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)
      (exists_totallySingular_quadPlus (by omega) K)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ hpℓ
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem deltaAlphaTwo_orthMinus : DeltaAlphaTwo .orthMinus := by
  intro G _ _ A D hD _ hZ _ p hp
  cases D with
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨ℓ, hpℓ⟩ := hp
    show DeltaCentral A p (alphaGroup e p)
    exact deltaCentral_of_typeA_orth_of_eight_le_card (quadMinus n K b c)
      (StatedQuadMinus n K b c) (coe_quadMinus n K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
      (exists_totallySingular_quadMinus hn K b c)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ hpℓ
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD

end Families

end CFSG.ComponentClassification.RankTwoClassical
