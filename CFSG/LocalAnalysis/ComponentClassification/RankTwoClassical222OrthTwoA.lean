module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222PairRank
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthPair
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222SpBC

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

section Linear

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

theorem commutant_typeA_of_singular (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0) (hsing : ∀ v, Q (N *ᵥ v) = 0) (hN0 : N ≠ 0)
    {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w) (hXN : (X : Matrix ι ι K) * N = N * X)
    (hzero : ∀ w, Q w = 0 → N *ᵥ w ≠ 0 →
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X) :
    ∃ c : K, (X : Matrix ι ι K) = 1 + c • N := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hXNv : ∀ v, (X : Matrix ι ι K) *ᵥ (N *ᵥ v) = N *ᵥ ((X : Matrix ι ι K) *ᵥ v) := fun v => by
    rw [mulVec_mulVec, hXN, ← mulVec_mulVec]
  have hlift : ∀ w, N *ᵥ w ≠ 0 → ∃ y, Q (w + N *ᵥ y) = 0 := fun w hw => by
    obtain ⟨y, hy⟩ := exists_polarBilin_eq_one hQ hw
    refine ⟨Q w • y, ?_⟩
    rw [quad_add, hsing, add_zero, ← hadj, map_smul, smul_eq_mul, hBs (N *ᵥ w), hy, mul_one,
      CharTwo.add_self_eq_zero]
  have hfix : ∀ y, (X : Matrix ι ι K) *ᵥ (N *ᵥ y) = N *ᵥ y := fun y => by
    by_cases hy : N *ᵥ y = 0
    · rw [hy, mulVec_zero]
    obtain ⟨z, hz⟩ := hlift y hy
    have hNz : N *ᵥ (y + N *ᵥ z) = N *ᵥ y := by rw [mulVec_add, hNN, add_zero]
    have hy' : N *ᵥ (y + N *ᵥ z) ≠ 0 := by rwa [hNz]
    obtain ⟨c, hc⟩ := exists_sub_one_mulVec_of_commute hQ hN hXB hXN hy' (hzero _ hz hy')
    rw [sub_mulVec, one_mulVec] at hc
    have h1 := congrArg (N *ᵥ ·) hc
    simp only [mulVec_sub, mulVec_smul, hNN, smul_zero] at h1
    rw [← hNz, hXNv]
    exact sub_eq_zero.mp h1
  have hmem : ∀ w, N *ᵥ w ≠ 0 → ∃ c : K, ((X : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w) := by
    intro w hw
    obtain ⟨y, hy⟩ := hlift w hw
    have hNw : N *ᵥ (w + N *ᵥ y) = N *ᵥ w := by rw [mulVec_add, hNN, add_zero]
    have hw' : N *ᵥ (w + N *ᵥ y) ≠ 0 := by rwa [hNw]
    obtain ⟨c, hc⟩ := exists_sub_one_mulVec_of_commute hQ hN hXB hXN hw' (hzero _ hy hw')
    have h0 : ((X : Matrix ι ι K) - 1) *ᵥ (N *ᵥ y) = 0 := by
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

omit [CharP K 2] in
theorem rank_le_rank_add_mul_cTwoX (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) {w : ι → K} (hw : N *ᵥ w ≠ 0) :
    N.rank ≤ (N + (1 + N) * cTwoX Q (N *ᵥ w) w).rank + 1 := by
  classical
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  set X := cTwoX Q (N *ᵥ w) w with hX
  set f := N + (1 + N) * X with hf
  have hli : LinearIndependent K ![N *ᵥ w, w] := LinearIndependent.pair_iff.mpr fun s t hst => by
    have h1 := congrArg (N *ᵥ ·) hst
    simp only [mulVec_add, mulVec_smul, hNN, smul_zero, zero_add, mulVec_zero] at h1
    have ht : t = 0 := (smul_eq_zero.mp h1).resolve_right hw
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hw, ht⟩
  obtain ⟨z, hz⟩ := exists_polar_dual Q hQ ![N *ᵥ w, w] hli
  have h00 : Q.polarBilin (N *ᵥ w) (z 0) = 1 := by simpa using hz 0 0
  have h10 : Q.polarBilin w (z 0) = 0 := by simpa using hz 1 0
  have h01 : Q.polarBilin (N *ᵥ w) (z 1) = 0 := by simpa using hz 0 1
  have h11 : Q.polarBilin w (z 1) = 1 := by simpa using hz 1 1
  set H : Submodule K (ι → K) := LinearMap.ker (Q.polarBilin.flip (N *ᵥ w)) ⊓
    LinearMap.ker (Q.polarBilin.flip w) with hH
  have hmemH : ∀ v, v ∈ H ↔ Q.polarBilin v (N *ᵥ w) = 0 ∧ Q.polarBilin v w = 0 := fun v => by
    simp [hH, LinearMap.flip_apply]
  have hfH : ∀ v ∈ H, f *ᵥ v = N *ᵥ v := by
    intro v hv
    obtain ⟨h1, h2⟩ := (hmemH v).mp hv
    rw [hf, add_mulVec, ← mulVec_mulVec, hX, cTwoX_mulVec, h1, h2, zero_smul, zero_smul,
      add_zero, mulVec_zero, add_zero]
  set R := Submodule.span K (Set.range ![N *ᵥ z 0, N *ᵥ z 1]) with hR
  have hcov : LinearMap.range N.mulVecLin ≤ H.map f.mulVecLin ⊔ R := by
    rintro _ ⟨v, rfl⟩
    set h := v - Q.polarBilin v (N *ᵥ w) • z 0 - Q.polarBilin v w • z 1 with hh
    have hhH : h ∈ H := by
      rw [hmemH, hh]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hBs (z 0), hBs (z 1), h00, h10, h01, h11, mul_one, mul_zero, sub_zero, sub_self,
        and_self]
    have hv : N *ᵥ v = f *ᵥ h + (Q.polarBilin v (N *ᵥ w) • (N *ᵥ z 0) +
        Q.polarBilin v w • (N *ᵥ z 1)) := by
      rw [hfH h hhH, hh, mulVec_sub, mulVec_sub, mulVec_smul, mulVec_smul]
      abel
    rw [Matrix.mulVecLin_apply, hv]
    refine Submodule.add_mem_sup ⟨h, hhH, rfl⟩ (Submodule.add_mem _ ?_ ?_)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  have hR2 : finrank K R ≤ 2 := by
    have h := finrank_range_le_card (R := K) ![N *ᵥ z 0, N *ᵥ z 1]
    rw [Fintype.card_fin] at h
    exact h
  have h1 : N.rank ≤ finrank K (H.map f.mulVecLin) + 2 := by
    have h2 := Submodule.finrank_mono hcov
    have h3 := Submodule.finrank_add_le_finrank_add_finrank (H.map f.mulVecLin) R
    exact h2.trans (h3.trans (by omega))
  have hHN : H.map f.mulVecLin ≤ LinearMap.range N.mulVecLin := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, by rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hfH v hv]⟩
  have hfz : f *ᵥ z 0 ∉ LinearMap.range N.mulVecLin := by
    rintro ⟨y, hy⟩
    rw [Matrix.mulVecLin_apply] at hy
    have e : f *ᵥ z 0 = N *ᵥ z 0 + (w + N *ᵥ w) := by
      rw [hf, add_mulVec, ← mulVec_mulVec, hX, cTwoX_mulVec, hBs (z 0), h00, hBs (z 0), h10,
        one_smul, zero_smul, add_zero, add_mulVec, one_mulVec]
    have hw' : w = N *ᵥ (y - z 0) - N *ᵥ w := by
      rw [mulVec_sub, hy, e]
      abel
    apply hw
    rw [hw', mulVec_sub, hNN, hNN, sub_self]
  have h4 : finrank K (H.map f.mulVecLin) + 1 ≤ f.rank := by
    have hle : H.map f.mulVecLin ⊔ Submodule.span K {f *ᵥ z 0} ≤ LinearMap.range f.mulVecLin :=
      sup_le (by rintro _ ⟨v, -, rfl⟩; exact ⟨v, rfl⟩)
        (Submodule.span_le.mpr (by
          rintro _ rfl
          exact ⟨z 0, rfl⟩))
    have hdisj : H.map f.mulVecLin ⊓ Submodule.span K {f *ᵥ z 0} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv2
      by_contra hc
      have hc0 : c ≠ 0 := fun h0 => hc (by rw [h0, zero_smul])
      apply hfz
      have h5 := hHN hv1
      have h6 := Submodule.smul_mem _ c⁻¹ h5
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h6
    have hfz0 : f *ᵥ z 0 ≠ 0 := fun h0 => hfz (h0 ▸ Submodule.zero_mem _)
    have h5 := Submodule.finrank_sup_add_finrank_inf_eq (H.map f.mulVecLin)
      (Submodule.span K {f *ᵥ z 0})
    rw [hdisj, finrank_bot, add_zero, finrank_span_singleton hfz0] at h5
    have h6 := Submodule.finrank_mono hle
    unfold Matrix.rank
    omega
  omega

omit [CharP K 2] in
theorem rank_cTwoX_le (a b : ι → K) : (cTwoX Q a b).rank ≤ 2 := by
  unfold Matrix.rank
  have h : LinearMap.range (cTwoX Q a b).mulVecLin ≤ Submodule.span K (Set.range ![a, b]) := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, cTwoX_mulVec]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
  have h2 := finrank_range_le_card (R := K) ![a, b]
  rw [Fintype.card_fin] at h2
  exact (Submodule.finrank_mono h).trans h2

end Linear

section Groups

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)}

omit [CharP K 2] in
theorem eq_one_of_units_of_card_eq_two (hK : Nat.card K = 2) (c : Kˣ) : c = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  by_contra hc
  have hc' : (c : K) ≠ 1 := fun h => hc (Units.ext h)
  have h3 : ({(c : K), 0, 1} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [c.ne_zero, hc']), Finset.card_pair zero_ne_one]
  have h4 := Finset.card_le_univ ({(c : K), 0, 1} : Finset K)
  rw [h3, Fintype.card_eq_nat_card, hK] at h4
  omega

theorem noPairOrbit_typeA_orth_two (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K)
    (hq : ⇑Q = q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : Nat.card K = 2) {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)}
    (hZ : Odd (Nat.card (center ↥A))) {p : G} (hp2 : orderOf p = 2) {M : GL ι K}
    (hpM : Represents e p M) (hM2 : orderOf M = 2)
    (hsing : ∀ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0) (hℓ : 4 ≤ commRank M) :
    NoPairOrbit A p := by
  subst hq
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hMQ := statedOmega_isometry hpM.2.1
  have hadj := polarBilin_sub_one_adj (polarBilin_mulVec_of_isometry Q hMQ) hM2
  have hN : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0 := sub_one_mul_self hM2'
  have hN0 : (M : Matrix ι ι K) - 1 ≠ 0 := sub_one_ne_zero fun h => by
    rw [h, orderOf_one] at hM2
    omega
  have hrk : 4 ≤ ((M : Matrix ι ι K) - 1).rank := hℓ
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hadj hsing hN hN0 hrk
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0 := fun v => by
    have h1 := hMQ v
    rw [hMN, add_mulVec, one_mulVec, quad_add, hsing, add_zero] at h1
    exact add_eq_left.mp h1
  have hcomm : ∀ X : GL ι K, X * M = M * X → (X : Matrix ι ι K) * N = N * X := fun X hXM => by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hXM
    simp only [Units.val_mul] at h1
    rw [hNdef, Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]
  intro u hu hu2 horb
  have hu2' : u * u = 1 := by rw [← _root_.sq]; exact hu2
  obtain ⟨U, hU⟩ := exists_represents e (mem_inf.mp hu).1
  have hUM : U * M = M * U := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hU.mul_comm_of_commute hpM hM2' (mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2))
  have hUB := polarBilin_mulVec_of_isometry Q (statedOmega_isometry hU.2.1)
  have key : ∀ w, Q w = 0 → N *ᵥ w ≠ 0 →
      (U : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * U := by
    intro w hw hNw
    have hab : Q.polarBilin (N *ᵥ w) w = 0 := by rw [hBs]; exact halt w
    have hE : cTwoX Q (N *ᵥ w) w * cTwoX Q (N *ᵥ w) w = 0 := cTwoX_mul_self hab
    set S := unipGL (cTwoX Q (N *ᵥ w) w) hE 1 with hS
    have hSv : (S : Matrix ι ι K) = 1 + cTwoX Q (N *ᵥ w) w := by
      rw [hS, coe_unipGL, one_smul]
    have hSH : S ∈ StatedOmega ⇑Q := mem_statedOmega_of Q hQ hT
      (fun v => by rw [hS, coe_unipGL]; exact cTwoX_isometry (hsing w) hw hab 1 v)
      (by rw [hS, commRank_unipGL hE one_ne_zero]; exact even_rank_cTwoX hQ _ _)
    have hSM : S * M = M * S := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hSv, hMN]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        cTwoX_commute_typeA hN hadj w]
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
        have h3 := rank_le_rank_add_mul_cTwoX hQ hN hNw
        have e : ((M * S : GL ι K) : Matrix ι ι K) - 1 =
            N + (1 + N) * cTwoX Q (N *ᵥ w) w := by
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
  obtain ⟨c, hc⟩ := commutant_typeA_of_singular hQ hN hadj halt hsing hN0 hUB (hcomm U hUM) key
  refine central_of_commute_all hZ hpM hM2' hu2 hU fun X _ hXM => Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hcomm X hXM]

end Groups

end CFSG.ComponentClassification.RankTwoClassical
