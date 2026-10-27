module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieSpin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieComp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieBlock
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieMap
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOProps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOZ
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthFam
public import CFSG.LieType.Steinberg.CentralExt.POmegaOddMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Foundations
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBL2Reduction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bLift
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

namespace P58b.OLie

theorem exists_spin_compat {Y : Type} [Group Y] [Finite Y] {n : ℕ} {K : Type} [Field K]
    [Finite K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) (h5K : 5 ≤ Nat.card K) (hY : IsQuasisimple Y)
    (hZ : Nat.card (center Y) = 2)
    (e : Y ⧸ center Y ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    ∃ α : spinGroup (quadOdd n K) ≃* Y, ∀ s, e (QuotientGroup.mk (α s)) =
      spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn) s := by
  have : Finite (spinGroup (quadOdd n K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have : Group.IsPerfect Y := hY.1
  obtain ⟨hβs, -, -⟩ := spinToStatedProj_quadOdd h2 hn
  set β := spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn) with hβ
  set η : Y →* StatedProj (StatedOmega (StatedQuadOdd n K)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center Y)) with hη
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ2 : IsPGroup 2 (center Y) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect
    (fun E _ _ π hπ hcen _ =>
      LieType.Steinberg.CentralExt.SpinOddClosed.spinOdd_exists_section_of_central h2 hn h5K
        hπ hcen)
    hβs hηs (hηker ▸ le_rfl) (hηker ▸ hZ2)
  have hβcard : Nat.card β.ker = 2 :=
    LieType.Steinberg.CentralExt.SpinOddClosed.card_ker_spinToStatedProj_quadOdd h2 hn
  have hαβ : α.ker ≤ β.ker := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    rw [← hα, hA, map_one]
  have hne : α.ker ≠ β.ker := by
    intro h1
    have hbot : center Y = ⊥ := by
      rw [← hηker, hker, ← h1, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    rw [hbot, Subgroup.card_bot] at hZ
    exact absurd hZ (by norm_num)
  have hdvd : Nat.card α.ker ∣ Nat.card β.ker := Subgroup.card_dvd_of_le hαβ
  have h1 : Nat.card α.ker = 1 := by
    rw [hβcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hαβ (by rw [h, hβcard])) hne
  have hinj : Function.Injective α :=
    (MonoidHom.ker_eq_bot_iff α).1 (Subgroup.eq_bot_of_card_eq _ h1)
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hαs⟩, fun s => hα s⟩

theorem coordinateOdd_proj_spin {n : ℕ} {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    {R : GL (Fin (2 * n + 1)) K}
    (hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadOdd n K v)
    (s : spinGroup (quadOdd n K)) :
    ∃ T : matrixDerived (oQ R),
      oTransport 1 1 hS₁ (statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n K)
        (coe_quadOdd n K) (spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn) s)) =
        projH _ T ∧
      T.val.val = Matrix.reindex (oddIndexEquiv n) (oddIndexEquiv n)
          (spinMatrix (quadOdd n K) s).val := by
  have hA := spinMatrix_mem_of_range_eq (quadOdd n K) (range_spinMatrix_quadOdd h2 hn) s
  refine ⟨derivedTransport 1 1 hS₁ (statedDerivedReindexEquiv (oddIndexEquiv n) (quadOdd n K)
    (coe_quadOdd n K) ⟨spinMatrix (quadOdd n K) s, hA⟩), ?_, ?_⟩
  · rw [spinToStatedProj_apply]
    exact (congrArg (oTransport 1 1 hS₁) (statedProjectiveReindexEquiv_mk _ _ _ _)).trans
      (oTransport_proj 1 1 hS₁ _)
  · have hcoe : ∀ Y : matrixDerived (coordinateQuadOdd n K),
        (derivedTransport 1 1 hS₁ Y).val.val = Y.val.val := fun Y => by
      change (1 * Y.val * 1⁻¹ : GL (Fin (2 * n + 1)) K).val = Y.val.val
      rw [inv_one, mul_one, one_mul]
    refine (hcoe _).trans ?_
    rw [statedDerivedReindexEquiv_val]
    rfl

theorem finrank_ker_add_rank {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
    (Q : QuadraticForm K (σ → K)) (s : spinGroup Q) :
    Module.finrank K (LinearMap.ker ((spinAction Q s : (σ → K) →ₗ[K] σ → K) + LinearMap.id)) +
      ((spinMatrix Q s : Matrix σ σ K) + 1).rank = Fintype.card σ := by
  have hlin : ((spinMatrix Q s : Matrix σ σ K) + 1).mulVecLin =
      (spinAction Q s : (σ → K) →ₗ[K] σ → K) + LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.one_mulVec, spinMatrix_mulVec,
      LinearMap.add_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
  rw [Matrix.rank, hlin, add_comm, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_fintype_fun_eq_card]

theorem typeB_block {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X) {p k : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {c t : X} {Q L : Subgroup X} (hcfg : Lemma58bConfig X p k c t Q)
    (hL : IsTwoComponentIn L (centralizer {t})) (htL : t ∈ L) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) {f : ℕ} (hKc : Nat.card K = p ^ f) {d : ℕ} (hd : Odd d)
    {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (θ : X ⧸ center X ≃* StatedProj (matrixDerived (oQ R))) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = 1)
    (hθT : θ (QuotientGroup.mk t) = projH _ ⟨T, hT⟩) :
    k = f ∧ ((T : Matrix (Fin d) (Fin d) K) + 1).rank = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hz1, R₁, R₂, h₁H, h₁, ⟨e₁⟩, h₂H, h₂, hz₂, -⟩ := comps_of_config hX hp2 hcfg hL htL θ
  rw [hθT] at h₁H h₁ h₂H h₂ hz₂ hz1
  obtain ⟨w, hw, J, I, hJev, hrank, hI, hIc, hNF, hq, h3, ⟨eI⟩, hIcev, -⟩ :=
    two_comps_of_model hK hR hT hT2 hz1 h₁H h₁ e₁ h₂H h₂ hz₂
  have hcomp : Iᶜ.card = d - I.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hIle : I.card ≤ d := by
    have := Finset.card_le_univ I
    rwa [Fintype.card_fin] at this
  have hIodd : ¬ Even I.card := by
    intro hev
    rw [hcomp] at hIcev
    obtain ⟨a, ha⟩ := hev
    obtain ⟨b, hb⟩ := hIcev
    obtain ⟨c, hc⟩ := hd
    omega
  have hIJ : I = Jᶜ := by
    rcases hI with rfl | rfl
    · exact absurd hJev hIodd
    · rfl
  have h5 : 5 ≤ p ^ k := hcfg.2.2.2.2.2.2.1
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk
  have hsimple : IsSimpleGroup PSL(2, GaloisField p k) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 (GaloisField p k) le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  let eQ : ↥(blockP K hw I) ⧸ pPrimeCore 2 ↥(blockP K hw I) ≃* PSL(2, GaloisField p k) :=
    (QuotientGroup.congr _ _ eI.symm (pPrimeCore_map_iso 2 eI.symm)).trans e₁
  have hO := GSThmB.QPUCl.pPrimeCore_blockP_eq_bot hK hw hIc hNF hq eQ.toEquiv.nontrivial
  have hcard : Nat.card (blockP K hw I) * 2 = p ^ k * ((p ^ k) ^ 2 - 1) := by
    have h1 := card_eq_card_pPrimeCore_mul (R := ↥(blockP K hw I))
    rw [Nat.card_congr eQ.toEquiv, hO, Subgroup.card_bot, one_mul] at h1
    have hF2 : ringChar (GaloisField p k) ≠ 2 := ringChar_galoisField_ne_two hp2
    rw [h1, card_PSL_mul_two hF2, GorensteinWalter.sl2_card_formula, hcardF]
  rcases block_psl2_cases hw hK (Fact.out) hKc hIc h3 h5 hcard with ⟨h3', hkf⟩ | ⟨h4, -, -⟩
  · exact ⟨hkf, by rw [hrank, ← hIJ, h3']⟩
  · exact absurd (by rw [h4]; decide) hIodd

end P58b.OLie

open P58b.OLie

theorem harris82Lemma58bRowLie_POmegaOdd (hGA : TBLit.GriessMultipliersAllModels) (n : ℕ) :
    Harris82Lemma58bRowLie .POmegaOdd n := by
  intro X _ _ hX hO p f hp hp2 hm k c t Q L hcfg hL htL _
  have : Fact p.Prime := ⟨hp⟩
  have hZ2 := P58b.card_center_eq_two_of_POmegaOdd hGA hX hO hcfg.1 hcfg.2.1 hm
  have hm₀ := hm
  rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨-, -, hn, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n K)
    (regular_coordinateQuadOdd n K h2 hn).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadOdd n K v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  set θ := (coordinateOddWitnessEquiv K e).trans (oTransport 1 1 hS₁) with hθ
  obtain ⟨hzz, -, -⟩ := comps_of_config hX hp2 hcfg hL htL θ
  obtain ⟨T, hT, hθT, hT2 | hT2⟩ := P51e.Orth.exists_lift_sq h2 (by omega) hR hzz
  rotate_left
  · exfalso
    have hdet := det_eq_one_of_mem_commutator hT
    have h1 := congrArg Matrix.det hT2
    rw [Matrix.det_mul, hdet, Matrix.det_neg, Matrix.det_one, Fintype.card_fin,
      (show Odd (2 * n + 1) from ⟨n, rfl⟩).neg_one_pow, mul_one, mul_one] at h1
    exact h2 (by linear_combination h1)
  have hd : Odd (2 * n + 1) := ⟨n, rfl⟩
  obtain ⟨hkf, -⟩ := typeB_block hX hp2 hcfg hL htL hK hKc hd hR θ hT hT2 hθT
  subst hkf
  have h5K : 5 ≤ Nat.card K := hKc ▸ hcfg.2.2.2.2.2.2.1
  obtain ⟨α, hα⟩ := exists_spin_compat h2 hn h5K hX hZ2 e
  set s := α.symm t with hs
  have hss : s * s = 1 := by
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [hcfg.2.2.1, pow_two] at this
    rw [hs, ← map_mul, htt, map_one]
  obtain ⟨T', hT'p, hT'm⟩ := coordinateOdd_proj_spin h2 hn hS₁ s
  have hθT' : θ (QuotientGroup.mk t) = projH _ T' := by
    have ht : t = α s := by rw [hs, MulEquiv.apply_symm_apply]
    change oTransport 1 1 hS₁ (statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n K)
      (coe_quadOdd n K) (e (QuotientGroup.mk t))) = projH _ T'
    rw [ht, hα s]
    exact hT'p
  have hM2 : (spinMatrix (quadOdd n K) s).val * (spinMatrix (quadOdd n K) s).val = 1 := by
    rw [← Units.val_mul, ← map_mul, hss, map_one, Units.val_one]
  have hT'2 : T'.val.val * T'.val.val = 1 := by
    rw [hT'm, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hM2, Matrix.submatrix_one_equiv]
  obtain ⟨-, hrank'⟩ := typeB_block hX hp2 hcfg hL htL hK hKc hd hR θ T'.2 hT'2 hθT'
  have hrankM : ((spinMatrix (quadOdd n K) s).val + 1).rank = 3 := by
    calc ((spinMatrix (quadOdd n K) s).val + 1).rank =
        (Matrix.reindex (oddIndexEquiv n) (oddIndexEquiv n)
          ((spinMatrix (quadOdd n K) s).val + 1)).rank :=
          (Matrix.rank_reindex _ _ _).symm
      _ = (T'.val.val + 1).rank := by
          rw [hT'm, Matrix.reindex_apply, Matrix.reindex_apply]
          congr 1
          ext i j
          simp [Matrix.one_apply]
      _ = 3 := hrank'
  have hcardσ : Fintype.card (Fin n ⊕ Fin n ⊕ Unit) = 2 * n + 1 := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    ring
  have hker := finrank_ker_add_rank (quadOdd n K) s
  rw [hrankM, hcardσ] at hker
  have hev := even_choose_finrank_ker h2 (nondegenerate_polarBilin_quadOdd n K h2) s hss
  have hmk : Module.finrank K (LinearMap.ker ((spinAction (quadOdd n K) s :
      (Fin n ⊕ Fin n ⊕ Unit → K) →ₗ[K] Fin n ⊕ Fin n ⊕ Unit → K) + LinearMap.id)) =
      2 * (n - 1) := by omega
  rw [hmk, Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ two_pos, Nat.even_mul] at hev
  have hodd : Odd n := by
    rcases hev with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨j, by omega⟩
    · omega
  exact ⟨n, hodd, hn, hX, hZ2, hm₀⟩

end CFSG.ComponentClassification.HarrisLit.T1
