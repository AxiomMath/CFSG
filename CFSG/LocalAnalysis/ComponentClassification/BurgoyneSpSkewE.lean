module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewComp
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Polynomial
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

theorem one_add_smul_pow {ι : Type} [Fintype ι] [DecidableEq ι] {N : Matrix ι ι K}
    (hN : N * N = 0) (c : K) (n : ℕ) : (1 + c • N) ^ n = 1 + ((n : K) * c) • N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hN, smul_zero, add_zero, Nat.cast_succ]
    module

theorem exists_norm_neg_one [Fintype K] (hK : Fintype.card K % 2 = 1) {d : K} (hd0 : d ≠ 0) :
    ∃ a b : K, a ^ 2 - d * b ^ 2 = -1 := by
  obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := C 1 * X ^ 2 + C 0 * X + C 0) (g := C (-d) * X ^ 2 + C 0 * X + C 1)
    (degree_quadratic one_ne_zero) (degree_quadratic (neg_ne_zero.2 hd0)) hK
  refine ⟨a, b, ?_⟩
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at h
  linear_combination h

theorem skewNs_apply_inr_inl (d : K) (i : Fin r) : skewNs r K d (Sum.inr i) (Sum.inl i) = 1 := by
  simp [skewNs]

theorem skewNsGsp_ne_scalar (hr : 1 ≤ r) {d : K} (hd0 : d ≠ 0) (c : Kˣ) :
    (skewNsGsp r K hd0 : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  intro h
  have e := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
    (Fin r ⊕ Fin r) K) (Sum.inr ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) h
  simp only [coe_skewNsGsp, skewNs_apply_inr_inl, GeneralLinearGroup.coe_scalar,
    scalar_apply, diagonal_apply_ne _ Sum.inr_ne_inl] at e
  exact one_ne_zero e

theorem blockDiag_add_smul_skewNs (i₀ : Fin r) (d p s : K) :
    BlockDiag (lrPair i₀) (p • 1 + s • skewNs r K d) := by
  rw [blockDiag_iff]
  rintro (k | k) (l | l) h <;>
  · have hkl : k ≠ l := by
      rintro rfl
      simp [lrPair] at h
    simp [skewNs, one_apply, hkl]

theorem add_smul_mul_self {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι K} {d : K}
    (hM : M * M = d • 1) (p s : K) :
    (p • (1 : Matrix ι ι K) + s • M) * (p • 1 + s • M) =
      (p ^ 2 + d * s ^ 2) • 1 + (2 * p * s) • M := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hM, smul_smul]
  module

theorem orderOf_conjAut_skewNs [Finite K] (hr : 1 ≤ r) {d : K} (hd0 : d ≠ 0) :
    orderOf (conjAut r K (skewNsGsp r K hd0)) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two, ← map_mul, conjAut_eq_one_iff hr]
    refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_skewNsGsp,
      skewNs_mul_self, Matrix.smul_one_eq_diagonal]
    rfl
  · intro h1
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hr _).1 h1
    exact skewNsGsp_ne_scalar hr hd0 c hc

theorem skewNs_oddCore [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hrq : 3 ≤ r ∨ 5 ≤ ℓ ^ f)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d) (hd0 : d ≠ 0) {y : MulAut (StatedProj (StatedSp r K))}
    (hy : y ∈ oddCoreIn B (conjAut r K (skewNsGsp r K hd0))) :
    ∃ (D : gsp r K) (p s : K), y = conjAut r K D ∧
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        p • 1 + s • skewNs r K d := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hcard : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, hKc]
    exact Nat.odd_iff.1 (hℓ.odd_of_ne_two hℓ2).pow
  have hAA : ((skewNsGsp r K hd0 : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * ((skewNsGsp r K hd0 : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1 := skewNs_mul_self d
  obtain ⟨L, hLF, hLn, hLq, hLp⟩ := exists_unitary_component hℓ hℓ2 hf hKc hr hrq
    (skewNsGsp_ne_scalar (by omega) hd0) hd hAA (skewNs_similitude d)
  have hoddy := odd_orderOf_of_mem_oddCoreIn hy
  have hyt := commute_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  have hfix : ∀ g ∈ L, (conjAut r K D * fieldAut r K τ) (proj r K g) = proj r K g :=
    fun g hg => commute_oddCoreIn_of_normal hinj hB (conjSp r K (skewNsGsp r K hd0)).toMonoidHom
      (conjAut_proj _) hLF hLn (isQuasisimple_map_conjProjH hinj hLq) hy hg
  have hperf := commutator_eq_self_of_isQuasisimple hLq
  obtain ⟨a, b, hab⟩ := exists_norm_neg_one hcard hd0
  have hab' : (-a) ^ 2 - d * (-b) ^ 2 = -1 := by linear_combination hab
  set Dm := ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hDm
  have key : ∀ i j : Fin r, i ≠ j → ∀ a' b' : K, a' ^ 2 - d * b' ^ 2 = -1 → τ = 1 ∧
      Dm * skN d i j a' (b' * d) = skN d i j a' (b' * d) * Dm := by
    intro i j hij a' b' hab''
    obtain ⟨c1, c2, c3⟩ := skN_conds (r := r) hij hab''
    have hmem : ∀ c : K, unipSp c1 c2 c3 c ∈ L := by
      intro c
      have hc : unipSp c1 c2 c3 c ∈ spCent r K (skewNsGsp r K hd0) := by
        rw [mem_spCent, coe_unipSp, coe_skewNsGsp, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul,
          (skN_commute d i j a' (b' * d)).symm]
      refine hLp _ hc (statedSp_ext ?_)
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, coe_unipSp, one_add_smul_pow c3,
        CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
      rfl
    refine fix_unipotent_family_matrix (skN_apply_ne_zero hij d a' (b' * d)) fun c => ?_
    have h := semilinear_eq_of_fix hperf hfix (hmem c)
    rwa [coe_unipSp, map_one_add_smul] at h
  have h01 : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hτ := (key _ _ h01 a b hab).1
  rw [hτ, map_one, mul_one] at hoddy hyt ⊢
  obtain ⟨D', ⟨m, hm⟩, hD'D, hD'A⟩ := exists_commute_of_odd (by omega) hd0 hAA hyt hoddy
  set M' := ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM'
  have hM'pow : M' = Dm ^ m := by rw [hM', hm, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  obtain ⟨p, s, hps⟩ := eq_add_smul_of_commute_skN (by omega) h2 hd0 hab (M := M') hD'A
    fun i j hij => ⟨by rw [hM'pow]; exact (Commute.pow_left (key i j hij a b hab).2 m).eq,
      by rw [hM'pow]; exact (Commute.pow_left (key i j hij (-a) (-b) hab').2 m).eq⟩
  exact ⟨D', p, s, hD'D.symm, hps⟩

theorem conjAut_eq_one_of_eq_smul (hr : 1 ≤ r) [Finite K] {D : gsp r K} {p : K}
    (hD : ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      p • 1) : conjAut r K D = 1 := by
  have hp0 : p ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun (Units.mul_inv (D : GL (Fin r ⊕ Fin r) K))
      (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
    rw [hD, h0, zero_smul, Matrix.zero_mul, one_apply_eq] at h1
    exact zero_ne_one h1
  rw [conjAut_eq_one_iff hr]
  refine ⟨Units.mk0 p hp0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, hD, Matrix.smul_one_eq_diagonal]
  rfl

theorem skewNs_propAConclusionIn [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (h5 : 5 ≤ ℓ ^ f)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d) (hd0 : d ≠ 0)
    {Y : Subgroup (MulAut (StatedProj (StatedSp r K)))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (conjAut r K (skewNsGsp r K hd0))) :
    PropAConclusionIn B (conjAut r K (skewNsGsp r K hd0)) Y := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set i₀ : Fin r := ⟨0, by omega⟩ with hi₀
  have hcore := fun {y} (hy : y ∈ oddCoreIn B (conjAut r K (skewNsGsp r K hd0))) =>
    skewNs_oddCore hℓ hℓ2 hf hKc hr (Or.inr h5) hinj hB hd hd0 hy
  have hA₁ : ((skewNsGsp r K hd0 : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (0 : K) • 1 + (1 : K) • skewNs r K d := by
    rw [coe_skewNsGsp, zero_smul, one_smul, zero_add]
  refine slice_propAConclusionIn hinj hB (longRoot_inf hr i₀) hK (by rw [hKc]; omega)
    (lrInv_mem i₀) (longRootEquiv K i₀) (longRootEquiv_lrInv i₀) (longRoot_commute i₀)
    (longRoot_normalized h2 i₀) (orderOf_conjAut_skewNs (by omega) hd0) hY hYO
    (conjAut_mem_normalizer_slice (by rw [hA₁]; exact blockDiag_add_smul_skewNs _ _ _ _)) ?_ ?_
    ?_
  · by_contra h
    push Not at h
    obtain ⟨-, h10, -⟩ := pairBlock_scalar_of_commute_slice (p := ℓ) hinj
      (by rw [hA₁]; exact blockDiag_add_smul_skewNs _ _ _ _) h
    rw [coe_skewNsGsp, skewNs_apply_inr_inl] at h10
    exact one_ne_zero h10
  · intro y hy
    obtain ⟨D, p, s, rfl, hD⟩ := hcore hy
    exact conjAut_mem_normalizer_slice (by rw [hD]; exact blockDiag_add_smul_skewNs _ _ _ _)
  · intro y hy hc
    obtain ⟨D, p, s, rfl, hD⟩ := hcore hy
    obtain ⟨-, h10, -⟩ := pairBlock_scalar_of_commute_slice (p := ℓ) hinj
      (by rw [hD]; exact blockDiag_add_smul_skewNs _ _ _ _) hc
    have hs : s = 0 := by
      rw [hD] at h10
      simpa [skewNs, one_apply] using h10
    refine conjAut_eq_one_of_eq_smul (by omega) (p := p) ?_
    rw [hD, hs, zero_smul, add_zero]

theorem pow_eight_add_smul_three [Finite K] (h3 : Nat.card K = 3) {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι K} (hM : M * M = (-1 : K) • 1) {p s : K}
    (hps : p ≠ 0 ∨ s ≠ 0) : (p • (1 : Matrix ι ι K) + s • M) ^ 8 = 1 := by
  have h2 := two_eq_neg_one_of_three h3
  have e : (p • (1 : Matrix ι ι K) + s • M) ^ 8 =
      ((p • 1 + s • M) * (p • 1 + s • M) * ((p • 1 + s • M) * (p • 1 + s • M))) *
        ((p • 1 + s • M) * (p • 1 + s • M) * ((p • 1 + s • M) * (p • 1 + s • M))) := by
    rw [show (8 : ℕ) = 2 * 2 * 2 from rfl, pow_mul, pow_mul, pow_two, pow_two, pow_two]
  rw [e, add_smul_mul_self hM, add_smul_mul_self hM, add_smul_mul_self hM]
  rcases three_elements h3 p with rfl | rfl | rfl <;>
    rcases three_elements h3 s with rfl | rfl | rfl
  · simp at hps
  all_goals simp only [h2]; norm_num

theorem skewNs_oddCoreIn_eq_bot_three [Finite K] (h3 : Nat.card K = 3) (hr : 3 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d) (hd0 : d ≠ 0) :
    oddCoreIn B (conjAut r K (skewNsGsp r K hd0)) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hoddy := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨D, p, s, rfl, hD⟩ := skewNs_oddCore (ℓ := 3) (f := 1) Nat.prime_three (by norm_num)
    le_rfl (by rw [h3]; norm_num) (by omega) (Or.inl hr) hinj hB hd hd0 hy
  have hdm : d = -1 := by
    rcases three_elements h3 d with h | h | h
    · exact absurd h hd0
    · exact absurd (by rw [h, one_pow]) (hd 1)
    · exact h
  have hps : p ≠ 0 ∨ s ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    have h1 := congrFun (congrFun (Units.mul_inv (D : GL (Fin r ⊕ Fin r) K))
      (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
    rw [hD, zero_smul, zero_smul, add_zero, Matrix.zero_mul, one_apply_eq] at h1
    exact zero_ne_one h1
  have hM : skewNs r K d * skewNs r K d = (-1 : K) • 1 := by rw [skewNs_mul_self, hdm]
  have h8 : conjAut r K (D ^ 2 ^ 3) = 1 := by
    rw [conjAut_eq_one_iff (by omega)]
    refine ⟨1, Units.ext ?_⟩
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hD, show 2 ^ 3 = 8 by norm_num,
      pow_eight_add_smul_three h3 hM hps, map_one, Units.val_one]
  rw [map_pow] at h8
  exact UnbalancedCatalog.SpChain.eq_one_of_odd_orderOf hoddy h8

end CFSG.ComponentClassification.Burgoyne.Sp
