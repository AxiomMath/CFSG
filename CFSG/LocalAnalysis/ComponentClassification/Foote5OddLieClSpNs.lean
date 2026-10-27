module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpSplit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewE

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.ClSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Polynomial
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K] [Finite K]
  {R : Subgroup (MulAut (StatedProj (StatedSp r K)))}

omit [Finite K] in
theorem commute_add_smul {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι K)
    (a b a' b' : K) :
    (a • 1 + b • X) * (a' • 1 + b' • X) = (a' • 1 + b' • X) * (a • 1 + b • X) := by
  have h : Commute (a • (1 : Matrix ι ι K) + b • X) (a' • 1 + b' • X) := by
    refine Commute.add_left ((Commute.one_left _).smul_left a) (Commute.add_right ?_ ?_)
    · exact ((Commute.one_right _).smul_right a').smul_left b
    · exact ((Commute.refl X).smul_right b').smul_left b
  exact h.eq

theorem nonsplitSelf_core {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {A : gsp r K}
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • formJ r K)
    (hRodd : Odd (Nat.card R)) (hRi : ∀ y ∈ R, y * conjAut r K A = conjAut r K A * y)
    (hRc : ∀ s, conjAut r K A s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) {y} (hy : y ∈ R) :
    ∃ (D' : gsp r K) (α β : K), y = conjAut r K D' ∧
      ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        α • 1 + β • ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have : NeZero r := ⟨by omega⟩
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd0 : d ≠ 0 := fun h => hd 0 (by rw [h]; ring)
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hJA : Mᵀ * formJ r K = formJ r K * M := transpose_mul_formJ hd0 hJ hAA
  have hq := isQuasisimple_spCent_nonsplit hℓ hℓ2 hf hKc hr hAns hd hAA hJ
  have hmem : ∀ v c, symSp (bJ_mulVec_self h2 hJA v) c ∈ spCent r K A := by
    intro v c
    rw [mem_spCent, coe_symSp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, symN_commute hJA hAA v]
  have hoddy := odd_orderOf_of_mem hRodd hy
  have hyt := hRi y hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  have hfix : ∀ g ∈ spCent r K A, (conjAut r K D * fieldAut r K τ) (proj r K g) = proj r K g :=
    fun g hg => fix_of_spCent hinj hRodd hRi hRc rfl le_rfl
      (fun f hf q hq' => mul_mem (mul_mem hf hq') (inv_mem hf)) hq hy hg
  have hperf := commutator_eq_self_of_isQuasisimple hq
  set Dm := ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hDm
  have key : ∀ v : Fin r ⊕ Fin r → K, v ≠ 0 → τ = 1 ∧
      Dm * symN (M *ᵥ v) v = symN (M *ᵥ v) v * Dm := by
    intro v hv
    obtain ⟨x, hx1, hx2⟩ := exists_dual_pair hd hJA hAA hv
    have hNx : symN (M *ᵥ v) v *ᵥ x = v := by
      rw [symN_mulVec, hx1, hx2, zero_smul, one_smul, zero_add]
    have hN0 : symN (M *ᵥ v) v ≠ 0 := by
      intro h0
      rw [h0, zero_mulVec] at hNx
      exact hv hNx.symm
    obtain ⟨a, b, hab⟩ := exists_ne_zero_entry hN0
    refine fix_unipotent_family_matrix hab fun c => ?_
    have h := semilinear_eq_of_fix hperf hfix (hmem v c)
    rwa [coe_symSp, map_one_add_smul] at h
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : Fin r ⊕ Fin r → K, v₁ ≠ 0 :=
    ⟨Pi.single (Sum.inl ⟨0, by omega⟩) 1, fun h => by
      have := congrFun h (Sum.inl ⟨0, by omega⟩)
      simp at this⟩
  have hτ := (key v₁ hv₁).1
  rw [hτ, map_one, mul_one] at hoddy hyt ⊢
  obtain ⟨D', ⟨m, hm⟩, hD'D, hD'A⟩ := exists_commute_of_odd (by omega) hd0 hAA hyt hoddy
  set Dm' := ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    with hDm'
  have hDm'pow : Dm' = Dm ^ m := by
    rw [hDm', hm, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have key' : ∀ v : Fin r ⊕ Fin r → K, v ≠ 0 →
      Dm' * symN (M *ᵥ v) v = symN (M *ᵥ v) v * Dm' := by
    intro v hv
    rw [hDm'pow]
    exact (Commute.pow_left (key v hv).2 m).eq
  have hspan : ∀ v, ∃ p q : K, Dm' *ᵥ v = p • v + q • (M *ᵥ v) := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, 0, by simp [hv]⟩
    obtain ⟨x, hx1, hx2⟩ := exists_dual_pair hd hJA hAA hv
    have hNx : symN (M *ᵥ v) v *ᵥ x = v := by
      rw [symN_mulVec, hx1, hx2, zero_smul, one_smul, zero_add]
    refine ⟨bJ (M *ᵥ v) (Dm' *ᵥ x), bJ v (Dm' *ᵥ x), ?_⟩
    have := congrArg (· *ᵥ x) (key' v hv)
    simp only [← mulVec_mulVec, hNx, symN_mulVec] at this
    rw [this, add_comm]
  obtain ⟨α, β, hαβ⟩ := exists_eq_add_smul hd hAA hD'A hspan
  exact ⟨D', α, β, hD'D.symm, hαβ⟩

theorem commute_nonsplitSelf {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {A : gsp r K}
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • formJ r K)
    (hRodd : Odd (Nat.card R)) (hRi : ∀ y ∈ R, y * conjAut r K A = conjAut r K A * y)
    (hRc : ∀ s, conjAut r K A s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  intro r₁ h₁ r₂ h₂
  obtain ⟨D, a, b, rfl, hD⟩ :=
    nonsplitSelf_core hℓ hℓ2 hf hKc hr hinj hAns hd hAA hJ hRodd hRi hRc h₁
  obtain ⟨D', a', b', rfl, hD'⟩ :=
    nonsplitSelf_core hℓ hℓ2 hf hKc hr hinj hAns hd hAA hJ hRodd hRi hRc h₂
  refine conjAut_commute ?_
  rw [hD, hD']
  exact commute_add_smul _ a b a' b'

theorem skewNs_core {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hrq : 3 ≤ r ∨ 5 ≤ ℓ ^ f)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d) (hd0 : d ≠ 0) (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * conjAut r K (skewNsGsp r K hd0) = conjAut r K (skewNsGsp r K hd0) * y)
    (hRc : ∀ s, conjAut r K (skewNsGsp r K hd0) s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) {y} (hy : y ∈ R) :
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
  have hoddy := odd_orderOf_of_mem hRodd hy
  have hyt := hRi y hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  have hfix : ∀ g ∈ L, (conjAut r K D * fieldAut r K τ) (proj r K g) = proj r K g :=
    fun g hg => fix_of_spCent hinj hRodd hRi hRc rfl hLF hLn hLq hy hg
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

theorem commute_skewNs {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hrq : 3 ≤ r ∨ 5 ≤ ℓ ^ f)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d) (hd0 : d ≠ 0) (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * conjAut r K (skewNsGsp r K hd0) = conjAut r K (skewNsGsp r K hd0) * y)
    (hRc : ∀ s, conjAut r K (skewNsGsp r K hd0) s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  intro r₁ h₁ r₂ h₂
  obtain ⟨D, a, b, rfl, hD⟩ := skewNs_core hℓ hℓ2 hf hKc hr hrq hinj hd hd0 hRodd hRi hRc h₁
  obtain ⟨D', a', b', rfl, hD'⟩ := skewNs_core hℓ hℓ2 hf hKc hr hrq hinj hd hd0 hRodd hRi hRc h₂
  refine conjAut_commute ?_
  rw [hD, hD']
  exact commute_add_smul _ a b a' b'

end CFSG.ComponentClassification.Foote5.OddLieCore.ClSp
