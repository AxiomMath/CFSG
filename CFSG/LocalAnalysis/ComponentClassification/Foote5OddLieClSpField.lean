module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSp
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLRed
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.ClSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam coe_lam pairMat statedSp_ext
  mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom
  subfieldSpHom_injective exists_subfieldSpHom_eq)
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K] [Finite K]
  {R : Subgroup (MulAut (StatedProj (StatedSp r K)))}

theorem odd_orderOf_of_mem {G : Type*} [Group G] {H : Subgroup G} (hH : Odd (Nat.card H))
    {y : G} (hy : y ∈ H) : Odd (orderOf y) :=
  hH.of_dvd_nat (Subgroup.orderOf_dvd_natCard H hy)

theorem eq_one_field (hK : ringChar K ≠ 2) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) (hσ : σ ≠ 1) (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * fieldAut r K σ = fieldAut r K σ * y)
    (hRc : ∀ s, fieldAut r K σ s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) {y} (hy : y ∈ R) : y = 1 := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have i₀ : Fin r := ⟨0, by omega⟩
  have hodd := odd_orderOf_of_mem hRodd hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  have hq := isQuasisimple_spFixed hK hr σ (r := r)
  have hfix : ∀ g ∈ spFixed r σ,
      (conjAut r K D * fieldAut r K τ) (proj r K g) = proj r K g :=
    fun g hg => fix_of_normal hinj hRodd hRi hRc (fieldSp r K σ) (fieldAut_proj σ)
      (Q := spFixed r σ) (fun _ h => h)
      (fun f hf q hq => mul_mem (mul_mem (show f ∈ spFixed r σ from hf) hq)
        (inv_mem (show f ∈ spFixed r σ from hf))) hq hy hg
  have hperf := commutator_eq_self_of_isQuasisimple hq
  have hex := fun {g : StatedSp r K} (hg : g ∈ spFixed r σ) => semilinear_eq_of_fix hperf hfix hg
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set Mi : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
  have hMMi : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set S₀ : Set K := {c | σ c = c} with hS₀
  have h1S : (1 : K) ∈ S₀ := map_one σ
  have hup : ∀ i : Fin r, (∀ c ∈ S₀, τ c = c) ∧
      M * single (Sum.inl i) (Sum.inr i) 1 = single (Sum.inl i) (Sum.inr i) 1 * M := by
    intro i
    refine fix_unipotent_on (x := Sum.inl i) (y := Sum.inr i) (by simp) hMMi hMiM h1S
      fun c hc => ?_
    obtain ⟨X, hX⟩ : ∃ X : SL(2, K), (X : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] :=
      ⟨⟨_, by simp [det_fin_two_of]⟩, rfl⟩
    have h := hex (lam_upper_mem_spFixed i hc hX)
    rw [coe_lam, hX] at h
    change M * (pairMat _ _ _).map τ.toRingHom * Mi = _ at h
    rw [pairMat_map, pairMat_upper Sum.inl_ne_inr] at h
    have e : (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K).map τ.toRingHom = !![1, τ c; 0, 1] := by
      ext s t
      fin_cases s <;> fin_cases t <;> simp
    rwa [e, pairMat_upper Sum.inl_ne_inr] at h
  have hlo : ∀ i : Fin r,
      M * single (Sum.inr i) (Sum.inl i) 1 = single (Sum.inr i) (Sum.inl i) 1 * M := by
    intro i
    refine (fix_unipotent_on (τ := τ) (x := Sum.inr i) (y := Sum.inl i) (by simp) hMMi hMiM h1S
      fun c hc => ?_).2
    obtain ⟨X, hX⟩ : ∃ X : SL(2, K), (X : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] :=
      ⟨⟨_, by simp [det_fin_two_of]⟩, rfl⟩
    have h := hex (lam_lower_mem_spFixed i hc hX)
    rw [coe_lam, hX] at h
    change M * (pairMat _ _ _).map τ.toRingHom * Mi = _ at h
    rw [pairMat_map, pairMat_lower Sum.inl_ne_inr] at h
    have e : (!![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) K).map τ.toRingHom = !![1, 0; τ c, 1] := by
      ext s t
      fin_cases s <;> fin_cases t <;> simp
    rwa [e, pairMat_lower Sum.inl_ne_inr] at h
  have hmid : ∀ i j : Fin r, M * fromBlocks 0 (single i j 1 + single j i 1) 0 0 =
      fromBlocks 0 (single i j 1 + single j i 1) 0 0 * M := by
    intro i j
    have hN : (fromBlocks 0 (single i j 1 + single j i 1) 0 0 :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl i) (Sum.inr j) ≠ 0 := by
      by_cases hij : i = j
      · subst hij
        simpa [one_add_one_eq_two] using h2
      · simp [hij]
    refine (fix_unipotent_on (τ := τ) hN hMMi hMiM h1S fun c hc => ?_).2
    have h := hex (upper_mem_spFixed i j hc)
    rw [coe_upperUnipotentSp] at h
    have e1 : (fromBlocks 1 (symSingle i j c) 0 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        1 + c • fromBlocks 0 (single i j 1 + single j i 1) 0 0 := by
      rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
      simp [symSingle]
    have e2 : (fromBlocks 1 (symSingle i j c) 0 1 :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map τ =
        1 + τ c • fromBlocks 0 (single i j 1 + single j i 1) 0 0 := by
      rw [fromBlocks_map, Matrix.map_one _ (map_zero τ) (map_one τ),
        Matrix.map_zero _ (map_zero τ), ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
      congr 1
      · simp
      · ext x y
        simp [symSingle, single_apply]
        split_ifs <;> simp
      · simp
      · simp
    rwa [e2, e1] at h
  have hτS : ∀ c, σ c = c → τ c = c := (hup i₀).1
  have hDs := eq_scalar_of_commute_roots i₀ (fun i => (hup i).2) hlo hmid
  have hD : conjAut r K D = 1 := by
    rw [conjAut_eq_one_iff (by omega)]
    have hu : IsUnit (M (Sum.inl i₀) (Sum.inl i₀)) := by
      rw [isUnit_iff_ne_zero]
      intro h0
      have : M = 0 := by rw [hDs, h0, map_zero]
      have h1 := hMMi
      rw [this, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 (Sum.inl i₀)) (Sum.inl i₀)
      simp at this
    refine ⟨hu.unit, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar]
    exact hDs
  rw [hD, one_mul] at hodd ⊢
  have hτk : τ ^ orderOf (fieldAut r K τ) = 1 := by
    have h1 : conjAut r K 1 * fieldAut r K (τ ^ orderOf (fieldAut r K τ)) = 1 := by
      rw [map_one, one_mul, map_pow, pow_orderOf_eq_one]
    exact ((CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff (by omega) 1
      _).1 h1).1
  rw [eq_one_of_fix_fixField h2 hσσ hσ hτS hodd hτk, map_one]

theorem commute_field {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = p ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {A : gsp r K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hi : orderOf (conjAut r K A * fieldAut r K σ) = 2) (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * (conjAut r K A * fieldAut r K σ) = (conjAut r K A * fieldAut r K σ) * y)
    (hRc : ∀ s, (conjAut r K A * fieldAut r K σ) s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨-, -, -, -, -, -, -, -, -, hdesc⟩ :=
    RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hp hf hr hKc
  have hmem : conjAut r K A * fieldAut r K σ ∈ spSemilinearAutGroup r K :=
    mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)
  have hnot : conjAut r K A * fieldAut r K σ ∉ spLinearAutGroup r K :=
    conjAut_mul_fieldAut_not_mem (by omega) hσ
  obtain ⟨-, σ', hσ', -, h, hh, hht⟩ := hdesc 2 Nat.prime_two _ hmem hnot hi
  have hrange : spLinearAutGroup r K = (conjAut r K).range := by
    rw [spLinearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [hrange] at hh
  obtain ⟨H, rfl⟩ := hh
  have hσσ : ∀ x, σ' (σ' x) = x := by
    intro x
    have h2 : σ' ^ 2 = 1 := by rw [← hσ', pow_orderOf_eq_one]
    have := congrArg (fun τ : K ≃+* K => τ x) h2
    simpa [pow_two] using this
  have hσ'1 : σ' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ'
    exact absurd hσ' (by decide)
  refine commute_of_congr (conjAut r K H)⁻¹ (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
  have hcg : MulAut.congr (conjAut r K H)⁻¹ (conjAut r K A * fieldAut r K σ) =
      fieldAut r K σ' := by
    rw [congr_eq_conj, hht]
    group
  rw [hcg] at hR'i hR'c
  intro r₁ h₁ r₂ h₂
  rw [eq_one_field hK hr hinj hσσ hσ'1 hR'odd hR'i hR'c h₁,
    eq_one_field hK hr hinj hσσ hσ'1 hR'odd hR'i hR'c h₂]

end CFSG.ComponentClassification.Foote5.OddLieCore.ClSp
