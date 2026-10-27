module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalBlock
public import CFSG.RankThree.PartOne.KC.UnitaryHigherInnerPlaneLift

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryNonsplit
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryBlock CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitaryPair CFSG.RankThree.PartOne.KCUnitaryGt
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem exists_orthonormal_eigenbasis_pair (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1)
    {A B : primeFormUnitary h (idGram K n)} (hAB : A * B = B * A) (hA : A ^ p = 1)
    (hB : B ^ p = 1) :
    ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (μA μB : Fin n → K), IsOrthonormalFamily h b ∧
      (∀ i, ((toLinU h n A : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (b i) = μA i • b i) ∧
      (∀ i, ((toLinU h n B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (b i) = μB i • b i) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have := h.finite
  obtain ⟨ζ, hζ⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h hp hpq
  let g : Fin 2 → Module.End K (Fin n → K) := ![((toLinU h n A : LinearMap.GeneralLinearGroup K
    (Fin n → K)) : Module.End K (Fin n → K)), ((toLinU h n B : LinearMap.GeneralLinearGroup K
    (Fin n → K)) : Module.End K (Fin n → K))]
  have hcomm : ∀ i j, Commute (g i) (g j) := by
    have hAB' : Commute ((toLinU h n A : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ((toLinU h n B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) := commute_toLinU hAB |>.map (Units.coeHom _) |> fun x => x
    intro i j
    fin_cases i <;> fin_cases j <;> simp [g, hAB', hAB'.symm, Commute.refl]
  have hpow : ∀ i, g i ^ p = 1 := by
    intro i
    fin_cases i
    · have : (toLinU h n A) ^ p = 1 := by rw [← map_pow, hA, map_one]
      have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
        (g : Module.End K (Fin n → K))) this
      change ((toLinU h n A : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ^ p = 1
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h2
    · have : (toLinU h n B) ^ p = 1 := by rw [← map_pow, hB, map_one]
      have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
        (g : Module.End K (Fin n → K))) this
      change ((toLinU h n B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ^ p = 1
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h2
  have hiso : ∀ i v w, idForm h n (g i v) (g i w) = idForm h n v w := by
    intro i v w
    fin_cases i
    · exact (mem_sesqUnitaryGroup.mp (toLinU_mem A)) v w
    · exact (mem_sesqUnitaryGroup.mp (toLinU_mem B)) v w
  obtain ⟨b, μ, hbμ, hbo⟩ := exists_orthonormal_common_eigenbasis h hζ hpq (idForm_isSymm h n)
    (idForm_separatingLeft h n) g hcomm hpow hiso
  let e : Fin (Module.finrank K (Fin n → K)) ≃ Fin n := finCongr (Module.finrank_fin_fun K)
  refine ⟨b.reindex e, fun i => μ 0 (e.symm i), fun i => μ 1 (e.symm i), fun i j => ?_,
    fun i => ?_, fun i => ?_⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hbo]
    simp
  · rw [Module.Basis.reindex_apply]
    exact hbμ 0 _
  · rw [Module.Basis.reindex_apply]
    exact hbμ 1 _


theorem pow_apply_of_eigen' {V : Type*} [AddCommGroup V] [Module K V] {T : Module.End K V}
    {μ : K} {v : V} (hv : T v = μ • v) (k : ℕ) : (T ^ k) v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ]; ring_nf

theorem eigenvalue_pow_eq_one {x : primeFormUnitary h (idGram K n)} (hx : x ^ p = 1) {μ : K}
    {v : Fin n → K} (hv0 : v ≠ 0)
    (hv : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = μ • v) : μ ^ p = 1 := by
  have h1 : (toLinU h n x) ^ p = 1 := by rw [← map_pow, hx, map_one]
  have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
    (g : Module.End K (Fin n → K))) h1
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
  have h3 := pow_apply_of_eigen' hv p
  rw [h2, Module.End.one_apply] at h3
  have h4 : (μ ^ p - 1) • v = 0 := by rw [sub_smul, one_smul, ← h3, sub_self]
  rcases smul_eq_zero.mp h4 with h5 | h5
  · exact sub_eq_zero.mp h5
  · exact absurd h5 hv0


theorem toLinU_mul_apply_of_eigen {A B : primeFormUnitary h (idGram K n)} {v : Fin n → K}
    {μA μB : K} (hA : ((toLinU h n A : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = μA • v)
    (hB : ((toLinU h n B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = μB • v) (k : ℕ) :
    ((toLinU h n (A ^ k * B) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = (μA ^ k * μB) • v := by
  rw [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, Module.End.mul_apply, hB,
    map_smul, pow_apply_of_eigen' hA, smul_smul, mul_comm]

theorem exists_split_pair_element (hp : p.Prime) {A B : primeFormUnitary h (idGram K n)}
    (hAB : A * B = B * A) (hA : A ^ p = 1) (hB : B ^ p = 1)
    (hA1 : primeFormConjHom h (idGram K n) A ≠ 1)
    (hBA : primeFormConjHom h (idGram K n) B ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K n) A))
    {b : Fin n → Fin n → K} (hb0 : ∀ i, b i ≠ 0) {μA μB : Fin n → K}
    (hAe : ∀ i, ((toLinU h n A : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (b i) = μA i • b i)
    (hBe : ∀ i, ((toLinU h n B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (b i) = μB i • b i) (i j : Fin n) :
    ∃ (M : primeFormUnitary h (idGram K n)) (lam : Fin n → K), M ^ p = 1 ∧
      primeFormConjHom h (idGram K n) M ∈
        Subgroup.closure {primeFormConjHom h (idGram K n) A, primeFormConjHom h (idGram K n) B} ∧
      primeFormConjHom h (idGram K n) M ≠ 1 ∧
      (∀ l, ((toLinU h n M : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (b l) = lam l • b l) ∧ lam i = lam j := by
  have : Fact p.Prime := ⟨hp⟩
  have hpA := fun l => eigenvalue_pow_eq_one hA (hb0 l) (hAe l)
  have hpB := fun l => eigenvalue_pow_eq_one hB (hb0 l) (hBe l)
  have hne0 : ∀ {d : Fin n → K}, (∀ l, d l ^ p = 1) → ∀ l, d l ≠ 0 := by
    intro d hd l h0
    have := hd l
    rw [h0, zero_pow hp.ne_zero] at this
    exact zero_ne_one this
  have hAE : primeFormConjHom h (idGram K n) A ∈
      Subgroup.closure {primeFormConjHom h (idGram K n) A, primeFormConjHom h (idGram K n) B} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  by_cases hAij : μA i = μA j
  · exact ⟨A, μA, hA, hAE, hA1, hAe, hAij⟩
  · set α : K := μA i / μA j with hα
    have hα1 : α ≠ 1 := fun h' => hAij ((div_eq_one_iff_eq (hne0 hpA j)).1 h')
    have hαp : α ^ p = 1 := by rw [hα, div_pow, hpA i, hpA j, div_one]
    have hprim : IsPrimitiveRoot α p := IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hαp hα1)
    have hβp : (μB j / μB i) ^ p = 1 := by rw [div_pow, hpB j, hpB i, div_one]
    obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hβp
    refine ⟨A ^ k * B, fun l => μA l ^ k * μB l, ?_, ?_, ?_,
      fun l => toLinU_mul_apply_of_eigen (hAe l) (hBe l) k, ?_⟩
    · rw [(show Commute (A ^ k) B from (show Commute A B from hAB).pow_left k).mul_pow,
        ← pow_mul, mul_comm, pow_mul, hA, one_pow, hB, one_mul]
    · rw [map_mul, map_pow]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hAE k)
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    · rw [map_mul, map_pow]
      intro h1
      apply hBA
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k)
    · have hAj := hne0 hpA j
      have hBi := hne0 hpB i
      rw [hα, div_pow, div_eq_div_iff (pow_ne_zero k hAj) hBi] at hk
      show μA i ^ k * μB i = μA j ^ k * μB j
      rw [hk, mul_comm]


theorem exists_norm_one_primitiveRoot (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) :
    ∃ ζ : Kˣ, IsPrimitiveRoot ζ p ∧ h.norm (ζ : K) = 1 := by
  obtain ⟨ζ, hζ⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h hp hpq
  have hζu : IsUnit ζ := hζ.isUnit hp.ne_zero
  refine ⟨hζu.unit, ?_, ?_⟩
  · exact IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  · change ζ * h.bar ζ = 1
    rw [mul_comm]
    exact bar_eq_inv_of_pow_eq_one h hpq hζ.pow_eq_one

theorem exists_norm_one_ne_one_sq_ne_one (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) :
    ∃ ζ : Kˣ, h.norm (ζ : K) = 1 ∧ ζ ≠ 1 ∧ ζ ^ 2 ≠ 1 := by
  obtain ⟨ζ, hζ, hζn⟩ := exists_norm_one_primitiveRoot (h := h) hp hpq
  refine ⟨ζ, hζn, hζ.ne_one hp.one_lt, fun h2 => ?_⟩
  have := hζ.dvd_of_pow_eq_one 2 h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)

theorem ne_char_of_dvd_add_one (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1)
    (hf : 1 ≤ f) : p ≠ ℓ := by
  rintro rfl
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have := (Nat.dvd_add_right h1).mp hpq
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)


theorem hmat_refl (g : GL (Fin n) K) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (RingEquiv.refl K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  ext
  rfl

theorem localDeltaIn_eq_bot_of_unitary_split (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq3 : 3 < ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {A B : primeFormUnitary h (idGram K n)} (hAB : A * B = B * A) (hA : A ^ p = 1)
    (hB : B ^ p = 1) (hA1 : primeFormConjHom h (idGram K n) A ≠ 1)
    (hBA : primeFormConjHom h (idGram K n) B ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K n) A))
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    localDeltaIn p H (Subgroup.closure {primeFormConjHom h (idGram K n) A,
      primeFormConjHom h (idGram K n) B}) = ⊥ := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have hpℓ : p ≠ ℓ := ne_char_of_dvd_add_one hp hpq h.one_le
  obtain ⟨b, μA, μB, hbON, hAe, hBe⟩ := exists_orthonormal_eigenbasis_pair hp hpq hAB hA hB
  have hb0 : ∀ i, b i ≠ 0 := fun i => b.ne_zero i
  obtain ⟨ζ, hζ, hζn⟩ := exists_norm_one_primitiveRoot (h := h) hp hpq
  have hζ' := exists_norm_one_ne_one_sq_ne_one (h := h) hp hp2 hpq
  have hpairs := fun i j => exists_split_pair_element hp hAB hA hB hA1 hBA hb0 hAe hBe i j
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨⟨M', τ⟩, rfl⟩ := surjective_primeFormPsi_of_ne (h := h) hn hne g
  have hmat1 := hmat_refl (n := n) (K := K)
  have hcert : ∀ i j : Fin n, i ≠ j → ∃ (M : primeFormUnitary h (idGram K n)) (lam : Fin n → K),
      (∀ l, ((toLinU h n M : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (b l) = lam l • b l) ∧ lam i = lam j ∧
      h.bar (lam i) * lam i = 1 ∧
      ∃ (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n M))
        (hmem : (X - C (lam i) : K[X]) ∈ primaryFactors ((toLinU h n M :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))),
        IsGoodBlock h (toLinU h n M) ⟨X - C (lam i), hmem⟩ ∧
        ∀ Y ∈ gBlock h M (X - C (lam i)),
          primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M', τ⟩ *
            primeFormConjHom h (idGram K n) Y =
          primeFormConjHom h (idGram K n) Y *
            primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M', τ⟩ := by
    intro i j hij
    obtain ⟨M, lam, hMp, hME, hM1, hMe, hlam⟩ := hpairs i j
    have hMs : (M : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
      have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hMp
      simpa using this
    have H0 := primaryData_of_pow_eq_scalar hp hpℓ hMs
    have hlamp : ∀ l, lam l ^ p = 1 := fun l => eigenvalue_pow_eq_one hMp (hb0 l) (hMe l)
    have hμ : h.bar (lam i) * lam i = 1 := bar_eq_inv_of_pow_eq_one h hpq (hlamp i)
    have hx₁ := hMe i
    have hx₂ : ((toLinU h n M : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (b j) = lam i • b j := by rw [hlam]; exact hMe j
    obtain ⟨hmem, hgood⟩ := isGoodBlock_of_eigenpair (h := h) hq3 (hbON.pair hij) hx₁ hx₂
    refine ⟨M, lam, hMe, hlam, hμ, H0, hmem, hgood, ?_⟩
    exact commute_of_mem_localDeltaIn_gBlock hp hn hne hq2 H0 ⟨X - C (lam i), hmem⟩ hgood hH hg
      hME hM1 (dvd_card_map_gBlock_of_torus hp hp2 hn hne H0 hμ hmem (hbON.pair hij) hx₁ hx₂
        hζ hζn)
  have hMunit : IsUnit ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (M' : GL (Fin n) K).isUnit
  have hTC : ∀ i j : Fin n, i ≠ j →
      TorusComm h ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) τ (b i) (b j) := by
    intro i j hij
    obtain ⟨M, lam, hMe, hlam, hμ, H0, hmem, hgood, hβ⟩ := hcert i j hij
    exact torusComm_of_block hn hne hq2 H0 hμ hmem hgood (hbON.pair hij) (hMe i)
      (by rw [hlam]; exact hMe j) M' τ hβ
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := fun h' => by simpa [i0, i1] using congrArg Fin.val h'
  have h02 : i0 ≠ i2 := fun h' => by simpa [i0, i2] using congrArg Fin.val h'
  have h12 : i1 ≠ i2 := fun h' => by simpa [i1, i2] using congrArg Fin.val h'
  have hτ : τ = RingEquiv.refl K :=
    tau_eq_one_of_torus h hMunit (hbON.pair h01) (hbON.pair h02)
      (hbON.linearIndependent_triple h01 h02 h12) (hTC i0 i1 h01) (hTC i0 i2 h02)
  subst hτ
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hdiag : ∀ i, ∃ d : K, ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i =
      d • b i := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    exact (exists_smul_of_torusComm (hbON.pair hj.symm) (hTC i j hj.symm) hζ').1
  have hsame : ∀ i j : Fin n, i ≠ j → ∀ di dj : K,
      ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i = di • b i →
      ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b j = dj • b j → di = dj := by
    intro i j hij di dj hi hj
    obtain ⟨M, lam, hMe, hlam, hμ, H0, hmem, hgood, hβ⟩ := hcert i j hij
    have hMM : M' * M = M * M' := by
      apply toLinU_injective (h := h) (n := n)
      apply Units.ext
      refine b.ext fun l => ?_
      obtain ⟨d, hd⟩ := hdiag l
      have e1 : ((toLinU h n M' : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) (b l) = d • b l := by rw [toLinU_apply_eq]; exact hd
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Module.End.mul_apply,
        Module.End.mul_apply, hMe, e1, map_smul, map_smul, hMe, e1, smul_smul, smul_smul,
        mul_comm]
    have hF : Group.IsPerfect (gBlock h M (X - C (lam i))) :=
      (isQuasisimple_gBlock hq2 H0 ⟨X - C (lam i), hmem⟩ hgood).1
    have hblock' : ∀ g ∈ gBlock h M (X - C (lam i)), M' * g = g * M' := by
      intro g hg
      have := matrix_comm_of_perfect hn hne hF M' (RingEquiv.refl K) hβ g hg
      rw [hmat1] at this
      exact Subtype.ext (Units.ext this)
    obtain ⟨c, hc⟩ := exists_scalar_of_commute_gBlock_X_sub_C hq2 H0 hmem hgood M' hMM hblock'
    have e1 := hc (b i) (by rw [hMe i])
    have e2 := hc (b j) (by rw [hMe j, hlam])
    rw [hi] at e1
    rw [hj] at e2
    exact (smul_left_injective K (hb0 i) e1).trans (smul_left_injective K (hb0 j) e2).symm
  obtain ⟨d0, hd0⟩ := hdiag i0
  have hall : ∀ i, ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i = d0 • b i := by
    intro i
    by_cases hi : i = i0
    · rw [hi]; exact hd0
    · obtain ⟨d, hd⟩ := hdiag i
      rw [hd, hsame i0 i (Ne.symm hi) d0 d hd0 hd]
  have hlin : Matrix.toLin' ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      d0 • LinearMap.id := by
    refine b.ext fun i => ?_
    rw [Matrix.toLin'_apply, hall]
    simp
  exact psi_eq_one_of_scalar hn hne M' d0 fun v => by
    have := LinearMap.congr_fun hlin v
    simpa [Matrix.toLin'_apply] using this

end CFSG.HardMathSupport.Timmesfeld.CrossChar
