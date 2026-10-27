module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2LinRes
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodUnitaryDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
open Matrix

section LinAlg

variable {K : Type} [Field K]

theorem eq_one_of_commute_eigenbasis [CharP K 2] {n : ℕ} (b : Module.Basis (Fin n) K (Fin n → K))
    {μ : Fin n → K} (hμ : Function.Injective μ) {T U : Module.End K (Fin n → K)}
    (hT : ∀ i, T (b i) = μ i • b i) (hTU : T * U = U * T) (hU2 : U * U = 1) : U = 1 := by
  classical
  have hdiag : LinearMap.toMatrix b b T = diagonal μ := by
    ext i j
    rw [LinearMap.toMatrix_apply, hT, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg (Ne.symm hij), if_neg hij, smul_zero]
  have hcomm : diagonal μ * LinearMap.toMatrix b b U = LinearMap.toMatrix b b U * diagonal μ := by
    rw [← hdiag, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, hTU]
  have hsq : LinearMap.toMatrix b b U * LinearMap.toMatrix b b U = 1 := by
    rw [← LinearMap.toMatrix_mul, hU2, LinearMap.toMatrix_one]
  have h1 := HDescLinRes.eq_one_of_commute_diagonal_of_mul_self_eq_one hμ hcomm hsq
  apply (LinearMap.toMatrix b b).injective
  rw [h1, LinearMap.toMatrix_one]

theorem mul_comm_of_eq_conj_mul_central {G : Type*} [Group G] {x u s : G} (hu2 : u * u = 1)
    (hs : ∀ g, s * g = g * s) (hs3 : s ^ 3 = 1) (h : u = x * u * x⁻¹ * s) : x * u = u * x := by
  have hs2 : s * s = 1 := by
    have h1 : u * u = (x * u * x⁻¹) * (x * u * x⁻¹) * (s * s) := by
      conv_lhs => rw [h]
      rw [show x * u * x⁻¹ * s * (x * u * x⁻¹ * s) = x * u * x⁻¹ * (s * (x * u * x⁻¹)) * s by
        group]
      rw [hs (x * u * x⁻¹)]
      group
    have h2 : (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := by
      calc (x * u * x⁻¹) * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    rw [h2, one_mul, hu2] at h1
    exact h1.symm
  have hs1 : s = 1 := by
    calc s = s ^ 3 * (s * s)⁻¹ := by group
      _ = 1 := by rw [hs3, hs2]; group
  rw [hs1, mul_one] at h
  calc x * u = x * u * x⁻¹ * x := by group
    _ = u * x := by rw [← h]

end LinAlg

section Model

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem exists_lift_sq_eq_one {t : primeFormP h (idGram K 3)} (ht : t ^ 2 = 1) :
    ∃ U : gramSU h (idGram K 3), (U : primeFormP h (idGram K 3)) = t ∧ U ^ 2 = 1 := by
  obtain ⟨U₀, rfl⟩ := QuotientGroup.mk_surjective t
  have hs : U₀ ^ 2 ∈ normOneScalars h (gramSU h (idGram K 3)) 3 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact ht
  obtain ⟨c, -, hc3, hcU⟩ := hs
  refine ⟨U₀ ^ 3, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, pow_succ, ht, one_mul]
  · apply Subtype.ext
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, Subgroup.coe_pow, hcU, ← map_pow, hc3,
      map_one, Subgroup.coe_one]

theorem mul_comm_of_primeFormConjHom_fix {X : primeFormUnitary h (idGram K 3)}
    {U : gramSU h (idGram K 3)} (hU2 : U ^ 2 = 1)
    (hfix : primeFormConjHom h (idGram K 3) X (U : primeFormP h (idGram K 3)) = U) :
    (X : GL (Fin 3) K) * U = U * X := by
  rw [primeFormConjHom_mk, QuotientGroup.eq] at hfix
  obtain ⟨c, -, hc3, hc⟩ := hfix
  have hW : ((⟨(X : GL (Fin 3) K) * U * (X : GL (Fin 3) K)⁻¹,
      conj_mem_gramSU h (idGram K 3) X.2 U.2⟩ : gramSU h (idGram K 3))⁻¹ * U :
        gramSU h (idGram K 3)) =
      ((X : GL (Fin 3) K) * U * (X : GL (Fin 3) K)⁻¹)⁻¹ * (U : GL (Fin 3) K) := rfl
  rw [hW] at hc
  refine mul_comm_of_eq_conj_mul_central (s := GeneralLinearGroup.scalar (Fin 3) c) ?_
    (fun g => GeneralLinearGroup.scalar_commute c g) (by rw [← map_pow, hc3, map_one]) ?_
  · rw [← Subgroup.coe_mul, ← sq, hU2, Subgroup.coe_one]
  · rw [← hc, mul_inv_cancel_left]

theorem noGoodTwoLocal_primeFormP_three (h : UnitaryFieldData ℓ f K) [CharP K 2]
    (h3 : 3 ∣ ℓ ^ f + 1) (hq3 : 3 < ℓ ^ f) :
    HDescLinRes.NoGoodTwoLocal 3 (primeFormP h (idGram K 3)) := by
  classical
  have := h.finite
  have hne : ¬ (3 = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  intro D hD hD2 hDinn hno T hT2 hT hDT
  obtain ⟨e, heD, he1, t, -, ht2, het⟩ :=
    HDescLinRes.exists_ne_one_fix_involution Nat.prime_three (by norm_num) hD hD2 hT2 hT hDT
  obtain ⟨X, b, hbn, hXb, rfl⟩ := exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived h
    isPrimeFormGram_idGram (le_refl 3) hne (hDinn heD) (hD.2 _ heD)
  have ht2' : t ^ 2 = 1 := by
    rw [← ht2]
    exact pow_orderOf_eq_one t
  obtain ⟨U, rfl, hU2⟩ := exists_lift_sq_eq_one ht2'
  have hU1 : (U : GL (Fin 3) K) ≠ 1 := by
    intro h1
    have hU : U = 1 := Subtype.ext h1
    rw [hU, QuotientGroup.mk_one, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hU2' : (U : GL (Fin 3) K) * U = 1 := by
    rw [← Subgroup.coe_mul, ← sq, hU2, Subgroup.coe_one]
  have hXU := mul_comm_of_primeFormConjHom_fix hU2 het
  obtain ⟨μ, hμ⟩ := HDescLinRes.exists_cube_root_of_commute hXb hU1 hU2' hXU
  have hμn : h.norm (μ : K) = 1 :=
    norm_eq_one_of_pow_norm Nat.prime_three (by norm_num) h3 (by rw [hμ]; exact hbn)
  have hμ'n : h.norm ((μ⁻¹ : Kˣ) : K) = 1 := by
    simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hμn
  set Y := scalarU h 3 μ⁻¹ hμ'n * X with hY
  have hY3 : Y ^ 3 = 1 := rescale_pow_eq_one (le_refl 3) hne hμ'n (by rw [hμ]; exact hXb)
  have hYc : primeFormConjHom h (idGram K 3) Y = primeFormConjHom h (idGram K 3) X := by
    rw [hY, map_mul, conjHom_scalarU (le_refl 3) hne, one_mul]
  have hYU : (Y : GL (Fin 3) K) * U = U * Y := by
    rw [hY, Subgroup.coe_mul, coe_scalarU, mul_assoc, hXU, ← mul_assoc, ← mul_assoc,
      GeneralLinearGroup.scalar_commute]
  obtain ⟨bs, μA, -, hbo, hAe, -⟩ :=
    exists_orthonormal_eigenbasis_pair (h := h) Nat.prime_three h3 (A := Y) (B := Y) rfl hY3 hY3
  by_cases hinj : Function.Injective μA
  · exfalso
    apply hU1
    have hTY : ((toLinU h 3 Y : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) = Matrix.toLin' ((Y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [toLinU_apply, Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply']
    have hTU : ((toLinU h 3 Y : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) * Matrix.toLin' ((U : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.toLin' ((U : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((toLinU h 3 Y : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
            Module.End K (Fin 3 → K)) := by
      rw [hTY, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
        ← Matrix.toLin'_mul, ← Units.val_mul, ← Units.val_mul, hYU]
    have hUU : Matrix.toLin' ((U : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        Matrix.toLin' ((U : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Units.val_mul, hU2', Units.val_one,
        Matrix.toLin'_one]
      rfl
    have h1 := eq_one_of_commute_eigenbasis bs hinj hAe hTU hUU
    apply Units.ext
    rw [Units.val_one]
    apply Matrix.toLin'.injective
    rw [h1, Matrix.toLin'_one]
    rfl
  · rw [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨i, j, hμij, hij⟩ := hinj
    obtain ⟨P, hPle, hPperf, hPdvd⟩ :=
      KD264Lie.exists_perfect_fixSubgroup_of_onPair (le_refl 3) hne hq3 Nat.prime_three
        (by norm_num) h3 hY3 (hbo.pair hij) (hAe i) (by rw [hμij]; exact hAe j)
    rw [hYc] at hPle
    exact hno ⟨_, heD, he1, P, hPle, hPperf, hPdvd⟩

end Model

theorem lpEpsNoGoodTwoLocal_unitary (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.p = 2) :
    HDesc.LpEpsNoGoodTwoLocal 3 ⟨.twistedA 2 q, hv⟩ := by
  intro hlp D hD hD2 hDinn _ hno T hT2 hT hDT
  obtain ⟨r, q', K, _, hU, -, hdA, hne, ⟨eP⟩⟩ :=
    KD264Lie.exists_primeFormP_mulEquiv_of_isUnitaryIdx (d := ⟨.twistedA 2 q, hv⟩) trivial
  injection hdA with hr hqq
  subst hr hqq
  have h3 : 3 ∣ q.card + 1 := by
    obtain ⟨q'', ⟨hq'', -⟩ | ⟨hq'', h⟩⟩ := hlp
    · exact absurd hq'' (by simp)
    · injection hq'' with _ h2
      rw [h2]
      exact h
  haveI := hU.charP
  haveI : CharP K 2 := CharP.congr q.p hq
  have hcard := TauCeti.PrimePower.card_def q
  have h3' : 3 ∣ q.p ^ q.exponent + 1 := by rwa [← hcard]
  have hq3 : 3 < q.p ^ q.exponent := by
    have hne' : q.card ≠ 2 := fun h2 => hne ⟨rfl, h2⟩
    have he := q.exponent_pos
    rw [hcard, hq] at hne'
    rw [hq]
    rcases Nat.lt_or_ge q.exponent 2 with h1 | h1
    · interval_cases q.exponent
      · exact absurd rfl hne'
    · calc 3 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h1
  exact HDescLinRes.NoGoodTwoLocal.of_mulEquiv eP (noGoodTwoLocal_primeFormP_three hU h3' hq3) D
    hD hD2 hDinn hno T hT2 hT hDT

end CFSG.LocalAnalysis.GLTheoremA.HDescUniRes
