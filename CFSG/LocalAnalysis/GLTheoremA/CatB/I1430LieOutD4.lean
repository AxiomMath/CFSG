module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutTriD4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4Aux.Normal
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutEnt

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.RankThree.PartOne.Sec66T
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux
  CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open CFSG.HardMathSupport.Lang.E6Descent (twistedEntrywiseAut)
open CFSG.HardMathSupport.Dickson.Sec6 (FamD4 blueprintLieModel_D)
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (not_mem_range_conj_of_not_mem_innAutDerived)
open scoped commutatorElement

variable {T Pc : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}


section D4

theorem typeLayer_entrywiseAdjointAut_D4W (hD : LieSOutTypeW T tm tf tN)
    {d : ℕ} (hd : 1 ≤ d) {K : Type}
    [Field K] [Finite K] (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 2 ^ d) :
    TypeLayer T (entrywiseAdjointAut Tag.D4 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  obtain ⟨hs, hnab⟩ := isSimple_adjointD4 (fixSubfield σ)
  exact typeLayer_entrywise σ hs hnab fun h =>
    absurd (hD.det h (lieModel_adjointD4 Nat.prime_two hd (fixSubfield σ) hk)).1 (by decide)

theorem typeLayer_twistedEntrywiseAut_D4_oneW (hD : LieSOutTypeW T tm tf tN)
    {d : ℕ} (hd : 1 ≤ d) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ d) ^ 3) (r : ℕ) (hr : r = 1 ∨ r = 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ ((2 ^ d) ^ r)) :
    TypeLayer T (twistedEntrywiseAut TwistTag.D4 1 σ) False := by
  classical
  haveI := finite_adjointD4 K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := d * 3) (by omega) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨-, -, htw, hs, hnab⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group
    2 d Nat.prime_two hd K hK (AlgebraicClosure K) r hr σ.toRingHom hσ
    (iterateFrobenius (AlgebraicClosure K) 2 d) (fun c => iterateFrobenius_def _ _ _)
  have hcard := (triality_both_orientations_exact_finite_order 2 d Nat.prime_two hd K hK r hr
    σ.toRingHom hσ).1
  haveI := hs
  let e : ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroupTwistedEntrywiseAutOneEquiv
      TwistTag.D4 σ).trans (MulEquiv.subgroupCongr htw)
  refine typeLayer_of_fixed_equiv _ e hs hnab fun hT => ?_
  have h1 := hD.card_eq hT
  rw [hcard] at h1
  have h2 : 2 ≤ 2 ^ d :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  exact hD.ord.ne_triD4 _ h2 h1.symm

theorem typeLayer_twistedEntrywiseAut_D4W (hD : LieSOutTypeW T tm tf tN)
    {d : ℕ} (hd : 1 ≤ d) {K : Type}
    [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ d) ^ 3) (Tf : K ≃+* K) (hT : ∀ c, Tf c = c ^ (2 ^ d)) (j : ℤ)
    (hj : j = 1 ∨ j = 2) : TypeLayer T (twistedEntrywiseAut TwistTag.D4 j Tf) False := by
  rcases hj with rfl | rfl
  · exact typeLayer_twistedEntrywiseAut_D4_oneW hD hd hK 1 (Or.inl rfl) Tf (by simpa using hT)
  · have hT3 := ringEquiv_cube_apply_eq hK hT
    have hTinv : ∀ c, Tf⁻¹ c = c ^ ((2 ^ d) ^ 2) := by
      intro c
      have h1 : Tf⁻¹ (Tf (Tf (Tf c))) = Tf (Tf c) := RingEquiv.symm_apply_apply Tf _
      rw [hT3] at h1
      rw [h1, hT, hT, ← pow_mul, sq]
    exact typeLayer_of_fix_eq
      (CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroup_twistedEntrywiseAut_D4_two Tf)
      (typeLayer_twistedEntrywiseAut_D4_oneW hD hd hK 2 (Or.inr rfl) Tf⁻¹ hTinv)

theorem typeLayer_adjointD4_of_fieldTypeW (hD : LieSOutTypeW T tm tf tN) {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0)) :
    TypeLayer T α False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hK
  obtain ⟨d, Tf, hd0, hdf, hT, hT3, hσT⟩ := exists_frobenius_of_cube Nat.prime_two hf K hK σ hσ3 hσ1
  rw [d4Graph_zero, mul_one] at hαeq
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact four_le_card Nat.prime_two (by omega)
  have hKd : Nat.card K = (2 ^ d) ^ 3 := by rw [hK, ← pow_mul, hdf]
  have hfix : Nat.card (fixSubfield Tf) = 2 ^ d :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_two hd0 hKd Tf hT
  have hfield : TypeLayer T (entrywiseAdjointAut Tag.D4 Tf) False :=
    typeLayer_entrywiseAdjointAut_D4W hD hd0 Tf hfix
  have hconj : ∀ (β : MulAut (adjointGroup Tag.D4 K)) (g' : adjointGroup Tag.D4 K)
      (a' : Fin Tag.D4.rank → Kˣ), β = MulAut.conj g' * exactNormalAut Tag.D4 K a' Tf 0 →
      β ^ 3 = 1 → TypeLayer T β False := by
    intro β g' a' hβ hβ3
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_entrywiseAdjointAut_D4 hK hK4 hd0 hdf Tf hT g' a' β hβ hβ3
    exact typeLayer_of_conj ψ β (hψ ▸ hfield)
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    exact hconj α g a hαeq hα3
  · obtain ⟨g', a', hα2⟩ := sq_conj_mul_exactNormalAut g a σ
    have hσ2 : σ ^ 2 = Tf := by
      rw [hσ, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
    rw [hσ2, ← hαeq] at hα2
    have hα23 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα3, one_pow]
    have hα22 : (α ^ 2) ^ 2 = α := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hα3, one_mul]
    have hfixeq : fixSubgroup α = fixSubgroup (α ^ 2) := fixedSubgroup_pow_eq hα22
    exact typeLayer_of_fix_eq hfixeq (hconj (α ^ 2) g' a' hα2 hα23)

theorem typeLayer_adjointD4_of_graphFieldTypeW (hD : LieSOutTypeW T tm tf tN) {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (hε : ε < 3) (hε0 : ε ≠ 0)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    TypeLayer T α False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨e, Tf, he, hef, hT, hσT⟩ := exists_frobenius_eq_or_inv_of_orderOf_three Nat.prime_two hf K
    hK σ hord
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact four_le_card Nat.prime_two (by omega)
  have hKe : Nat.card K = (2 ^ e) ^ 3 := by rw [hK, ← pow_mul, hef]
  have hε' : ε = 1 ∨ ε = 2 := by omega
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    obtain ⟨ψ, hψ⟩ :=
      exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef Tf hT α hα3 g a ε hαeq
    refine typeLayer_of_conj ψ α ?_
    rw [hψ]
    exact typeLayer_twistedEntrywiseAut_D4W hD he hKe Tf hT (ε : ℤ) (by omega)
  · rw [hσ] at hαeq
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef Tf Tf⁻¹
      hT (mul_inv_cancel Tf) α hα3 g a ε hαeq
    have hshift : twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) Tf =
        twistedEntrywiseAut TwistTag.D4 (3 - (ε : ℤ)) Tf := by
      have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-(ε : ℤ)) 1 Tf
      rw [show -(ε : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 3 - (ε : ℤ) by
        change -(ε : ℤ) + 1 * 3 = _
        ring] at h
      exact h.symm
    have hinv : TypeLayer T α⁻¹ False := by
      refine typeLayer_of_conj ψ α⁻¹ ?_
      rw [hψ, hshift]
      exact typeLayer_twistedEntrywiseAut_D4W hD he hKe Tf hT (3 - (ε : ℤ)) (by omega)
    exact (typeLayer_inv_iff α False).1 hinv

theorem typeLayer_adjointD4_of_graphTypeW (hD : LieSOutTypeW T tm tf tN)
    {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) :
    TypeLayer T α False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv hf K hK α
      hα3 g a hε hαeq
  haveI := finite_graphFixedRootGroup_D4 Fr
  exact typeLayer_of_fixEquiv e (typeLayer_three_D4_outer_twoW hD hf hK₃ Fr hFr φ hφ3 hφout)

theorem typeLayer_adjointD4_outerW (hD : LieSOutTypeW T tm tf tN)
    {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 K)) :
    TypeLayer T α False := by
  obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ := outer_cube_normal_form_cases α hα3 hα
  rcases hcase with ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩
  · subst hε0
    exact typeLayer_adjointD4_of_fieldTypeW hD hf K hK α hα3 g a σ hσ3 hσ1 hαeq
  · exact typeLayer_adjointD4_of_graphFieldTypeW hD hf K hK α hα3 g a σ ε hε hε0 hσ3 hσ1 hαeq
  · subst hσ1
    exact typeLayer_adjointD4_of_graphTypeW hD hf K hK α hα3 g a (by omega) hαeq

end D4

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
