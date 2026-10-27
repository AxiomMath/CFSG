module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearPrincipalEquality
public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesFixed

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.CentralSL2

section Values

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem principalInduced_inl_eq_sum (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1)
    (ν : parameterStabilizer hSigma P →* ℂˣ) (C : Finset Sigma)
    (hC : ∀ q : Sigma ⧸ parameterStabilizer hSigma P,
      ∃! σ, σ ∈ C ∧ (σ : Sigma ⧸ parameterStabilizer hSigma P) = q)
    (g : CentralExtension F b m hm heven) :
    principalInduced (hm := hm) (heven := heven) hSigma P ν (SemidirectProduct.inl g) =
      ∑ σ ∈ C, principalSeries F b m hm heven
        (torusCharacter F b m hm heven (fieldParameter hSigma σ P)) g := by
  obtain ⟨-, -, -, hrest, -⟩ := principal_clifford (hm := hm) (heven := heven) hSigma hb hd hP
  have h := congrFun ((hrest C hC).1 ν) g
  rw [Finset.sum_apply] at h
  exact h

theorem principalInduced_unipotent (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1)
    (ν : parameterStabilizer hSigma P →* ℂˣ) {t : F} (ht : t ≠ 0) :
    principalInduced (hm := hm) (heven := heven) hSigma P ν
        (SemidirectProduct.inl (unipotentElement F b m hm heven t)) =
      ((parameterStabilizer hSigma P).index : ℂ) := by
  obtain ⟨C, hC⟩ := CFSG.Wreathed.exists_leftCoset_reps (parameterStabilizer hSigma P)
  rw [principalInduced_inl_eq_sum hSigma hb hd hP ν C hC]
  have hterm : ∀ σ : Sigma, principalSeries F b m hm heven
      (torusCharacter F b m hm heven (fieldParameter hSigma σ P))
        (unipotentElement F b m hm heven t) = 1 := by
    intro σ
    have h := principalSeries_unipotent F b m hm heven
      (torusCharacter F b m hm heven (fieldParameter hSigma σ P)) 0 ht
    rw [zpow_zero, one_mul, zpow_zero] at h
    exact h
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, nsmul_eq_mul, mul_one,
    card_coset_reps _ C hC]

omit [Fintype F] in
theorem torusDiag_not_mem_zpowers {c : Fˣ} (hc : (c : F) ^ 2 ≠ 1) :
    torusDiag F b m hm heven c ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  intro h
  have h1 := zpowers_cyclicGenerator_sq_smul F b m hm heven h (some 1)
  rw [torusDiag_smul_some, mul_one, Option.some.injEq] at h1
  exact hc h1

theorem principalInduced_torusDiag (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1)
    (ν : parameterStabilizer hSigma P →* ℂˣ) (C : Finset Sigma)
    (hC : ∀ q : Sigma ⧸ parameterStabilizer hSigma P,
      ∃! σ, σ ∈ C ∧ (σ : Sigma ⧸ parameterStabilizer hSigma P) = q)
    {c : Fˣ} (hc : (c : F) ^ 2 ≠ 1) :
    principalInduced (hm := hm) (heven := heven) hSigma P ν
        (SemidirectProduct.inl (torusDiag F b m hm heven c)) =
      ∑ σ ∈ C, (((fieldParameter hSigma σ P).1.1 c : ℂˣ) +
        ((fieldParameter hSigma σ P).1.1 c⁻¹ : ℂ)) := by
  rw [principalInduced_inl_eq_sum hSigma hb hd hP ν C hC]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [principalSeries_splitTorus F b m hm heven hb _
    (torusDiag_mem_splitTorus F b m hm heven c) (torusDiag_not_mem_zpowers hc)]
  have hw : (⟨(weylElement F b m hm heven)⁻¹ * torusDiag F b m hm heven c *
      weylElement F b m hm heven, weyl_conj_mem_splitTorus F b m hm heven
        (torusDiag_mem_splitTorus F b m hm heven c)⟩ : splitTorus F b m hm heven) =
      ⟨torusDiag F b m hm heven c⁻¹, torusDiag_mem_splitTorus F b m hm heven c⁻¹⟩ :=
    Subtype.ext (weylElement_inv_conj_torusDiag F b m hm heven c)
  rw [hw, torusCharacter_torusDiag, torusCharacter_torusDiag]

theorem fixedPointCount_inl_unipotent {t : F} (ht : t ≠ 0) :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F)
      (SemidirectProduct.inl (unipotentElement F b m hm heven t)) = 1 := by
  rw [fixedPointCount_inl]
  have h1 := card_fixed_unipotent (F := F) (b := b) (hm := hm) (heven := heven)
    (Subgroup.one_mem _) ht
  rw [one_mul] at h1
  rw [h1, Nat.cast_one]

theorem fixedPointCount_inl_torusDiag (hb : ¬ IsSquare b) {c : Fˣ} (hc : (c : F) ^ 2 ≠ 1) :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F)
      (SemidirectProduct.inl (torusDiag F b m hm heven c)) = 2 := by
  rw [fixedPointCount_inl, card_fixed_splitTorus hb (torusDiag_mem_splitTorus F b m hm heven c)
    (torusDiag_not_mem_zpowers hc)]
  norm_num

omit [Fintype F] in
theorem torusCharacter_pow_eq_one (P : PrincipalSeriesParameter F b m) {k : ℕ}
    (hk : P.1.1 ^ (2 ^ k) = 1) (t : splitTorus F b m hm heven) :
    torusCharacter F b m hm heven P t ^ (m * 2 ^ k) = 1 := by
  obtain ⟨c, j, hj⟩ := splitTorus_normalForm F b m hm heven t t.2
  have ht : t = ⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c⟩ *
      ⟨torusGenerator F b m hm heven, torusGenerator_mem_splitTorus F b m hm heven⟩ ^ (j : ℕ) :=
    Subtype.ext (by rw [hj]; rfl)
  have hηc : P.1.1 c ^ (2 ^ k) = 1 := by
    rw [← MonoidHom.pow_apply, hk, MonoidHom.one_apply]
  have hz : P.1.2 ^ (m * 2 ^ k) = 1 := by
    rw [pow_mul, P.2, ← MonoidHom.pow_apply, hk, MonoidHom.one_apply]
  rw [ht, map_mul, map_pow, torusCharacter_torusDiag, torusCharacter_torusGenerator, mul_pow]
  have h1 : (P.1.1 c) ^ (m * 2 ^ k) = 1 := by rw [mul_comm, pow_mul, hηc, one_pow]
  have h2 : (P.1.2 ^ (j : ℕ)) ^ (m * 2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  rw [h1, h2, one_mul]

theorem units_eq_one_of_two_pow_of_odd {w : ℂˣ} {a t : ℕ} (ha : w ^ (2 ^ a) = 1) (ht : Odd t)
    (hwt : w ^ t = 1) : w = 1 := by
  have hcop : Nat.Coprime (2 ^ a) t := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr ht)
  have h := pow_gcd_eq_one.mpr ⟨ha, hwt⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

omit [Fintype F] in
theorem mem_semilinearBorel_iff_smul_none {P : PrincipalSeriesParameter F b m}
    (hP : parameterStabilizer hSigma P = ⊤)
    (x : SemilinearExtension F b m hm heven Sigma hSigma) :
    x ∈ semilinearBorel hSigma (parameterStabilizer hSigma P) ↔ x • (none : Omega F) = none := by
  rw [mem_semilinearBorel_iff, semilinear_smul_none, hP]
  simp only [Subgroup.mem_top, and_true]
  exact Iff.rfl

omit [Fintype F] in
theorem inl_smul (g : CentralExtension F b m hm heven) (x : Omega F) :
    (SemidirectProduct.inl g : SemilinearExtension F b m hm heven Sigma hSigma) • x = g • x := by
  rw [semilinearExtension_smul_def, CentralSL2.semilinearAction_inl]
  rfl

theorem principalInduced_one_odd (hd : Odd (Nat.card Sigma)) {a : ℕ} (hma : m = 2 ^ a)
    {P : PrincipalSeriesParameter F b m} {k : ℕ} (hk : orderOf P.1.1 = 2 ^ k)
    {g : SemilinearExtension F b m hm heven Sigma hSigma} (hg : Odd (orderOf g)) :
    principalInduced (hm := hm) (heven := heven) hSigma P 1 g =
      fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) g := by
  have hStab := parameterStabilizer_eq_top_of_two_power hSigma hd P hk
  set S := parameterStabilizer hSigma P with hSdef
  have hH := mem_semilinearBorel_iff_smul_none (hm := hm) (heven := heven) hSigma hStab
  let rep : Omega F → SemilinearExtension F b m hm heven Sigma hSigma := fun p =>
    SemidirectProduct.inl (borelRep F b m hm heven p)
  have hrep : ∀ p, rep p • (none : Omega F) = p := fun p => by
    change (SemidirectProduct.inl (borelRep F b m hm heven p) :
      SemilinearExtension F b m hm heven Sigma hSigma) • (none : Omega F) = p
    rw [inl_smul, borelRep_smul]
  have hμ : ∀ s t : semilinearBorel (hm := hm) (heven := heven) hSigma S,
      (borelTwist hSigma P S le_rfl 1 (s * t * s⁻¹) : ℂ) = borelTwist hSigma P S le_rfl 1 t :=
    fun s t => congrArg Units.val (units_hom_conj _ s t)
  have hηk : P.1.1 ^ (2 ^ k) = 1 := by rw [← hk, pow_orderOf_eq_one]
  have hterm : ∀ p : Omega F, extendByZero (semilinearBorel hSigma S)
      (fun x => (borelTwist hSigma P S le_rfl 1 x : ℂ)) ((rep p)⁻¹ * g * rep p) =
        if g • p = p then 1 else 0 := by
    intro p
    by_cases hgp : g • p = p
    · rw [ite_eq_left hgp]
      have hmem : (rep p)⁻¹ * g * rep p ∈ semilinearBorel hSigma S :=
        conj_mem_of_stabilizer hH (hrep p) hgp
      rw [extendByZero_of_mem _ _ hmem]
      set y : semilinearBorel (hm := hm) (heven := heven) hSigma S := ⟨_, hmem⟩ with hy
      have hyodd : Odd (orderOf y) := by
        rw [← Subgroup.orderOf_coe]
        change Odd (orderOf ((rep p)⁻¹ * g * rep p))
        have hconj : (rep p)⁻¹ * g * rep p = MulAut.conj (rep p)⁻¹ g := by
          rw [MulAut.conj_apply, inv_inv]
        rw [hconj, MulEquiv.orderOf_eq]
        exact hg
      have hw2 : borelTwist hSigma P S le_rfl 1 y ^ (2 ^ (a + k)) = 1 := by
        rw [borelTwist_apply, MonoidHom.one_apply, mul_one, pow_add, ← hma]
        exact torusCharacter_pow_eq_one P hηk _
      have hwt : borelTwist hSigma P S le_rfl 1 y ^ orderOf y = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [units_eq_one_of_two_pow_of_odd hw2 hyodd hwt, Units.val_one]
    · rw [ite_eq_right hgp]
      apply extendByZero_of_not_mem
      intro hmem
      apply hgp
      have h := (conj_mem_iff_of_stabilizer hH (rep p) g).mp hmem
      rwa [hrep] at h
  rw [principalInduced, principalTwist, inducedFunction_stabilizer hH _ hμ rep hrep g,
    Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_boole, fixedPointCount]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem principalInduced_eq_mul_of_top {P : PrincipalSeriesParameter F b m}
    (hP : parameterStabilizer hSigma P = ⊤) (ν : parameterStabilizer hSigma P →* ℂˣ)
    (g : SemilinearExtension F b m hm heven Sigma hSigma) :
    principalInduced (hm := hm) (heven := heven) hSigma P ν g =
      principalInduced hSigma P 1 g *
        (ν ⟨g.right, hP ▸ Subgroup.mem_top g.right⟩ : ℂ) := by
  let χ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ := fun h =>
    (ν ⟨h.right, hP ▸ Subgroup.mem_top h.right⟩ : ℂ)
  have hχ : CFSG.BlocksIsClassFunction χ := by
    intro x h
    change (ν ⟨(h * x * h⁻¹).right, _⟩ : ℂ) = (ν ⟨x.right, _⟩ : ℂ)
    have hmem : (⟨(h * x * h⁻¹).right, hP ▸ Subgroup.mem_top _⟩ :
        parameterStabilizer hSigma P) =
        ⟨h.right, hP ▸ Subgroup.mem_top _⟩ * ⟨x.right, hP ▸ Subgroup.mem_top _⟩ *
          (⟨h.right, hP ▸ Subgroup.mem_top _⟩ : parameterStabilizer hSigma P)⁻¹ := by
      apply Subtype.ext
      simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, Subgroup.coe_mul,
        Subgroup.coe_inv]
    rw [hmem, units_hom_conj]
  have hfun : (fun x : semilinearBorel (hm := hm) (heven := heven) hSigma
      (parameterStabilizer hSigma P) =>
      (borelTwist hSigma P (parameterStabilizer hSigma P) le_rfl ν x : ℂ)) =
      fun x => (borelTwist hSigma P (parameterStabilizer hSigma P) le_rfl 1 x : ℂ) * χ x := by
    funext x
    rw [borelTwist_apply, borelTwist_apply, MonoidHom.one_apply, mul_one, Units.val_mul]
  rw [principalInduced, principalTwist, hfun, CentralSL2.inducedFunction_mul_classFunction _ _ hχ]
  rfl

end Values

end CFSG.Wreathed
