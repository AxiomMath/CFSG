module

public import CFSG.CharacterTheory.Wreathed.ConditionalCuspidalSelectionCount
public import CFSG.CharacterTheory.Wreathed.ConditionalExplicitPrincipalOrderDual
public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesValues

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
  CFSG.TwoRankLowerBound.Helpers

section Families

variable {H : Type} [Group H] [Fintype H]

theorem sum_moment_of_families (basis : FiniteIrreducibleCharacterBasis H) {m : ℕ}
    (B0 PL CH : Finset basis.index) (lbl₁ lbl₂ : Fin m → basis.index)
    (hB0 : B0 = Finset.univ.image lbl₁ ∪ Finset.univ.image lbl₂ ∪ PL ∪ CH)
    (hinj₁ : Function.Injective lbl₁) (hinj₂ : Function.Injective lbl₂) (Y Z : H) (q : ℕ)
    (hq : 3 ≤ q) (Φ : ℂ)
    (h₁ : ∀ r, (basis.representation (lbl₁ r)).character Y ^ 2 = 1 ∧
      (basis.representation (lbl₁ r)).character Z = 1 ∧
      (basis.representation (lbl₁ r)).character 1 = 1)
    (h₂ : ∀ r, (basis.representation (lbl₂ r)).character Y ^ 2 = 1 ∧
      (basis.representation (lbl₂ r)).character Z = Φ ∧
      (basis.representation (lbl₂ r)).character 1 = q)
    (hP : ∀ l ∈ PL, (basis.representation l).character Z = 1 + Φ ∧
      (basis.representation l).character 1 = (q : ℂ) + 1)
    (hC : ∀ l ∈ CH, (basis.representation l).character Z = Φ - 1 ∧
      (basis.representation l).character 1 = (q : ℂ) - 1) :
    ∑ l ∈ B0, (basis.representation l).character Y ^ 2 * (basis.representation l).character Z /
        (basis.representation l).character 1 =
      m + m * Φ / q + (∑ l ∈ PL, (basis.representation l).character Y ^ 2) * (1 + Φ) / (q + 1) +
        (∑ l ∈ CH, (basis.representation l).character Y ^ 2) * (Φ - 1) / (q - 1) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqp : (q : ℂ) + 1 ≠ 0 := by exact_mod_cast (show q + 1 ≠ 0 by omega)
  have hqm : (q : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero, ← Nat.cast_one, Ne, Nat.cast_inj]
    omega
  have hq1 : (1 : ℂ) ≠ q := by exact_mod_cast (show 1 ≠ q by omega)
  have hdeg₁ : ∀ l ∈ Finset.univ.image lbl₁, (basis.representation l).character 1 = 1 := by
    intro l hl
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hl
    exact (h₁ r).2.2
  have hdeg₂ : ∀ l ∈ Finset.univ.image lbl₂, (basis.representation l).character 1 = q := by
    intro l hl
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hl
    exact (h₂ r).2.2
  have hd : ∀ {X Y' : Finset basis.index} {c d : ℂ},
      (∀ l ∈ X, (basis.representation l).character 1 = c) →
      (∀ l ∈ Y', (basis.representation l).character 1 = d) → c ≠ d → Disjoint X Y' := by
    intro X Y' c d hX hY hcd
    rw [Finset.disjoint_left]
    intro l hlX hlY
    exact hcd ((hX l hlX).symm.trans (hY l hlY))
  have hP1 : ∀ l ∈ PL, (basis.representation l).character 1 = (q : ℂ) + 1 :=
    fun l hl => (hP l hl).2
  have hC1 : ∀ l ∈ CH, (basis.representation l).character 1 = (q : ℂ) - 1 :=
    fun l hl => (hC l hl).2
  have d12 := hd hdeg₁ hdeg₂ hq1
  have d13 := hd hdeg₁ hP1 (by
    intro h
    have : (0 : ℂ) = q := by linear_combination h
    exact hq0 this.symm)
  have d14 := hd hdeg₁ hC1 (by
    intro h
    have : ((2 : ℕ) : ℂ) = q := by push_cast; linear_combination h
    exact (show (2 : ℕ) ≠ q by omega) (by exact_mod_cast this))
  have d23 := hd hdeg₂ hP1 (by
    intro h
    have : (0 : ℂ) = 1 := by linear_combination h
    exact zero_ne_one this)
  have d24 := hd hdeg₂ hC1 (by
    intro h
    have : (1 : ℂ) = 0 := by linear_combination h
    exact one_ne_zero this)
  have d34 := hd hP1 hC1 (by
    intro h
    have : (2 : ℂ) = 0 := by linear_combination h
    exact two_ne_zero this)
  rw [hB0, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
      ⟨d14, d24⟩, d34⟩),
    Finset.sum_union (Finset.disjoint_union_left.mpr ⟨d13, d23⟩), Finset.sum_union d12,
    Finset.sum_image fun r _ r' _ h => hinj₁ h, Finset.sum_image fun r _ r' _ h => hinj₂ h]
  have hs₁ : ∑ r : Fin m, (basis.representation (lbl₁ r)).character Y ^ 2 *
      (basis.representation (lbl₁ r)).character Z / (basis.representation (lbl₁ r)).character 1 =
        m := by
    rw [Finset.sum_congr rfl fun r _ => by rw [(h₁ r).1, (h₁ r).2.1, (h₁ r).2.2]]
    simp
  have hs₂ : ∑ r : Fin m, (basis.representation (lbl₂ r)).character Y ^ 2 *
      (basis.representation (lbl₂ r)).character Z / (basis.representation (lbl₂ r)).character 1 =
        m * Φ / q := by
    rw [Finset.sum_congr rfl fun r _ => by rw [(h₂ r).1, (h₂ r).2.1, (h₂ r).2.2]]
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsP : ∑ l ∈ PL, (basis.representation l).character Y ^ 2 *
      (basis.representation l).character Z / (basis.representation l).character 1 =
      (∑ l ∈ PL, (basis.representation l).character Y ^ 2) * (1 + Φ) / (q + 1) := by
    rw [Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun l hl => by rw [(hP l hl).1, (hP l hl).2]
  have hsC : ∑ l ∈ CH, (basis.representation l).character Y ^ 2 *
      (basis.representation l).character Z / (basis.representation l).character 1 =
      (∑ l ∈ CH, (basis.representation l).character Y ^ 2) * (Φ - 1) / (q - 1) := by
    rw [Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun l hl => by rw [(hC l hl).1, (hC l hl).2]
  rw [hs₁, hs₂, hsP, hsC]

end Families

section PrincipalSeries

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem principalInduced_inl_of_two_power (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1) {k : ℕ} (hk : orderOf P.1.1 = 2 ^ k)
    (g : CentralExtension F b m hm heven) :
    principalInduced (hm := hm) (heven := heven) hSigma P 1 (SemidirectProduct.inl g) =
      principalSeries F b m hm heven (torusCharacter F b m hm heven P) g := by
  have hStab := parameterStabilizer_eq_top_of_two_power hSigma hd P hk
  have hC : ∀ q : Sigma ⧸ parameterStabilizer hSigma P,
      ∃! σ, σ ∈ ({1} : Finset Sigma) ∧ (σ : Sigma ⧸ parameterStabilizer hSigma P) = q := by
    intro q
    refine ⟨1, ⟨Finset.mem_singleton_self 1, ?_⟩, fun σ hσ => Finset.mem_singleton.mp hσ.1⟩
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.eq, hStab]
    exact Subgroup.mem_top _
  rw [principalInduced_inl_eq_sum hSigma hb hd hP 1 {1} hC g, Finset.sum_singleton,
    fieldParameter_one]

theorem principalInduced_eq_iff_of_two_power (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P Q : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1) (hQ : Q.1.1 ≠ 1) {k : ℕ}
    (hk : orderOf P.1.1 = 2 ^ k) :
    principalInduced (hm := hm) (heven := heven) hSigma P 1 = principalInduced hSigma Q 1 ↔
      Q = P ∨ Q = weylParameter F b m heven P := by
  rw [principalInduced_eq_iff hSigma hb hd hP hQ]
  have hkw : orderOf (weylParameter F b m heven P).1.1 = 2 ^ k :=
    (orderOf_inv P.1.1).trans hk
  constructor
  · rintro ⟨⟨σ, hσ | hσ⟩, -⟩
    · left
      rw [hσ, fieldParameter_eq_of_two_power hSigma hd hk]
    · right
      rw [hσ, fieldParameter_eq_of_two_power hSigma hd hkw]
  · intro h
    refine ⟨⟨1, ?_⟩, fun τ h₁ h₂ => rfl⟩
    rw [fieldParameter_one, fieldParameter_one]
    exact h

end PrincipalSeries

section Moments

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
  {H : Type} [Group H] [Fintype H]

theorem sum_principalSeriesLabels_sq [Fintype (PrincipalSeriesParameter F b m)]
    (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    (Ψ : SemilinearExtension F b m hm heven Sigma hSigma ≃* H)
    (basis : FiniteIrreducibleCharacterBasis H) (PL : Finset basis.index) {PH : Set (H → ℂ)}
    (hPL : ∀ l, l ∈ PL ↔ (basis.representation l).character ∈ PH)
    (hPHlab : ∀ θ ∈ PH, ∃ l, (basis.representation l).character = θ)
    (hPH : PH = (fun P : PrincipalSeriesParameter F b m => fun h => principalInduced
      (hm := hm) (heven := heven) hSigma P 1 (Ψ.symm h)) ''
        {P | (∃ k : ℕ, orderOf P.1.1 = 2 ^ k) ∧ P.1.1 ≠ 1}) (g : CentralExtension F b m hm heven) :
    ∑ l ∈ PL, (basis.representation l).character (Ψ (SemidirectProduct.inl g)) ^ 2 =
      (∑ P ∈ Finset.univ.filter (fun P : PrincipalSeriesParameter F b m =>
          P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k),
        principalSeries F b m hm heven (torusCharacter F b m hm heven P) g ^ 2) / 2 := by
  set S := Finset.univ.filter (fun P : PrincipalSeriesParameter F b m =>
    P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k) with hS
  set f : PrincipalSeriesParameter F b m → H → ℂ := fun P h =>
    principalInduced (hm := hm) (heven := heven) hSigma P 1 (Ψ.symm h) with hf
  have hmemS : ∀ P, P ∈ S ↔ P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k := fun P => by
    simp [hS]
  have himage : PL.image (fun l => (basis.representation l).character) = S.image f := by
    ext θ
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have h1 := (hPL l).mp hl
      rw [hPH] at h1
      obtain ⟨P, ⟨hk, hP⟩, hPθ⟩ := h1
      exact ⟨P, (hmemS P).mpr ⟨hP, hk⟩, hPθ⟩
    · rintro ⟨P, hPS, rfl⟩
      have hmem : f P ∈ PH := by
        rw [hPH]
        obtain ⟨hP, hk⟩ := (hmemS P).mp hPS
        exact ⟨P, ⟨hk, hP⟩, rfl⟩
      obtain ⟨l, hl⟩ := hPHlab _ hmem
      exact ⟨l, (hPL l).mpr (hl ▸ hmem), hl⟩
  have hsum1 : ∑ l ∈ PL, (basis.representation l).character (Ψ (SemidirectProduct.inl g)) ^ 2 =
      ∑ θ ∈ S.image f, θ (Ψ (SemidirectProduct.inl g)) ^ 2 := by
    rw [← himage, Finset.sum_image fun l _ l' _ h => basis.distinct h]
  have hpairs := sum_comp_eq_two_mul_sum_image f (weylParameter F b m heven) S
    (fun P hP => by
      obtain ⟨hP1, k, hk⟩ := (hmemS P).mp hP
      refine ⟨(hmemS _).mpr ⟨weylParameter_ne_one F b m heven hP1, k,
        (orderOf_inv P.1.1).trans hk⟩, ?_⟩
      exact (ne_weylParameter F b m heven hb hP1).symm)
    (fun P hP Q hQ => by
      obtain ⟨hP1, k, hk⟩ := (hmemS P).mp hP
      obtain ⟨hQ1, -⟩ := (hmemS Q).mp hQ
      rw [← principalInduced_eq_iff_of_two_power hSigma hb hd hP1 hQ1 hk]
      constructor
      · intro h
        funext w
        have := congrFun h (Ψ w)
        simpa only [hf, MulEquiv.symm_apply_apply] using this
      · intro h
        show (fun w => principalInduced (hm := hm) (heven := heven) hSigma P 1 (Ψ.symm w)) =
          fun w => principalInduced (hm := hm) (heven := heven) hSigma Q 1 (Ψ.symm w)
        rw [h])
    (fun θ => θ (Ψ (SemidirectProduct.inl g)) ^ 2)
  rw [hsum1]
  rw [eq_div_iff two_ne_zero, mul_comm, ← hpairs]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hP1, k, hk⟩ := (hmemS P).mp hP
  rw [hf]
  dsimp only
  rw [MulEquiv.symm_apply_apply, principalInduced_inl_of_two_power hSigma hb hd hP1 hk]

theorem sum_cuspidalLabels_sq {E : Type} [Field E] [Algebra F E]
    {basis : Module.Basis (Fin 2) F E} {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b)
    (h2 : (2 : F) ≠ 0) (z₀ : Eˣ) (hz₀ : (z₀ : E) * (z₀ : E) ^ Nat.card F = algebraMap F E b)
    (y₀ : Eˣ) (hy₀ : (y₀ : E) * (y₀ : E) ^ Nat.card F = -1) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    [Fintype (NonsplitParameter F E b m h2 z₀ hz₀)]
    (Ψ : SemilinearExtension F b m hm heven Sigma hSigma ≃* H)
    (basisH : FiniteIrreducibleCharacterBasis H) (CH : Finset basisH.index)
    (hbij : Set.BijOn (fun l => fun g => (basisH.representation l).character
        (Ψ (SemidirectProduct.inl g))) ↑CH
      ((fun P : NonsplitParameter F E b m h2 z₀ hz₀ =>
        cuspidalCharacter hb ψ (nonsplitCharacter F b m hm heven E basis h2 z₀ hz₀ P)) ''
          {P | P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k}))
    (g : CentralExtension F b m hm heven) :
    ∑ l ∈ CH, (basisH.representation l).character (Ψ (SemidirectProduct.inl g)) ^ 2 =
      (∑ P ∈ Finset.univ.filter (fun P : NonsplitParameter F E b m h2 z₀ hz₀ =>
          P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k),
        cuspidalCharacter hb ψ (nonsplitCharacter F b m hm heven E basis h2 z₀ hz₀ P) g ^ 2) /
        2 := by
  set T := Finset.univ.filter (fun P : NonsplitParameter F E b m h2 z₀ hz₀ =>
    P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k) with hT
  set f := fun P : NonsplitParameter F E b m h2 z₀ hz₀ =>
    cuspidalCharacter hb ψ (nonsplitCharacter F b m hm heven E basis h2 z₀ hz₀ P) with hf
  set r := fun l => fun g : CentralExtension F b m hm heven =>
    (basisH.representation l).character (Ψ (SemidirectProduct.inl g)) with hr
  have hmemT : ∀ P, P ∈ T ↔ P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k := fun P => by
    simp [hT]
  have himage : CH.image r = T.image f := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_image, hbij.image_eq]
    congr 1
    ext P
    rw [Finset.mem_coe, hmemT]
    rfl
  have hsum1 : ∑ l ∈ CH, (basisH.representation l).character (Ψ (SemidirectProduct.inl g)) ^ 2 =
      ∑ θ ∈ T.image f, θ g ^ 2 := by
    rw [← himage, Finset.sum_image fun l hl l' hl' h => hbij.2.1 hl hl' h]
  have hpairs := sum_comp_eq_two_mul_sum_image f
    (nonsplitWeylParameter F b m heven E basis h2 z₀ hz₀) T
    (fun P hP => by
      obtain ⟨h1, h2'⟩ := nonsplitWeylParameter_two_pow hb h2 z₀ hz₀ ((hmemT P).mp hP)
      exact ⟨(hmemT _).mpr h1, h2'⟩)
    (fun P hP Q _ => cuspidalCharacter_nonsplit_eq_iff hpodd hb h2 z₀ hz₀ y₀ hy₀ hψ
      ((hmemT P).mp hP).1)
    (fun θ => θ g ^ 2)
  rw [hsum1, eq_div_iff two_ne_zero, mul_comm, ← hpairs]

end Moments

end CFSG.Wreathed
