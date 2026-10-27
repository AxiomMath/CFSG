module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SLFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SUFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OmegaFacts
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.Assembly.LowTwoRank

private def OrthCompData (P : (X : Type) → [Group X] → Prop) (H : Type) [Group H] : Prop :=
  ∃ (X : Type) (_ : Group X) (_ : Finite X) (f : X →* H), P X ∧
    Function.Surjective f ∧ f.ker ≤ Subgroup.center X

private def LieFactorProperty (ℓ : ℕ) (X : Type) [Group X] : Prop :=
  LieFactorData ℓ X ∧
    (SLAltSixFacts → SUAltSixFacts → OmegaAltSixFacts → ℓ ≠ 3 →
      IsEmpty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)))

private def OrthFactorDataCard (ℓ q : ℕ) (X : Type) [Group X] : Prop :=
  OrthFactorOver ℓ q X ∧ LieFactorProperty ℓ X

private theorem OrthCompData.mono {P Q : (X : Type) → [Group X] → Prop}
    (h : ∀ (X : Type) [Group X], P X → Q X) {H : Type} [Group H]
    (hH : OrthCompData P H) : OrthCompData Q H := by
  obtain ⟨X, _, _, f, hP, hf, hk⟩ := hH
  exact ⟨X, inferInstance, inferInstance, f, h X hP, hf, hk⟩

private theorem OrthCompData.of_surj {P : (X : Type) → [Group X] → Prop}
    (hperf : ∀ (X : Type) [Group X], P X → commutator X = ⊤) {H H' : Type} [Group H]
    [Group H'] (h : OrthCompData P H) (φ : H →* H') (hφ : Function.Surjective φ)
    (hk : φ.ker ≤ Subgroup.center H) : OrthCompData P H' := by
  obtain ⟨X, _, _, f, hX, hf, hfk⟩ := h
  refine ⟨X, inferInstance, inferInstance, φ.comp f, hX, hφ.comp hf, ?_⟩
  intro x hx
  have h1 : f x ∈ Subgroup.center H := hk hx
  rw [← comap_center_of_surjective (hperf X hX) f hf hfk]
  exact h1

private theorem OrthCompData.of_mulEquiv {P : (X : Type) → [Group X] → Prop} {H H' : Type}
    [Group H] [Group H'] (h : OrthCompData P H) (e : H ≃* H') : OrthCompData P H' := by
  obtain ⟨X, _, _, f, hX, hf, hk⟩ := h
  refine ⟨X, inferInstance, inferInstance, e.toMonoidHom.comp f, hX, e.surjective.comp hf, ?_⟩
  intro x hx
  apply hk
  exact e.injective (by simpa using hx)

private theorem OrthCompData.of_model {P : (X : Type) → [Group X] → Prop} {X H : Type}
    [Group X] [Finite X] [Group H] (hX : P X) (e : X ≃* H) : OrthCompData P H := by
  refine OrthCompData.of_mulEquiv ⟨X, inferInstance, inferInstance, MonoidHom.id X, hX,
    Function.surjective_id, ?_⟩ e
  intro x hx
  have : x = 1 := hx
  rw [this]
  exact one_mem _

private theorem ker_subgroupMap_le_center {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (A : Subgroup ↥(orthDerived Q)) :
    ((QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).subgroupMap A).ker ≤
      Subgroup.center ↥A := by
  intro x hx
  have h1 : QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
      (x : ↥(orthDerived Q)) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp h1)
  rw [Subgroup.mem_center_iff]
  intro g
  refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))
  change (g : V ≃ₗ[K] V) ((x : V ≃ₗ[K] V) v) = (x : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v)
  rw [hc v, hc, map_smul]

private theorem OrthCompData.map_projective {P : (X : Type) → [Group X] → Prop}
    (hperf : ∀ (X : Type) [Group X], P X → commutator X = ⊤)
    {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {F : Subgroup (V ≃ₗ[K] V)} (hFΩ : F ≤ orthDerived Q)
    (h : OrthCompData P ↥F) :
    OrthCompData P ↥((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) :=
  (h.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFΩ).symm).of_surj hperf _
    (MonoidHom.subgroupMap_surjective _ _) (ker_subgroupMap_le_center _)

private theorem ringChar_eq_three_of_card_eq_nine' {E : Type} [Field E] [Fintype E]
    (h9 : Fintype.card E = 9) : ringChar E = 3 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card E (ringChar E)
  have hdvd : ringChar E ∣ 3 ^ 2 := by
    have : ringChar E ∣ ringChar E ^ (n : ℕ) := dvd_pow_self _ n.ne_zero
    rw [← hn, h9] at this
    simpa using this
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)

private theorem nontrivial_of_isQuasisimple' {K : Type*} [Group K] (h : CFSG.IsQuasisimple K) :
    Nontrivial K := by
  obtain ⟨a, b, hab⟩ := h.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [h])⟩

private theorem false_of_isQuasisimple_of_isSolvable' {K : Type*} [Group K]
    (h : CFSG.IsQuasisimple K) (hs : Group.IsSolvable K) : False := by
  haveI := nontrivial_of_isQuasisimple' h
  haveI : Group.IsPerfect K := h.1
  exact Group.IsPerfect.not_isSolvable K hs

private theorem isSolvable_sl_two_of_card_lt_four' {E : Type} [Field E] [Finite E]
    (h : Nat.card E < 4) : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) := by
  have hcard : Nat.card E = 2 ∨ Nat.card E = 3 := by
    have h2 : 1 < Nat.card E := Finite.one_lt_card
    omega
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) E) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable E hcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) E →* _))
    Matrix.SpecialLinearGroup.toGL_injective

private theorem orthCompData_specialBlock_paired (hSL : SLFactorFacts) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (h : K[X]) (hirr : Irreducible h)
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    OrthCompData (OrthFactorDataCard (ringChar K) (Nat.card K)) ↥(specialBlock Q x h) := by
  letI : Fact (Irreducible h) := ⟨hirr⟩
  letI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)
  have h4 : 4 ≤ Fintype.card (AdjoinRoot h) := by
    have := hx.p_lt_card_adjoinRoot hp hh hne1
    have := hp.two_le
    rw [Fintype.card_eq_nat_card]
    omega
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      Matrix.SpecialLinearGroup (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h) :=
    ((MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩).trans
      (Matrix.SpecialLinearGroup.toLin_equiv b).symm)
  have hX := hSL (AdjoinRoot h) (primaryMultiplicity x.toLinearMap h) hm (fun _ => h4)
  have hchar : ringChar (AdjoinRoot h) = ringChar K := (Algebra.ringChar_eq K (AdjoinRoot h)).symm
  rw [hchar] at hX
  have hcardE : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree :=
    CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h
  have hdpos : 1 ≤ h.natDegree := (Fact.out : Irreducible h).natDegree_pos
  have hfac : OrthFactorOver (ringChar K) (Nat.card K)
      (Matrix.SpecialLinearGroup (Fin (primaryMultiplicity x.toLinearMap h))
        (AdjoinRoot h)) :=
    Or.inl ⟨primaryMultiplicity x.toLinearMap h, h.natDegree, AdjoinRoot h, inferInstance,
      inferInstance, hm, hdpos, hchar, by rw [← Nat.card_eq_fintype_card]; exact hcardE,
      (fun _ => h4), ⟨MulEquiv.refl _⟩⟩
  refine OrthCompData.of_model ⟨hfac, hX, fun hA6 _ _ hℓ3 => ⟨fun e6 => ?_⟩⟩ e₁.symm
  obtain ⟨-, h9⟩ := hA6 (AdjoinRoot h) _ hm ⟨e6⟩
  exact hℓ3 (hchar ▸ ringChar_eq_three_of_card_eq_nine' h9)

private theorem orthCompData_specialBlock_selfDual (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (h : K[X])
    (hirr : Irreducible h) (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    OrthCompData (OrthFactorDataCard (ringChar K) (Nat.card K)) ↥(specialBlock Q x h) := by
  letI : Fact (Irreducible h) := ⟨hirr⟩
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hdpos : 1 ≤ d := by
    have := (Fact.out : Irreducible h).natDegree_pos
    omega
  obtain ⟨ℓ, f, hU, hq0, hbar⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_unitaryFieldData (K := K) (E := AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  haveI := hU.finite
  haveI : Fact ℓ.Prime := ⟨hU.prime⟩
  haveI := hU.charP
  letI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  have hE : Nat.card (AdjoinRoot h) = (ℓ ^ (f * d)) ^ 2 := by
    rw [hU.card, ← pow_mul, mul_comm]
  have hK : Fintype.card (AdjoinRoot h) = (ℓ ^ (f * d)) ^ 2 := by
    rw [Fintype.card_eq_nat_card, hE]
  have hchar : ringChar (AdjoinRoot h) = ringChar K := (Algebra.ringChar_eq K (AdjoinRoot h)).symm
  have hℓ : ringChar (AdjoinRoot h) = ℓ := ringChar.eq _ ℓ
  have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)
  have hfinV : Finite ↥(sesqSpecialUnitaryGroup B) := by
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    exact Finite.of_equiv _ e₁.toEquiv
  rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap h) 3 with hm3 | hm3
  ·
    have hm2 : Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 := by
      have : primaryMultiplicity x.toLinearMap h = 2 := by omega
      exact this
    obtain ⟨φ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU hBsymm
      hBl hm2
    letI : Fintype ↥hU.fixedField := Fintype.ofFinite _
    have hcardF : Fintype.card ↥hU.fixedField = ℓ ^ (f * d) := by
      rw [Fintype.card_eq_nat_card, hU.card_fixedField]
    have h4 : 4 ≤ Fintype.card ↥hU.fixedField := by
      by_contra hlt
      refine false_of_isQuasisimple_of_isSolvable' hq ?_
      haveI := isSolvable_sl_two_of_card_lt_four' (E := ↥hU.fixedField)
        (by rw [Nat.card_eq_fintype_card]; omega)
      exact Group.isSolvable_of_isSolvable_injective (f := (e₁.trans φ).toMonoidHom)
        (e₁.trans φ).injective
    have hX := hSL ↥hU.fixedField 2 le_rfl (fun _ => h4)
    have hcharF : ringChar ↥hU.fixedField = ringChar K := by
      rw [← hchar]
      exact Algebra.ringChar_eq ↥hU.fixedField (AdjoinRoot h)
    rw [hcharF] at hX
    have hcardNat : Nat.card ↥hU.fixedField = Nat.card K ^ d := by
      rw [Nat.card_eq_fintype_card, hcardF, hq0, ← pow_mul]
    have hfac : OrthFactorOver (ringChar K) (Nat.card K)
        (Matrix.SpecialLinearGroup (Fin 2) ↥hU.fixedField) :=
      Or.inl ⟨2, d, ↥hU.fixedField, inferInstance, inferInstance, le_rfl, hdpos, hcharF,
        by rw [← Nat.card_eq_fintype_card]; exact hcardNat, (fun _ => h4),
        ⟨MulEquiv.refl _⟩⟩
    refine OrthCompData.of_model ⟨hfac, hX, fun hA6 _ _ hℓ3 => ⟨fun e6 => ?_⟩⟩
      (φ.symm.trans e₁.symm)
    obtain ⟨-, h9⟩ := hA6 ↥hU.fixedField 2 le_rfl ⟨e6⟩
    exact hℓ3 (hcharF ▸ ringChar_eq_three_of_card_eq_nine' h9)
  ·
    by_cases hexc : primaryMultiplicity x.toLinearMap h = 3 ∧ ℓ ^ (f * d) = 2
    · exfalso
      refine false_of_isQuasisimple_of_isSolvable' hq ?_
      haveI : Group.IsSolvable ↥(sesqSpecialUnitaryGroup B) := by
        refine isSolvable_of_card_primeFactors_le_two ?_
        have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
          (n := primaryMultiplicity x.toLinearMap h) rfl (by omega)).2.1
        obtain ⟨hm3', hq2⟩ := hexc
        rw [hm3', hq2] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 2 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide +kernel
        have h216 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
          exact_mod_cast hcard.trans e
        rw [h216]
        decide +kernel
      exact Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective
    · have hmq : (primaryMultiplicity x.toLinearMap h, ℓ ^ (f * d)) ≠ (3, 2) := fun e =>
        hexc ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
      have hX := hSU (AdjoinRoot h) (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d)) hK hm3 hmq
      rw [hchar] at hX
      have hq' : ℓ ^ (f * d) = Nat.card K ^ d := by rw [hq0, ← pow_mul]
      obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
      obtain ⟨e₂⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU
        e₀ he₀
      have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
          (primaryMultiplicity x.toLinearMap h) =
          CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
            (AdjoinRoot h) := by
        rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
        exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
      let e₃ : ↥(CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
          (AdjoinRoot h)) ≃* ↥(sesqSpecialUnitaryGroup B) :=
        (e₂.trans (MulEquiv.subgroupCongr hS)).symm
      have hfac : OrthFactorOver (ringChar K) (Nat.card K)
          ↥(CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
            (AdjoinRoot h)) :=
        Or.inr (Or.inl ⟨primaryMultiplicity x.toLinearMap h, d, ℓ ^ (f * d), AdjoinRoot h,
          inferInstance, inferInstance, hm3, hdpos, hchar, hq', hK, hmq,
          ⟨MulEquiv.refl _⟩⟩)
      exact OrthCompData.of_model ⟨hfac, hX,
        (fun _ hSU6 _ _ =>
          hSU6 (AdjoinRoot h) (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d)) hK hm3)⟩
        (e₃.trans e₁.symm)

private theorem orthCompData_fixedFactor_of {p : ℕ} {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {P : (X : Type) → [Group X] → Prop}
    (hprov : ∀ L : Subgroup ↥(orthDerived (Q.comp (fixedSpace x).subtype)),
      L.Normal → CFSG.IsQuasisimple ↥L →
        ∃ (X : Type) (_ : Group X) (_ : Finite X), P X ∧
          ∃ f : X →* ↥L, Function.Surjective f ∧ f.ker ≤ Subgroup.center X)
    (F : Subgroup (V ≃ₗ[K] V))
    (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    OrthCompData P ↥F := by
  have hQW := hx.polarBilin_fixed_nondegenerate
  letI : Fintype K := Fintype.ofFinite K
  let e := supportedFixedDerivedEquiv hx
  let A : Subgroup ↥(supportedFixedDerived Q x) := F.subgroupOf (supportedFixedDerived Q x)
  let L : Subgroup ↥(orthDerived (Q.comp (fixedSpace x).subtype)) := A.map e.toMonoidHom
  have hLn : L.Normal := hFn.map e.toMonoidHom e.surjective
  let eAF : ↥A ≃* ↥F := Subgroup.subgroupOfEquivOfLe hFle
  let eAL : ↥A ≃* ↥L := A.equivMapOfInjective e.toMonoidHom e.injective
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (eAF.symm.trans eAL) hFq
  obtain ⟨X, _, _, hP, f, hf, hfk⟩ := hprov L hLn hLq
  have hL : OrthCompData P ↥L := ⟨X, inferInstance, inferInstance, f, hP, hf, hfk⟩
  exact hL.of_mulEquiv (eAL.symm.trans eAF)

private theorem orthCompData_fixedFactor (hOm : OmegaFactorFacts)
    {p : ℕ} {K : Type} [Field K]
    [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (F : Subgroup (V ≃ₗ[K] V))
    (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    OrthCompData (LieFactorProperty (ringChar K)) ↥F :=
  orthCompData_fixedFactor_of (P := LieFactorProperty (ringChar K))
    (hprov := fun L hLn hLq => by
      have hQW := hx.polarBilin_fixed_nondegenerate
      letI : Fintype K := Fintype.ofFinite K
      obtain ⟨X, _, _, hX, f, hf, hfk⟩ :=
        hOm (K := K) (V := fixedSpace x) (Q := Q.comp (fixedSpace x).subtype) hQW L hLn hLq
      refine ⟨X, inferInstance, inferInstance, ⟨hX, fun _ _ hOm6 hℓ3 => ?_⟩, f, hf, hfk⟩
      refine ⟨fun e6 => ?_⟩
      obtain ⟨e'⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f hf hfk
      obtain ⟨h3, -⟩ := hOm6 (K := K) (V := fixedSpace x)
        (Q := Q.comp (fixedSpace x).subtype) hQW L hLn hLq ⟨e'.symm.trans e6⟩
      exact hℓ3 h3)
    hx F hFq hFle hFn

private theorem orthCompData_fixedFactor_card (hOmF : OmegaFactorField)
    {p : ℕ} {K : Type} [Field K]
    [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (F : Subgroup (V ≃ₗ[K] V))
    (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    OrthCompData (OrthFactorDataCard (ringChar K) (Nat.card K)) ↥F :=
  orthCompData_fixedFactor_of (P := OrthFactorDataCard (ringChar K) (Nat.card K))
    (hprov := fun L hLn hLq => by
      have hQW := hx.polarBilin_fixed_nondegenerate
      letI : Fintype K := Fintype.ofFinite K
      obtain ⟨X, _, _, hX, hfac, f, hf, hfk⟩ :=
        hOmF (K := K) (V := fixedSpace x) (Q := Q.comp (fixedSpace x).subtype) hQW L hLn hLq
      refine ⟨X, inferInstance, inferInstance, ⟨hfac, ⟨hX, fun _ _ hOm6 hℓ3 => ?_⟩⟩, f, hf, hfk⟩
      refine ⟨fun e6 => ?_⟩
      obtain ⟨e'⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f hf hfk
      obtain ⟨h3, -⟩ := hOm6 (K := K) (V := fixedSpace x)
        (Q := Q.comp (fixedSpace x).subtype) hQW L hLn hLq ⟨e'.symm.trans e6⟩
      exact hℓ3 h3)
    hx F hFq hFle hFn

private theorem exists_fixedFactors {p : ℕ} {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) :
    ∃ (n : ℕ) (F : Fin n → Subgroup (V ≃ₗ[K] V)),
      (∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q x ∧
        ((F i).subgroupOf (supportedFixedDerived Q x)).Normal) ∧
      (FixedLayerListed Q x → ⨆ i, F i = supportedFixedDerived Q x) ∧
      (¬ FixedLayerListed Q x → n = 0) := by
  by_cases hlist : FixedLayerListed Q x
  · have hQW := hx.polarBilin_fixed_nondegenerate
    by_cases hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
        ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0
    · refine ⟨1, fun _ => supportedFixedDerived Q x, fun _ =>
        ⟨hx.isQuasisimple_supportedFixedDerived hT, le_rfl, ?_⟩, fun _ => iSup_const,
        fun h => absurd hlist h⟩
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.normal_top
    · obtain ⟨-, h2⟩ := orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype) hQW
        hlist.1
      obtain ⟨n, F, -, -, hsup, hF, -, -⟩ := hx.exists_supported_factors (h2 hlist.2)
      exact ⟨n, F, hF, fun _ => hsup, fun h => absurd hlist h⟩
  · exact ⟨0, fun i => i.elim0, fun i => i.elim0, fun h => absurd h hlist, fun _ => rfl⟩

private theorem oddOrderIsometry_of_pow_eq_one {p : ℕ} (hp : p.Prime) {K : Type} [Field K]
    [Finite K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hpℓ : p ≠ ringChar K) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (x : ↥(orthDerived Q)) (hxp : x ^ p = 1) : OddOrderIsometry Q p (x : V ≃ₗ[K] V) := by
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec K p).mp h0
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact hℓ.one_lt.ne' h2
    · exact hpℓ h2.symm
  exact ⟨orthDerived_le_orthogonalGroup x.2, congrArg Subtype.val hxp, hpK, fun v hv =>
    hQ.1 v fun w => by simpa using hv w⟩

private theorem orthCompData_component_of {p : ℕ} {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hp : p.Prime) (hp2 : p ≠ 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : p ≠ ringChar K)
    {P : (X : Type) → [Group X] → Prop}
    (hperfP : ∀ (X : Type) [Group X], P X → commutator X = ⊤)
    (hpaired : ∀ {x : V ≃ₗ[K] V}, OddOrderIsometry Q p x → ∀ (h : K[X]), Irreducible h →
      h ∈ primaryFactors x.toLinearMap → h ≠ X - 1 → h ≠ reciprocalPolynomial h →
      CFSG.IsQuasisimple ↥(specialBlock Q x h) → OrthCompData P ↥(specialBlock Q x h))
    (hself : ∀ {x : V ≃ₗ[K] V}, OddOrderIsometry Q p x → ∀ (h : K[X]), Irreducible h →
      h ∈ primaryFactors x.toLinearMap → h ≠ X - 1 → h = reciprocalPolynomial h →
      CFSG.IsQuasisimple ↥(specialBlock Q x h) → OrthCompData P ↥(specialBlock Q x h))
    (hfixed : ∀ {x : V ≃ₗ[K] V}, OddOrderIsometry Q p x → ∀ (F : Subgroup (V ≃ₗ[K] V)),
      CFSG.IsQuasisimple ↥F → F ≤ supportedFixedDerived Q x →
      (F.subgroupOf (supportedFixedDerived Q x)).Normal → OrthCompData P ↥F)
    (a : ProjOrthDerived Q) (ha : a ^ p = 1) (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) :
    OrthCompData P ↥J := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  obtain ⟨x, hxa, hx, hcent⟩ : ∃ x : ↥(orthDerived Q), ρ x = a ∧
      OddOrderIsometry Q p (x : V ≃ₗ[K] V) ∧
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))).map ρ := by
    by_cases h1 : a = 1
    · refine ⟨1, by rw [h1, map_one], oddOrderIsometry_of_pow_eq_one hp hpℓ hQ 1 (one_pow p),
        ?_⟩
      have e1 : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) = ⊤ := by
        ext g
        simp [h1, Subgroup.mem_centralizer_iff]
      have e2 : Subgroup.centralizer ({(1 : ↥(orthDerived Q))} : Set ↥(orthDerived Q)) = ⊤ := by
        ext g
        simp [Subgroup.mem_centralizer_iff]
      rw [e1, e2, Subgroup.map_top, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    · obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
        CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
      obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift p hp hp2 a (orderOf_eq_prime ha h1)
      exact ⟨x, hxa, oddOrderIsometry_of_orthDerived hp hpℓ hQ x hxp, hcent⟩
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
  have hNeq : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) = N := by
    rw [hcent]
    exact CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x
  rw [hNeq] at hJ
  obtain ⟨n, F, hFq, hFsup, hFn0⟩ := exists_fixedFactors hx
  have hFΩ : ∀ i, F i ≤ orthDerived Q := fun i =>
    (hFq i).2.1.trans hx.supportedFixedDerived_le_orthDerived
  set C : Fin n → Subgroup (ProjOrthDerived Q) := fun i => ((F i).subgroupOf (orthDerived Q)).map ρ
    with hC
  have hCsup : (⨆ i, C i) = fixedLayerImage Q xe := by
    by_cases hlist : FixedLayerListed Q xe
    · rw [fixedLayerImage_of_listed hlist]
      unfold fixedComponentImage
      rw [← hFsup hlist, subgroupOf_iSup_of_le F _ hFΩ, Subgroup.map_iSup]
    · have hn := hFn0 hlist
      subst hn
      simp [fixedLayerImage, hlist]
  have hCle : ∀ i, C i ≤ fixedComponentImage Q xe := fun i =>
    Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
      ((hFq i).2.1 (Subgroup.mem_subgroupOf.mp hg))
  have hCcomp : ∀ i, CFSG.Open.IsComponentOf (C i) N := by
    intro i
    have hconj := map_conj_mem ρ (F := (F i).subgroupOf (orthDerived Q))
      (F' := (supportedFixedDerived Q xe).subgroupOf (orthDerived Q)) (fun h k hh hk => by
        have := (Subgroup.normal_subgroupOf_iff (hFq i).2.1).mp (hFq i).2.2 (h : V ≃ₗ[K] V)
          (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this)
    refine isComponentOf_of_normal_normal (hCle i) fixedComponentImage_le_centralizerImage ?_
      hx.normal_fixedComponentImage (isQuasisimple_map_projective (hFΩ i) (hFq i).1)
    rw [Subgroup.normal_subgroupOf_iff (hCle i)]
    intro h k hh hk
    exact hconj _ _ hh hk
  let ι₁ := {r : ↥Rep // r.1 ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q xe r.1)}
  have hspecΩ : ∀ r : ι₁, specialBlock Q xe r.1.1 ≤ orthDerived Q := fun r =>
    specialBlock_le_orthDerived_of_perfect r.2.2.1
      ((specialBlock_le_isometryCentralizer r.1.1).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let S : ι₁ → Subgroup (ProjOrthDerived Q) := fun r => componentImage Q xe r.1.1
  have hScomp : ∀ r, CFSG.Open.IsComponentOf (S r) N := fun r =>
    isComponentOf_of_normal_normal componentImage_le_centralizerImage le_rfl normal_componentImage
      (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (isQuasisimple_map_projective (hspecΩ r) r.2.2)
  set EN : Subgroup (ProjOrthDerived Q) := (⨆ r, S r) ⊔ fixedLayerImage Q xe with hEN
  have hSN : ∀ r, S r ≤ N := fun r => componentImage_le_centralizerImage
  have hENN : EN ≤ N :=
    sup_le (iSup_le hSN) fixedLayerImage_le_centralizerImage
  have hENnormal : (EN.subgroupOf N).Normal :=
    normal_subgroupOf_sup (iSup_le hSN) fixedLayerImage_le_centralizerImage
      (normal_subgroupOf_iSup S hSN fun r => normal_componentImage) hx.normal_fixedLayerImage
  have hENn : ∀ c ∈ N, ∀ e ∈ EN, c * e * c⁻¹ ∈ EN := fun c hc e he =>
    (Subgroup.normal_subgroupOf_iff hENN).mp hENnormal e c he hc
  have hperf : ∀ P : Subgroup (ProjOrthDerived Q), P ≤ N → commutator ↥P = ⊤ → P ≤ EN := by
    intro P hPN hP
    obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ := exists_solvable_comm_le hQ hp hp2 x hx hRep EN
      (fun h hh hne hq => le_sup_of_le_left
        (le_iSup S (⟨⟨h, hh⟩, hne, hq⟩ : ι₁)))
      (fun hlist => by
        rw [← fixedLayerImage_of_listed hlist]
        exact le_sup_right)
    haveI := hS₀sol
    exact perfect_le_of_le_sup_solvable hENN hS₀N hENn hcomm hPN (Subgroup.isPerfect_iff.1 ⟨hP⟩)
  let Fm : ι₁ ⊕ Fin n → Subgroup (ProjOrthDerived Q) := Sum.elim S C
  have hFm : ∀ i, CFSG.Open.IsComponentOf (Fm i) N := by
    rintro (r | i)
    · exact hScomp r
    · exact hCcomp i
  have hiSup : (⨆ i, Fm i) = EN := by
    rw [iSup_sum]
    simp only [Fm, Sum.elim_inl, Sum.elim_inr]
    rw [hCsup]
  obtain ⟨i, rfl⟩ := component_mem_named_factors Fm hFm
    (fun P hPN hP => hiSup ▸ hperf P hPN hP) hJ
  rcases i with ⟨⟨h, hh⟩, hne, hq⟩ | i
  · have hh' : h ∈ primaryFactors xe.toLinearMap := hRep.1 hh
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh'⟩
    refine OrthCompData.map_projective (P := P) hperfP (hspecΩ ⟨⟨h, hh⟩, hne, hq⟩) ?_
    by_cases hself' : h = reciprocalPolynomial h
    · exact hself hx h (Fact.out) hh' hne hself' hq
    · exact hpaired hx h (Fact.out) hh' hne hself' hq
  · exact OrthCompData.map_projective (P := P) hperfP (hFΩ i)
      (hfixed hx (F i) (hFq i).1 (hFq i).2.1 (hFq i).2.2)

private theorem orthCompData_specialBlock_paired_old (hSL : SLFactorFacts) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (h : K[X]) (hirr : Irreducible h)
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    OrthCompData (LieFactorProperty (ringChar K)) ↥(specialBlock Q x h) :=
  (orthCompData_specialBlock_paired hSL hp hp2 hx h hirr hh hne1 hne hq).mono
    (fun X _ h => ⟨h.2.1, h.2.2⟩)

private theorem orthCompData_specialBlock_selfDual_old (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (h : K[X])
    (hirr : Irreducible h) (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    OrthCompData (LieFactorProperty (ringChar K)) ↥(specialBlock Q x h) :=
  (orthCompData_specialBlock_selfDual hSL hSU hp hp2 hx h hirr hh hne1 hself hq).mono
    (fun X _ h => ⟨h.2.1, h.2.2⟩)

private theorem orthCompData_component (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    (hOm : OmegaFactorFacts) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : p ≠ ringChar K)
    (a : ProjOrthDerived Q) (ha : a ^ p = 1) (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) : OrthCompData (LieFactorProperty (ringChar K)) (↥J) :=
  
  orthCompData_component_of (P := LieFactorProperty (ringChar K)) (hp := hp) (hp2 := hp2)
    (hQ := hQ) (hT := hT) (hpℓ := hpℓ) (hperfP := fun X _ h => h.1.perfect)
    (hpaired := fun hx h hirr hh hne1 hne hq =>
      orthCompData_specialBlock_paired_old hSL hp hp2 hx h hirr hh hne1 hne hq)
    (hself := fun hx h hirr hh hne1 hself hq =>
      orthCompData_specialBlock_selfDual_old hSL hSU hp hp2 hx h hirr hh hne1 hself hq)
    (hfixed := fun hx F hFq hFle hFn => orthCompData_fixedFactor hOm hx F hFq hFle hFn)
    (a := a) (ha := ha) (J := J) (hJ := hJ)

private theorem orthCompData_component_card (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    (hOmF : OmegaFactorField) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : p ≠ ringChar K)
    (a : ProjOrthDerived Q) (ha : a ^ p = 1) (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) :
    OrthCompData (OrthFactorDataCard (ringChar K) (Nat.card K)) ↥J :=
  orthCompData_component_of (P := OrthFactorDataCard (ringChar K) (Nat.card K)) (hp := hp)
    (hp2 := hp2) (hQ := hQ) (hT := hT) (hpℓ := hpℓ)
    (hperfP := fun X _ h => h.2.1.perfect)
    (hpaired := fun hx h hirr hh hne1 hne hq =>
      orthCompData_specialBlock_paired hSL hp hp2 hx h hirr hh hne1 hne hq)
    (hself := fun hx h hirr hh hne1 hself hq =>
      orthCompData_specialBlock_selfDual hSL hSU hp hp2 hx h hirr hh hne1 hself hq)
    (hfixed := fun hx F hFq hFle hFn => orthCompData_fixedFactor_card hOmF hx F hFq hFle hFn)
    (a := a) (ha := ha) (J := J) (hJ := hJ)

private theorem fixSubgroup_conj_eq_centralizer {X : Type*} [Group X] (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem congr_conj {S G : Type*} [Group S] [Group G] (e : S ≃* G) (a : S) :
    MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
  ext y
  simp [MulAut.conj_apply]

private theorem exists_projOrth_model_card {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (Q : QuadraticForm K V),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      Nat.card K = ℓ ^ f ∧ ringChar K = ℓ ∧
      Nonempty (G ≃* ProjOrthDerived Q) := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h3 : 3 ≤ n ∧ ℓ ≠ 2 := hadm.2.2
    have hring : ringChar K = ℓ :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, CFSG.ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two
        (by rw [hring]; exact hadm.1), hring]
      exact h3.2
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := K) (n := n) h2 h3.1
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard,
      hring, ⟨e.trans (projOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadOdd n K))⟩⟩
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    have hring : ringChar K = ℓ :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n)
      (by omega)
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard,
      hring, ⟨e.trans (projOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadPlus (n := n) (K := K)))⟩⟩
  · obtain ⟨hadm, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    have hring : ringChar K = ℓ :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := n) h4 hirr
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard,
      hring, ⟨e.trans (projOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c))⟩⟩

private theorem exists_projOrth_model {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (Q : QuadraticForm K V),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧ ringChar K = ℓ ∧
      Nonempty (G ≃* ProjOrthDerived Q) := by
  obtain ⟨K, hfield, hfinite, V, hAdd, hMod, hFin, Q, hQ, hT, hcard, hring, he⟩ :=
    exists_projOrth_model_card ht hG
  exact ⟨K, hfield, hfinite, V, hAdd, hMod, hFin, Q, hQ, hT, hring, he⟩

theorem exists_lieFactor_of_component_conj_omega_card (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    (hOmF : OmegaFactorField)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) (hpℓ : p ≠ ℓ) (a : G) (ha : a ^ p = 1)
    (J : Subgroup G) (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a))) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X),
      LieFactorData ℓ X ∧ OrthFactorOver ℓ (ℓ ^ f) X ∧
      (SLAltSixFacts → SUAltSixFacts → OmegaAltSixFacts → ℓ ≠ 3 →
        ¬ Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6))) ∧
      ∃ g : X →* ↥J, Function.Surjective g ∧ g.ker ≤ Subgroup.center X := by
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hcardK, hring, ⟨e⟩⟩ := exists_projOrth_model_card ht hG
  subst hring
  have hfix : fixSubgroup (MulAut.congr e (MulAut.conj a)) =
      (fixSubgroup (MulAut.conj a)).map (e : G →* ProjOrthDerived Q) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (MulAut.conj a (e.symm x)) = x ↔ MulAut.conj a (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hJ' : CFSG.Open.IsComponentOf (J.map (e : G →* ProjOrthDerived Q))
      (Subgroup.centralizer ({e a} : Set (ProjOrthDerived Q))) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ
    rw [← hfix, congr_conj, fixSubgroup_conj_eq_centralizer] at h1
    exact h1
  obtain ⟨X, _, _, fX, ⟨hfac, hX, hA⟩, hf, hfk⟩ :=
    orthCompData_component_card hSL hSU hOmF hp hp2 hQ hT hpℓ
      (e a) (by rw [← map_pow, ha, map_one]) _ hJ'
  let g : ↥(J.map (e : G →* ProjOrthDerived Q)) ≃* ↥J :=
    (J.equivMapOfInjective (e : G →* ProjOrthDerived Q) e.injective).symm
  have hfac' : OrthFactorOver (ringChar K) ((ringChar K) ^ f) X := by
    rw [← hcardK]
    exact hfac
  refine ⟨X, inferInstance, inferInstance, hX, hfac',
    fun hA6 hSU6 hOm6 hℓ3 ⟨e6⟩ => (hA hA6 hSU6 hOm6 hℓ3).false e6,
    g.toMonoidHom.comp fX, g.surjective.comp hf, ?_⟩
  intro x hx
  apply hfk
  rw [MonoidHom.mem_ker] at hx ⊢
  apply g.injective
  rw [map_one]
  exact hx

theorem exists_lieFactor_of_component_conj_omega (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    (hOm : OmegaFactorFacts) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) (hpℓ : p ≠ ℓ) (a : G) (ha : a ^ p = 1)
    (J : Subgroup G) (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a))) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData ℓ X ∧
      (SLAltSixFacts → SUAltSixFacts → OmegaAltSixFacts → ℓ ≠ 3 →
        ¬ Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6))) ∧
      ∃ g : X →* ↥J, Function.Surjective g ∧ g.ker ≤ Subgroup.center X := by
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hring, ⟨e⟩⟩ := exists_projOrth_model ht hG
  subst hring
  have hfix : fixSubgroup (MulAut.congr e (MulAut.conj a)) =
      (fixSubgroup (MulAut.conj a)).map (e : G →* ProjOrthDerived Q) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (MulAut.conj a (e.symm x)) = x ↔ MulAut.conj a (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hJ' : CFSG.Open.IsComponentOf (J.map (e : G →* ProjOrthDerived Q))
      (Subgroup.centralizer ({e a} : Set (ProjOrthDerived Q))) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ
    rw [← hfix, congr_conj, fixSubgroup_conj_eq_centralizer] at h1
    exact h1
  obtain ⟨X, _, _, f, ⟨hX, hA⟩, hf, hfk⟩ := orthCompData_component hSL hSU hOm hp hp2 hQ hT
    hpℓ (e a) (by rw [← map_pow, ha, map_one]) _ hJ'
  let g : ↥(J.map (e : G →* ProjOrthDerived Q)) ≃* ↥J :=
    (J.equivMapOfInjective (e : G →* ProjOrthDerived Q) e.injective).symm
  refine ⟨X, inferInstance, inferInstance, hX, fun hA6 hSU6 hOm6 hℓ3 ⟨e6⟩ =>
    (hA hA6 hSU6 hOm6 hℓ3).false e6, (g : _ →* ↥J).comp f, g.surjective.comp hf, ?_⟩
  intro x hx
  apply hfk
  rw [MonoidHom.mem_ker] at hx ⊢
  apply g.injective
  rw [map_one]
  exact hx

theorem lieCompExport_conj_omega (hSL : SLFactorFacts) (hA6 : SLAltSixFacts)
    (hSU : SUFactorFacts) (hSU6 : SUAltSixFacts) (hOm : OmegaFactorFacts)
    (hOm6 : OmegaAltSixFacts) {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) (hℓ3 : ℓ ≠ 3) (a : G) (ha : a ^ 3 = 1) :
    LieCompExport ℓ (MulAut.conj a) := by
  have hpℓ : 3 ≠ ℓ := fun h => hℓ3 h.symm
  refine ⟨LieSemisimple.perfectInLayer_conj_omega ht hG Nat.prime_three (by decide) hpℓ a ha,
    fun J hJ => ?_, fun ⟨J, hJ, ⟨e6⟩⟩ => ?_⟩
  · obtain ⟨X, _, _, hX, -, g, hg, hker⟩ := exists_lieFactor_of_component_conj_omega hSL hSU hOm
      Nat.prime_three (by decide) ht hG hpℓ a ha J hJ
    exact ⟨X, inferInstance, inferInstance, hX, g, hg, hker⟩
  · exfalso
    obtain ⟨X, _, _, hX, hnA6, g, hg, hker⟩ := exists_lieFactor_of_component_conj_omega hSL hSU
      hOm Nat.prime_three (by decide) ht hG hpℓ a ha J hJ
    obtain ⟨e'⟩ := nonempty_centralQuotient_mulEquiv hX.perfect g hg hker
    exact hnA6 hA6 hSU6 hOm6 hℓ3 ⟨e'.trans e6⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
