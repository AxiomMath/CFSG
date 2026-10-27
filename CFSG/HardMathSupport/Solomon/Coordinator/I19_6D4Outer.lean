module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6Red
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthD4Family

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open TensorProduct Matrix Module CFSG.GroupTheory.SteinbergBK CFSG.Blueprint.EvenSource
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.RankThree.Classical.SteinbergBY
  CFSG.RankThree.PartOne.KCOrthogonalDescent
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin CFSG.RankThree.PartOne
open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.RankThree.Classical2 CFSG.RankThree.PartTwo.Census
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.Coordinator
open scoped Pointwise

set_option linter.unusedSectionVars false

theorem i196_three_dvd_ordD_four_of_dvd {q : ℕ} (hq : 3 ∣ q) : 3 ∣ CFSG.Open.ordD 4 q := by
  unfold CFSG.Open.ordD
  set P := ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1) with hP
  set g := Nat.gcd 4 (q ^ 4 - 1) with hg
  have hN3 : 3 ∣ q ^ (4 * (4 - 1)) * (q ^ 4 - 1) * P :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow hq (by norm_num)) _) _
  have hgN : g ∣ q ^ (4 * (4 - 1)) * (q ^ 4 - 1) * P :=
    (Nat.gcd_dvd_right 4 (q ^ 4 - 1)).trans
      ((dvd_mul_left (q ^ 4 - 1) (q ^ (4 * (4 - 1)))).trans (dvd_mul_right _ P))
  have hg3 : Nat.Coprime 3 g :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 4 _) (by norm_num)
  have hmul := Nat.div_mul_cancel hgN
  have : 3 ∣ q ^ (4 * (4 - 1)) * (q ^ 4 - 1) * P / g * g := by rw [hmul]; exact hN3
  exact hg3.dvd_of_dvd_mul_right this

theorem i196_d4_localDeltaIn_eq_bot_of_field (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (ha : a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K))
    (haD : a ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range) (hap : orderOf a = 3)
    {D H : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (haDm : a ∈ D) (hH : innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨hℓ, hf, hn4⟩ := h.1
  obtain ⟨hdvd, hdesc⟩ := d4_field_descent3 G h hp hp2 K hK e a ha haD hap
  obtain ⟨g, hg⟩ := ha
  obtain ⟨hord, hcard, U, c, Q₀, hUκ, hUr, hFFD, hdisp⟩ := hdesc g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, hS₀, hmodel₀, S, ν', hQ', hS, hSU, Θ, hΘ, g', hg'l, hg'r, hg'⟩ := hdisp
  set σ := g.val.right with hσ
  set k := semilinearFixedSubfield σ with hk
  have hσk : ∀ x, x ∈ k ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have Sset := subfieldSetup_plus k hσk hp hp2 hord (n := 4) (by norm_num)
  have hmodelK : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 K))
      .POmegaPlus 4 ℓ f :=
    ⟨⟨hℓ, hf, hn4⟩, K, inferInstance, inferInstance, hK, ⟨(statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm⟩⟩
  have hE : ∀ β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      (∀ t ∈ subfieldDerivedImage k Sset.hext, β t = t) →
      β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := fun β hβ =>
    mem_matrixProjectiveImage_plus_four k hK hmodelK (statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm Sset.hext Sset.hnd₀ Sset.hT₀ β hβ
  have hconc := subfield_conclusion orthogonal_high_Witt_subfield_pointwise_centralizer Sset hE
  obtain ⟨⟨-, hsimp, hnonab⟩, hordy, hfixN, hJN, hJnorm, -, -, -, hfixJ, -⟩ := hconc
  have hd : 0 < 2 * 4 := by norm_num
  have hinj := CFSG.RankThree.PartOne.K133C.conj_injective_of_center_bot
    (center_matrix_eq_bot hd Sset.hnd Sset.hT)
  have hg'eq : g' = fieldPair (coordinateQuadPlus 4 K) σ Sset.hQσ :=
    Subtype.ext (SemidirectProduct.ext hg'l (hg'r.trans hUr))
  have hconj : ∀ x, a x = Θ.symm (fieldAutT (coordinateQuadPlus 4 K) σ Sset.hQσ (Θ x)) := by
    intro x
    have h1 := hg' x
    rw [hUκ, hg'eq] at h1
    apply Θ.injective
    rw [MulEquiv.apply_symm_apply]
    exact h1
  have ha1 : a ≠ 1 := fun h1 => haD (h1 ▸ (linearConjugationHom _).range.one_mem)
  have hTq : CFSG.IsQuasisimple (subfieldDerivedImage k Sset.hext) := by
    have := hsimp
    have hab : ∃ x y : subfieldDerivedImage k Sset.hext, x * y ≠ y * x := hnonab
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hab).1
  have hfp : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd hf hdvd) hp.pos
  have hmodelk : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 ↥k))
      .POmegaPlus 4 ℓ (f / 3) :=
    ⟨⟨hℓ, hfp, hn4⟩, ↥k, inferInstance, inferInstance, hcard, ⟨(statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (quadPlus 4 ↥k) (coe_quadPlus 4 ↥k)).symm⟩⟩
  have hTp : 3 ∣ Nat.card (subfieldDerivedImage k Sset.hext) := by
    rw [← Nat.card_congr (inclEquiv k Sset.hext hd).toEquiv, card_model_plus hmodelk]
    by_cases h3 : 3 ∣ ℓ ^ (f / 3)
    · exact i196_three_dvd_ordD_four_of_dvd h3
    · exact three_dvd_ordD_four h3
  refine localDeltaIn_eq_bot_of_conj_normal_quasisimple_fixSub hp hinj hH haDm ha1 Θ.symm
    (fieldAutT (coordinateQuadPlus 4 K) σ Sset.hQσ) ?_ (subfieldDerivedImage k Sset.hext)
    (fun t ht => (hfixN t).2 (hJN ht)) ?_ hTq hTp ?_
  · ext x
    exact hconj x
  · intro x hx t ht
    have hxN : x ∈ subfieldFixedGroup k (coordinateQuadPlus 4 k) (coordinateQuadPlus 4 K) :=
      (hfixN x).1 hx
    have := hJnorm.conj_mem ⟨t, hJN ht⟩ (Subgroup.mem_subgroupOf.2 ht) ⟨x, hxN⟩
    exact Subgroup.mem_subgroupOf.1 this
  · intro g₁ hg₁ hfix
    have hmem : g₁ ∈ fixingSubgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (subfieldDerivedImage k Sset.hext :
          Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :=
      (mem_fixingSubgroup_iff _).mpr fun t ht => by simpa using hfix t ht
    rw [hfixJ] at hmem
    have h1 : orderOf g₁ ∣ 3 := by rw [← hordy]; exact orderOf_dvd_of_mem_zpowers hmem
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hg₁.symm h1)


theorem i196_d4_outer_exists (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (D : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2)
    (hout : D ⊓ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) = ⊥) :
    ∃ a ∈ D, a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
      a ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range ∧ orderOf a = 3 := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 ℓ f h K hK e
  obtain ⟨-, -, ⟨hInnL, k, hrel⟩, horb, -, hEA, -⟩ := hgates
  have : Finite (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := inferInstance
  have : Finite (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := inferInstance
  have hidx : (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3 := by
    have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
        (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
          (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
      MulAction.index_stabilizer _ _
    rw [← hEA, hst]
    exact horb
  set E := matrixProjectiveImage (coordinateQuadPlus 4 K) with hE
  have h1 : E.relIndex D ≤ E.index := by
    have h := Subgroup.relIndex_le_of_le_right (H := E) (le_top : D ≤ ⊤)
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
    rwa [Subgroup.relIndex_top_right] at h
  have h2 := Subgroup.relIndex_mul_card E D
  rw [hcard, inf_comm] at h2
  have hge : 3 ≤ Nat.card (D ⊓ E : Subgroup _) := by
    by_contra hlt
    push Not at hlt
    have h3 : E.relIndex D * Nat.card (D ⊓ E : Subgroup _) ≤ 3 * 2 :=
      Nat.mul_le_mul (h1.trans hidx) (by omega)
    omega
  have hnt : Nontrivial (D ⊓ E : Subgroup _) := by
    have : Finite (D ⊓ E : Subgroup _) := inferInstance
    exact Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (1 : (D ⊓ E : Subgroup _))
  have ha1' : a ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  refine ⟨a, ha.1, ha.2, ?_, orderOf_eq_prime (hD.2 a ha.1) ha1'⟩
  intro hl
  apply ha1'
  have hainn : a ∈ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    mem_of_pow_mem_of_relIndex_two_pow hrel hl (j := 1) (by
      rw [pow_one, hD.2 a ha.1]
      exact Subgroup.one_mem _)
  have : a ∈ D ⊓ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := ⟨ha.1, hainn⟩
  rw [hout] at this
  exact Subgroup.mem_bot.1 this

theorem i196_map_innerAut_congr {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') :
    (innerAut X).map (MulAut.congr e).toMonoidHom = innerAut X' := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨e y, ?_⟩
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, ?_⟩
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem i196_isElemAbelian_map {M M' : Type*} [Group M] [Group M'] (ψ : M →* M') {p : ℕ}
    {D : Subgroup M} (hD : IsElemAbelian p D) : IsElemAbelian p (D.map ψ) :=
  CFSG.Open.IsElemAbelian.map hD _

theorem i196_outerNine_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : ∀ D' : Subgroup (MulAut X'), IsElemAbelian 3 D' → Nat.card D' = 3 ^ 2 →
      D' ⊓ innerAut X' = ⊥ → ∀ H' : Subgroup (MulAut X'), innerAut X' ≤ H' →
        localDeltaIn 3 H' D' = ⊥) :
    ∀ D : Subgroup (MulAut X), IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
      D ⊓ innerAut X = ⊥ → ∀ H : Subgroup (MulAut X), innerAut X ≤ H →
        localDeltaIn 3 H D = ⊥ := by
  intro D hD hcard hout H hH
  set ψ := (MulAut.congr e).toMonoidHom with hψ
  have hinj : Function.Injective ψ := (MulAut.congr e).injective
  have hinn : (innerAut X).map ψ = innerAut X' := i196_map_innerAut_congr e
  have hout' : D.map ψ ⊓ innerAut X' = ⊥ := by
    rw [← hinn, ← Subgroup.map_inf D (innerAut X) ψ hinj, hout, Subgroup.map_bot]
  have hH' : innerAut X' ≤ H.map ψ := hinn ▸ Subgroup.map_mono hH
  have h0 := h (D.map ψ) (i196_isElemAbelian_map ψ hD)
    (by rw [Subgroup.card_map_of_injective hinj, hcard]) hout' (H.map ψ) hH'
  have hle := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_localDeltaIn_le 3 ψ hinj H D
  rw [h0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hinj] at hle
  exact hle

theorem i196_d4_outer_balanced (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) :
    ∀ D : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
      IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
      D ⊓ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) = ⊥ →
      ∀ H : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
        innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤ H →
        localDeltaIn 3 H D = ⊥ := by
  intro D hD hcard hout H hH
  obtain ⟨a, haD, haE, haL, hao⟩ := i196_d4_outer_exists G h K hK e D hD hcard hout
  exact i196_d4_localDeltaIn_eq_bot_of_field G h K hK e a haE haL hao haD hH

theorem defCharThreeD4Outer_proved : DefCharThreeD4Outer := by
  intro S _ _ hS hnab idx hD4 hS0 hch D hD hcard hout H hH hDH
  obtain ⟨e0⟩ := hS0
  obtain ⟨q, hq⟩ := hD4
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcardF : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.D 4 q, hv⟩ 4 q (Or.inr (Or.inl rfl))
  let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv
  have hmodel : StatedClassicalModel (Cat ⟨.D 4 q, hv⟩) .POmegaPlus 4 q.p q.exponent :=
    statedClassicalModel_typeD 4 q hv (MulEquiv.refl _)
  exact i196_outerNine_of_mulEquiv (e0.trans (coordinatePlusWitnessEquiv F e₁))
    (i196_d4_outer_balanced (Cat ⟨.D 4 q, hv⟩) hmodel F hcardF e₁) D hD hcard hout H hH

end CFSG.HardMathSupport.Solomon.Coordinator
