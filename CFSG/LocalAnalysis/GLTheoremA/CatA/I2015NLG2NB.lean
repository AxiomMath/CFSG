module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLG2N
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLChev
import CFSG.SignalizerFunctorTheorem.NonLocalExc.Chevalley
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremA.FQ
  CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge
  CFSG.SignalizerFunctorTheorem.NonLocalExc

section Generic

theorem nlWitness_of_no_normalized_two {R P : Type} [Group R] [Group P] (e : R ≃* P)
    {f : MulAut R} {D : Subgroup P} (hs : IsSimpleGroup ↥D) (hna : ∃ x y : ↥D, x * y ≠ y * x)
    (hN : ∀ U : Subgroup P, U ≠ ⊥ → IsPGroup 2 ↥U → ¬ D ≤ Subgroup.normalizer (U : Set P))
    (hfix : D.map e.symm.toMonoidHom ≤ fixSub f) : NLWitness f := by
  have eD := D.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  refine ⟨D.map e.symm.toMonoidHom, hfix, (MulEquiv.isSimpleGroup_congr eD).1 hs, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eD x, eD y, fun h => hxy (eD.injective (by rw [map_mul, map_mul]; exact h))⟩
  · intro U hU hU2 hN'
    have hU' : U.map e.toMonoidHom ≠ ⊥ := fun hbot =>
      hU ((Subgroup.map_eq_bot_iff_of_injective U e.injective).1 hbot)
    refine hN _ hU' (hU2.map e.toMonoidHom) ?_
    have h1 := map_le_normalizer_map e hN'
    have h2 : (D.map e.symm.toMonoidHom).map e.toMonoidHom = D := by
      ext x
      simp only [Subgroup.mem_map]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
    rwa [h2] at h1

end Generic

section Model

set_option linter.unusedSectionVars false


theorem chevWitness_aux_of_subgroup {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (D : Subgroup ↥(adjointGroup τ K)) (hsD : IsSimpleGroup ↥D) (hna : ∃ x y : ↥D, x * y ≠ y * x)
    (hN : ∀ U : Subgroup ↥(adjointGroup τ K), U ≠ ⊥ → IsPGroup 2 ↥U →
      ¬ D ≤ Subgroup.normalizer (U : Set ↥(adjointGroup τ K)))
    (hDfix : ∀ x ∈ D, Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) = x)
    (S : (Fin τ.rank → ℤ) → Prop) (hS : S = IsRoot τ) (H : Subgroup (MarkChev.GLS S K))
    (hH : H = MarkChev.chevH τ.cartan S K false) {f : MulAut (↥H ⧸ Subgroup.center ↥H)}
    (hf : ∀ x : ↥H,
      MarkChev.entrywise S K σ (map_zero σ) ((x : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
        ((x : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) →
      f (QuotientGroup.mk x) = QuotientGroup.mk x) : NLWitness f := by
  subst hS
  have hH' : H = adjointGroup τ K := hH.trans (chevH_false_eq_adjointGroup K τ)
  subst hH'
  haveI : Finite (ModGL τ K) := finite_modGL
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let e : (↥(adjointGroup τ K) ⧸ Subgroup.center ↥(adjointGroup τ K)) ≃* ↥(adjointGroup τ K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine nlWitness_of_no_normalized_two e hsD hna hN ?_
  rintro _ ⟨x, hx, rfl⟩
  have hfix : Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) = x := hDfix x hx
  show f (e.symm x) = e.symm x
  have hex : e.symm x = QuotientGroup.mk x := rfl
  rw [hex]
  exact hf x (congrArg Units.val hfix)

theorem chevWitness_of_fixed_of_subgroup {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (D : Subgroup ↥(adjointGroup τ K)) (hsD : IsSimpleGroup ↥D) (hna : ∃ x y : ↥D, x * y ≠ y * x)
    (hN : ∀ U : Subgroup ↥(adjointGroup τ K), U ≠ ⊥ → IsPGroup 2 ↥U →
      ¬ D ≤ Subgroup.normalizer (U : Set ↥(adjointGroup τ K)))
    (hDfix : ∀ x ∈ D, Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) = x)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))}
    (hf : ∀ x : ↥(LargeEvenChevH τ.cartan K false), chevRho τ K σ x = x →
      f (QuotientGroup.mk x) = QuotientGroup.mk x) : NLWitness f := by
  refine chevWitness_aux_of_subgroup σ D hsD hna hN hDfix (LargeEvenIsRoot τ.cartan)
    (largeEvenIsRoot_eq_isRoot τ) (LargeEvenChevH τ.cartan K false)
    (largeEvenChevH_eq τ.cartan K false) fun x hx => hf x ?_
  apply Subtype.ext
  apply Units.ext
  show ((chevAct τ.cartan K σ (x : LargeEvenChevGL τ.cartan K) : LargeEvenChevGL τ.cartan K) :
    Module.End K (LargeEvenChevModule τ.cartan K)) = _
  rw [chevAct_val]
  exact hx

end Model

section Derived

set_option linter.unusedSectionVars false


theorem g2N_derived_subfield {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hk : Nat.card (fixSubfield σ) = 2) :
    ∃ D : Subgroup ↥(adjointGroup .G2 K), IsSimpleGroup ↥D ∧ Nat.card ↥D = 6048 ∧
      ∀ x ∈ D, Units.map (entrywiseHom σ.toRingHom) (x : ModGL .G2 K) = x := by
  classical
  set k := fixSubfield σ with hkdef
  set f := baseChangeGL (τ := .G2) k.subtype with hf
  have hfinj : Function.Injective f := baseChangeGL_injective _
  set D : Subgroup (ModGL .G2 k) := ⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ with hD
  set Jd : Subgroup (ModGL .G2 K) := D.map f with hJd
  have hJdeq : Jd = ⁅fixedFieldImage .G2 σ, fixedFieldImage .G2 σ⁆ := by
    rw [hJd, hD, Subgroup.map_commutator]
    rfl
  have hJdJ : Jd ≤ fixedFieldImage .G2 σ := by
    rw [hJdeq]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hJdX : Jd ≤ adjointGroup .G2 K := hJdJ.trans (fixedFieldImage_le_adjointGroup σ)
  have hLie := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hLie
  have hDsimple : IsSimpleGroup ↥D := by
    rcases hLie with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hM).2
    all_goals exact absurd h0 (by norm_num)
  let e2 : ↥D ≃* ↥Jd := D.equivMapOfInjective f hfinj
  let e3 : ↥(Jd.subgroupOf (adjointGroup .G2 K)) ≃* ↥D :=
    (Subgroup.subgroupOfEquivOfLe hJdX).trans e2.symm
  refine ⟨Jd.subgroupOf (adjointGroup .G2 K), e3.isSimpleGroup, ?_, fun x hx => ?_⟩
  · rw [Nat.card_congr e3.toEquiv, Nat.card_congr e1.toEquiv,
      CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      (CFSG.GH74.KGroups.U33.QP_valid).2]
  · have hxJ : (x : ModGL .G2 K) ∈ fixedFieldImage .G2 σ := hJdJ hx
    exact (mem_entrywiseFixedGroup.1 (fixedFieldImage_le hxJ)).2

theorem g2N_witness_of_fixed {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ p) (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 2)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH Tag.G2.cartan K false))}
    (hf : ∀ x : ↥(LargeEvenChevH Tag.G2.cartan K false), chevRho Tag.G2 K σ x = x →
      f (QuotientGroup.mk x) = QuotientGroup.mk x) : NLWitness f := by
  obtain ⟨D, hsD, hcard, hfix⟩ := g2N_derived_subfield σ hk
  haveI : Finite (ModGL Tag.G2 K) := finite_modGL
  have hna : ∃ x y : ↥D, x * y ≠ y * x := by
    refine FR.Res.nonab_of_simple hsD ?_
    rw [hcard]
    norm_num
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  obtain ⟨-, h1, h2⟩ := g2N_two_pow_arith hp hp2
  rw [← hK] at h1 h2
  refine chevWitness_of_fixed_of_subgroup σ D hsD hna (fun U hU hU2 hle => ?_) hfix hf
  exact g2N_no_normalized_two_subgroup h1 h2 D (by rw [hcard]; norm_num) U hU hU2 hle

end Derived

section Family

set_option linter.unusedSectionVars false


theorem i2015NLResG2_holds : I2015NLResG2 := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_
    (fun p _ h => by rw [ht] at h; exact absurd h.1 (by decide))
  intro p hp hp2 _ _ hC
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht hC
  subst ht
  obtain ⟨-, -, hn2⟩ := hlab
  unfold regN at hC
  dsimp only at hC hn2
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  refine ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf hord _ _ => ?_⟩
  obtain ⟨σ₀, -, -, hcard, hfix⟩ := chevSigmaZero (τ := .G2) (Or.inl rfl) (by omega) hK hp hf hord
  subst hC
  have hk : Nat.card (fixSubfield σ₀) = 2 := by
    rw [hcard, Nat.div_self hp.pos, pow_one]
  exact g2N_witness_of_fixed hp hp2 hK σ₀ hk hfix

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
