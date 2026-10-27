module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.MI

@[expose] def I2015NLAtLabelWhen (C : LargeEvenLabel → ℕ → Prop) (lab : LargeEvenLabel) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (lab.tag = .triD4 ∧ p = 3) → C lab p →
    CAll lab (LargeEvenSimpleGuard fun R _ _ F =>
      ∀ f ∈ F, orderOf f = p → Finite R → NoLocalTwo p f)

@[expose] def I2015NLOnTagsWhen (T : LargeEvenLieTag → Prop) (C : LargeEvenLabel → ℕ → Prop) : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → T lab.tag → I2015NLAtLabelWhen C lab

@[expose] def I2015NLOnTags (T : LargeEvenLieTag → Prop) : Prop :=
  I2015NLOnTagsWhen T (fun _ _ => True)

theorem I2015NLOnTagsWhen.union {T : LargeEvenLieTag → Prop} {C : LargeEvenLabel → ℕ → Prop}
    (h₁ : I2015NLOnTagsWhen T C) (h₂ : I2015NLOnTagsWhen T fun lab p => ¬ C lab p) :
    I2015NLOnTags T := fun lab hlab ht p hp hp2 h3 _ => by
  by_cases hc : C lab p
  · exact h₁ lab hlab ht p hp hp2 h3 hc
  · exact h₂ lab hlab ht p hp hp2 h3 hc

theorem I2015NLOnTagsWhen.cover {T : LargeEvenLieTag → Prop} {C₁ C₂ C₃ : LargeEvenLabel → ℕ → Prop}
    (hcov : ∀ (lab : LargeEvenLabel) (p : ℕ), LargeEvenInLambda2 lab → T lab.tag →
      C₁ lab p ∨ C₂ lab p ∨ C₃ lab p)
    (h₁ : I2015NLOnTagsWhen T C₁) (h₂ : I2015NLOnTagsWhen T C₂) (h₃ : I2015NLOnTagsWhen T C₃) :
    I2015NLOnTags T := fun lab hlab ht p hp hp2 h3 _ => by
  rcases hcov lab p hlab ht with hc | hc | hc
  · exact h₁ lab hlab ht p hp hp2 h3 hc
  · exact h₂ lab hlab ht p hp hp2 h3 hc
  · exact h₃ lab hlab ht p hp hp2 h3 hc

@[expose] def regRank2N (lab : LargeEvenLabel) (p : ℕ) : Prop := lab.rank = 2 ∧ lab.n = p

@[expose] def regN (lab : LargeEvenLabel) (p : ℕ) : Prop := lab.n = p

@[expose] def regRank (r : ℕ) (lab : LargeEvenLabel) (_ : ℕ) : Prop := lab.rank = r

@[expose] def regRankGe (r : ℕ) (lab : LargeEvenLabel) (_ : ℕ) : Prop := r ≤ lab.rank

@[expose] def regThree (_ : LargeEvenLabel) (p : ℕ) : Prop := p = 3

@[expose] def I2015NLOnLinear : Prop := I2015NLOnTags fun t => t = .A

@[expose] def I2015NLOnUnitary : Prop := I2015NLOnTags fun t => t = .twA

@[expose] def I2015NLOnSymplectic : Prop :=
  I2015NLOnTagsWhen (fun t => t = .B ∨ t = .C) fun lab p => ¬ regRank2N lab p

@[expose] def I2015NLResSp4 : Prop :=
  I2015NLOnTagsWhen (fun t => t = .B ∨ t = .C) regRank2N

@[expose] def I2015NLOnD3 : Prop := I2015NLOnTagsWhen (fun t => t = .D) (regRank 3)

@[expose] def I2015NLOnOmegaPlus : Prop := I2015NLOnTagsWhen (fun t => t = .D) (regRankGe 4)

@[expose] def I2015NLOnTwD2 : Prop := I2015NLOnTagsWhen (fun t => t = .twD) (regRank 2)

@[expose] def I2015NLOnTwD3 : Prop := I2015NLOnTagsWhen (fun t => t = .twD) (regRank 3)

@[expose] def I2015NLOnOmegaMinus : Prop := I2015NLOnTagsWhen (fun t => t = .twD) (regRankGe 4)

@[expose] def I2015NLOnG2 : Prop :=
  I2015NLOnTagsWhen (fun t => t = .G2) fun lab p => ¬ regN lab p

@[expose] def I2015NLResG2 : Prop := I2015NLOnTagsWhen (fun t => t = .G2) regN

@[expose] def I2015NLOnF4 : Prop := I2015NLOnTags fun t => t = .F4

@[expose] def I2015NLOnE : Prop := I2015NLOnTags fun t => t = .E6 ∨ t = .E7 ∨ t = .E8

@[expose] def I2015NLOnTwE6 : Prop :=
  I2015NLOnTagsWhen (fun t => t = .twE6) fun lab p => ¬ regThree lab p

@[expose] def I2015NLResTwE6 : Prop := I2015NLOnTagsWhen (fun t => t = .twE6) regThree

@[expose] def I2015NLOnTriD4 : Prop := I2015NLOnTags fun t => t = .triD4

@[expose] def I2015NLOnSuzuki : Prop := I2015NLOnTags fun t => t = .twB2

@[expose] def I2015NLOnTwF4 : Prop :=
  I2015NLOnTagsWhen (fun t => t = .twF4) fun lab p => ¬ regN lab p

@[expose] def I2015NLResTwF4 : Prop := I2015NLOnTagsWhen (fun t => t = .twF4) regN

@[expose] def I2015NLOnDerived : Prop :=
  I2015NLOnTags fun t => t = .B2der ∨ t = .G2der ∨ t = .twF4der

@[expose] def IsTD4Simple (S : Type) [Group S] : Prop :=
  catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)

@[expose] def I2015NLOnTD4Outer : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsChevSimple 2 S → IsTD4Simple S →
    ∀ β : MulAut S, β ^ 3 = 1 → β ∉ (MulAut.conj : S →* MulAut S).range → NoLocalTwo 3 β

structure I2015NLFamilies : Prop where
  linear : I2015NLOnLinear
  unitary : I2015NLOnUnitary
  symplectic : I2015NLOnSymplectic
  resSp4 : I2015NLResSp4
  d3 : I2015NLOnD3
  omegaPlus : I2015NLOnOmegaPlus
  twD2 : I2015NLOnTwD2
  twD3 : I2015NLOnTwD3
  omegaMinus : I2015NLOnOmegaMinus
  g2 : I2015NLOnG2
  resG2 : I2015NLResG2
  f4 : I2015NLOnF4
  e : I2015NLOnE
  twE6 : I2015NLOnTwE6
  resTwE6 : I2015NLResTwE6
  triD4 : I2015NLOnTriD4
  suzuki : I2015NLOnSuzuki
  twF4 : I2015NLOnTwF4
  resTwF4 : I2015NLResTwF4
  derived : I2015NLOnDerived
  td4Outer : I2015NLOnTD4Outer

theorem I2015NLFamilies.atLabel (h : I2015NLFamilies) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) : I2015NLAtLabelWhen (fun _ _ => True) lab := by
  have hsp : I2015NLOnTags fun t => t = .B ∨ t = .C := h.resSp4.union h.symplectic
  have hg2 : I2015NLOnTags fun t => t = .G2 := h.resG2.union h.g2
  have htwE6 : I2015NLOnTags fun t => t = .twE6 := h.resTwE6.union h.twE6
  have htwF4 : I2015NLOnTags fun t => t = .twF4 := h.resTwF4.union h.twF4
  have hD : I2015NLOnTags fun t => t = .D :=
    I2015NLOnTagsWhen.cover (C₁ := regRank 3) (C₂ := regRankGe 4) (C₃ := regRankGe 4)
      (fun lab p hlab ht => by
        have h3 : 3 ≤ lab.rank := by
          have := hlab.2
          rw [ht] at this
          exact this
        unfold regRank regRankGe
        omega) h.d3 h.omegaPlus h.omegaPlus
  have htwD : I2015NLOnTags fun t => t = .twD :=
    I2015NLOnTagsWhen.cover (C₁ := regRank 2) (C₂ := regRank 3) (C₃ := regRankGe 4)
      (fun lab p hlab ht => by
        have h2 : 2 ≤ lab.rank := by
          have := hlab.2
          rw [ht] at this
          exact this
        unfold regRank regRankGe
        omega) h.twD2 h.twD3 h.omegaMinus
  obtain ⟨t, r, n⟩ := lab
  cases t
  · exact h.linear _ hlab rfl
  · exact h.unitary _ hlab rfl
  · exact hsp _ hlab (Or.inl rfl)
  · exact hsp _ hlab (Or.inr rfl)
  · exact hD _ hlab rfl
  · exact htwD _ hlab rfl
  · exact h.e _ hlab (Or.inl rfl)
  · exact h.e _ hlab (Or.inr (Or.inl rfl))
  · exact h.e _ hlab (Or.inr (Or.inr rfl))
  · exact h.f4 _ hlab rfl
  · exact htwE6 _ hlab rfl
  · exact h.triD4 _ hlab rfl
  · exact hg2 _ hlab rfl
  · exact h.suzuki _ hlab rfl
  · exact htwF4 _ hlab rfl
  · exact h.derived _ hlab (Or.inl rfl)
  · exact h.derived _ hlab (Or.inr (Or.inl rfl))
  · exact h.derived _ hlab (Or.inr (Or.inr rfl))

theorem largeEvenMarking_and_all {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    {P' : LargeEvenLabel → LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → CAll lab (LargeEvenSimpleGuard (P' lab)))
    (h : CFSG.Assembly.LargeEvenMarking X P) :
    CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ P' lab R I F := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hraw' := hall lab hlab _ hraw
  refine ⟨hX, lab, hlab, Canonical.largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP' hs hna⟩

theorem cAll_of_forall {lab : LargeEvenLabel} {P : LargeEvenRawCont}
    (h : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F) : CAll lab P := fun _ hQ =>
  Canonical.largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq, h R I F⟩) hQ

private theorem mem_inner_of_central_surjective {Q Q' : Type*} [Group Q] [Group Q']
    [Group.IsPerfect Q] (Ψ : Q →* Q') (hΨ : Function.Surjective Ψ) (hker : Ψ.ker ≤ Subgroup.center Q)
    {θ : MulAut Q} {θ' : MulAut Q'} (hθ : ∀ q, Ψ (θ q) = θ' (Ψ q))
    (h : θ' ∈ (MulAut.conj : Q' →* MulAut Q').range) : θ ∈ (MulAut.conj : Q →* MulAut Q).range := by
  obtain ⟨q', hq'⟩ := h
  obtain ⟨q₀, rfl⟩ := hΨ q'
  let φ : Q →* Q := ((MulAut.conj q₀⁻¹ : MulAut Q) : Q →* Q).comp (θ : Q →* Q)
  have hc : ∀ q, q⁻¹ * φ q ∈ Subgroup.center Q := by
    intro q
    apply hker
    rw [MonoidHom.mem_ker]
    have h1 : Ψ (φ q) = (Ψ q₀)⁻¹ * θ' (Ψ q) * Ψ q₀ := by
      show Ψ (q₀⁻¹ * θ q * q₀⁻¹⁻¹) = _
      rw [map_mul, map_mul, map_inv, hθ, inv_inv]
    rw [map_mul, map_inv, h1, ← hq', MulAut.conj_apply]
    group
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    φ hc
  refine ⟨q₀, ?_⟩
  ext q
  have h2 := congrArg (fun f : Q →* Q => f q) hid
  simp only [φ, MonoidHom.comp_apply, MonoidHom.id_apply] at h2
  change q₀⁻¹ * θ q * q₀⁻¹⁻¹ = q at h2
  change q₀ * q * q₀⁻¹ = θ q
  calc q₀ * q * q₀⁻¹ = q₀ * (q₀⁻¹ * θ q * q₀⁻¹⁻¹) * q₀⁻¹ := by rw [h2]
    _ = θ q := by group

theorem psAut_not_inner {H : Type} [Group H] (p : ℕ) (δ : MulAut H)
    (hperf : commutator (ppQuot p H) = ⊤) (hnon : ¬ InnerAutGrp p H δ) :
    psAut p δ ∉ (MulAut.conj : psimpleOf p H →* MulAut (psimpleOf p H)).range := by
  intro hin
  haveI : Group.IsPerfect (ppQuot p H) := Group.isPerfect_def.2 hperf
  obtain ⟨q₀, hq₀⟩ := mem_inner_of_central_surjective
    (QuotientGroup.mk' (Subgroup.center (ppQuot p H))) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (θ := ppAut p δ) (θ' := psAut p δ)
    (fun k => (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
      (ppAut p δ) k).symm) hin
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective q₀
  refine hnon ⟨l₀⁻¹, fun y => ?_⟩
  have h1 := congrArg (fun φ : MulAut (ppQuot p H) => φ (QuotientGroup.mk y)) hq₀
  simp only [MulAut.conj_apply, ppAut_mk] at h1
  have h2 : (QuotientGroup.mk (l₀ * y * l₀⁻¹) : ppQuot p H) = QuotientGroup.mk (δ y) := by
    simpa using h1
  have := QuotientGroup.eq.1 h2
  simpa using this

theorem noLocalTwo_of_fieldAutOn (hfam : I2015NLFamilies) {H : Type} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {δ : MulAut H} (hδ : δ ^ p = 1)
    (hperf : commutator (ppQuot p H) = ⊤) (hchev : IsChevSimple 2 (psimpleOf p H))
    (hfield : FieldAutOn p H δ) : NoLocalTwo p (psAut p δ) := by
  rcases hfield with hmark | ⟨hp3, hT, hnon⟩
  · have h := largeEvenMarking_and_all
      (P' := fun lab R _ I F => ¬ (lab.tag = .triD4 ∧ p = 3) →
        ∀ f ∈ F, orderOf f = p → Finite R → NoLocalTwo p f)
      (fun lab hlab => by
        by_cases h3 : lab.tag = .triD4 ∧ p = 3
        · exact cAll_of_forall fun R _ I F _ _ h => absurd h3 h
        · exact ((hfam.atLabel hlab) p hp hp2 h3 trivial).mono fun R _ I F h' hs hna _ => h' hs hna) hmark
    obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, hP, hP'⟩ :=
      Canonical.largeEvenMarking_exists h
    obtain ⟨hne, f, hf, u, hu, hord, hind⟩ := hP
    have h3 : ¬ (lab.tag = .triD4 ∧ p = 3) := by
      rintro ⟨h, h'⟩
      rcases hne with h0 | h0
      · exact h0 h
      · exact h0 h'
    haveI : Finite R := Finite.of_equiv _ θ.toEquiv
    have hNL : NoLocalTwo p f := hP' h3 f hf hord inferInstance
    have hconj : MulAut.congr θ (psAut p δ) = u * f * u⁻¹ :=
      ((glaInduces_relOfAut_iff p δ θ _).1 hind).symm
    have hu' : MulAut.congr (u : R ≃* R) f = u * f * u⁻¹ := by
      ext x
      simp [MulAut.congr_apply]
    have h1 : NoLocalTwo p (MulAut.congr (u : R ≃* R) f) := noLocalTwo_congr hp _ hNL
    rw [hu', ← hconj] at h1
    have h2 := noLocalTwo_congr hp θ.symm h1
    have h4 : MulAut.congr θ.symm (MulAut.congr θ (psAut p δ)) = psAut p δ := by
      ext x
      simp [MulAut.congr_apply]
    rwa [h4] at h2
  · subst hp3
    exact hfam.td4Outer _ hchev hT _ (psAut_pow_eq_one 3 δ hδ) (psAut_not_inner 3 δ hperf hnon)

theorem i2015NoParabolicFact_of_families (hfam : I2015NLFamilies) : I2015NoParabolicFact :=
  noParabolicFact_of_noLocalTwo fun _ _ _ _ _ hp hp2 hδ hperf hchev hfield =>
    noLocalTwo_of_fieldAutOn hfam hp hp2 hδ hperf hchev hfield

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
