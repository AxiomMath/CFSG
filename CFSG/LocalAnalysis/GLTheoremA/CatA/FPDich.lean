module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPFieldN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I91
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI

theorem marking_or_split {X : Type} [Group X] {P₁ P₂ : LargeEvenMarkProp X}
    (h : CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ => P₁ lab R I F θ ∨ P₂ lab R I F θ) :
    CFSG.Assembly.LargeEvenMarking X P₁ ∨ CFSG.Assembly.LargeEvenMarking X P₂ := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have h' : CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ, P₁ lab R I F θ) ∨
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ, P₂ lab R I F θ) := by
    refine Canonical.largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hθ | hθ⟩
    exacts [Or.inl ⟨hs, hna, θ, hθ⟩, Or.inr ⟨hs, hna, θ, hθ⟩]
  rcases canonRawDatum_or h' with h1 | h2
  · exact Or.inl ⟨hX, lab, hlab, h1⟩
  · exact Or.inr ⟨hX, lab, hlab, h2⟩

section Induced

variable {G : Type} [Group G] [Finite G]

theorem indAut_pow_eq_one {p : ℕ} {L : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hbp : b ^ p = 1) : indAut p L b hbN ^ p = 1 := by
  unfold indAut
  rw [← map_pow]
  have h : (⟨b⁻¹, Subgroup.inv_mem _ hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
    Subtype.ext (by simp [inv_pow, hbp])
  rw [h, map_one]

theorem indAut_zpow {p : ℕ} {L : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (k : ℤ) :
    indAut p L (b ^ k) (Subgroup.zpow_mem _ hbN k) = indAut p L b hbN ^ k := by
  unfold indAut
  rw [← map_zpow]
  congr 1
  exact Subtype.ext (by simp [zpow_neg, inv_zpow])

end Induced

@[expose] def NoTrialityAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSTriple 3 B x L →
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) → IsChevSimple 2 (PSimple 3 L) →
    catalogIs (PSimple 3 L) isD4any → ∀ b ∈ B,
      CFSG.Assembly.LargeEvenMarking (PQuot 3 L) fun lab R _ I F θ =>
        ∀ φ : MulAut R, LargeEvenInduces θ (indRel 3 L b) φ → CentralMod I φ

section Main


variable {G : Type} [Group G] [Finite G]

theorem fieldOn_or_td4_of_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hbp : b ^ p = 1)
    (hnon : ¬ InnDiagOn p (Subgroup.zpowers b) L)
    (hM : CFSG.Assembly.LargeEvenMarking (PQuot p L) fun lab R _ I F θ =>
      ∀ φ : MulAut R, LargeEvenInduces θ (indRel p L b) φ → CentralMod I φ) :
    FieldOn p b L ∨ (p = 3 ∧ IsTD4 3 L) := by
  have h1 := canon_marking_and_labelAll_simple' (P' := TransportFacts p)
    (fun lab hlab => canonTransportFacts hp hp2 hlab) hM
  have h2 := CFSG.StandardType.Canonical.largeEvenMarking_markedModel h1
  have h3 : CFSG.Assembly.LargeEvenMarking (PQuot p L) fun lab R _ I F θ =>
      (∀ a ∈ Subgroup.zpowers b, ∃ φ ∈ I, LargeEvenInduces θ (indRel p L a) φ) ∨
        (((lab.tag = .triD4 ∧ p = 3) ∧ MarkedModel lab R) ∨
          GLAPrimeField p lab I F (GLAInduces θ (indRel p L b))) := by
    refine Canonical.largeEvenMarking_mono ?_ h2
    rintro lab R _ I F θ ⟨⟨hcent, ⟨hI, hC, hlift⟩⟩, hMM⟩
    obtain ⟨hmul, hinv, hconj, hFI⟩ := hI
    have h1 : (1 : MulAut R) ∈ I := by simpa using hconj 1
    set α := MulAut.congr θ (indAut p L b hbN) with hα
    have hind : LargeEvenInduces θ (indRel p L b) α := (induces_indRel_iff hbN θ).2 rfl
    have hcα : CentralMod I α := hcent α hind
    by_cases hαI : α ∈ I
    · left
      intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have hak : b ^ k ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ hbN k
      let S : Subgroup (MulAut R) :=
        { carrier := I, mul_mem' := fun ha hb => hmul _ ha _ hb, one_mem' := h1,
          inv_mem' := fun ha => hinv _ ha }
      refine ⟨α ^ k, S.zpow_mem hαI k, (induces_indRel_iff hak θ).2 ?_⟩
      rw [indAut_zpow hbN k, map_zpow]
    · right
      by_cases ht : lab.tag = .triD4 ∧ p = 3
      · exact Or.inl ⟨ht, hMM⟩
      · right
        have hne : lab.tag ≠ .triD4 ∨ p ≠ 3 := not_and_or.mp ht
        obtain ⟨hOdd, hLS⟩ := hlift ht
        have hpα : α ^ p = 1 := by
          rw [hα, ← map_pow, indAut_pow_eq_one hbN hbp, map_one]
        obtain ⟨u, hu, f, hf, huf⟩ := hOdd α hpα hcα
        have hnot : u * f ∉ I := huf ▸ hαI
        have hpow : (u * f) ^ p = 1 := huf ▸ hpα
        obtain ⟨f', hf', u', hu', hord, heq⟩ := hLS u hu f hf hnot hpow
        exact ⟨hne, f', hf', u', hu', hord, (induces_indRel_iff hbN θ).2 (by rw [← hα, huf, heq])⟩
  rcases marking_or_split h3 with hA | hB
  · exact absurd ⟨Subgroup.zpowers_le.2 hbN, hA⟩ hnon
  · rcases marking_or_split hB with hT | hF
    · obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨⟨ht, hp3⟩, hMM⟩⟩ :=
        Canonical.largeEvenMarking_exists hT
      subst hp3
      obtain ⟨tg, rk, nn⟩ := lab
      dsimp only at ht
      subst ht
      have hL : CFSG.Blueprint.LieModel R .trialityD4 0 2 nn := hMM
      obtain ⟨i, hi, ⟨e⟩⟩ := catalog_TD4_of_lieModel hL
      exact Or.inr ⟨rfl, i, hi, ⟨θ.trans e⟩⟩
    · exact Or.inl ⟨hbN, hF⟩

theorem fieldDichotomyAt_of_noTriality (hNT : NoTrialityAt G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : FieldDichotomyAt G p := by
  intro B x L hS hK hchev b hb hnon
  have hbN := hnon.1
  have hbp : b ^ p = 1 := hS.1.1.2 b hb
  rcases i91_holds G p hp hp2 _ L b hS.2.2 hchev hbN hbp hnon with hF | ⟨hp3, hD4 | hT⟩
  · exact Or.inl hF
  · subst hp3
    exact fieldOn_or_td4_of_central hp hp2 hbN hbp hnon.2 (hNT B x L hS hK hchev hD4 b hb)
  · exact Or.inr ⟨hp3, hT⟩

end Main

end FP

end CFSG.LocalAnalysis.GLTheoremA
