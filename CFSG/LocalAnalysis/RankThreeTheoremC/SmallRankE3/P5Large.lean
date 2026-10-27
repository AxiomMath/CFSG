module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
import CFSG.LocalAnalysis.RankThreeTheoremC.D2FusionFocal3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def Fail614NormalizerRankGen (p : ℕ) (P : Sylow p G) (M B : Subgroup G) : Prop :=
  ∀ T : Subgroup G, IsMaxTwoInvariantIn B M T →
    CFSG.Open.pRank p (P : Subgroup G) ≤ CFSG.Open.pRank p (M ⊓ normalizer (T : Set G))

structure Fail614OptimalGen (p : ℕ) (M : Subgroup G) (x z : G) (H S : Subgroup G) : Prop where
  ext : Prop614Extremal M (zpowers x ⊔ zpowers z) H S
  eq_normalizer : H = normalizer (pCoreOf 2 H : Set G)
  maxInv : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S
  core_le : pCoreOf 2 H ≤ S
  norm_le : ∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S →
    S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M
  char_le : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
    normalizer (S₀ : Set G) ≤ M
  pRank_le : CFSG.Open.pRank p H ≤ 2
  sylow_le : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ H → zpowers x ⊔ zpowers z ≤ Q → Q ≤ M

private theorem fail614G_fusionIsSylowIn (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) (hα : HasPrimeConstraint (G := M) p)
    {x z : G} (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {T : Subgroup G}
    (hT : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T) :
    fusionIsSylowIn 2 T (GLBPrimeCore p M) := by
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  have hp2 : p ≠ 2 := sigmaA_odd p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hp⟩
  set B : Subgroup G := zpowers x ⊔ zpowers z
  set D : Subgroup G := GLBPrimeCore p M
  have hpl : SmallRankPlane p (P : Subgroup G) x z := SmallRankPlane.of_situation hS hsit hx hz
  have hB3 : IsPGroup p B := IsPGroup.of_card (n := 2) hpl.card_eq
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hBM : B ≤ M := (sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)).trans hPM
  obtain ⟨⟨hTM, hT2, hBT⟩, hmax⟩ := hT
  have hT3 : Nat.Coprime p (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hTD : T ≤ D := by
    exact CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains hp hp2
      hα hB3 hBM
      (fun y _ hyB hord => hpl.mem_of_mem_centralizer y hyB (by
        rw [← hord]
        exact pow_orderOf_eq_one y)) hTM hT3 hBT
  have hDp : ¬ p ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd hp).mp
    (CFSG.AGLEmbedding.glbPrimeCore_coprime p M)
  have hBD : B ≤ normalizer (D : Set G) :=
    hBM.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p M)
  obtain ⟨R, hRsyl, hTR, hBR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hp Nat.prime_two hB3 hDp hBD hTD hT2 hBT
  have hRT : R = T :=
    hmax R ⟨hRsyl.1.trans (CFSG.AGLEmbedding.glbPrimeCore_le p M), hRsyl.2.1, hBR⟩ hTR
  rwa [← hRT]

theorem fail614G_exists_conj_le_normalizer (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M)
    (hα : HasPrimeConstraint (G := M) p) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {T : Subgroup G}
    (hT : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T) :
    ∃ g : G, g ∈ M ∧
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ normalizer (T : Set G) := by
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup G := GLBPrimeCore p M
  have hTD : fusionIsSylowIn 2 T D := fail614G_fusionIsSylowIn hS hsit hα hx hz hT
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hDp : ¬ p ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd hp).mp
    (CFSG.AGLEmbedding.glbPrimeCore_coprime p M)
  have hPD : (P : Subgroup G) ≤ normalizer (D : Set G) :=
    hPM.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p M)
  have hbot2 : IsPGroup 2 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hbotp : IsPGroup p (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hPbot : (P : Subgroup G) ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨S, hSsyl, -, hPS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hp Nat.prime_two P.isPGroup' hDp hPD bot_le hbot2 hPbot
  obtain ⟨c, hc, hTc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    hp Nat.prime_two hbotp hDp bot_le hSsyl hTD bot_le bot_le
  refine ⟨c, CFSG.AGLEmbedding.glbPrimeCore_le p M (mem_inf.mp hc).1, ?_⟩
  rw [hTc, ← Subgroup.map_equiv_normalizer_eq]
  exact map_mono hPS

theorem fail614GNormalizerRank_of_alpha (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) (hα : HasPrimeConstraint (G := M) p)
    {x z : G} (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) :
    Fail614NormalizerRankGen p P M (zpowers x ⊔ zpowers z) := by
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  intro T hT
  obtain ⟨g, hgM, hPg⟩ := fail614G_exists_conj_le_normalizer hS hsit hα hx hz hT
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hle : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ M ⊓ normalizer (T : Set G) := by
    refine le_inf ?_ hPg
    rintro _ ⟨a, ha, rfl⟩
    exact M.mul_mem (M.mul_mem hgM (hPM ha)) (M.inv_mem hgM)
  calc CFSG.Open.pRank p (P : Subgroup G)
      = CFSG.Open.pRank p ((P : Subgroup G).map (MulAut.conj g).toMonoidHom) :=
        (pRank_map_automorphism p hp.one_lt _ _).symm
    _ ≤ CFSG.Open.pRank p (M ⊓ normalizer (T : Set G)) :=
        CFSG.SectionRank.pRank_mono hp.one_lt hle

private theorem fail614G_exists_mem_normalizer_not_mem {q : ℕ} [Fact q.Prime] {Q R : Subgroup G}
    (hR : IsPGroup q R) (hQR : Q < R) : ∃ y ∈ R, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : Q.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQR.ne ?_
    exact le_antisymm hQR.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQR.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

private theorem fail614G_lt_inf_normalizer {q : ℕ} [Fact q.Prime] {S T : Subgroup G}
    (hT : IsPGroup q T) (hST : S < T) : S < T ⊓ normalizer (S : Set G) := by
  obtain ⟨y, hyT, hyN, hyS⟩ := fail614G_exists_mem_normalizer_not_mem hT hST
  refine lt_of_le_of_ne (le_inf hST.le le_normalizer) fun h => hyS ?_
  rw [h]
  exact mem_inf.mpr ⟨hyT, hyN⟩

omit [Finite G] in
private theorem fail614G_normalizer_le_normalizer {S S₀ : Subgroup G} (h1 : S₀ ≤ S)
    (h3 : (S₀.subgroupOf S).Characteristic) :
    normalizer (S : Set G) ≤ normalizer (S₀ : Set G) := by
  have key : ∀ g ∈ normalizer (S : Set G), ∀ c ∈ S₀, g * c * g⁻¹ ∈ S₀ := by
    intro g hg c hc
    let φ : S ≃* S :=
      { toFun := fun s => ⟨g * s * g⁻¹, (mem_normalizer_iff.mp hg s).mp s.2⟩
        invFun := fun s => ⟨g⁻¹ * s * g, (mem_normalizer_iff''.mp hg s).mp s.2⟩
        left_inv := fun s => Subtype.ext (by simp [mul_assoc])
        right_inv := fun s => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun s t => Subtype.ext (by simp [mul_assoc]) }
    have hc' : (⟨c, h1 hc⟩ : S) ∈ S₀.subgroupOf S := hc
    exact characteristic_iff_map_le.mp h3 φ (mem_map_of_mem φ.toMonoidHom hc')
  intro g hg
  refine mem_normalizer_iff.mpr fun c => ⟨key g hg c, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc

omit [Finite G] in
private theorem fail614G_le_normalizer_inf {B S T : Subgroup G}
    (hBT : B ≤ normalizer (T : Set G)) (hBS : B ≤ normalizer (S : Set G)) :
    B ≤ normalizer ((T ⊓ normalizer (S : Set G) : Subgroup G) : Set G) :=
  (le_inf hBT (hBS.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf

private theorem fail614G_false_of_card_lt {M B H S H₁ R : Subgroup G}
    (h : Prop614Extremal M B H S) (hH₁ : IsTwoLocal H₁) (hBH₁ : B ≤ H₁) (hH₁M : ¬ H₁ ≤ M)
    (hR : IsTwoInvariantIn B (H₁ ⊓ M) R) (hcard : Nat.card S < Nat.card R) : False := by
  obtain ⟨S₁, hRS₁, hS₁⟩ := exists_isMaxTwoInvariantIn_of_le hR
  have hlt : Nat.card S < Nat.card S₁ := hcard.trans_le (Subgroup.card_le_of_le hRS₁)
  have hS₁1 : S₁ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hlt
    have : 0 < Nat.card S := Nat.card_pos
    omega
  exact h.max H₁ S₁ ⟨hH₁, hBH₁, hH₁M, hS₁, hS₁1⟩ (Or.inl hlt)

theorem fail614GIsMax_top (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G}
    (hnr : Fail614NormalizerRankGen p P M (zpowers x ⊔ zpowers z)) {T : Subgroup G}
    (hT : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T) (hT1 : T ≠ ⊥) :
    IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) ⊤ T := by
  set B : Subgroup G := zpowers x ⊔ zpowers z
  have hT2 : IsPGroup 2 T := hT.1.2.1
  have hBT : B ≤ normalizer (T : Set G) := hT.1.2.2
  refine ⟨⟨le_top, hT2, hBT⟩, fun R hR hTR => ?_⟩
  obtain ⟨-, hR2, hBR⟩ := hR
  by_contra hne
  have hlt : T < R := lt_of_le_of_ne hTR (Ne.symm hne)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyR, hyN, hyT⟩ := fail614G_exists_mem_normalizer_not_mem hR2 hlt
  set L : Subgroup G := normalizer (T : Set G)
  have hL : IsTwoLocal L := ⟨T, hT1, hT2, rfl⟩
  have hrank : 3 ≤ CFSG.Open.pRank p (L ⊓ M) := by
    have h1 : CFSG.Open.pRank p (P : Subgroup G) ≤ CFSG.Open.pRank p (M ⊓ L) := hnr T hT
    rw [inf_comm] at h1
    have := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).2
    omega
  have hLM : L ≤ M :=
    le_of_three_le_pRank_inf hD1 hsit.mem_sigmaA hsit.isCoreMaxLocal hL hrank
  have hBL : B ≤ normalizer (L : Set G) := hBT.trans le_normalizer
  have hR₁ : IsTwoInvariantIn B M (R ⊓ L) :=
    ⟨inf_le_right.trans hLM, hR2.to_le inf_le_left,
      (le_inf hBR hBL).trans inf_normalizer_le_normalizer_inf⟩
  have hR₁T := hT.2 (R ⊓ L) hR₁ (le_inf hTR le_normalizer)
  exact hyT (hR₁T ▸ mem_inf.mpr ⟨hyR, hyN⟩)

theorem fail614GIsMax_self (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G}
    (hnr : Fail614NormalizerRankGen p P M (zpowers x ⊔ zpowers z)) {H S : Subgroup G}
    (h : Prop614Extremal M (zpowers x ⊔ zpowers z) H S) :
    IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hSHM, hS2, hBS⟩, hSmax⟩ := h.pair.isMax
  refine ⟨⟨hSHM.trans inf_le_left, hS2, hBS⟩, fun R hR hSR => ?_⟩
  by_contra hRS
  have hSltR : S < R := lt_of_le_of_ne hSR (Ne.symm hRS)
  obtain ⟨T, hST, hT⟩ := exists_isMaxTwoInvariantIn_of_le
    (⟨hSHM.trans inf_le_right, hS2, hBS⟩ : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S)
  have hT1 : T ≠ ⊥ := fun hT1 => h.pair.ne_bot (le_bot_iff.mp (hT1 ▸ hST))
  have hTG := fail614GIsMax_top hS hD1 hsit hnr hT hT1
  have hSltT : S < T := by
    refine lt_of_le_of_ne hST fun hST' => hRS ?_
    exact (hTG.2 R ⟨le_top, hR.2.1, hR.2.2⟩ (hST'.symm.le.trans hSR)).trans hST'.symm
  by_cases hH₁M : normalizer (S : Set G) ≤ M
  ·
    have hSltR₁ := fail614G_lt_inf_normalizer hR.2.1 hSltR
    exact hSltR₁.ne (hSmax _ ⟨le_inf (inf_le_left.trans hR.1) (inf_le_right.trans hH₁M),
      hR.2.1.to_le inf_le_left, fail614G_le_normalizer_inf hR.2.2 hBS⟩ hSltR₁.le).symm
  ·
    exact fail614G_false_of_card_lt h ⟨S, h.pair.ne_bot, hS2, rfl⟩ hBS hH₁M
      ⟨le_inf inf_le_right (inf_le_left.trans hT.1.1), hT.1.2.1.to_le inf_le_left,
        fail614G_le_normalizer_inf hT.1.2.2 hBS⟩
      (Subgroup.card_lt_of_lt (fail614G_lt_inf_normalizer hT.1.2.1 hSltT))

theorem fail614G_normalizer_le_of_characteristic (hS : Setting G) (hD1 : TheoremD1 G)
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G}
    (hnr : Fail614NormalizerRankGen p P M (zpowers x ⊔ zpowers z)) {H S : Subgroup G}
    (h : Prop614Extremal M (zpowers x ⊔ zpowers z) H S) {S₀ : Subgroup G} (h1 : S₀ ≤ S)
    (h2 : S₀ ≠ ⊥) (h3 : (S₀.subgroupOf S).Characteristic) :
    normalizer (S₀ : Set G) ≤ M := by
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hSHM, hS2, hBS⟩, -⟩ := h.pair.isMax
  have hNN := fail614G_normalizer_le_normalizer h1 h3
  have hH₁ : IsTwoLocal (normalizer (S₀ : Set G)) := ⟨S₀, h2, hS2.to_le h1, rfl⟩
  obtain ⟨T, hST, hT⟩ := exists_isMaxTwoInvariantIn_of_le
    (⟨hSHM.trans inf_le_right, hS2, hBS⟩ : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S)
  rcases hST.eq_or_lt with rfl | hSltT
  ·
    have hrank : 3 ≤ CFSG.Open.pRank p (normalizer (S₀ : Set G) ⊓ M) := by
      have h1 := hnr S hT
      have h2 : M ⊓ normalizer (S : Set G) ≤ normalizer (S₀ : Set G) ⊓ M :=
        fun g hg => ⟨hNN hg.2, hg.1⟩
      have h3 := CFSG.SectionRank.pRank_mono hp.one_lt h2
      have := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).2
      omega
    exact le_of_three_le_pRank_inf hD1 hsit.mem_sigmaA hsit.isCoreMaxLocal hH₁ hrank
  ·
    by_contra hH₁M
    exact fail614G_false_of_card_lt h hH₁ (hBS.trans hNN) hH₁M
      ⟨le_inf inf_le_right (inf_le_left.trans hT.1.1), hT.1.2.1.to_le inf_le_left,
        fail614G_le_normalizer_inf hT.1.2.2 (hBS.trans hNN)⟩
      (Subgroup.card_lt_of_lt ((fail614G_lt_inf_normalizer hT.1.2.1 hSltT).trans_le
        (inf_le_inf_left T hNN)))

theorem fail614G_le_of_plane_le (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {B : Subgroup G}
    (hBP : B ≤ (P : Subgroup G)) (hBC : centralizer (B : Set G) ≤ M) {Q : Subgroup G}
    (hQ : IsPGroup p Q) (hBQ : B ≤ Q) : Q ≤ M := by
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hp⟩
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hp P ⊤ le_top Q hQ le_top
  set g : G := (m : G)⁻¹ with hgdef
  have hgP : ∀ q ∈ Q, g⁻¹ * q * g ∈ (P : Subgroup G) := by
    intro q hq
    have := hm ⟨q, hq, rfl⟩
    simpa [hgdef, MulAut.conj_apply] using this
  have hmap : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using hgP b (hBQ hb)
  obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le_of_gamma_two hS hsit.mem_sigmaA
    hsit.isCoreMaxLocal hsit.gamma_two_le hBP hmap
  have hd : g * c⁻¹ ∈ centralizer (B : Set G) := by
    rw [mem_centralizer_iff]
    intro b hb
    have h1 := hc b hb
    calc b * (g * c⁻¹) = g * (g⁻¹ * b * g) * c⁻¹ := by group
      _ = g * (c⁻¹ * b * c) * c⁻¹ := by rw [h1]
      _ = g * c⁻¹ * b := by group
  have hgM : g ∈ M := by
    have := M.mul_mem (hBC hd) hcM
    simpa using this
  intro q hq
  have hqP := hgP q hq
  have hqM : g * (g⁻¹ * q * g) * g⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hgM (hPM hqP)) (M.inv_mem hgM)
  simpa [mul_assoc] using hqM

theorem fail614G_pRank_le_two (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {H S : Subgroup G}
    (h : Prop614Pair M (zpowers x ⊔ zpowers z) H S) : CFSG.Open.pRank p H ≤ 2 := by
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hp⟩
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hB3 : IsPGroup p ↥(zpowers x ⊔ zpowers z) := IsPGroup.of_card (n := 2) hpl.card_eq
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  have hB3' : IsPGroup p ↥((zpowers x ⊔ zpowers z).subgroupOf H) :=
    hB3.of_equiv (subgroupOfEquivOfLe h.le).symm
  obtain ⟨Q', hQ'⟩ := hB3'.exists_le_sylow
  set Q : Subgroup G := (Q' : Subgroup H).map H.subtype with hQ
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf p Q H := ⟨Q', rfl⟩
  have hBQ : zpowers x ⊔ zpowers z ≤ Q := by
    intro b hb
    have hbH : (⟨b, h.le hb⟩ : H) ∈ (zpowers x ⊔ zpowers z).subgroupOf H := hb
    exact ⟨⟨b, h.le hb⟩, hQ' hbH, rfl⟩
  have hQM : Q ≤ M :=
    fail614G_le_of_plane_le hS hsit hBP (centralizer_plane_le hS hsit hx hz) hQsyl.isPGroup hBQ
  by_contra hbig
  push Not at hbig
  have hQrank : 3 ≤ CFSG.Open.pRank p (H ⊓ M) := by
    have := pRank_eq_of_isSylowOf3 hp hQsyl
    have h2 := CFSG.SectionRank.pRank_mono hp.one_lt (le_inf hQsyl.le hQM)
    omega
  exact h.not_le
    (le_of_three_le_pRank_inf hD1 hsit.mem_sigmaA hsit.isCoreMaxLocal h.isTwoLocal hQrank)

theorem exists_fail614GOptimal (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z)
    (hnr : Fail614NormalizerRankGen p P M (zpowers x ⊔ zpowers z))
    (hex : ∃ H S : Subgroup G, Prop614Pair M (zpowers x ⊔ zpowers z) H S) :
    ∃ H S : Subgroup G, Fail614OptimalGen p M x z H S := by
  obtain ⟨H, S, hext⟩ := exists_prop614Extremal hex
  have hmax := fail614GIsMax_self hS hD1 hsit hnr hext
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  exact ⟨H, S, ⟨hext, hext.eq_normalizer_pCoreOf, hmax,
    pCoreOf_le_of_isMaxTwoInvariantIn hext.pair.le hmax,
    fun _ h1 h2 h3 => hext.normalizer_le_of_pCoreOf_lt h1 h2 h3,
    fun _ h1 h2 h3 => fail614G_normalizer_le_of_characteristic hS hD1 hsit hnr hext h1 h2 h3,
    fail614G_pRank_le_two hS hD1 hsit hx hz hext.pair,
    fun Q hQ _ hBQ =>
      fail614G_le_of_plane_le hS hsit hBP (centralizer_plane_le hS hsit hx hz) hQ hBQ⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
