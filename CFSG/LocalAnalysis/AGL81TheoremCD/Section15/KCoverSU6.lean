module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixSUKill
public import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.QuasithinUnique
open CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbedding.ParabHub

theorem two_le_pRank_of_subgroupOf_q {W : Type*} [Group W] [Finite W] {L A : Subgroup W}
    {r : ℕ}
    (hr : r.Prime) (hA : A ≤ L) (h : 2 ≤ CFSG.Open.pRank r (A.subgroupOf L)) :
    2 ≤ CFSG.Open.pRank r A := by
  have h1 := CFSG.SectionRank.pRank_le_map hr.one_lt L.subtype L.subtype_injective
    (A.subgroupOf L)
  rw [Subgroup.map_subgroupOf_eq_of_le hA] at h1
  exact h.trans h1

section NodePair

variable {W : Type} [Group W] [Finite W] {L : Subgroup W} {K : Type} [Group K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}
  {π : K →* ↥L ⧸ Subgroup.center ↥L} {r : ℕ}

theorem two_le_pRank_of_nodePair_q (hbq : BorelQuotient D n H π M) {A : Subgroup W} (hA : A ≤ L)
    (hr : r.Prime) (hr2 : r ≠ 2) {k k' : Fin D.rank} (hk : NodeIn (D := D) L A π k)
    (hk' : NodeIn (D := D) L A π k') {a b m : K} (ha : a ∈ rankOne D.rootGroup k)
    (hm : m ∈ rankOne D.rootGroup k)
    (hb : b ∈ rankOne D.rootGroup k ⊔ rankOne D.rootGroup k') (har : a ^ r = 1)
    (ha1 : a ∉ Subgroup.center K) (hbr : b ^ r = 1) (hb1 : b ∉ Subgroup.center K)
    (hma : m * a * m⁻¹ = a⁻¹) (hab : a * b = b * a) (hmb : m * b = b * m) :
    2 ≤ CFSG.Open.pRank r A := by
  have hjoin : (rankOne D.rootGroup k ⊔ rankOne D.rootGroup k').map π ≤
      (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
    rw [Subgroup.map_sup]
    exact sup_le hk hk'
  exact two_le_pRank_of_subgroupOf_q hr hA (two_le_pRank_of_images_q hr hr2 hbq.ker_central
    (hk ⟨a, ha, rfl⟩) (hjoin ⟨b, hb, rfl⟩) (hk ⟨m, hm, rfl⟩) har ha1 hbr hb1 hma hab hmb)

theorem two_le_pRank_of_badPair_q (hr : r.Prime) (hr2 : r ≠ 2)
    (hbq : BorelQuotient D n H π M) (hdiv : D.divisible = ∅)
    (hodd : ∀ i, OddNode (rankOne D.rootGroup i) r) {A : Subgroup W} (hA : A ≤ L)
    {i j : Fin D.rank} (hb : BadPair D i j) (hi : NodeIn (D := D) L A π i)
    (hj : NodeIn (D := D) L A π j) :
    2 ≤ CFSG.Open.pRank r A := by
  refine two_le_pRank_of_subgroupOf_q hr hA ?_
  obtain ⟨hij, h0 | h2⟩ := hb
  · exact two_le_pRank_of_orthogonal_nodes_q hr hr2 hbq.ker_central hi hj (hodd i) (hodd j)
      (rankOne_commute_of_cartan_zero hbq.extras hij h0)
  · rcases cartan_pair_cases D.isFiniteType hij with ⟨h1, h2'⟩ | ⟨h1, h2'⟩ | ⟨h1, h2'⟩ |
      ⟨h1, h2'⟩ | ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · rw [h1, h2'] at h2
      norm_num at h2
    · rw [h1, h2'] at h2
      norm_num at h2
    · exact two_le_pRank_of_conj_nodes_q hr hr2 hbq.ker_central hi
        (hj ⟨n j, hbq.ct.n_mem j, rfl⟩) (hodd i)
        (rankOne_conj_commute_of_cartan_B2 hbq.ct hbq.extras hdiv hij h1 h2')
    · exact two_le_pRank_of_conj_nodes_q hr hr2 hbq.ker_central hj
        (hi ⟨n i, hbq.ct.n_mem i, rfl⟩) (hodd j)
        (rankOne_conj_commute_of_cartan_B2 hbq.ct hbq.extras hdiv hij.symm h2' h1)
    · rw [h1, h2'] at h2
      norm_num at h2
    · rw [h1, h2'] at h2
      norm_num at h2

end NodePair

section Six

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W}
  {F : Type} [Field F] [Finite F] [CharP F 2] {f q : ℕ}

theorem false_of_su_six_q (hS : IsSylowTwoOf S₀ L)
    (hcov : CoveredByTwo L S₀ A₁ A₂) (hA₁ : A₁ ≤ L) (hA₂ : A₂ ≤ L)
    (h₁ : CFSG.Open.pRank q A₁ ≤ 1) (h₂ : CFSG.Open.pRank q A₂ ≤ 1)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : q.Prime) (hq5 : 5 ≤ q) (hqf : q ∣ 2 ^ f + 1)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* StatedProj (StatedSU 6 (2 ^ f) F)) : False := by
  have hq2 : q ≠ 2 := by omega
  have hpd : q ∣ (2 ^ f) ^ 2 - 1 :=
    hqf.trans (CFSG.AGLEmbedding.ParabPrime.sub_one_dvd_and_add_one_dvd (2 ^ f)
      (Nat.one_le_two_pow)).2
  obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero hF
  have hbq := borelQuotient_su (n := 6) hF (by norm_num) ζ hζ e
  obtain ⟨π', hπ', hcl⟩ := cover_classes hS hcov hbq
  have hdiv : (Unitary.rootDatum hF 6).divisible = ∅ := by
    show Unitary.divisible 6 = ∅
    simp only [Unitary.divisible, if_pos (show Even 6 by decide)]
  have hodd : ∀ i, OddNode (rankOne (Unitary.rootDatum hF 6).rootGroup i) q := fun i =>
    CFSG.LocalAnalysis.RankThreeUC.S15.K517ChevGenQ.oddNode_su_sq hF (by norm_num) i hq hq2 hpd
  let i0 : Fin (6 / 2) := ⟨0, by norm_num⟩
  let i1 : Fin (6 / 2) := ⟨1, by norm_num⟩
  let i2 : Fin (6 / 2) := ⟨2, by norm_num⟩
  have hbad02 : BadPair (Unitary.rootDatum hF 6) i0 i2 := by
    show BadPairMat (Unitary.cartan 6) i0 i2
    unfold Unitary.cartan
    rw [if_pos (show Even 6 by decide)]
    decide +kernel
  have hbad12 : BadPair (Unitary.rootDatum hF 6) i1 i2 := by
    show BadPairMat (Unitary.cartan 6) i1 i2
    unfold Unitary.cartan
    rw [if_pos (show Even 6 by decide)]
    decide +kernel
  obtain ⟨a, b, m, ha, hm, hb, haq, hbq', ha1, hb1, hma, hab, hmb⟩ :=
    su_short_pair_q hF (by norm_num) (by decide) hq hq5 hqf i0 i1 (by norm_num) (by norm_num)
  have key : ∀ {A : Subgroup W}, A ≤ L → CFSG.Open.pRank q A ≤ 1 →
      ¬ (NodeIn (D := Unitary.rootDatum hF 6) L A π' i0 ∧
        NodeIn (D := Unitary.rootDatum hF 6) L A π' i1) ∧
      ¬ (NodeIn (D := Unitary.rootDatum hF 6) L A π' i0 ∧
        NodeIn (D := Unitary.rootDatum hF 6) L A π' i2) ∧
      ¬ (NodeIn (D := Unitary.rootDatum hF 6) L A π' i1 ∧
        NodeIn (D := Unitary.rootDatum hF 6) L A π' i2) := by
    intro A hA hr
    refine ⟨fun ⟨hi, hj⟩ => ?_, fun ⟨hi, hj⟩ => ?_, fun ⟨hi, hj⟩ => ?_⟩
    · have := two_le_pRank_of_nodePair_q hπ' hA hq hq2 hi hj ha hm hb haq ha1 hbq' hb1 hma hab
        hmb
      omega
    · have := two_le_pRank_of_badPair_q hq hq2 hπ' hdiv hodd hA hbad02 hi hj
      omega
    · have := two_le_pRank_of_badPair_q hq hq2 hπ' hdiv hodd hA hbad12 hi hj
      omega
  exact false_of_triple_classes (a := i0) (b := i1) (c := i2) hcl (key hA₁ h₁) (key hA₂ h₂)

end Six

theorem KCoverSU6_holds :
    ∀ (W : Type) [Group W] [Finite W] (L S₀ A₁ A₂ : Subgroup W), CFSG.Open.IsQuasisimple ↥L →
      CFSG.QuasithinUnique.IsSylowTwoOf S₀ L → CoveredByTwo L S₀ A₁ A₂ → A₁ ≤ L → A₂ ≤ L →
      ∀ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 → Even Q.exponent →
        d.1 = .twistedA 5 Q →
        Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ q : ℕ, q.Prime → q ∣ Q.card + 1 → 2 ≤ CFSG.Open.pRank q A₁ ∨ 2 ≤ CFSG.Open.pRank q A₂ := by
  intro W _ _ L S₀ A₁ A₂ hL hS hcov hA₁ hA₂ d Q hQ2 heven hd e q hq hqQ
  by_cases h1 : 2 ≤ CFSG.Open.pRank q A₁
  · exact Or.inl h1
  · right
    by_contra h2
    have h1' : CFSG.Open.pRank q A₁ ≤ 1 := by omega
    have h2' : CFSG.Open.pRank q A₂ ≤ 1 := by omega
    obtain ⟨d, hv⟩ := d
    obtain ⟨e⟩ := e
    dsimp only at hd
    subst hd
    have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 Q hv e
    rw [hQ2] at hmodel
    obtain ⟨⟨-, -, -, -⟩, F, hFfield, hFfin, hcard, ⟨e'⟩⟩ := hmodel
    letI : Field F := hFfield
    letI : Finite F := hFfin
    letI : Fintype F := Fintype.ofFinite F
    have hchar : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := Q.exponent * 2)
        (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
    letI : CharP F 2 := hchar
    have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ2]
    have hqf : q ∣ 2 ^ Q.exponent + 1 := by
      rw [← hQc]
      exact hqQ
    have hq2 : q ≠ 2 := by
      have heven2 : Even (2 ^ Q.exponent) := even_two.pow_of_ne_zero Q.exponent_pos.ne'
      rintro rfl
      exact heven2.add_one.not_two_dvd_nat hqf
    have hq3 : q ≠ 3 := by
      rintro rfl
      have hmod := CFSG.two_pow_mod_three_of_even heven
      have hmod2 : (2 ^ Q.exponent + 1) % 3 = 2 := by
        simp [Nat.add_mod, hmod]
      have h0 : (2 ^ Q.exponent + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.1 hqf
      omega
    have hq4 : q ≠ 4 := by
      rintro rfl
      exact absurd hq (by norm_num)
    have hq5 : 5 ≤ q := by
      have := hq.two_le
      omega
    exact false_of_su_six_q (f := Q.exponent) hS hcov hA₁ hA₂ h1' h2' hcard hq hq5 hqf e'

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
