module

public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA4
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeviSection
public import CFSG.Quasithin.Background.PSL3TwoOrderFour
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Quasithin.H13.U4ParTwoElem

public section

namespace CFSG.SectionRank.QTK

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem u4ParabolicSq_holds :
    ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.Blueprint.LieModel X .PSU 4 2 f →
      ∀ (T : Sylow 2 X) (P : Subgroup X), P ≠ ⊤ →
        Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ P →
        ∃ Q : Subgroup X, IsPGroup 2 Q ∧ P ≤ Subgroup.normalizer (Q : Set X) ∧
          ∀ y ∈ P, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 ∈ Q := by
  intro X _ _ f hX T P hP hNP
  exact CFSG.Quasithin.H13.U4Par.exists_sq_mem_of_lieModel hX T hP hNP

theorem char2_branch_false_of_u4Sq
    {S : Type} [Group S] [Finite S] (hC : Char2Rank2List S)
    {L : Type} [Group L] [Finite L] (j : L →* S) (hj : Function.Injective j)
    (Q : Subgroup L) [Q.Normal] (hQ : IsPGroup 2 ↥Q)
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤)
    (hPSL : CFSG.Quasithin.IsPSL 3 2 2 (L ⧸ Q)) (hnt : ⁅Q, (⊤ : Subgroup L)⁆ ≠ ⊥) : False := by
  have hU4 := u4ParabolicSq_holds
  obtain ⟨t, n, f, hF, hLM⟩ := char2_lieModel hC
  have hsimp : IsSimpleGroup (L ⧸ Q) := CFSG.Quasithin.H13.A5.isSimpleGroup_of_isPSL34 hPSL
  haveI := hsimp
  have hQbot : Q ≠ ⊥ := by
    rintro rfl
    exact hnt (by simp)
  have hU : Q.map j ≠ ⊥ := by
    intro h
    apply hQbot
    exact Subgroup.map_injective hj (h.trans (Subgroup.map_bot j).symm)
  have hUr : IsPGroup 2 ↥(Q.map j) := by
    intro x
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (q : L) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (x : S) = j q := hqx.symm
    simp only [Subgroup.coe_pow, Subgroup.coe_one, h2, ← map_pow, h1, map_one]
  obtain ⟨T, P, hPne, hNU, -, -, hT1, hT2⟩ :=
    CFSG.LieType.BorelTits.lieModel_conclusion S t n 2 f hLM (Q.map j) hU hUr
  have hconj : ∀ x : L, ∀ h ∈ Q.map j, j x * h * (j x)⁻¹ ∈ Q.map j := by
    intro x h hh
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨x * q * x⁻¹, ?_, ?_⟩
    · exact Subgroup.Normal.conj_mem inferInstance q hq x
    · simp [map_mul, map_inv]
  have hY : j.range ≤ P := by
    rintro _ ⟨x, rfl⟩
    apply hNU
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj x h
    · intro hh
      have := hconj x⁻¹ _ hh
      simpa [map_inv, mul_assoc] using this
  let φ : ↥(j.range) →* L ⧸ Q :=
    (QuotientGroup.mk' Q).comp (MonoidHom.ofInjective hj).symm.toMonoidHom
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q y
    refine ⟨(MonoidHom.ofInjective hj) x, ?_⟩
    simp [φ]
  have hnab : ¬ ∀ a b : L ⧸ Q, a * b = b * a := by
    intro hcomm
    have hcomm' : ⁅(⊤ : Subgroup (L ⧸ Q)), (⊤ : Subgroup (L ⧸ Q))⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      exact hcomm a b
    have htop := commutator_eq_top_of_surjective (QuotientGroup.mk' Q)
      (QuotientGroup.mk'_surjective Q) hperf
    rw [htop] at hcomm'
    obtain ⟨x, hx⟩ := exists_ne (1 : L ⧸ Q)
    have hxbot : x ∈ (⊥ : Subgroup (L ⧸ Q)) := hcomm' ▸ Subgroup.mem_top x
    exact hx (Subgroup.mem_bot.mp hxbot)
  have hHc : ∃ a b : L ⧸ Q, a * b ≠ b * a := by
    by_contra h
    apply hnab
    intro a b
    by_contra hab
    exact h ⟨a, b, hab⟩
  have hcard : Nat.card (L ⧸ Q) = 20160 :=
    CFSG.Quasithin.H13.A5.card_of_isPSL34 hPSL
  have hH2 : ∃ g : L ⧸ Q, (∃ k : ℕ, g ^ 2 ^ k = 1) ∧ g ^ 2 ≠ 1 := by
    obtain ⟨g, hg4, hg2⟩ := CFSG.Quasithin.exists_sq_ne_one_of_isPSL_three_two hPSL
    exact ⟨g, ⟨2, hg4⟩, hg2⟩
  have hH3 : 3 ∣ Nat.card (L ⧸ Q) := by rw [hcard]; norm_num
  have hH168 : ¬ Nat.card (L ⧸ Q) ∣ 168 := by rw [hcard]; norm_num
  have hT1' : t ≠ StatedLieTag.Tits → Subgroup.normalizer (T : Set S) ≤ P := by
    intro ht
    simpa [Sylow.coe_coe] using hT1 ht
  have hlevi : CFSG.Quasithin.H13.K1262Two.Char2LeviFamily t n f →
      LieModel S t n 2 f → False := by
    intro hfam hmod
    exact CFSG.Quasithin.H13.K1262Two.false_of_char2LeviFamily_of_surjective
      (H := L ⧸ Q) hHc hH2 hH3 hH168 hfam hmod T (P := P) hPne hT1' hT2 hY φ hφs
  rcases hF with ⟨rfl, rfl, hf2⟩ | ⟨rfl, rfl, hf1⟩ | ⟨rfl, rfl, hf2⟩ |
    ⟨rfl, rfl, hf2⟩ | ⟨rfl, rfl, hf1⟩ | ⟨rfl, rfl, hf2⟩ | ⟨rfl, rfl, hf1⟩ |
    ⟨rfl, rfl, hodd, hf3⟩ | ⟨rfl, rfl, hodd, hf3⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    have hL2 : StatedClassicalModel S .PSL 2 2 f := hLM.statedClassicalModel (by decide)
    have hsqS : ∀ x : S, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 2 = 1 :=
      CFSG.Quasithin.H13.K1262Two.sq_eq_one_of_isPSL_two_two hf2 hL2
    obtain ⟨g, hg, hgne⟩ := hH2
    have hsq : ∀ y ∈ j.range, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 ∈ (⊥ : Subgroup S) := by
      intro y _ hy
      rw [Subgroup.mem_bot]
      exact hsqS y hy
    have hYQ : j.range ≤ Subgroup.normalizer ((⊥ : Subgroup S) : Set S) := by
      have htop : Subgroup.normalizer ((⊥ : Subgroup S) : Set S) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr inferInstance
      rw [htop]
      exact le_top
    exact hgne (CFSG.sq_eq_one_of_surjective_of_sq_mem (H := L ⧸ Q) hHc
      (IsPGroup.of_bot) hYQ hsq φ hφs hg)
  · exact hlevi (by simp [CFSG.Quasithin.H13.K1262Two.Char2LeviFamily, hf1]) hLM
  · exact hlevi (by simp [CFSG.Quasithin.H13.K1262Two.Char2LeviFamily, hf2]) hLM
  · exact hlevi (by simp [CFSG.Quasithin.H13.K1262Two.Char2LeviFamily, hf2]) hLM
  ·
    obtain ⟨Q₀, hQ₀, hPnorm, hsqP⟩ := hU4 S f hLM T P hPne (hT1 (by decide))
    have hYQ₀ : j.range ≤ Subgroup.normalizer (Q₀ : Set S) := hY.trans hPnorm
    have hsq₀ : ∀ y ∈ j.range, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 ∈ Q₀ := by
      intro y hy hy2
      exact hsqP y (hY hy) hy2
    obtain ⟨g, hg, hgne⟩ := hH2
    exact hgne (CFSG.sq_eq_one_of_surjective_of_sq_mem (H := L ⧸ Q) hHc hQ₀
      hYQ₀ hsq₀ φ hφs hg)
  · exact hlevi (by simp [CFSG.Quasithin.H13.K1262Two.Char2LeviFamily, hf2]) hLM
  · exact hlevi (by simp [CFSG.Quasithin.H13.K1262Two.Char2LeviFamily, hf1]) hLM
  · exact hlevi (by simp [CFSG.Quasithin.H13.K1262Two.Char2LeviFamily, hodd, hf3]) hLM
  ·
    exact CFSG.Quasithin.H13.K1262Two.false_of_sz_of_surjective hH3
      (show CFSG.Quasithin.IsSz f S from (LieModel.suzukiModel hLM).2) φ hφs
  ·
    have hclass : StatedClassicalModel S .PSU 5 2 2 := hLM.statedClassicalModel (by decide)
    have hcardS : Nat.card S = CFSG.Open.ordTwistedA 4 4 := by
      simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hclass).2.1 rfl
    have h7LQ : 7 ∣ Nat.card (L ⧸ Q) := by rw [hcard]; norm_num
    have h7S : 7 ∣ Nat.card S :=
      h7LQ.trans ((Subgroup.card_quotient_dvd_card Q).trans
        (Subgroup.card_dvd_of_injective j hj))
    rw [hcardS] at h7S
    have hU54 : CFSG.Open.ordTwistedA 4 4 = 53443952640000 := by
      unfold CFSG.Open.ordTwistedA
      decide
    rw [hU54] at h7S
    norm_num at h7S
  · exact hlevi (by simp [CFSG.Quasithin.H13.K1262Two.Char2LeviFamily]) hLM

theorem char2_branch_false_of_levi
    {S : Type} [Group S] [Finite S] (hC : Char2Rank2List S)
    {L : Type} [Group L] [Finite L] (j : L →* S) (hj : Function.Injective j)
    (Q : Subgroup L) [Q.Normal] (hQ : IsPGroup 2 ↥Q)
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤)
    (hPSL : CFSG.Quasithin.IsPSL 3 2 2 (L ⧸ Q)) (hnt : ⁅Q, (⊤ : Subgroup L)⁆ ≠ ⊥) : False :=
  char2_branch_false_of_u4Sq hC j hj Q hQ hperf hPSL hnt

end CFSG.SectionRank.QTK
