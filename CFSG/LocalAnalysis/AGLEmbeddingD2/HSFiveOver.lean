module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltDichotomy
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BlockInnerAt
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveFaithful

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms CFSG.QuasithinUnique

@[expose] def KFactHSFiveOver : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    Subgroup.centralizer (K : Set X) = ⊥ →
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group) →
    ∀ (R : Sylow 5 X) (X₀ : Subgroup X),
      Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ X₀ → X₀ ≠ ⊤ →
      X₀ ≠ Subgroup.normalizer ((R : Subgroup X) : Set X) →
      K = ⊤ ∧ ∃ U : Subgroup X, U ≤ X₀ ∧ X₀ ≤ Subgroup.normalizer (U : Set X) ∧ ⁅U, U⁆ = U ∧
        (R : Subgroup X) ≤ U ∧
        (∀ W : Subgroup X, W ≤ U → U ≤ Subgroup.normalizer (W : Set X) → W = ⊥ ∨ W = U) ∧
        (∀ W : Subgroup X, W ≤ X₀ → ⁅W, W⁆ = W → W ≤ U) ∧
        Subgroup.centralizer (U : Set X) = ⊥ ∧ ¬ 5 ∣ Nat.card (Outer U) ∧
        ∃ E : Subgroup X, E ≤ U ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2

@[expose] def KFactBlockFiveHeis : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L U : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    ∀ hUM : U ≤ M, U ≤ Subgroup.normalizer (S : Set G) →
    barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    Nat.card U = 5 ^ 3 → ¬ IsMulCommutative U → centralizerBar M hUM (barM M L) = ⊥ →
    3 ≤ Open.pRank 5 (blockPL M S L)

@[expose] def KFactBlockFiveHeisInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L U : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    BlockInnerNormalizerAt M S L →
    ∀ hUM : U ≤ M, U ≤ Subgroup.normalizer (S : Set G) →
    barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    Nat.card U = 5 ^ 3 → ¬ IsMulCommutative U → centralizerBar M hUM (barM M L) = ⊥ →
    3 ≤ Open.pRank 5 (blockPL M S L)

theorem KFactBlockFiveHeis.inner (h : KFactBlockFiveHeis) : KFactBlockFiveHeisInner :=
  fun G _ _ M S L U hK hA hL hX hS _ => h G M S L U hK hA hL hX hS

instance : Coe KFactBlockFiveHeis KFactBlockFiveHeisInner := ⟨KFactBlockFiveHeis.inner⟩

section Over

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

theorem D2AlmostSimple.heisOver_of_simple [Fact p.Prime] (hK : D2AlmostSimple p X R A X₀ K)
    (hcard : Nat.card (R : Subgroup X) = p ^ 3)
    (hC : Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R)
    (hZ : Nat.card ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :
      Subgroup X) = p)
    (hcomm : ⁅(R : Subgroup X), (R : Subgroup X)⁆ =
      (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X))
    (hexp : ∀ r ∈ (R : Subgroup X), r ^ p = 1)
    (hlines : ∃ t, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
      ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
      (∀ x ∈ (R : Subgroup X),
        ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
          t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
      (∀ x ∈ (R : Subgroup X),
        ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
          t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
      ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup X,
        (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ F →
          F ≤ (R : Subgroup X) → F.relIndex (R : Subgroup X) = p →
            t ^ j ∉ Subgroup.normalizer (F : Set X))
    {U : Subgroup X} (hUX₀ : U ≤ X₀) (hX₀U : X₀ ≤ Subgroup.normalizer (U : Set X))
    (hRU : (R : Subgroup X) ≤ U)
    (hUs : ∀ W : Subgroup X, W ≤ U → U ≤ Subgroup.normalizer (W : Set X) → W = ⊥ ∨ W = U)
    (hCU : Subgroup.centralizer (U : Set X) = ⊥) : D2HeisOver p R X₀ := by
  have hp : p.Prime := Fact.out
  set Z : Subgroup X := (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X)
  have hdich : ∀ W : Subgroup X, W ≤ X₀ → X₀ ≤ Subgroup.normalizer (W : Set X) →
      W = ⊥ ∨ Z ≤ W := by
    intro W hWX₀ hX₀W
    have hWUn : U ≤ Subgroup.normalizer ((W ⊓ U : Subgroup X) : Set X) :=
      fun u hu => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hX₀W (hUX₀ hu), Subgroup.le_normalizer hu⟩
    rcases hUs (W ⊓ U) inf_le_right hWUn with hWU | hWU
    · left
      rw [eq_bot_iff]
      intro w hw
      have hwC : w ∈ Subgroup.centralizer (U : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have hc : u * w * u⁻¹ * w⁻¹ ∈ W ⊓ U := by
          refine ⟨W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hX₀W (hUX₀ hu)) w).mp hw)
            (W.inv_mem hw), ?_⟩
          have h1 : w * u⁻¹ * w⁻¹ ∈ U :=
            (Subgroup.mem_normalizer_iff.mp (hX₀U (hWX₀ hw)) u⁻¹).mp (U.inv_mem hu)
          simpa [mul_assoc] using U.mul_mem hu h1
        rw [hWU, Subgroup.mem_bot] at hc
        calc u * w = (u * w * u⁻¹ * w⁻¹) * w * u := by group
          _ = w * u := by rw [hc, one_mul]
      rw [hCU] at hwC
      exact hwC
    · exact Or.inr ((inf_le_left.trans hRU).trans (hWU ▸ inf_le_left))
  have hZp : IsPGroup p Z := R.isPGroup'.to_le inf_le_left
  have hZne : Z ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hZ
    exact hp.one_lt.ne hZ
  exact ⟨hcard, hK.normalizer_le_of_rank _ hK.sylow_le R.isPGroup' (by rw [hK.pRank_eq]), hC, hZ,
    hcomm, hexp, hdich, primeComplementCore_eq_bot_of_dichotomy hdich hZp hZne, hlines⟩

end Over

section Perfect

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.exists_perfect_over [Fact p.Prime] (h : D2Escape p P M A H R)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hexp : ∀ r ∈ R, r ^ p = 1) {U : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hUX₀ : U ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hX₀U : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ≤
      Subgroup.normalizer (U : Set (H ⧸ primeComplementCore (G := H) p)))
    (hUU : ⁅U, U⁆ = U) (hRU : (Rbar : Subgroup _) ≤ U) :
    ∃ J : Subgroup G, J ≤ H ⊓ M ∧ ⁅J, J⁆ = J ∧ R ≤ J ∧
      (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) = U := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set φ : ↥(H ⊓ M) →* H ⧸ primeComplementCore (G := H) p :=
    π.comp (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H)) with hφ
  have hX₀φ : ((H ⊓ M).subgroupOf H).map π = φ.range := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion inf_le_left k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  obtain ⟨W, hWU, hWW, hWmap, hmax⟩ :=
    AltData.exists_perfect_lift φ hUU (hX₀φ ▸ hUX₀)
  have hWn : W.Normal := by
    refine ⟨fun w hw y => ?_⟩
    have hy : φ y ∈ Subgroup.normalizer (U : Set (H ⧸ primeComplementCore (G := H) p)) :=
      hX₀U (hX₀φ ▸ ⟨y, rfl⟩)
    exact (Subgroup.mem_normalizer_iff.mp
      (AltData.mem_normalizer_of_perfect_lift φ hmax hWU hWW hy) w).mp hw
  have hJsub : (W.map (H ⊓ M).subtype).subgroupOf H =
      W.map (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H)) := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, hwx⟩
      exact ⟨w, hw, Subtype.ext hwx⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  refine ⟨W.map (H ⊓ M).subtype, Subgroup.map_subtype_le _, ?_, fun r hr => ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hWW]
  ·
    have hrK : r ∈ H ⊓ M := ⟨h.le_H hr, h.le_M hr⟩
    set r' : ↥(H ⊓ M) := ⟨r, hrK⟩
    have hrU : φ r' ∈ U := hRU (hRbar ▸ ⟨⟨r, h.le_H hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩)
    rw [← hWmap] at hrU
    obtain ⟨w, hw, hwr⟩ := hrU
    have hker : ∀ n : ↥(H ⊓ M), φ n = 1 → (orderOf n).Coprime p := by
      intro n hn
      have hnN : (n : G) ∈ GLBPrimeCore p H :=
        (mem_glbPrimeCore_iff_mk_eq_one (Subgroup.inclusion inf_le_left n)).mpr hn
      have hdvd : orderOf n ∣ Nat.card (GLBPrimeCore p H) := by
        rw [← Subgroup.orderOf_coe]
        exact Subgroup.orderOf_dvd_natCard _ hnN
      exact Nat.Coprime.coprime_dvd_left hdvd (glbPrimeCore_coprime p H).symm
    have hr'p : r' ^ p = 1 := Subtype.ext (by simpa using hexp r hr)
    exact ⟨r', mem_of_psi_eq φ W hker hr'p hw hwr.symm, rfl⟩
  · rw [hJsub, Subgroup.map_map]
    exact hWmap

end Perfect

section Components

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

omit [Finite G] in
theorem range_mk_comp_inclusion {J : Subgroup G} (hJH : J ≤ H) :
    ((QuotientGroup.mk' (primeComplementCore (G := H) p)).comp (Subgroup.inclusion hJH)).range =
      (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨Subgroup.inclusion hJH j, Subgroup.mem_subgroupOf.mpr j.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩

theorem AGLPair.barM_le_centralizer_or_le_primeCore (h : AGLPair p M H R) (hD1 : D1For G)
    (hα : KFactThreeOrFiveDvd)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hexp : ∀ r ∈ R, r ^ p = 1) {U : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hUs : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p), W ≤ U →
      U ≤ Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) → W = ⊥ ∨ W = U)
    {J : Subgroup G} (hJK : J ≤ H ⊓ M) (hJ : ⁅J, J⁆ = J) (hRJ : R ≤ J)
    (hJU : (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) = U)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) :
    barM M R ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      ∀ c ∈ centralizerBar M (hJK.trans inf_le_right) Lb, (c : G) ∈ GLBPrimeCore p H := by
  have hJM : J ≤ M := hJK.trans inf_le_right
  have hJH : J ≤ H := hJK.trans inf_le_left
  have hnorm := h.le_normalizer_component hD1 hα hB3 hJK hJ hLb
  have hCn := normal_centralizerBar hJM hnorm
  set C := centralizerBar M hJM Lb with hC
  set φ : ↥J →* H ⧸ primeComplementCore (G := H) p :=
    (QuotientGroup.mk' (primeComplementCore (G := H) p)).comp (Subgroup.inclusion hJH) with hφ
  have hφU : φ.range = U := (range_mk_comp_inclusion hJH).trans hJU
  have hCU : C.map φ ≤ U := by
    rw [← hφU]
    exact Subgroup.map_le_range φ C
  have hCUn : U ≤ Subgroup.normalizer ((C.map φ : Subgroup _) :
      Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [← hφU]
    rintro _ ⟨j, rfl⟩
    refine AltData.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨j * c * j⁻¹, hCn.conj_mem c hc j, by simp only [map_mul, map_inv]⟩
  have hker : ∀ n : ↥J, φ n = 1 → (orderOf n).Coprime p := by
    intro n hn
    have hnN : (n : G) ∈ GLBPrimeCore p H :=
      (mem_glbPrimeCore_iff_mk_eq_one (Subgroup.inclusion hJH n)).mpr hn
    have hdvd : orderOf n ∣ Nat.card (GLBPrimeCore p H) := by
      rw [← Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard _ hnN
    exact Nat.Coprime.coprime_dvd_left hdvd (glbPrimeCore_coprime p H).symm
  rcases hUs _ hCU hCUn with hbot | htop
  · right
    intro c hc
    have h1 : φ c = 1 := by
      have : φ c ∈ C.map φ := Subgroup.mem_map_of_mem φ hc
      rwa [hbot, Subgroup.mem_bot] at this
    exact (mem_glbPrimeCore_iff_mk_eq_one (Subgroup.inclusion hJH c)).mpr h1
  · left
    rintro _ ⟨⟨r, hrM⟩, hr, rfl⟩
    have hrR : r ∈ R := Subgroup.mem_subgroupOf.mp hr
    set r' : ↥J := ⟨r, hRJ hrR⟩
    have hφr : φ r' ∈ C.map φ := by
      rw [htop, ← hφU]
      exact ⟨r', rfl⟩
    obtain ⟨c, hc, hcr⟩ := hφr
    have hr'p : r' ^ p = 1 := Subtype.ext (by simpa using hexp r hrR)
    exact mem_of_psi_eq φ C hker hr'p hc hcr.symm

theorem D2HeisDataCore.false_of_faithful_weakSBlock_inner {Z : Subgroup G}
    (hdata : D2HeisDataCore 5 M H R Z) (h85 : Asc81bEightFive) (hNX : NoXBlockFor G)
    (hF : KFactBlockFiveHeisInner) {J : Subgroup G} (hJM : J ≤ M) (hRJ : R ≤ J)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hb : BlockInnerNormalizerAt M (pCoreOf 2 H) L)
    (hsup : barM M J ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hbad : ∀ c ∈ centralizerBar M hJM (barM M L), (c : G) ∈ GLBPrimeCore 5 H) : False := by
  have hpair := hdata.pair
  have hRM : R ≤ M := hpair.le_M
  have hKeq := hpair.inf_eq_inf_normalizer_twoCore
  have hRS : R ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    rw [hpair.normalizer_twoCore_H]
    exact hpair.le_H
  have hRN : R ⊓ GLBPrimeCore 5 H = ⊥ :=
    inf_eq_bot_of_isPGroup Nat.prime_five hpair.isPGroup_R (glbPrimeCore_coprime 5 H)
  have hnab : ¬ IsMulCommutative R := by
    intro hc
    have hle : R ≤ Subgroup.centralizer (R : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : R) ⟨x, hx⟩)
    have h1 : ⁅R, R⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    have h2 := hdata.heis.1
    rw [← hdata.heis.2.1, h1, Subgroup.card_bot] at h2
    norm_num at h2
  have hfaith : centralizerBar M hRM (barM M L) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have hcN := hbad ⟨c, hRJ c.2⟩ hc
    have hmem : (c : G) ∈ R ⊓ GLBPrimeCore 5 H := ⟨c.2, hcN⟩
    rw [hRN, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have h3 := hF G M (pCoreOf 2 H) L R hpair.isKGroup.1 hpair.asc81bHyp hL
    (hpair.nineThree_not_one h85 hNX hL).1 (hpair.not_isSylowTwoOf_inf h85 hNX hL) hb hRM hRS
    ((barM_mono hRJ).trans hsup) hdata.card_R hnab hfaith
  have hPK : blockPL M (pCoreOf 2 H) L ≤ barM M (H ⊓ M) :=
    barM_mono (by rw [hKeq]; exact le_inf (inf_le_right.trans hL.le) inf_le_left)
  have h3' := (h3.trans (SectionRank.pRank_mono (by norm_num) hPK)).trans
    (pRank_barM_le Nat.prime_five (by decide) M (H ⊓ M) inf_le_right)
  have h2 := hdata.pRank_le
  omega

theorem AGLPair.false_of_faithful_le_primeCore [Fact p.Prime] (h : AGLPair p M H R)
    (hexp : ∀ r ∈ R, r ^ p = 1) (hR1 : R ≠ ⊥) {J : Subgroup G} (hJM : J ≤ M) (hRJ : R ≤ J)
    {L : Subgroup G} (hLM : L ≤ M) (hLN : L ≤ GLBPrimeCore p H)
    (hsup : barM M J ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hbad : ∀ c ∈ centralizerBar M hJM (barM M L), (c : G) ∈ GLBPrimeCore p H) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨ρ, hρ⟩ := exists_hom_centerQuotient (barM M L) (barElt M hJM)
    (fun j => hsup (barElt_mem_barM hJM j))
  obtain ⟨⟨r, hrR⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR1
  have hRN : R ⊓ GLBPrimeCore p H = ⊥ :=
    inf_eq_bot_of_isPGroup hp h.isPGroup_R (glbPrimeCore_coprime p H)
  set r' : ↥J := ⟨r, hRJ hrR⟩
  have hρr : ρ r' ≠ 1 := by
    intro h1
    have hrN := hbad r' ((hρ r').mp h1)
    have hmem : r ∈ R ⊓ GLBPrimeCore p H := ⟨hrR, hrN⟩
    rw [hRN, Subgroup.mem_bot] at hmem
    exact hr1 (Subtype.ext hmem)
  have hord : orderOf (ρ r') = p := by
    have hr'p : r' ^ p = 1 := Subtype.ext (by simpa using hexp r hrR)
    have hdvd : orderOf (ρ r') ∣ p :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hr'p, map_one])
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hρr
    · exact h1
  have h1 : orderOf (ρ r') ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    orderOf_dvd_natCard _
  have h2 : Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∣ Nat.card ↥(barM M L) :=
    Subgroup.index_dvd_card _
  have h3 : Nat.card ↥(barM M L) ∣ Nat.card ↥L := by
    have := Subgroup.card_range_dvd (barElt M hLM)
    rwa [range_barElt hLM] at this
  have h4 : Nat.card ↥L ∣ Nat.card (GLBPrimeCore p H) := Subgroup.card_dvd_of_le hLN
  rw [hord] at h1
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (glbPrimeCore_coprime p H)
    (h1.trans (h2.trans (h3.trans h4))))

theorem AGLPair.map_inf_le_normalizer_of_normal_sup (h : AGLPair p M H R)
    (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal) :
    ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      Subgroup.normalizer ((((R.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p))) : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hQH : pCoreOf 2 M ≤ H :=
    h.twoCore_M_le.trans (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 H)
  have hRQM : R ⊔ pCoreOf 2 M ≤ M :=
    sup_le h.le_M (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 M)
  have hmap : ((R ⊔ pCoreOf 2 M).subgroupOf H).map π = (R.subgroupOf H).map π := by
    rw [Subgroup.subgroupOf_sup h.le_H hQH, Subgroup.map_sup]
    have hQ : ((pCoreOf 2 M).subgroupOf H).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro q hq
      exact (mem_glbPrimeCore_iff_mk_eq_one q).mp
        (h.twoCore_M_le_glbPrimeCore (Subgroup.mem_subgroupOf.mp hq))
    rw [hQ, sup_bot_eq]
  rintro _ ⟨k, hk, rfl⟩
  have hkM : (k : G) ∈ M := (Subgroup.mem_subgroupOf.mp hk).2
  refine AltData.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [← hmap] at hx ⊢
  obtain ⟨r, hr, rfl⟩ := hx
  refine ⟨k * r * k⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr ⊢
  have hrM : (r : G) ∈ M := hRQM hr
  have hc := hRQ.conj_mem ⟨r, hrM⟩ (Subgroup.mem_subgroupOf.mpr hr) ⟨k, hkM⟩
  rw [Subgroup.mem_subgroupOf] at hc
  simpa using hc

end Components

@[expose] def D2HSFiveCaseTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (P : Sylow 5 G) (M A H R : Subgroup G), D2Escape 5 P M A H R → D2EscapeMax 5 P M R →
    5 ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 5)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)) →
      D2AlmostSimple 5 (H ⧸ primeComplementCore (G := H) 5) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5))) K →
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group) →
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)) ≠
        Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) :
          Set (H ⧸ primeComplementCore (G := H) 5))) →
      ∀ L : Subgroup G, IsTwoPrimeComponent M L → L ≤ H ⊓ M → ¬ L ≤ GLBPrimeCore 5 H → False

theorem false_of_hsFiveNonBorel {G : Type} [Group G] [Finite G] (hHS : KFactHSFiveOver)
    (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hF : KFactBlockFiveHeisInner) (hglob : AGLGlobal G)
    (hD1 : D1For G) (hNX : NoXBlockFor G) {P : Sylow 5 G} {M A H R : Subgroup G}
    (hesc : D2Escape 5 P M A H R) {Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 5)}
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
    (hK : D2AlmostSimple 5 (H ⧸ primeComplementCore (G := H) 5) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5))) K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group))
    (hne : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)) ≠
      Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) :
        Set (H ⧸ primeComplementCore (G := H) 5))))
    (hII : ∀ L : Subgroup G, IsTwoPrimeComponent M L → L ≤ H ⊓ M → ¬ L ≤ GLBPrimeCore 5 H →
      False) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hNX₀ : Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5))) :
      Set (H ⧸ primeComplementCore (G := H) 5)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)) :=
    hK.normalizer_le_of_rank _ hK.sylow_le Rbar.isPGroup' (by rw [hK.pRank_eq])
  obtain ⟨-, U, hUX₀, hX₀U, hUU, hRU, hUs, -, hCU, -, -⟩ :=
    hHS _ K hK.normal hK.centralizer_eq_bot he Rbar _ hNX₀ hK.ne_top hne
  obtain ⟨-, hcard, hC, hZ, hcomm, hexp, -, hlines⟩ :=
    hloc _ K hK.normal hK.centralizer_eq_bot he 5 rfl Rbar
  have hover := hK.heisOver_of_simple hcard hC hZ hcomm hexp hlines hUX₀ hX₀U hRU hUs hCU
  have hdata := hesc.heisDataCore_of_over hglob hRbar hK hover
  have hpair := hdata.pair
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L :=
    fun L hL => hpair.blockHasThree h85 h86 h93 hNX hK2 hC3 hK5 hL
  have hRexp : ∀ r ∈ R, r ^ 5 = 1 := hdata.heis.2.2
  obtain ⟨J, hJK, hJ, hRJ, hJU⟩ := hesc.exists_perfect_over hRbar hRexp hUX₀ hX₀U hUU hRU
  have hJM : J ≤ M := hJK.trans inf_le_right
  have hR1 : R ≠ ⊥ := by
    intro h0
    have h1 := hdata.card_R
    rw [h0, Subgroup.card_bot] at h1
    norm_num at h1
  have hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M R ≤ Subgroup.centralizer (Lbar : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro Lbar hLbar
    rcases hpair.barM_le_centralizer_or_le_primeCore hD1 hα hB3 hRexp hUs hJK hJ hRJ hJU hLbar
      with hgood | hbad
    · exact hgood
    exfalso
    have hsup := hpair.le_sup_centralizer_component hD1 hα hSch hB3 hJK hJ hLbar
    obtain ⟨L, hL2, rfl, hL⟩ := hpair.exists_weakSBlock_or_le_inf hLbar
    rcases hL with hblock | hLK
    · exact hdata.false_of_faithful_weakSBlock_inner h85 hNX hF hJM hRJ hblock
        (hpair.blockInnerNormalizerAt h84 h86 hNX hblock) hsup hbad
    · by_cases hLN : L ≤ GLBPrimeCore 5 H
      · exact hpair.false_of_faithful_le_primeCore hRexp hR1 hJM hRJ hL2.le hLN hsup hbad
      · exact hII L hL2 hLK hLN
  have hRQ := hdata.normal_sup_of_components hD1 le_rfl h84 hNX hcomp
  refine hne (le_antisymm ?_ hNX₀)
  rw [hRbar]
  exact hpair.map_inf_le_normalizer_of_normal_sup hRQ

theorem d2HSFiveNonBorel_of (hHS : KFactHSFiveOver)
    (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hF : KFactBlockFiveHeisInner) (hII : D2HSFiveCaseTwo) :
    D2HSFiveNonBorel := by
  intro G _ _ hglob hD1 P M A H R hesc hmax hβ Rbar K hRbar hK he hne
  exact false_of_hsFiveNonBorel hHS hloc hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hF hglob.toAGLGlobal
    hD1 (hD2.noXBlockFor hglob.toD1Global) hesc hRbar hK he hne fun L hL2 hLK hLN =>
      hII G hglob hD1 P M A H R hesc hmax hβ Rbar K hRbar hK he hne L hL2 hLK hLN

end CFSG.AGLEmbeddingD2
