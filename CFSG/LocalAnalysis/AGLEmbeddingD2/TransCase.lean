module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.TransBorel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisCaseFor
import CFSG.LocalAnalysis.AGLEmbeddingD2.CompetitorR
import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.TransMSide

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem D2TransData.survivorData [Fact p.Prime] {M H R X A : Subgroup G}
    (h : D2TransData p M H R X A) : AGLSurvivorData p M H R X where
  pair := h.pair
  le_R := h.le_A.trans h.A_le
  ne_bot := by
    intro hbot
    have hc := h.card
    rw [hbot, Subgroup.card_bot] at hc
    exact (Fact.out : p.Prime).one_lt.ne hc
  normal_dichotomy := h.normal_dichotomy
  centralizer_le := h.centralizer_le

section Escape

variable {P : Sylow p G} {M A H R : Subgroup G}

theorem D2Escape.not_le_of_nclIn_le_of_le (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    {X : Subgroup G} (hXR : X ≤ R) (hX : X ≠ ⊥) {H' : Subgroup G} (hJH' : nclIn H X ≤ H') :
    ¬ H' ≤ M := by
  intro hH'M
  obtain ⟨Rbar, K, -, hK⟩ := h.almostSimple hglob
  have hXH : X ≤ H := hXR.trans h.le_H
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  have hJn : (((nclIn H X).subgroupOf H).map π).Normal :=
    (nclIn_normal H X).map π (QuotientGroup.mk'_surjective _)
  have hJ1 : ((nclIn H X).subgroupOf H).map π ≠ ⊥ := by
    intro hbot
    have hle : (X.subgroupOf H).map π ≤ ⊥ :=
      hbot ▸ Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_nclIn hXH))
    have hc := h.card_map_eq hXR
    rw [le_bot_iff.mp hle, Subgroup.card_bot] at hc
    exact hX (Subgroup.eq_bot_of_card_eq X hc.symm)
  apply hK.not_le
  refine (hK.le_of_normal hJn hJ1).trans (Subgroup.map_mono (Subgroup.subgroupOf_mono H ?_))
  exact le_inf (nclIn_le_self H X) (hJH'.trans hH'M)

theorem D2Escape.isCyclic_of_le_nclIn [Fact p.Prime]
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKn : K.Normal)
    (hcyc : ∀ T : Sylow p K, IsCyclic T) {z : H}
    (hzK : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈ K) :
    ∀ Y : Subgroup G, Y ≤ nclIn H (Subgroup.zpowers (z : G)) → IsPGroup p Y → IsCyclic Y := by
  intro Y hYJ hYp
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hYH : Y ≤ H := hYJ.trans (nclIn_le_self H _)
  set T : Subgroup H := Y.subgroupOf H with hT
  have hTp : IsPGroup p T := hYp.comap_subtype
  have hJK : ((nclIn H (Subgroup.zpowers (z : G))).subgroupOf H).map π ≤ K := by
    have hsub : (nclIn H (Subgroup.zpowers (z : G))).subgroupOf H =
        Subgroup.normalClosure (((Subgroup.zpowers (z : G)).subgroupOf H : Subgroup H) : Set H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [hsub, Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    have : y = z ^ n := Subtype.ext (by simpa using hn.symm)
    rw [this, map_zpow]
    exact K.zpow_mem hzK n
  have hTK : T.map π ≤ K :=
    (Subgroup.map_mono (Subgroup.subgroupOf_mono H hYJ)).trans hJK
  have hTKp : IsPGroup p ((T.map π).subgroupOf K) := (hTp.map π).comap_subtype
  obtain ⟨S, hS⟩ := hTKp.exists_le_sylow
  have := hcyc S
  have hcycTK : IsCyclic ((T.map π).subgroupOf K) :=
    isCyclic_of_injective (Subgroup.inclusion hS) (Subgroup.inclusion_injective hS)
  have hcycT' : IsCyclic (T.map π) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTK).surjective
  have hinj : Function.Injective (π.subgroupMap T) := fun a b hab =>
    Subtype.ext (eq_of_mk_eq_of_mem hYp (Subgroup.mem_subgroupOf.mp a.2)
      (Subgroup.mem_subgroupOf.mp b.2) (congrArg Subtype.val hab))
  have hcycT : IsCyclic T := isCyclic_of_injective _ hinj
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hYH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hYH).surjective

theorem D2Escape.transMember [Fact p.Prime] (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    {zb : H ⧸ primeComplementCore (G := H) p}
    (hB : D2TransBorel p Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K zb) :
    AGLSurvivorData p M H R (R ⊓ Subgroup.centralizer (R : Set G)) ∧
      Nat.card (R ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p ∧
      ∀ Y : Subgroup G, Y ≤ nclIn H (R ⊓ Subgroup.centralizer (R : Set G)) → IsPGroup p Y →
        IsCyclic Y := by
  obtain ⟨z, -, hz, hdata, hcen⟩ := h.exists_transData_of_borel hglob hRbar hB
  rw [← hcen]
  exact ⟨hdata.survivorData, hdata.card,
    D2Escape.isCyclic_of_le_nclIn hK.normal hB.cyclic (by rw [hz]; exact hB.mem_K)⟩

theorem D2Escape.pCore_ne_bot_of_transBorel [Fact p.Prime] (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (h : D2Escape p P M A H R) (hglob : AGLGlobal G) (hD1 : D1For G) (hX : NoXBlockFor G)
    (hp5 : 5 ≤ p) {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    {zb : H ⧸ primeComplementCore (G := H) p}
    (hB : D2TransBorel p Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K zb) :
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥ := by
  obtain ⟨z, -, hz, hdata, -⟩ := h.exists_transData_of_borel hglob hRbar hB
  have hXK : ((Subgroup.zpowers (z : G)).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    have : y = z ^ n := Subtype.ext (by simpa using hn.symm)
    rw [this, map_zpow, hz]
    exact K.zpow_mem hB.mem_K n
  exact hdata.pCore_ne_bot_of_components hD1 hp5 h84 hX
    (fun L hL hLK => h.barM_le_centralizer_of_le_inf_of_simple hdata.pair
      hdata.perfect_le hK (hdata.le_A.trans hdata.A_le) hXK hD1 hp5 hα hSch hL hLK)
    (fun L hL => hdata.barM_le_centralizer_of_weakSBlock hD1 h84 h85 h86 h93 hX hK2 hC3 hK5 hKin
      hKP hC3p hK5p hp5 hL)

end Escape

@[expose] def D2TransMSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (P : Sylow p G) (M A H R : Subgroup G),
      D2Escape p P M A H R → D2EscapeMax p P M R → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (zb : H ⧸ primeComplementCore (G := H) p),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      D2TransBorel p Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K zb →
      CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

theorem d2TransMSide_of (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime) : D2TransMSide := by
  intro G _ _ hglob hD1 p _ hp5 P M A H R hesc _ _ Rbar K zb hRbar hK hB
  exact hesc.pCore_ne_bot_of_transBorel hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKin hKP hC3p hK5p
    hglob.toAGLGlobal hD1 (hD2.noXBlockFor hglob.toD1Global) hp5 hRbar hK hB

section Closure

variable {P : Sylow p G} {M A H R : Subgroup G}

theorem D2Escape.false_of_transBorelFor [Fact p.Prime] (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hglob : AGLGlobal G) (hD1p : D1At G p)
    (hX : NoXBlockFor G) (hmax : D2EscapeMax p P M R)
    (hcomp : ∀ H' : Subgroup G, D2Escape p P M A H' R →
      ∃ (Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p))
        (K' : Subgroup (H' ⧸ primeComplementCore (G := H') p))
        (zb' : H' ⧸ primeComplementCore (G := H') p),
        (Rbar' : Subgroup _) = (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore p)) ∧
        D2AlmostSimple p _ Rbar' ((A.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore p)))
          (((H' ⊓ M).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore p))) K' ∧
        D2TransBorel p Rbar' ((A.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore p)))
          (((H' ⊓ M).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore p))) K' zb')
    (hO : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥) (h : D2Escape p P M A H R) : False := by
  have hmem : ∀ H' : Subgroup G, D2Escape p P M A H' R →
      AGLSurvivorData p M H' R (R ⊓ Subgroup.centralizer (R : Set G)) ∧
        Nat.card (R ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p ∧
        ∀ Y : Subgroup G, Y ≤ nclIn H' (R ⊓ Subgroup.centralizer (R : Set G)) → IsPGroup p Y →
          IsCyclic Y := fun H' h' => by
    obtain ⟨Rbar', K', zb', hRbar', hK', hB'⟩ := hcomp H' h'
    exact h'.transMember hglob hRbar' hK' hB'
  refine false_of_aglSurvivorsOn h84 hCGT hX (C := fun H' => D2Escape p P M A H' R)
    (X := R ⊓ Subgroup.centralizer (R : Set G)) (fun H' h' => (hmem H' h').1) hO ?_ h
  intro H₁ h₁ H' hH' hJH' hRH'
  obtain ⟨hsurv, hcard, hcyc⟩ := hmem H₁ h₁
  have hH'M := h₁.not_le_of_nclIn_le_of_le hglob inf_le_left hsurv.ne_bot hJH'
  exact ⟨h₁.eq_of_maxTwoLocal_R hmax hD1p hH' hRH' hH'M,
    nclIn_le_nclIn_of_isCyclic (inf_le_left.trans h₁.le_H) hcard hcyc hJH'⟩

end Closure

section Five

variable {P : Sylow p G} {M A H R : Subgroup G}

theorem D2HeisLocalEqAt.pow_eq_one {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : D2HeisLocalEqAt i Pp) {X : Type} [Group X] [Finite X] {q : ℕ} (hq : Pp q)
    {S : Sylow q X} {B X₀ K : Subgroup X} (hK : D2AlmostSimple q X S B X₀ K)
    (he : Nonempty (K ≃* i.Group)) : ∀ r ∈ (S : Subgroup X), r ^ q = 1 :=
  (h X K hK.normal hK.centralizer_eq_bot he q hq S).2.2.2.2.2.1

omit [Finite G] in
theorem exists_pow_ne_one_of_map {Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hRbar : Rbar = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hb : ∃ b ∈ Rbar, b ^ p ≠ 1) : ∃ b ∈ R, b ^ p ≠ 1 := by
  obtain ⟨_, hbR, hb⟩ := hb
  rw [hRbar] at hbR
  obtain ⟨b, hb', rfl⟩ := hbR
  refine ⟨b, Subgroup.mem_subgroupOf.mp hb', fun h1 => hb ?_⟩
  have : b ^ p = 1 := Subtype.ext (by simpa using h1)
  rw [← map_pow, this, map_one]

theorem D2Escape.false_of_pow_eq_one [Fact p.Prime] (h : D2Escape p P M A H R)
    {Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hRbar : Rbar = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hb : ∃ b ∈ R, b ^ p ≠ 1) (hexp : ∀ r ∈ Rbar, r ^ p = 1) : False := by
  obtain ⟨b, hbR, hb⟩ := hb
  have hbH : b ∈ H := h.le_H hbR
  have h1 := hexp _ (hRbar ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbR) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨b, hbH⟩ ∈ Rbar)
  rw [← map_pow] at h1
  have := eq_of_mk_eq_of_mem h.isPGroup (a := ⟨b, hbH⟩ ^ p) (b := 1)
    (by simpa using R.pow_mem hbR p) R.one_mem (by rw [h1, map_one])
  exact hb (by simpa using congrArg Subtype.val this)

theorem D2Escape.false_of_A_eq_of_pow (h : D2Escape p P M A H R) (hAR : A = R)
    (hb : ∃ b ∈ R, b ^ p ≠ 1) : False := by
  obtain ⟨b, hbR, hb⟩ := hb
  exact hb (h.elem.2 b (hAR ▸ hbR))

theorem D2Escape.transBorel_of_exp (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (hKU2 : KFactUnitarySylowStructure)
    (hSzB : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2TransBorelAt (.lie d) fun p => p = 5)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusBorelAt (.lie d) fun p => p = 5)
    (hHS : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hMcL : D2HeisLocalEqAt (.sporadic .McL) fun p => p = 5)
    {P : Sylow 5 G}
    (hSpor : ∀ s : TauCeti.SporadicName, s ≠ .HS → s ≠ .McL →
      D2IndexCaseFor 5 P M A R (.sporadic s))
    (hglob : AGLGlobal G) (h : D2Escape 5 P M A H R) (hb : ∃ b ∈ R, b ^ 5 ≠ 1) :
    ∃ (Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 5))
      (zb : H ⧸ primeComplementCore (G := H) 5),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)) ∧
      D2AlmostSimple 5 _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5))) K ∧
      D2TransBorel 5 Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5))) K zb := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Rbar, K, hRbar, hK⟩ := h.almostSimple hglob
  obtain ⟨i, hi⟩ := hK.catalog
  have hnexp : (∀ r ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)), r ^ 5 = 1) →
      False := fun hexp =>
    h.false_of_pow_eq_one hRbar hb hexp
  have hnA : A = R → False := fun hAR => h.false_of_A_eq_of_pow hAR hb
  cases i with
  | cyclic q hq => exact (d2IndexCaseFor_cyclic q hq H h Rbar K hRbar hK hi).elim
  | sporadic s =>
    exfalso
    by_cases h1 : s = .HS
    · subst h1
      exact hnexp (hHS.pow_eq_one rfl hK hi)
    by_cases h2 : s = .McL
    · subst h2
      exact hnexp (hMcL.pow_eq_one rfl hK hi)
    exact hSpor s h1 h2 H h Rbar K hRbar hK hi
  | alternating n hn =>
    exfalso
    obtain ⟨e⟩ := hi
    have hn2 : n = 2 * 5 := hK.eq_two_mul_of_alternating hn e
    subst hn2
    have hRA := hK.sylow_eq_of_alternating le_rfl e
    rw [hRbar] at hRA
    exact hnA (h.A_eq_of_map_eq hRA)
  | lie d =>
    obtain ⟨e⟩ := hi
    by_cases hchar : 5 = d.1.characteristic
    · exfalso
      obtain ⟨q, hqp, hq⟩ := hK.lieChar_cases hrank hL3 d e hchar
      rcases hq with ⟨hq2, hd⟩ | ⟨hq1, hd⟩
      · obtain ⟨e'⟩ :=
          nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 5) (n := 2) ⟨q, hd, hqp, hq2⟩
        exact hnA (h.A_eq_of_psl2 hRbar hK (e.trans e'))
      · obtain ⟨hdu, hnu⟩ := isUnitaryIndex_of_twistedA hqp hq1 hd
        exact hnexp (hK.commutator_eq_of_u3 hKU2 hdu hnu e).2
    · by_cases hexcp : IsD2SeitzException 5 d.1
      · rcases hexcp with ⟨h53, -⟩ | ⟨-, hd | hd⟩
        · norm_num at h53
        · exfalso
          have hT := hTits d hd _ 5 rfl Rbar _ _ K hK ⟨e⟩
          exact hnA (h.A_eq_of_map_eq (hRbar.symm.trans hT.eq_A))
        · obtain ⟨zb, hB⟩ := hSzB d hd _ 5 rfl Rbar _ _ K hK ⟨e⟩
          exact ⟨Rbar, K, zb, hRbar, hK, hB⟩
      · exact (hK.false_of_seitzCross hS d e hchar hexcp).elim

end Five

theorem d2IndexCaseAt_sz32_five (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (hKU2 : KFactUnitarySylowStructure) (hMS : D2TransMSide)
    (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (hSzB : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2TransBorelAt (.lie d) fun p => p = 5)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusBorelAt (.lie d) fun p => p = 5)
    (hHS : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hMcL : D2HeisLocalEqAt (.sporadic .McL) fun p => p = 5)
    (hSpor : ∀ s : TauCeti.SporadicName, s ≠ .HS → s ≠ .McL →
      D2IndexCaseAt (.sporadic s) fun p => p = 5)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .suzuki 2) :
    D2IndexCaseAt (.lie d) fun p => p = 5 := by
  intro G _ _ hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he
  subst hp
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨zb, hB⟩ := hSzB d hd _ 5 rfl Rbar _ _ K hK he
  have hb : ∃ b ∈ R, b ^ 5 ≠ 1 := exists_pow_ne_one_of_map hRbar hB.exp
  exact hesc.false_of_transBorelFor h84 hCGT hglob.toAGLGlobal (hD1.at hβ)
    (hD2.noXBlockFor hglob.toD1Global) hmax
    (fun H' h' => h'.transBorel_of_exp hrank hL3 hS hKU2 hSzB hTits hHS hMcL
      (fun s h1 h2 => (hSpor s h1 h2).for hglob hD1 rfl hmax hβ) hglob.toAGLGlobal hb)
    (hMS G hglob hD1 5 (le_refl 5) P M A H R hesc hmax hβ Rbar K zb hRbar hK hB)

end CFSG.AGLEmbeddingD2
