module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarOn
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockClosure
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Survivor

variable {G : Type} [Group G] [Finite G]

@[expose] def pCorePreimage (p : ℕ) (M : Subgroup G) : Subgroup G :=
  ((CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map
    M.subtype

structure D1SurvivorData (p : ℕ) (P : Sylow p G) (M H R X : Subgroup G) : Prop where
  ph3 : D1PhaseThree p P M H R
  le_R : X ≤ R
  ne_bot : X ≠ ⊥
  normal_dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore p H ∨ X ≤ Y
  centralizer_le : ∀ d ∈ H ⊓ M, (∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ GLBPrimeCore p H) →
    d ∈ R ⊔ GLBPrimeCore p H

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

open CFSG.AGLEmbeddingD2 (NoXBlockFor)

omit [Finite G] in
theorem pCorePreimage_le (p : ℕ) (M : Subgroup G) : pCorePreimage p M ≤ M :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem pCorePreimage_subgroupOf (p : ℕ) (M : Subgroup G) :
    (pCorePreimage p M).subgroupOf M =
      (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

omit [Finite G] in
theorem le_normalizer_pCorePreimage (p : ℕ) (M : Subgroup G) :
    M ≤ Subgroup.normalizer (pCorePreimage p M : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (pCorePreimage_le p M)).mp
    (pCorePreimage_subgroupOf p M ▸ Subgroup.Normal.comap inferInstance _)

theorem TwoLocalPhaseThree.pCorePreimage_le_inf {M H : Subgroup G} (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (hp : p.Prime) (hp2 : p ≠ 2) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) : pCorePreimage p M ≤ H ⊓ M := by
  have : Fact p.Prime := ⟨hp⟩
  set Q := pCoreOf 2 M with hQdef
  set Ob := CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) with hOb
  have hkerQ : ∀ m : M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) m = 1 → (m : G) ∈ Q :=
    coe_mem_pCoreOf_two_of_mk_eq_one
  have hObOdd : Ob ≤ CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) := by
    refine le_sSup ⟨inferInstance, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p)
      (G := ↥M ⧸ CFSG.pCore 2 ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr
      (fun h2 => hp2 h2.symm))
  have hcent := hObOdd.trans (h.oddCore_le_centralizer hK h84 hD2)
  have hYS : pCorePreimage p M ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    refine le_normalizer_of_forall_map_conj_le fun g hg => ?_
    obtain ⟨m, hm, rfl⟩ := hg
    rintro _ ⟨s, hs, rfl⟩
    have hsM : s ∈ M := h.twoCore_le hs
    have hsbar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨s, hsM⟩ ∈ barM M (pCoreOf 2 H) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
    have hcomm := Subgroup.mem_centralizer_iff.mp (hcent hm) _ hsbar
    have hc : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨s, hsM⟩ * m * (⟨s, hsM⟩)⁻¹ * m⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hq : ((⟨s, hsM⟩ * m * (⟨s, hsM⟩)⁻¹ * m⁻¹ : M) : G) ∈ Q := hkerQ _ hc
    have hQS : Q ≤ pCoreOf 2 H := h.twoCore_M_le h.twoCore_inf
    have heq : (MulAut.conj (m : G)).toMonoidHom s =
        (((⟨s, hsM⟩ * m * (⟨s, hsM⟩)⁻¹ * m⁻¹ : M) : G))⁻¹ * s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
    change (MulAut.conj (m : G)).toMonoidHom s ∈ pCoreOf 2 H
    rw [heq]
    exact (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem (hQS hq)) hs
  exact fun y hy => h.inf_eq_inf_normalizer_twoCore ▸
    ⟨pCorePreimage_le p M hy, hYS hy⟩

theorem D1PhaseThree.pCorePreimage_le_inf (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) : pCorePreimage p M ≤ H ⊓ M :=
  h.toTwoLocalPhaseThree.pCorePreimage_le_inf h.isKGroup.1 h.prime h.ne_two h84 (hD2 G h.glob)

theorem pCorePreimage_inf_glbPrimeCore_le (hp : p.Prime) (M H : Subgroup G) :
    pCorePreimage p M ⊓ GLBPrimeCore p H ≤ pCoreOf 2 M := by
  have : Fact p.Prime := ⟨hp⟩
  rintro y ⟨⟨m', hm', hmm'⟩, hyN⟩
  have hmm'' : (m' : G) = y := hmm'
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := ↥M ⧸ CFSG.pCore 2 ↥M)
    ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m', hm'⟩
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m' ^ p ^ k = 1 := congrArg Subtype.val hk
  have hord1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m') ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one hk'
  have hord2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m') ∣
      Nat.card (GLBPrimeCore p H) :=
    (orderOf_map_dvd _ _).trans (by
      rw [← Subgroup.orderOf_coe, hmm'']
      exact Subgroup.orderOf_dvd_natCard _ hyN)
  have hcop : Nat.Coprime (p ^ k) (Nat.card (GLBPrimeCore p H)) :=
    Nat.Coprime.pow_left k (glbPrimeCore_coprime p H)
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m') = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  rw [← hmm'']
  exact coe_mem_pCoreOf_two_of_mk_eq_one m' (orderOf_eq_one_iff.mp h1)

theorem D1PhaseThree.pCorePreimage_inf_le (h : D1PhaseThree p P M H R) :
    pCorePreimage p M ⊓ GLBPrimeCore p H ≤ pCoreOf 2 M :=
  pCorePreimage_inf_glbPrimeCore_le h.prime M H

theorem pCorePreimage_not_le_glbPrimeCore (hp : p.Prime) {M H : Subgroup G}
    (hO : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥) :
    ¬ pCorePreimage p M ≤ GLBPrimeCore p H := by
  intro hle
  apply hO
  rw [eq_bot_iff]
  intro o ho
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) o
  have hmY : (m : G) ∈ pCorePreimage p M := ⟨m, ho, rfl⟩
  obtain ⟨m', hm', hmm'⟩ := pCorePreimage_inf_glbPrimeCore_le hp M H ⟨hmY, hle hmY⟩
  have : m' = m := Subtype.ext hmm'
  subst this
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr hm')

theorem D1PhaseThree.pCorePreimage_not_le (h : D1PhaseThree p P M H R)
    (hO : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥) :
    ¬ pCorePreimage p M ≤ GLBPrimeCore p H :=
  pCorePreimage_not_le_glbPrimeCore h.prime hO

theorem TwoLocalPhaseThree.commutator_pCorePreimage_le {M H : Subgroup G}
    (h : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M) (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : GLBPrimeCore p H ≤ M) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) :
    ⁅GLBPrimeCore p H, pCorePreimage p M⁆ ≤ pCoreOf 2 M :=
  (commutator_le_inf_of_le_normalizer le_rfl (hN.trans
    (le_normalizer_pCorePreimage p M)) (((h.pCorePreimage_le_inf hK hp hp2 h84 hD2).trans
      inf_le_left).trans (le_normalizer_glbPrimeCore p H))).trans
    ((inf_comm _ _).le.trans (pCorePreimage_inf_glbPrimeCore_le hp M H))

theorem D1PhaseThree.commutator_pCorePreimage_le (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) :
    ⁅GLBPrimeCore p H, pCorePreimage p M⁆ ≤ pCoreOf 2 M :=
  h.toTwoLocalPhaseThree.commutator_pCorePreimage_le h.isKGroup.1 h.prime h.ne_two
    h.primeCore_le h84 (hD2 G h.glob)

theorem TwoLocalPhaseThree.inf_sup_twoCore_eq {M H R : Subgroup G} (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (hp : p.Prime) (hp2 : p ≠ 2)
    (hRS : ∃ T : Sylow p H, (T : Subgroup H).map H.subtype = R) (hRK : R ≤ H ⊓ M)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) :
    (R ⊓ pCorePreimage p M) ⊔ pCoreOf 2 M = pCorePreimage p M := by
  have : Fact p.Prime := ⟨hp⟩
  set Y := pCorePreimage p M with hYdef
  set Q := pCoreOf 2 M with hQdef
  have hYK := h.pCorePreimage_le_inf hK hp hp2 h84 hD2
  have hYM : Y ≤ M := pCorePreimage_le p M
  have hQM : Q ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hQY : Q ≤ Y := by
    intro q hq
    refine ⟨⟨q, hQM hq⟩, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨q, hQM hq⟩ ∈ CFSG.pCore p _
    rw [(mk_eq_one_iff_coe_mem_pCoreOf _).mpr hq]
    exact Subgroup.one_mem _
  have hle : (R ⊓ Y) ⊔ Q ≤ Y := sup_le inf_le_right hQY
  have hRK : CFSG.ABGLocalTools.IsSylowOf p R (H ⊓ M) := by
    have hRH : CFSG.ABGLocalTools.IsSylowOf p R H := hRS
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hRH ⊢
    refine ⟨hRK, hRH.2.1, fun hdvd => hRH.2.2 ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex R (H ⊓ M) H hRK inf_le_left]
    exact hdvd.mul_right _
  have hXY : CFSG.ABGLocalTools.IsSylowOf p (R ⊓ Y) Y :=
    hRK.inf_of_le_normalizer hYK (inf_le_right.trans (le_normalizer_pCorePreimage p M))
  have hidx := ((CFSG.ABGLocalTools.isSylowOf_iff).mp hXY).2.2
  have hQn : (Q.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQY).mpr
    (hYM.trans (localGroup_le_normalizer_pCoreOf 2 M))
  have hpq : IsPGroup p (↥Y ⧸ Q.subgroupOf Y) := by
    intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨m, hm, rfl⟩ := hy
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := ↥M ⧸ CFSG.pCore 2 ↥M)
      ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hm⟩
    refine ⟨k, ?_⟩
    have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (m ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hmQ := (mk_eq_one_iff_coe_mem_pCoreOf _).mp hk'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hmQ)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpq
  have hQidx : Q.relIndex Y = p ^ n := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, hn]
  have h1 := Subgroup.relIndex_mul_relIndex (R ⊓ Y) ((R ⊓ Y) ⊔ Q) Y le_sup_left hle
  have h2 := Subgroup.relIndex_mul_relIndex Q ((R ⊓ Y) ⊔ Q) Y le_sup_right hle
  have hd1 : ((R ⊓ Y) ⊔ Q).relIndex Y ∣ p ^ n := hQidx ▸ h2 ▸ Dvd.intro_left _ rfl
  have hd2 : ¬ p ∣ ((R ⊓ Y) ⊔ Q).relIndex Y := fun hp =>
    hidx (h1 ▸ hp.mul_left _)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd1
  have hj0 : j = 0 := by
    by_contra hj0
    exact hd2 (hj ▸ dvd_pow_self p hj0)
  rw [hj0, pow_zero] at hj
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hj)

theorem D1PhaseThree.inf_sup_twoCore_eq (h : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) : (R ⊓ pCorePreimage p M) ⊔ pCoreOf 2 M = pCorePreimage p M :=
  h.toTwoLocalPhaseThree.inf_sup_twoCore_eq h.isKGroup.1 h.prime h.ne_two h.isSylow h.le_inf
    h84 (hD2 G h.glob)

end Survivor

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open scoped commutatorElement

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem isKGroup (h : AGLPair p M H R) : Open.IsKGroup ↥M ∧ Open.IsKGroup ↥H :=
  h.toTwoLocalPair.isKGroup_of_isKProper h.glob.kProper

theorem inf_eq_inf_normalizer_twoCore (h : AGLPair p M H R) :
    H ⊓ M = M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  h.toTwoLocalPair.inf_eq_inf_normalizer_twoCore

theorem twoCore_inf_normalizer (h : AGLPair p M H R) :
    pCoreOf 2 (M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G)) = pCoreOf 2 H :=
  h.toTwoLocalPhaseThree.twoCore_inf_normalizer

theorem twoCore_H_ne_bot (h : AGLPair p M H R) : pCoreOf 2 H ≠ ⊥ :=
  h.toTwoLocalPair.twoCore_H_ne_bot

theorem asc81bHyp (h : AGLPair p M H R) : Asc81bHyp M (pCoreOf 2 H) :=
  h.toTwoLocalPhaseThree.asc81bHyp

theorem oddCore_le_centralizer (h : AGLPair p M H R) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) :
    CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) ≤
      Subgroup.centralizer (barM M (pCoreOf 2 H) : Set _) :=
  h.toTwoLocalPhaseThree.oddCore_le_centralizer h.isKGroup.1 h84 hD2

theorem pCorePreimage_le_inf (h : AGLPair p M H R) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) : pCorePreimage p M ≤ H ⊓ M :=
  h.toTwoLocalPhaseThree.pCorePreimage_le_inf h.isKGroup.1 h.prime h.ne_two h84 hD2

theorem pCorePreimage_inf_le (h : AGLPair p M H R) :
    pCorePreimage p M ⊓ GLBPrimeCore p H ≤ pCoreOf 2 M :=
  pCorePreimage_inf_glbPrimeCore_le h.prime M H

theorem pCorePreimage_not_le (h : AGLPair p M H R)
    (hO : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥) :
    ¬ pCorePreimage p M ≤ GLBPrimeCore p H :=
  pCorePreimage_not_le_glbPrimeCore h.prime hO

theorem commutator_pCorePreimage_le (h : AGLPair p M H R) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) : ⁅GLBPrimeCore p H, pCorePreimage p M⁆ ≤ pCoreOf 2 M :=
  h.toTwoLocalPhaseThree.commutator_pCorePreimage_le h.isKGroup.1 h.prime h.ne_two
    h.primeCore_le h84 hD2

theorem inf_sup_twoCore_eq (h : AGLPair p M H R) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) : (R ⊓ pCorePreimage p M) ⊔ pCoreOf 2 M = pCorePreimage p M :=
  h.toTwoLocalPhaseThree.inf_sup_twoCore_eq h.isKGroup.1 h.prime h.ne_two h.isSylow
    (le_inf h.le_H h.le_M) h84 hD2

end AGLPair

structure AGLSurvivorData {G : Type} [Group G] [Finite G] (p : ℕ) (M H R X : Subgroup G) :
    Prop where
  pair : AGLPair p M H R
  le_R : X ≤ R
  ne_bot : X ≠ ⊥
  normal_dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore p H ∨ X ≤ Y
  centralizer_le : ∀ d ∈ H ⊓ M, (∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ GLBPrimeCore p H) →
    d ∈ R ⊔ GLBPrimeCore p H

theorem AGLSurvivorData.le_pCorePreimage {G : Type} [Group G] [Finite G] {p : ℕ}
    {M H R X : Subgroup G} (h : AGLSurvivorData p M H R X) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) (hO : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥) :
    X ≤ pCorePreimage p M :=
  (h.normal_dichotomy _ (h.pair.pCorePreimage_le_inf h84 hD2)
    (inf_le_right.trans (le_normalizer_pCorePreimage p M))).resolve_left
    (h.pair.pCorePreimage_not_le hO)

theorem AGLSurvivorData.le_blockClosure {G : Type} [Group G] [Finite G] {p : ℕ}
    {M H R X : Subgroup G} (h : AGLSurvivorData p M H R X) (hp3 : p = 3)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hB : BlockHasThree M (pCoreOf 2 H) L) : X ≤ blockClosure M (H ⊓ M) L :=
  h.pair.toTwoLocalPair.le_blockClosure_of_dichotomy hp3 h.normal_dichotomy hL hB

section Survivors

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M R : Subgroup G}

theorem false_of_aglSurvivorsOn (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : NoXBlockFor G) {C : Subgroup G → Prop} {X : Subgroup G}
    (hC : ∀ H, C H → AGLSurvivorData p M H R X)
    (hO : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥)
    (hcomp : AGLJCompetitorsOn C R X) {H : Subgroup G} (h : C H) : False := by
  obtain ⟨H₀, h₀, hmax⟩ := Set.exists_max_image {H' : Subgroup G | C H'}
    (fun H' => Nat.card (nclIn H' X)) (Set.toFinite _) ⟨H, h⟩
  have hc₀ := hC H₀ h₀
  have h3 := hc₀.pair
  have hXY := hc₀.le_pCorePreimage h84 hD2 hO
  have hXH : X ≤ H₀ := hc₀.le_R.trans h3.le_H
  have hQS : pCoreOf 2 M ≤ pCoreOf 2 H₀ := h3.twoCore_M_le
  have hNY := h3.commutator_pCorePreimage_le h84 hD2
  have hNJ : ⁅GLBPrimeCore p H₀, nclIn H₀ X⁆ ≤ pCoreOf 2 H₀ :=
    CFSG.AGLEmbedding.commutator_nclIn_le hXH (le_normalizer_glbPrimeCore p H₀)
      (localGroup_le_normalizer_pCoreOf 2 H₀)
      (((Subgroup.commutator_mono le_rfl hXY).trans hNY).trans hQS)
  have huniq : ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → nclIn H₀ X ≤ H' → R ≤ H' →
      H' = H₀ := by
    intro H' hH' hJH' hRH'
    obtain ⟨h', hJJ'⟩ := hcomp H₀ h₀ H' hH' hJH' hRH'
    have heq : nclIn H₀ X = nclIn H' X := Subgroup.eq_of_le_of_card_ge hJJ' (hmax H' h')
    have hJn' : ((nclIn H₀ X).subgroupOf H').Normal := heq ▸ nclIn_normal H' X
    have hAJ : pCoreOf 2 (GLBPrimeCore p (nclIn H₀ X)) ≤ nclIn H₀ X :=
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans (glbPrimeCore_le p _)
    have hNA : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p (nclIn H₀ X)) : Set G) = H₀ :=
      maxTwoLocal_normalizer_eq_of_normal h3.maxTwoLocal_H
        (h3.pCoreOf_two_primeCore_ne_bot hc₀.le_R hc₀.ne_bot)
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
        (hAJ.trans (nclIn_le_self H₀ X))
        (normal_pCoreOf_two_glbPrimeCore p (nclIn_le_self H₀ X) (nclIn_normal H₀ X))
    have hH'H : H' ≤ H₀ := hNA ▸ (Subgroup.normal_subgroupOf_iff_le_normalizer
      (hAJ.trans hJH')).mp (normal_pCoreOf_two_glbPrimeCore p hJH' hJn')
    exact (hH'.2 H₀ h3.maxTwoLocal_H.1 hH'H).symm
  have hXQ : (((R ⊓ pCorePreimage p M) ⊔ pCoreOf 2 M).subgroupOf M).Normal := by
    rw [h3.inf_sup_twoCore_eq h84 hD2, pCorePreimage_subgroupOf]
    exact Subgroup.Normal.comap inferInstance _
  refine h3.false_of_unique_over' inf_le_left le_rfl hXQ
    ((Subgroup.commutator_mono le_rfl inf_le_right).trans hNY) ?_ hNJ huniq hCGT hD2
  rintro d ⟨hdK, hdC⟩
  refine hc₀.centralizer_le d hdK fun x hx => ?_
  have hxd : x * d = d * x :=
    Subgroup.mem_centralizer_iff.mp hdC x ⟨hc₀.le_R hx, hXY hx⟩
  have : d * x * d⁻¹ * x⁻¹ = 1 := by
    rw [← hxd]
    group
  rw [this]
  exact Subgroup.one_mem _

end Survivors

end CFSG.AGLEmbeddingD2

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section SurvivorInstances

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1SurvivorData.toAGL {X : Subgroup G} (h : D1SurvivorData p P M H R X) :
    CFSG.AGLEmbeddingD2.AGLSurvivorData p M H R X :=
  ⟨h.ph3.toPair, h.le_R, h.ne_bot, h.normal_dichotomy, h.centralizer_le⟩

theorem D1SurvivorData.le_pCorePreimage {X : Subgroup G} (h : D1SurvivorData p P M H R X)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hO : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥) : X ≤ pCorePreimage p M :=
  h.toAGL.le_pCorePreimage h84 (hD2 G h.ph3.glob) hO

theorem false_of_survivorsOn (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) {C : Subgroup G → Prop} {X : Subgroup G}
    (hC : ∀ H, C H → D1SurvivorData p P M H R X)
    (hO : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥)
    (hcomp : D1JCompetitorsOn C R X) {H : Subgroup G} (h : C H) : False :=
  CFSG.AGLEmbeddingD2.false_of_aglSurvivorsOn h84 hCGT (hD2 G (hC H h).ph3.glob)
    (fun H' h' => (hC H' h').toAGL) hO hcomp h

theorem D1SurvivorData.le_blockClosure {X : Subgroup G} (h : D1SurvivorData p P M H R X)
    (hp3 : p = 3)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hB : BlockHasThree M (pCoreOf 2 H) L) : X ≤ blockClosure M (H ⊓ M) L :=
  h.toAGL.le_blockClosure hp3 hL hB

end SurvivorInstances

end CFSG.AGLEmbedding
