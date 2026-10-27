module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Defs
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

structure Lemma212ConfigGe (n p : ℕ) {H : Type*} [Group H] [Finite H] (P : Sylow p H) (z : H)
    (D : Subgroup H) : Prop where
  rank : n ≤ CFSG.Open.pRank p (P : Subgroup H)
  ord : orderOf z = p
  central : z ∈ centralizer ((P : Subgroup H) : Set H)
  unique : ∀ y ∈ (P : Subgroup H), y ∈ centralizer ((P : Subgroup H) : Set H) → y ^ p = 1 →
    y ∈ zpowers z
  le : D ≤ (P : Subgroup H)
  elem : IsElemAbelian p D
  card : Nat.card D = p ^ 2
  mem : z ∈ D
  notNormal : ¬ (P : Subgroup H) ≤ normalizer (D : Set H)
  sylow : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set H))

theorem Lemma212ConfigGe.mono {m n p : ℕ} {H : Type*} [Group H] [Finite H] {P : Sylow p H}
    {z : H} {D : Subgroup H} (h : Lemma212ConfigGe n p P z D) (hmn : m ≤ n) :
    Lemma212ConfigGe m p P z D :=
  ⟨hmn.trans h.rank, h.ord, h.central, h.unique, h.le, h.elem, h.card, h.mem, h.notNormal,
    h.sylow⟩

@[expose] def KFactLemma212Ge (n : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (H : Type) [Group H] [Finite H],
    CFSG.AGLEmbedding.CatalogSimpleSections H → ∀ (P : Sylow p H) (z : H) (D : Subgroup H),
      Lemma212ConfigGe n p P z D → (∃ g, IsPlaneDiagonal p D z g) →
        HasPrimeConstraint (G := H) p ∨
          CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥

@[expose] def KFactLemma213Ge (n : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (H : Type) [Group H] [Finite H],
    CFSG.AGLEmbedding.CatalogSimpleSections H → ¬ HasPrimeConstraint (G := H) p →
      CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ →
      ∀ (P : Sylow p H) (z : H) (D : Subgroup H), Lemma212ConfigGe n p P z D →
        (∃ g, IsPlaneDiagonal p D z g) → CentralizerEmbeds D z →
        (∀ T : Subgroup H, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set H) →
            T ≤ primeComplementCore (G := H) p) ∨
          (∀ y ∈ D, y ≠ 1 → ∃ h ∈ normalizer (D : Set H),
            zpowers y = (zpowers z).map (MulAut.conj h).toMonoidHom)

variable {G : Type} [Group G] [Finite G]

theorem Lemma212ConfigGe.of_extremal {n : ℕ} (hS : ObstructionSetting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hn : n ≤ CFSG.Open.pRank p (P : Subgroup G))
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hzp : z ^ p = 1) (hSyl : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set G)))
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) (hCH : centralizer (D : Set G) ≤ H)
    (hzH : z ∈ H) :
    Lemma212ConfigGe n p (P.subtype hPH) ⟨z, hzH⟩ (D.subgroupOf H) := by
  classical
  have hprime : p.Prime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hDH : D ≤ H := hDP.trans hPH
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  obtain ⟨A, hAP, hA, hAc⟩ := hS.exists_elemAbelian_card_eq hp P
  obtain ⟨-, z₀, -, hz₀1, -, hz₀p, hz₀u⟩ := isolatedPlane_structure hprime P.isPGroup'
    (hext.isIsolatedPlane_of_isMulCommutative hprime hDab) hAP
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA) hAc
  have hzz₀ : z ∈ zpowers z₀ := hz₀u z (hDP hzD) hzc hzp
  have hzeq : zpowers z = zpowers z₀ := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzz₀)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hzp hz1,
      orderOf_eq_prime hz₀p hz₀1])
  have hPsub : ((P.subtype hPH : Sylow p H) : Subgroup H) = (P : Subgroup G).subgroupOf H :=
    Sylow.coe_subtype P hPH
  have hCD : centralizer ((D.subgroupOf H : Subgroup H) : Set H) =
      (centralizer (D : Set G)).subgroupOf H := by
    ext x
    rw [mem_centralizer_iff, Subgroup.mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro hx d hd
      exact congrArg Subtype.val (hx ⟨d, hDH hd⟩ hd)
    · intro hx d hd
      exact Subtype.ext (hx d hd)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hPsub, ← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hprime H.subtype
      H.subtype_injective, map_subgroupOf_eq_of_le hPH]
    exact hn
  ·
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hzp hz1
  ·
    rw [hPsub]
    refine mem_centralizer_iff.mpr fun t ht => ?_
    exact Subtype.ext (mem_centralizer_iff.mp hzc (t : G) ht)
  ·
    intro y hy hyc hyp
    rw [hPsub] at hy hyc
    have hyc' : (y : G) ∈ centralizer ((P : Subgroup G) : Set G) := by
      refine mem_centralizer_iff.mpr fun g hg => ?_
      exact congrArg Subtype.val (mem_centralizer_iff.mp hyc ⟨g, hPH hg⟩ hg)
    have hyz : (y : G) ∈ zpowers z := by
      rw [hzeq]
      exact hz₀u y hy hyc' (congrArg Subtype.val hyp)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyz
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  ·
    rw [hPsub]
    exact fun x hx => hDP hx
  ·
    exact CFSG.AGLEmbedding.isElemAbelian_subgroupOf hDe H
  ·
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv, hDc]
  ·
    exact hzD
  ·
    intro hle
    apply hPD
    rw [hPsub] at hle
    intro g hg
    have hg' : (⟨g, hPH hg⟩ : H) ∈ normalizer ((D.subgroupOf H : Subgroup H) : Set H) :=
      hle (show (⟨g, hPH hg⟩ : H) ∈ (P : Subgroup G).subgroupOf H from hg)
    have := Subgroup.le_normalizer_map H.subtype ⟨⟨g, hPH hg⟩, hg', rfl⟩
    rwa [map_subgroupOf_eq_of_le hDH] at this
  ·
    rw [hCD]
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).mp ?_
    rw [map_subgroupOf_eq_of_le hDH, map_subgroupOf_eq_of_le hCH]
    exact hSyl

end CFSG.LocalAnalysis.RankFourTheoremC
