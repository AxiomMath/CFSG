module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.HardMathSupport.Solomon.LocalBalance.TwoLocalTools
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FamilyRank
import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_mem {p : ℕ} {B : Subgroup G} {y : G} (hB : IsElemAbelian p B)
    (hy : y ∈ B) : B ≤ Subgroup.centralizer ({y} : Set G) := fun b hb =>
  Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact isElemAbelian_commute hB hy hb

theorem isElemAbelian_subgroupOf {p : ℕ} {B : Subgroup G} (X : Subgroup G)
    (hB : IsElemAbelian p B) : IsElemAbelian p (B.subgroupOf X) :=
  isElemAbelian_of_forall (fun a ha b hb => Subtype.ext
    (isElemAbelian_commute hB (Subgroup.mem_subgroupOf.1 ha) (Subgroup.mem_subgroupOf.1 hb)))
    fun x hx => Subtype.ext (hB.2 _ (Subgroup.mem_subgroupOf.1 hx))

theorem glaTwoLocalRank_le_pRank_of_isBmax {p : ℕ} (hp : p.Prime) {B : Subgroup G}
    (hB : GLAIsBmax p B) (X : Subgroup G) : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B :=
  (glaTwoLocalRank_subgroup_le hp X).trans
    (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB.1 hB.2.1)

theorem glaIsBmax_subgroupOf_centralizer {p : ℕ} (hp : p.Prime) {B : Subgroup G} {y : G}
    (hB : GLAIsBmax p B) (hy : IsEssential p B y) :
    GLATwoLocalRank p ↥(Subgroup.centralizer ({y} : Set G)) = GLATwoLocalRank p G ∧
      GLAIsBmax p (B.subgroupOf (Subgroup.centralizer ({y} : Set G))) := by
  set X : Subgroup G := Subgroup.centralizer ({y} : Set G)
  have hBX : B ≤ X := le_centralizer_of_mem hB.1 hy.1
  obtain ⟨T, hTX, hT2, hBT, hTB, -⟩ := hy.2.2
  have hT1 : T ≠ ⊥ := fun h => hTB (by rw [h]; exact Subgroup.commutator_bot_left B)
  have hB'el : IsElemAbelian p (B.subgroupOf X) := isElemAbelian_subgroupOf X hB.1
  have hcardB' : Nat.card ↥(B.subgroupOf X) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  have hT'ne : T.subgroupOf X ≠ ⊥ := fun h => hT1 (by
    have := congrArg (Subgroup.map X.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hTX, Subgroup.map_bot] at this)
  have hT'2 : IsPGroup 2 ↥(T.subgroupOf X) := hT2.comap_of_injective X.subtype X.subtype_injective
  have hB'N : B.subgroupOf X ≤ Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTX]
    exact fun x hx => hBT (Subgroup.mem_subgroupOf.1 hx)
  have h1 : CFSG.Open.pRank p (B.subgroupOf X) ≤ GLATwoLocalRank p ↥X :=
    pRank_le_glaTwoLocalRank_of_normalizes hp hT'ne hT'2 hB'N
  have h2 : GLATwoLocalRank p G ≤ CFSG.Open.pRank p (B.subgroupOf X) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB'el (by rw [hcardB']; exact hB.2.1)
  have heq : GLATwoLocalRank p ↥X = GLATwoLocalRank p G :=
    le_antisymm (glaTwoLocalRank_subgroup_le hp X) (h2.trans h1)
  exact ⟨heq, hB'el, by rw [hcardB', heq]; exact hB.2.1, T.subgroupOf X, hT'ne, hT'2, hB'N⟩

theorem glaPComponent_top_subgroupOf {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (hK : GLAPComponent p X K) : GLAPComponent p (⊤ : Subgroup ↥X) (K.subgroupOf X) := by
  have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥X) ⊓ X.subtype.ker)) := by
    rw [top_inf_eq, Subgroup.ker_subtype, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have htop : (⊤ : Subgroup ↥X).map X.subtype = X :=
    le_antisymm (by rintro _ ⟨y, -, rfl⟩; exact y.2) fun y hy => ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  have hK' : GLAPComponent p ((⊤ : Subgroup ↥X).map X.subtype) K := by
    rw [htop]
    exact hK
  obtain ⟨K₀, hK₀, hmap⟩ := exists_glaPComponent_map_eq hp X.subtype hker hK'
  have hK₀eq : K₀ = K.subgroupOf X := by
    rw [← hmap]
    exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective K₀).symm
  rwa [← hK₀eq]

theorem relIndex_normalizer_subgroupOf {X K B : Subgroup G} (hKX : K ≤ X) (hBX : B ≤ X) :
    (Subgroup.normalizer ((K.subgroupOf X : Subgroup ↥X) : Set ↥X)).relIndex (B.subgroupOf X) =
      (Subgroup.normalizer (K : Set G)).relIndex B := by
  rw [← Subgroup.subgroupOf_normalizer_eq hKX, Subgroup.relIndex_subgroupOf hBX]

theorem le_normalizer_subgroupOf_iff {X K B : Subgroup G} (hKX : K ≤ X) (hBX : B ≤ X) :
    B.subgroupOf X ≤ Subgroup.normalizer ((K.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      B ≤ Subgroup.normalizer (K : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hKX]
  constructor
  · intro hle b hb
    exact Subgroup.mem_subgroupOf.1
      (hle (Subgroup.mem_subgroupOf.2 hb : (⟨b, hBX hb⟩ : ↥X) ∈ B.subgroupOf X))
  · intro hle x hx
    exact Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hx))

@[expose] noncomputable def pQuotSubgroupOfEquiv (p : ℕ) {X K : Subgroup G} (hKX : K ≤ X) :
    (↥(K.subgroupOf X) ⧸ GLAPPrimeCore p ↥(K.subgroupOf X)) ≃* PQuot p K :=
  QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hKX)
    (glaPPrimeCore_map_iso p (Subgroup.subgroupOfEquivOfLe hKX))

end CFSG.LocalAnalysis.GLTheoremA
