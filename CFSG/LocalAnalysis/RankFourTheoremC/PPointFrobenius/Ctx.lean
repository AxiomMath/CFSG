module

public import CFSG.Yardstones.Md8ed6d263d89.Definitions
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Statement
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

structure FrobGlobal (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Open.IsKProper G
  charTwo : CFSG.Open.IsCharTwoType G
  rank : 4 ≤ CFSG.Open.evenRank G
  pre : CFSG.Open.GLBPreuniqueness G
  d1 : CFSG.AGLEmbeddingD2.D1For G
  fullCore : CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G

variable {G : Type} [Group G] [Finite G]

abbrev layerOf (x : G) : Subgroup G :=
  CFSG.Open.GLBLayer (centralizer ((zpowers x : Subgroup G) : Set G))

structure FrobLocal (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) : Prop where
  p5 : 5 ≤ p
  loc : CFSG.AGLEmbedding.D1Local p P M
  point : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x
  conf : ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → 2 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M
  abel : IsMulCommutative (P : Subgroup G)
  weak : ∀ g : G, CFSG.Open.GLBConj g (zpowers x) ≤ (P : Subgroup G) →
    CFSG.Open.GLBConj g (zpowers x) = zpowers x
  norm : ∀ P₁ : Subgroup G, P₁ ≤ (P : Subgroup G) → Nat.card P₁ = p → P₁ ≠ zpowers x →
    normalizer (P₁ : Set G) ≤ M
  layer : ∃ (_ : Fact p.Prime) (n : ℕ), 2 ≤ n ∧ Nonempty (layerOf x ≃* PSL(2, GaloisField p n))
  not_le : ¬ layerOf x ≤ M
  cyclic : ∀ S : Subgroup G, S ≤ centralizer ((zpowers x : Subgroup G) : Set G) ⊓
    centralizer ((layerOf x : Subgroup G) : Set G) → IsPGroup p S → IsCyclic S

@[expose] def FrobConclusion (p : ℕ) (M : Subgroup G) (x : G) : Prop :=
  Group.IsSolvable M ∧ CFSG.Open.GLBIsFrobenius (CFSG.Open.GLBPrimeCore p M ⊔ zpowers x)
    (CFSG.Open.pCoreOf 2 M)
    (CFSG.Open.GLBPrimeCore p (centralizer ((zpowers x : Subgroup G) : Set G)) ⊔ zpowers x)

theorem ysPPointFrobenius_of_local
    (h : ∀ (G : Type) [Group G] [Finite G], FrobGlobal G → ∀ (p : ℕ) (P : Sylow p G)
      (M : Subgroup G) (x : G), FrobLocal p P M x → FrobConclusion p M x) :
    CFSG.Yardstones.Md8ed6d263d89.YSPPointFrobenius := by
  intro G _ _ hs hnab hk hc hr hpre hd1 hfc p P M x hp5 hloc hpt hconf hab hwc hn1 hlay hlm hcyc
  exact h G ⟨hs, hnab, hk, hc, hr, hpre, hd1, hfc⟩ p P M x
    ⟨hp5, hloc, hpt, hconf, hab, hwc, hn1, hlay, hlm, hcyc⟩

structure FrobKFacts : Prop where
  inner : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction
  weak : CFSG.LocalAnalysis.RankThreeTheoremC.KFactWeakClosure
  kc : StronglyEmbeddedPSL2KFact
  coprimeAut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactCoprimeAutEvenCentralizer
  schreier : CFSG.AGLEmbedding.KFactCatalogSchreier

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

abbrev frU (P : Sylow p G) (x : G) : Subgroup G := (P : Subgroup G) ⊓ layerOf x

theorem layerOf_eq (x : G) :
    layerOf x = CFSG.Open.GLBLayer (centralizer ({x} : Set G)) := by
  unfold layerOf
  rw [zpowers_eq_closure, Subgroup.centralizer_closure]

theorem centralizer_zpowers_eq (x : G) :
    centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
  rw [zpowers_eq_closure, Subgroup.centralizer_closure]

theorem fr_P_le_centralizer (hl : FrobLocal p P M x) :
    (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
  intro g hg
  rw [mem_centralizer_singleton_iff]
  have h := hl.abel.is_comm.comm (⟨x, hl.point.mem⟩ : (P : Subgroup G)) ⟨g, hg⟩
  exact (congrArg Subtype.val h).symm

theorem fr_M_ne_top (hl : FrobLocal p P M x) : M ≠ ⊤ :=
  fun h => hl.not_le (h ▸ le_top)

open scoped Pointwise in
theorem fr_sylow_abelian [Fact p.Prime] (hl : FrobLocal p P M x) (Q : Sylow p G) :
    IsMulCommutative (Q : Subgroup G) := by
  have hPab := hl.abel
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  have hmem : ∀ y : G, y ∈ ((g • P : Sylow p G) : Subgroup G) ↔
      g⁻¹ * y * g ∈ (P : Subgroup G) := fun y => by
    change y ∈ MulAut.conj g • (P : Subgroup G) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h := hPab.is_comm.comm ⟨_, (hmem a).mp a.2⟩ ⟨_, (hmem b).mp b.2⟩
  have h2 : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * b * g * (g⁻¹ * a * g) := congrArg Subtype.val h
  have h3 : g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ =
      g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by rw [h2]
  simpa [mul_assoc] using h3

theorem fr_pGroup_abelian [Fact p.Prime] (hl : FrobLocal p P M x) :
    ∀ Q : Subgroup G, IsPGroup p Q → IsMulCommutative Q := by
  intro Q hQ
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  have hSab := fr_sylow_abelian hl S
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h := hSab.is_comm.comm ⟨a, hQS a.2⟩ ⟨b, hQS b.2⟩
  have h2 := congrArg Subtype.val h
  exact h2

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
