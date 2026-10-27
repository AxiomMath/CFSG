module

public import CFSG.Assembly.InCatalogConverse
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Interface
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294LayerLieQ
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

private theorem lieQ_layer_nonab {p : ℕ} (hp : p.Prime)
    (h : CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.LieQConstrainedInner p)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hab : ∃ a b : G, a * b ≠ b * a)
    (hChev : CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar p G) (u : G)
    (hu : orderOf u = p) :
    CFSG.Open.GLAPLayer p (Subgroup.centralizer ({u} : Set G)) = ⊥ := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    exact hp.one_lt.ne hu
  have hQ1 : Subgroup.zpowers u ≠ ⊥ := fun h0 => hu1 (Subgroup.zpowers_eq_bot.1 h0)
  haveI : Fact p.Prime := ⟨hp⟩
  have hQp : IsPGroup p ↥(Subgroup.zpowers u) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hu, pow_one]⟩
  have hc := h G inferInstance hab hChev (Subgroup.zpowers u) hQ1 hQp
  set N : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) with hN
  have fwd : ∀ y ∈ Subgroup.centralizer ({u} : Set G), ∀ x ∈ Subgroup.zpowers u,
      y * x * y⁻¹ ∈ Subgroup.zpowers u := by
    intro y hy x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hyu : Commute y u := Subgroup.mem_centralizer_singleton_iff.1 hy
    rw [(hyu.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) k
  have hCN : Subgroup.centralizer ({u} : Set G) ≤ N := by
    intro y hy
    show y ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fwd y hy x
    · intro hx
      have := fwd y⁻¹ (Subgroup.inv_mem _ hy) _ hx
      simpa [mul_assoc] using this
  have key : ∀ m c : G, m ∈ N → c ∈ Subgroup.centralizer ({u} : Set G) →
      m * c * m⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
    intro m c hm hc'
    have hq : m⁻¹ * u * m ∈ Subgroup.zpowers u := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem N hm) u).1
        (Subgroup.mem_zpowers u)
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hq
    have hcu0 : Commute c u := Subgroup.mem_centralizer_singleton_iff.1 hc'
    have hcu : Commute c (u ^ k) := hcu0.zpow_right k
    rw [hk] at hcu
    rw [Subgroup.mem_centralizer_singleton_iff]
    show m * c * m⁻¹ * u = u * (m * c * m⁻¹)
    calc m * c * m⁻¹ * u = m * (c * (m⁻¹ * u * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * u * m) * c) * m⁻¹ := by rw [hcu.eq]
      _ = u * (m * c * m⁻¹) := by group
  have hHn : ((Subgroup.centralizer ({u} : Set G)).subgroupOf N).Normal :=
    ⟨fun c hc' n => by
      rw [Subgroup.mem_subgroupOf] at hc' ⊢
      simpa using key (n : G) (c : G) n.2 hc'⟩
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.glaPLayer_eq_bot_of_constrained
    hp hCN hHn hc

private theorem lieQ_layer_comm {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    (hcomm : ∀ a b : G, a * b = b * a) (X : Subgroup G) :
    CFSG.Open.GLAPLayer p X = ⊥ := by
  refine eq_bot_iff.2 (sSup_le fun J hJ => ?_)
  exfalso
  have hJ' : CFSG.Open.GLAPComponent p X J := hJ
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ'
  haveI := isQuasisimple_nontrivial hq
  have hQc : ∀ a b : PQuot p J, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcomm x y)
  have hbot : commutator (PQuot p J) = ⊥ :=
    (commutator_eq_bot_iff (G := PQuot p J)).2 (isMulCommutative_iff.2 hQc)
  obtain ⟨x, hx⟩ := exists_ne (1 : PQuot p J)
  have hmem : x ∈ (⊤ : Subgroup (PQuot p J)) := Subgroup.mem_top x
  rw [← hq.1, hbot, Subgroup.mem_bot] at hmem
  exact hx hmem

section KDCharPLieQ

theorem kdCharP_of_lieQConstrainedInner {p : ℕ} (hp : p.Prime)
    (h : CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.LieQConstrainedInner p) :
    KDCharP p := by
  intro d hd u hu
  obtain ⟨hfin, hsimp⟩ := CFSG.Assembly.lie_finite_simple d
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := hfin
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := hsimp
  by_cases hab : ∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a
  · have hChev : CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar p
        (TauCeti.CFSGIndex.lie d).Group :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.isChevOfChar_of_characteristic
        hd (MulEquiv.refl _)
    exact lieQ_layer_nonab hp h hab hChev u hu
  · exact lieQ_layer_comm hp
      (fun a b => Classical.byContradiction fun hne => hab ⟨a, b, hne⟩) _

end KDCharPLieQ

end CFSG.LocalAnalysis.GLTheoremA
