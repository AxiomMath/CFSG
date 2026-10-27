module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Parts
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.BorelTitsConstrained
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294LayerLieQ
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.RadicalQuot
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3 Subgroup

theorem kd29DefChar_of_lieQConstrained (h : ∀ q : ℕ, q.Prime → 5 ≤ q → LieQConstrained q) :
    KD29DefChar := by
  intro p hp hp5 X _ _ L hLn hs hn _ hd _ hcen _ _ w hwL hw1 hwp
  obtain ⟨m, hm, ⟨e⟩⟩ := hd
  haveI : Fact p.Prime := ⟨hp⟩
  have hChev := isChevOfChar_of_characteristic hm e
  have hQL : Subgroup.zpowers w ≤ L := Subgroup.zpowers_le.2 hwL
  have hQ1 : Subgroup.zpowers w ≠ ⊥ := fun h0 => hw1 (Subgroup.zpowers_eq_bot.1 h0)
  have hQp : IsPGroup p ↥(Subgroup.zpowers w) := by
    rw [IsPGroup.iff_card]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, orderOf_eq_prime hwp hw1, pow_one]
  have hc := h p hp hp5 X L hLn hs hn hChev hcen (Subgroup.zpowers w) hQL hQ1 hQp
  set N : Subgroup X := Subgroup.normalizer ((Subgroup.zpowers w : Subgroup X) : Set X) with hN
  have fwd : ∀ y ∈ Subgroup.centralizer ({w} : Set X), ∀ x ∈ Subgroup.zpowers w,
      y * x * y⁻¹ ∈ Subgroup.zpowers w := by
    intro y hy x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hyw : Commute y w := Subgroup.mem_centralizer_singleton_iff.1 hy
    rw [(hyw.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers w) k
  have hCN : Subgroup.centralizer ({w} : Set X) ≤ N := by
    intro y hy
    show y ∈ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup X) : Set X)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fwd y hy x
    · intro hx
      have := fwd y⁻¹ (Subgroup.inv_mem _ hy) _ hx
      simpa [mul_assoc] using this
  have key : ∀ m c : X, m ∈ N → c ∈ Subgroup.centralizer ({w} : Set X) →
      m * c * m⁻¹ ∈ Subgroup.centralizer ({w} : Set X) := by
    intro m c hm hc'
    have hq : m⁻¹ * w * m ∈ Subgroup.zpowers w := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem N hm) w).1
        (Subgroup.mem_zpowers w)
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hq
    have hcw0 : Commute c w := Subgroup.mem_centralizer_singleton_iff.1 hc'
    have hcw : Commute c (w ^ k) := hcw0.zpow_right k
    rw [hk] at hcw
    rw [Subgroup.mem_centralizer_singleton_iff]
    show m * c * m⁻¹ * w = w * (m * c * m⁻¹)
    calc m * c * m⁻¹ * w = m * (c * (m⁻¹ * w * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * w * m) * c) * m⁻¹ := by rw [hcw.eq]
      _ = w * (m * c * m⁻¹) := by group
  have hHn : ((Subgroup.centralizer ({w} : Set X)).subgroupOf N).Normal :=
    ⟨fun c hc' n => by
      rw [Subgroup.mem_subgroupOf] at hc' ⊢
      simpa using key (n : X) (c : X) n.2 hc'⟩
  refine ⟨glaPLayer_eq_bot_of_constrained hp hCN hHn hc, ?_⟩
  have hON : GLAPPrimeCoreOf p N = ⊥ := glaPPrimeCoreOf_eq_bot_of_constrained hp hc
  have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_normal_aux p hCN hHn
  rw [hON] at h1
  exact le_bot_iff.1 h1

end CFSG.LocalAnalysis.RankFourTheoremC
