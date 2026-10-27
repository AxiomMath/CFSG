module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NC1c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NC1b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t g g0 : G} {P U S F M U0 P0 : Subgroup G}

theorem y7n_case1_comm (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0)
    (hMn : P0 ⊔ zpowers t ≤ normalizer (M : Set G)) :
    ⁅P0 ⊔ zpowers t, ⁅P0 ⊔ zpowers t,
        (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0)⁆⁆ = M := by
  have hFU := y7n_fuFacts h
  have hg0_mem_U0 : g0 ∈ U0 := by
    rw [h1.U0_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g0)
  have hg0t_mem : t * g0 * t⁻¹ ∈ conjSub t U0 :=
    (mem_conjSub_iff' t U0 _).mpr ⟨g0, hg0_mem_U0, rfl⟩
  have hg0_comm : g0 * (t * g0 * t⁻¹) = (t * g0 * t⁻¹) * g0 :=
    h1.direct.2.2 g0 hg0_mem_U0 _ hg0t_mem
  have hg0_sq : g0 * g0 = 1 := by simpa [pow_two] using h1.g0_sq
  have hg0_inv : g0⁻¹ = g0 := mul_eq_one_iff_inv_eq.mp hg0_sq
  have htg0 : ⁅t, g0⁆ = g := by
    rw [commutatorElement_def, hg0_inv]
    calc t * g0 * t⁻¹ * g0 = (t * g0 * t⁻¹) * g0 := by group
      _ = g0 * (t * g0 * t⁻¹) := hg0_comm.symm
      _ = g := h1.gg0
  have hUP1 : U ≤ P0 ⊔ zpowers t :=
    (h.wr.le_left.1.trans (y7n_c1_P_le h h1)).trans le_sup_left
  have hUtP1 : conjSub t U ≤ P0 ⊔ zpowers t :=
    (h.wr.le_left.2.trans (y7n_c1_P_le h h1)).trans le_sup_left
  have hg0_mem_J : g0 ∈ (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers g0))
  have hgK : g ∈ ⁅P0 ⊔ zpowers t,
      (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0)⁆ := by
    simpa only [htg0] using Subgroup.commutator_mem_commutator
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) hg0_mem_J
  refine le_antisymm ?_ ?_
  · have hgN : g ∈ normalizer (M : Set G) :=
      Subgroup.centralizer_le_normalizer (M : Set G)
        (Subgroup.mem_centralizer_iff.mpr fun m hm => (y7n_g_cent_M h m hm).symm)
    have hN : M ⊔ zpowers g ≤ normalizer (M : Set G) :=
      sup_le (Subgroup.le_normalizer (H := M)) (Subgroup.zpowers_le.mpr hgN)
    have hM1 : ⁅M, P0 ⊔ zpowers t⁆ ≤ M := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hMn
    have hM2 : ⁅zpowers g, P0 ⊔ zpowers t⁆ ≤ M :=
      y7n_commutator_zpowers_le hgN (y7n_c1_g_comm_M h h1 hMn)
    have hcomm : ⁅P0 ⊔ zpowers t,
        (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0)⁆ ≤ M ⊔ zpowers g := by
      rw [Subgroup.commutator_comm]
      exact y7n_c1_comm_D h h1 hMn
    calc ⁅P0 ⊔ zpowers t, ⁅P0 ⊔ zpowers t,
          (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0)⁆⁆
        ≤ ⁅P0 ⊔ zpowers t, M ⊔ zpowers g⁆ := Subgroup.commutator_mono_right hcomm
      _ = ⁅M ⊔ zpowers g, P0 ⊔ zpowers t⁆ := Subgroup.commutator_comm _ _
      _ ≤ M := y7n_commutator_sup_le (D := M) (X₁ := M) (X₂ := zpowers g)
          (A := P0 ⊔ zpowers t) hN hM1 hM2
  · rw [y7n_M_eq h]
    refine sup_le ?_ ?_
    · intro w hw
      obtain ⟨u, huU, hu⟩ := hFU.cls w hw
      have hw_eq : w = ⁅u, g⁆ := by
        rw [commutatorElement_def, hu]
        group
      rw [hw_eq]
      exact Subgroup.commutator_mem_commutator (hUP1 huU) hgK
    · intro y hy
      obtain ⟨w, hw, rfl⟩ := (mem_conjSub_iff' t (centEl U g) y).mp hy
      obtain ⟨u, huU, hu⟩ := hFU.cls w hw
      have hw_eq : w = ⁅u, g⁆ := by
        rw [commutatorElement_def, hu]
        group
      have hconj : t * w * t⁻¹ = ⁅t * u * t⁻¹, g⁆ := by
        rw [hw_eq, conjugate_commutatorElement,
          show t * g * t⁻¹ = g by rw [h.tg]; group]
      rw [hconj]
      exact Subgroup.commutator_mem_commutator
        (hUtP1 ((mem_conjSub_iff' t U _).mpr ⟨u, huU, rfl⟩)) hgK

theorem y7n_char_case1 (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0)
    {P1 : Subgroup G} (hP1 : P1 = P0 ⊔ zpowers t) (hMn : P1 ≤ normalizer (M : Set G))
    {n : G} (hn : conjSub n P1 = P1) : conjSub n M = M := by
  subst hP1
  have hJ := y7n_c1_J h h1
  have hJne : Nat.card ↥((centEl U g ⊔ zpowers g0) ⊔
      conjSub t (centEl U g ⊔ zpowers g0)) = 2 ^ 8 := hJ.2.1
  have hmax : ∀ E : Subgroup G, E ≤ P0 ⊔ zpowers t → IsElemAbelian 2 E →
      Nat.card E ≤ Nat.card ↥((centEl U g ⊔ zpowers g0) ⊔
        conjSub t (centEl U g ⊔ zpowers g0)) ∧
      (Nat.card E = Nat.card ↥((centEl U g ⊔ zpowers g0) ⊔
        conjSub t (centEl U g ⊔ zpowers g0)) →
        E = (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0)) := by
    intro E hE hel
    obtain ⟨hE₁, hE₂⟩ := y7n_case1_rank h h1 hE hel
    exact ⟨by rwa [hJne], fun hc => hE₂ (by rwa [hJne] at hc)⟩
  have hJn : conjSub n ((centEl U g ⊔ zpowers g0) ⊔
      conjSub t (centEl U g ⊔ zpowers g0)) =
      (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0) :=
    y7n_conj_eq_of_unique hJ.1 hJ.2.2 hmax hn
  calc conjSub n M = conjSub n ⁅P0 ⊔ zpowers t,
        ⁅P0 ⊔ zpowers t,
          (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0)⁆⁆ := by
        rw [y7n_case1_comm h h1 hMn]
    _ = ⁅conjSub n (P0 ⊔ zpowers t), ⁅conjSub n (P0 ⊔ zpowers t), conjSub n
          ((centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0))⁆⁆ := by
        simp only [y7n_conjSub_commutator]
    _ = ⁅P0 ⊔ zpowers t, ⁅P0 ⊔ zpowers t,
          (centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0)⁆⁆ := by
        rw [hn, hJn]
    _ = M := y7n_case1_comm h h1 hMn

end CFSG.OddStandard.HigherRank.YamadaG23
