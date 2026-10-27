module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NC2a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NXb

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t g : G} {P U S F M : Subgroup G}

theorem y7n_case2_comm (h : NtTwo t g P U S F M)
    (hMn : (P ⊔ zpowers g) ⊔ zpowers t ≤ normalizer (M : Set G)) :
    ⁅M ⊔ zpowers g, (P ⊔ zpowers g) ⊔ zpowers t⁆ = M := by
  have hgN : g ∈ normalizer (M : Set G) :=
    Subgroup.centralizer_le_normalizer (M : Set G) (by
      rw [Subgroup.mem_centralizer_iff]
      exact fun m hm => (y7n_g_cent_M h m hm).symm)
  refine le_antisymm ?_ ?_
  · have hMcomm : ⁅M, (P ⊔ zpowers g) ⊔ zpowers t⁆ ≤ M :=
      (Subgroup.le_normalizer_iff_commutator_le_left
        (H := (P ⊔ zpowers g) ⊔ zpowers t) (K := M)).mp hMn
    have hPP : ⁅P, zpowers g⁆ ≤ M := by
      have h' := y7n_commutator_zpowers_le (D := M) (A := P) hgN h.M_comm
      rwa [Subgroup.commutator_comm] at h'
    have hGG : ⁅zpowers g, zpowers g⁆ ≤ M := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [((Commute.refl g).zpow_zpow m k).commutator_eq]
      exact M.one_mem
    have hPG : ⁅P ⊔ zpowers g, zpowers g⁆ ≤ M :=
      y7n_commutator_sup_le (D := M) (X₁ := P) (X₂ := zpowers g) (A := zpowers g)
        (le_sup_left.trans hMn) hPP hGG
    have htG : ⁅zpowers t, zpowers g⁆ ≤ M := by
      refine y7n_commutator_zpowers_le (D := M) (A := zpowers g) ?_ ?_
      · exact hMn (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      · intro a ha
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        rw [((show Commute t g from h.tg).zpow_right k).commutator_eq]
        exact M.one_mem
    have hgP₁ : ⁅zpowers g, (P ⊔ zpowers g) ⊔ zpowers t⁆ ≤ M := by
      rw [Subgroup.commutator_comm]
      exact y7n_commutator_sup_le (D := M) (X₁ := P ⊔ zpowers g) (X₂ := zpowers t)
        (A := zpowers g) hMn hPG htG
    have hN : M ⊔ zpowers g ≤ normalizer (M : Set G) :=
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hgN)
    exact y7n_commutator_sup_le (D := M) (X₁ := M) (X₂ := zpowers g)
      (A := (P ⊔ zpowers g) ⊔ zpowers t) hN hMcomm hgP₁
  · refine (y7n_M_eq h).le.trans ?_
    apply sup_le
    · intro w hw
      obtain ⟨u, hu, hwu⟩ := (y7n_fuFacts h).cls w hw
      have hweq : w = ⁅u, g⁆ := by rw [commutatorElement_def, hwu]; group
      have huP₁ : u ∈ (P ⊔ zpowers g) ⊔ zpowers t :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_left (h.wr.le_left.1 hu))
      have hgJ : g ∈ M ⊔ zpowers g :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
      rw [hweq, Subgroup.commutator_comm (M ⊔ zpowers g) ((P ⊔ zpowers g) ⊔ zpowers t)]
      exact Subgroup.commutator_mem_commutator huP₁ hgJ
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := (mem_conjSub_iff' t (centEl U g) x).mp hx
      obtain ⟨u, hu, hwu⟩ := (y7n_fuFacts h).cls w hw
      have htg' : t * g * t⁻¹ = g := by rw [h.tg]; group
      have hconj := conjugate_commutatorElement (g₁ := u) (g₂ := g) (g₃ := t)
      rw [htg'] at hconj
      have hweq : w = ⁅u, g⁆ := by rw [commutatorElement_def, hwu]; group
      have hv : t * u * t⁻¹ ∈ conjSub t U := (mem_conjSub_iff' t U _).mpr ⟨u, hu, rfl⟩
      have hvP₁ : t * u * t⁻¹ ∈ (P ⊔ zpowers g) ⊔ zpowers t :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_left (h.wr.le_left.2 hv))
      have hgJ : g ∈ M ⊔ zpowers g :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
      rw [hweq, hconj,
        Subgroup.commutator_comm (M ⊔ zpowers g) ((P ⊔ zpowers g) ⊔ zpowers t)]
      exact Subgroup.commutator_mem_commutator hvP₁ hgJ

theorem y7n_char_case2 (h : NtTwo t g P U S F M) {P1 : Subgroup G}
    (hP1 : P1 = (P ⊔ zpowers g) ⊔ zpowers t) (hMn : P1 ≤ normalizer (M : Set G)) {n : G}
    (hn : conjSub n P1 = P1) : conjSub n M = M := by
  subst hP1
  have hJ : IsElemAbelian 2 (M ⊔ zpowers g) := (y7n_J2_facts h).1
  have hJQ : M ⊔ zpowers g ≤ (P ⊔ zpowers g) ⊔ zpowers t :=
    sup_le ((y7n_M_le_P h).trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)
  have hmax : ∀ E : Subgroup G, E ≤ (P ⊔ zpowers g) ⊔ zpowers t → IsElemAbelian 2 E →
      Nat.card E ≤ Nat.card ↥(M ⊔ zpowers g) ∧
        (Nat.card E = Nat.card ↥(M ⊔ zpowers g) → E = M ⊔ zpowers g) := by
    intro E hE hel
    rw [(y7n_J2_facts h).2]
    exact y7n_case2_rank h hE hel
  have hJn : conjSub n (M ⊔ zpowers g) = M ⊔ zpowers g :=
    y7n_conj_eq_of_unique hJ hJQ hmax hn
  calc conjSub n M
      = conjSub n ⁅M ⊔ zpowers g, (P ⊔ zpowers g) ⊔ zpowers t⁆ := by
        rw [y7n_case2_comm h hMn]
    _ = ⁅conjSub n (M ⊔ zpowers g), conjSub n ((P ⊔ zpowers g) ⊔ zpowers t)⁆ :=
        y7n_conjSub_commutator n _ _
    _ = ⁅M ⊔ zpowers g, (P ⊔ zpowers g) ⊔ zpowers t⁆ := by rw [hJn, hn]
    _ = M := y7n_case2_comm h hMn

end CFSG.OddStandard.HigherRank.YamadaG23
