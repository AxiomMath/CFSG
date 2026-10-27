module

public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Reduce
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Hopf
public import CFSG.LieType.Steinberg.CentralExt.GriessOmegaEightTwo
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pOuter
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (IsElemAbelian griessHopfMultiplier StatedClassicalModel)
open CFSG.Blueprint.Multiplier

theorem i1021_isElemAbelian_of_le {G : Type*} [Group G] {p : ℕ} {E P : Subgroup G}
    (hE : IsElemAbelian p E) (hPE : P ≤ E) : IsElemAbelian p P :=
  CFSG.Open.IsElemAbelian.mono hE hPE

theorem i1021_isElemAbelian_subgroupOf {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (H : Subgroup G) : IsElemAbelian p (E.subgroupOf H) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE H

theorem i1021_d4_pRank_ge_four
    {F : Type} [Group F] [Finite F] (h : StatedClassicalModel F .POmegaPlus 4 2 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : 1 < 3 := by norm_num
  have hLie : CFSG.Blueprint.LieModel F .POmegaPlus 4 2 1 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], h⟩
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have : Finite K := by assumption
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := by
    have hc : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card, hK]; rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime hc
  have h3 := CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three (K := K) (n := 4) le_rfl
  have h3F : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup F) := by
    rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e]
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup F)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 3 (n := 2) (by
    rw [hEc]
    exact pow_dvd_pow 3 (by omega))
  set P : Subgroup F := H.map E.subtype
  have hPE : P ≤ E := Subgroup.map_subtype_le H
  have hP9 : Nat.card P = 9 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hH]
    norm_num
  obtain ⟨E', hE', h81, hPE'⟩ := CFSG.RankThree.PartTwo.Sec4.Item434O8pOuter.exists_e81_of_e9_o8p
    hLie (i1021_isElemAbelian_of_le hE hPE) hP9
  have hE'3 : IsPGroup 3 E' := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE'.2 g g.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hE'3
  have h4 : 3 ^ 4 ≤ 3 ^ k := by
    rw [← hk]
    exact h81
  exact (Nat.pow_le_pow_iff_right hp1).1 h4 |>.trans
    (CFSG.SectionRank.le_pRank hp1 le_top hE' hk)

theorem i1021_card_table_D4 :
    Nat.card (generic .POmegaPlus 4 2 1 × exceptional .POmegaPlus 4 2 1) = 4 := by
  have hg : genericOrders .POmegaPlus 4 2 1 = (1, 1) := by simp [genericOrders]
  have he : exceptionalOrders .POmegaPlus 4 2 1 = (2, 2) := rfl
  unfold generic exceptional
  rw [hg, he]
  simp

theorem i1021_hcen_D4
    {F : Type} [Group F] [Finite F] (h : StatedClassicalModel F .POmegaPlus 4 2 1)
    (L : Type) [Group L] [Finite L] (ψ : L →* F) (hψ : Function.Surjective ψ)
    (hperf : commutator L = ⊤) (hker : ψ.ker ≤ Subgroup.center L) (hp : IsPGroup 3 ψ.ker) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLie : CFSG.Models.LieModel F .POmegaPlus 4 2 1 := ⟨h.1, Or.inl h⟩
  obtain ⟨-, ⟨eH⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_four_two_row
    hLie
  have : Finite (generic .POmegaPlus 4 2 1 × exceptional .POmegaPlus 4 2 1) :=
    Nat.finite_of_card_ne_zero (by rw [i1021_card_table_D4]; norm_num)
  have hdvd := i1021_card_ker_dvd ψ hψ hker hperf eH
  rw [i1021_card_table_D4] at hdvd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hp
  have hk0 : k = 0 := by
    rw [hk] at hdvd
    by_contra hne
    have h3 : 3 ∣ 4 := (dvd_pow_self 3 hne).trans hdvd
    omega
  have hbot : ψ.ker = ⊥ := by
    rw [hk0] at hk
    exact Subgroup.card_eq_one.1 (by simpa using hk)
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hbot
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
    (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩)]
  exact i1021_d4_pRank_ge_four h

theorem i1021_d4_of_two_rank
    {F : Type} [Group F] [Finite F] (h : StatedClassicalModel F .POmegaPlus 4 2 1)
    {V : Subgroup F} (hV : IsElemAbelian 2 V) (hVc : Nat.card V = 2 ^ 4)
    (X : Type) [Group X] [Finite X] (φ : X →* F) (hφ : Function.Surjective φ) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hLie : CFSG.Models.LieModel F .POmegaPlus 4 2 1 := ⟨h.1, Or.inl h⟩
  obtain ⟨hnt, hsimple⟩ := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
    F 4 2 1 h
  obtain ⟨hperfF, -⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_four_two_row
    hLie
  have hnc : ∃ a b : F, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have : commutator F = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact (hc a b).symm
    rw [hperfF] at this
    exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup F)).1 inferInstance this
  have hcen : ∀ (X1 : Type) [Group X1] [Finite X1] (ψ : X1 →* F), Function.Surjective ψ →
      commutator X1 = ⊤ → ψ.ker ≤ Subgroup.center X1 → IsPGroup 3 ψ.ker →
        4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X1) := by
    intro X1 _ _ ψ hψ hperf hker hp
    exact i1021_hcen_D4 h X1 ψ hψ hperf hker hp
  exact i1021_main hnc Nat.prime_three (by norm_num) (by norm_num) hV hVc hcen _ X le_rfl φ hφ

end CFSG.HardMathSupport.Solomon.Coordinator
