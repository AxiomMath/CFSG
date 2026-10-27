module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Seven
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Diag
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Rank
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65End
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Exact

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem a7_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : Nonempty (A ⧸ center A ≃* alternatingGroup (Fin 7))) (hZ : Odd (Nat.card (center A))) :
    Nonempty (B ⧸ center B ≃* alternatingGroup (Fin 7)) ∧ Odd (Nat.card (center B)) := by
  obtain ⟨f⟩ := hA
  refine ⟨⟨(QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e)).symm.trans f⟩, ?_⟩
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
  exact hZ

theorem mem_normalizer_of_conjSub_eq {X : Type} [Group X] {s : X} {L : Subgroup X}
    (h : conjSub s⁻¹ L = L) : s ∈ normalizer (L : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : x ∈ conjSub s⁻¹ L ↔ s * x * s⁻¹ ∈ L := by
    rw [CFSG.GH74.GLS.TwoThin.mem_conjSub_iff', inv_inv]
  rw [h] at h1
  exact h1

theorem isComponent_subgroupOf_of_le {X : Type} [Group X] {L C : Subgroup X}
    (hL : CFSG.IsComponent L) (hLC : L ≤ C) : CFSG.IsComponent (L.subgroupOf C) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC).symm hL.1,
    hL.2.comap C.subtype⟩

theorem abstract_final (h714 : IVK_7_14_g4) {X : Type} [Group X] [Finite X] (hX4 : Gen4 X)
    (hGH : ∀ L : Subgroup X, CFSG.IsComponent L → GHList (↥L ⧸ center ↥L))
    {s w : X} (hs : s * s = 1) (hw : w ∈ center X) (hw2 : orderOf w = 2)
    (h8 : ¬ 2 ^ 8 ∣ Nat.card X) {A : Subgroup X} (hAC : A ≤ centralizer ({s} : Set X))
    (hAc : CFSG.IsComponent (A.subgroupOf (centralizer ({s} : Set X))))
    (huniq : ∀ B : Subgroup X, B ≤ centralizer ({s} : Set X) →
      CFSG.IsComponent (B.subgroupOf (centralizer ({s} : Set X))) → B = A)
    (hA7 : Nonempty (↥A ⧸ center ↥A ≃* alternatingGroup (Fin 7)))
    (hZodd : Odd (Nat.card (center ↥A))) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hcases : (conjSub s⁻¹ L = L ∧ A ≤ L) ∨
      (conjSub s⁻¹ L ≠ L ∧ ∃ hAB : ⁅L, conjSub s⁻¹ L⁆ = ⊥, A ≤ (swapDiag hAB).range))
    {T : Subgroup X} (hT : M.Syl2In T ⊤) {C : Type} [Group C] (φ : C ≃* ↥T)
    (hC : ∀ c ∈ center C, c ≠ 1 → ∃ g : C, orderOf g = 8 ∧ g ^ 4 = c) : False := by
  have hAq : IsQuasisimple ↥A :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAC) hAc.1
  have hAperf : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.mp hAq.1
  rcases hcases with ⟨hstab, hAL⟩ | ⟨hne, hAB, hAD⟩
  ·
    have hsL := mem_normalizer_of_conjSub_eq hstab
    have hcent := lemma_seven h714 hs hw hw2 h8 hL hsL (hGH L hL) hAL hAC hA7 hZodd hAc huniq
    have hLC : L ≤ centralizer ({s} : Set X) := fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.2 (hcent l hl).symm
    have hLA : L = A := huniq L hLC (isComponent_subgroupOf_of_le hL hLC)
    have hAX : CFSG.IsComponent A := hLA ▸ hL
    have hnormA : ∀ g : X, ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
      intro g a ha
      have hA' : CFSG.IsComponent (A.map (MulAut.conj g).toMonoidHom) :=
        CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hAX
      rcases CFSG.LocalCores.distinct_components_commute hAX hA' with heq | hcomm
      · have : g * a * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
          ⟨a, ha, by simp [MulAut.conj_apply]⟩
        rwa [← heq] at this
      · exfalso
        have hcomm' : ∀ x ∈ A, ∀ y ∈ A.map (MulAut.conj g).toMonoidHom, x * y = y * x := by
          intro x hx y hy
          have h1 := Subgroup.commutator_mem_commutator hx hy
          rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
          exact h1
        obtain ⟨hA7', hZ'⟩ := a7_of_mulEquiv
          (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hA7 hZodd
        exact not_gen4_of_two_a7 hX4 hcomm' hA7 hA7' hZodd hZ' hw hw2
    have hSyl := hT.inf_normal (le_top : A ≤ ⊤) (fun x _ n hn => hnormA x n hn)
    obtain ⟨n, m, hn, hm, hcard⟩ := hSyl.card_eq_pow_mul
    have hAeven : Even (Nat.card ↥A) := even_card_of_quasisimple hAq
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hcard
      exact (Nat.not_even_iff_odd.2 hm) (hcard ▸ hAeven)
    have hne : T ⊓ A ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hn
      have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
      rw [← hn] at h2n
      omega
    exact endgame hA7 hZodd hT.2.1 (fun g _ a ha => hnormA g a ha) hne φ hC
  ·
    exact diag_false hs hw hw2 h8 hne hAB hAperf hAD hA7 hZodd

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
