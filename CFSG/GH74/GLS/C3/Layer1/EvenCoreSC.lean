module

public import CFSG.GH74.GLS.TwoThin.Struct

public section

namespace CFSG.GH74.GLS.EvenCore

open Subgroup CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

theorem le_layer_of_isTwoComponent {H : Type} [Group H] [Finite H]
    (hcore : CFSG.pPrimeCore 2 H = ⊥) {b : H} (hb : orderOf b = 2) {K : Subgroup H}
    (hK : K ≤ centralizer ({b} : Set H))
    (hKc : TwoComponents.IsTwoComponent (K.subgroupOf (centralizer ({b} : Set H)))) :
    K ≤ CFSG.layer H := by
  have hsq : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb, pow_two] at this
  have hodd : CFSG.Open.componentClassificationOddCore H = ⊥ := by
    rw [← CatalogueBAlternating.primeCore_two_eq_oddCore]
    exact hcore
  have h := CFSG.ClassicalInvolution.twoComponent_le_layer_of_l2PrimeBalance
    CFSG.ClassicalInvolution.l2PrimeBalance hodd hsq
    (C := centralizer ({b} : Set H)) rfl hKc
  rw [Subgroup.map_subgroupOf_eq_of_le hK, layer_subgroup_eq_layer] at h
  exact h

theorem false_of_three {α : Type*} {A B x y z : α} (hx : x = A ∨ x = B) (hy : y = A ∨ y = B)
    (hz : z = A ∨ z = B) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) : False := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp_all

section Orbit

variable {H : Type} [Group H]

theorem eq_or_eq_of_commutator_ne_bot [Finite H] {L : Subgroup H} {a : H}
    (hL : CFSG.IsComponent L) (hLa : conjSub a⁻¹ L ≠ L) {K : Subgroup H}
    (hKD : K ≤ (swapDiag (commutator_conjSub_eq_bot hL hLa)).range) {M : Subgroup H}
    (hM : CFSG.IsComponent M) (hKM : ⁅K, M⁆ ≠ ⊥) : M = L ∨ M = conjSub a⁻¹ L := by
  refine eq_or_eq_of_not_le_centralizer_diag hL hLa hM fun h => hKM ?_
  rw [commutator_eq_bot_iff_le_centralizer]
  exact hKD.trans (le_centralizer_iff.1 h)

theorem conjSub_ne_of_eq_or_eq {L M : Subgroup H} {b : H} (hb : b⁻¹ = b)
    (hLb : conjSub b⁻¹ L ≠ L) (hM : M = L ∨ M = conjSub b⁻¹ L) : conjSub b⁻¹ M ≠ M := by
  rcases hM with rfl | rfl
  · exact hLb
  · rw [conjSub_conjSub_of_inv_eq hb]
    exact fun h => hLb h.symm

theorem commutator_conjSub_ne_bot {K : Subgroup H} {t : H} (ht : t ∈ centralizer (K : Set H))
    {M : Subgroup H} (hKM : ⁅K, M⁆ ≠ ⊥) : ⁅K, conjSub t⁻¹ M⁆ ≠ ⊥ := by
  have h : conjSub t⁻¹ K = K :=
    conjSub_eq_of_mem_normalizer (centralizer_le_normalizer K (inv_mem ht))
  have h2 : ⁅K, conjSub t⁻¹ M⁆ = conjSub t⁻¹ ⁅K, M⁆ := by
    rw [← commutator_conjSub, h]
  rw [h2, Ne, conjSub_eq_bot_iff]
  exact hKM

theorem mem_centralizer_of_le_centralizer {K : Subgroup H} {b : H}
    (h : K ≤ centralizer ({b} : Set H)) : b ∈ centralizer (K : Set H) := by
  rw [mem_centralizer_iff]
  intro k hk
  exact (mem_centralizer_iff.1 (h hk) b rfl).symm

end Orbit

theorem exists_component_ge_of_fourGroup {H : Type} [Group H] [Finite H]
    (hcore : CFSG.pPrimeCore 2 H = ⊥) {K : Subgroup H} {u v : H}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u * v = v * u) (hne : u ≠ v)
    (hKu : K ≤ centralizer ({u} : Set H) ∧
      TwoComponents.IsTwoComponent (K.subgroupOf (centralizer ({u} : Set H))))
    (hKv : K ≤ centralizer ({v} : Set H) ∧
      TwoComponents.IsTwoComponent (K.subgroupOf (centralizer ({v} : Set H))))
    (hKw : K ≤ centralizer ({u * v} : Set H) ∧
      TwoComponents.IsTwoComponent (K.subgroupOf (centralizer ({u * v} : Set H)))) :
    ∃ L : Subgroup H, CFSG.IsComponent L ∧ K ≤ L := by
  have hu' : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two hu
  have hv' : v⁻¹ = v := inv_eq_self_of_orderOf_eq_two hv
  have hw : orderOf (u * v) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h1 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
      have h2 : v * v = 1 := by rw [← pow_two, ← hv]; exact pow_orderOf_eq_one v
      calc (u * v) ^ 2 = u * v * (u * v) := pow_two _
        _ = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [huv]
        _ = u * u * (v * v) := by group
        _ = 1 := by rw [h1, h2, one_mul]
    · intro h
      apply hne
      rw [mul_eq_one_iff_eq_inv, hv'] at h
      exact h
  have hw' : (u * v)⁻¹ = u * v := inv_eq_self_of_orderOf_eq_two hw
  by_contra hcon
  have hcon' : ∀ L : Subgroup H, CFSG.IsComponent L → ¬ K ≤ L := fun L hL hKL =>
    hcon ⟨L, hL, hKL⟩
  have hdata : ∀ {b : H}, orderOf b = 2 → K ≤ centralizer ({b} : Set H) →
      TwoComponents.IsTwoComponent (K.subgroupOf (centralizer ({b} : Set H))) →
      ∃ L : Subgroup H, conjSub b⁻¹ L ≠ L ∧
        ∀ M : Subgroup H, CFSG.IsComponent M → ⁅K, M⁆ ≠ ⊥ → M = L ∨ M = conjSub b⁻¹ L := by
    intro b hb hKC hKc
    obtain ⟨L, hL, hcase⟩ := exists_component_orbit_location hb hKC hKc
      (le_layer_of_isTwoComponent hcore hb hKC hKc)
    rcases hcase with ⟨-, hKL⟩ | ⟨hLb, hAB, hKD⟩
    · exact absurd hKL (hcon' L hL)
    · exact ⟨L, hLb, fun M hM hKM => eq_or_eq_of_commutator_ne_bot hL hLb hKD hM hKM⟩
  obtain ⟨Lu, hLu, hSu⟩ := hdata hu hKu.1 hKu.2
  obtain ⟨Lv, hLv, hSv⟩ := hdata hv hKv.1 hKv.2
  obtain ⟨Lw, hLw, hSw⟩ := hdata hw hKw.1 hKw.2
  have hnonempty : ∃ M : Subgroup H, CFSG.IsComponent M ∧ ⁅K, M⁆ ≠ ⊥ := by
    by_contra hcon2
    have hall : ∀ M : Subgroup H, CFSG.IsComponent M → ⁅K, M⁆ = ⊥ := fun M hM =>
      not_not.1 fun h => hcon2 ⟨M, hM, h⟩
    have hlay : CFSG.layer H ≤ centralizer (K : Set H) := by
      refine sSup_le fun M hM => ?_
      exact le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 (hall M hM))
    have hKlay := le_layer_of_isTwoComponent hcore hu hKu.1 hKu.2
    have hKK : ⁅K, K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 (hKlay.trans hlay)
    exact ne_bot_of_isTwoComponent hKu.2
      (by rw [← commutator_self_of_isTwoComponent hKu.1 hKu.2, hKK])
  obtain ⟨M, hM, hKM⟩ := hnonempty
  have hKu' := mem_centralizer_of_le_centralizer hKu.1
  have hKv' := mem_centralizer_of_le_centralizer hKv.1
  have hM₁c : CFSG.IsComponent (conjSub u⁻¹ M) := isComponent_conjSub hM u⁻¹
  have hM₂c : CFSG.IsComponent (conjSub v⁻¹ (conjSub u⁻¹ M)) :=
    isComponent_conjSub hM₁c v⁻¹
  have hKM₁ : ⁅K, conjSub u⁻¹ M⁆ ≠ ⊥ := commutator_conjSub_ne_bot hKu' hKM
  have hKM₂ : ⁅K, conjSub v⁻¹ (conjSub u⁻¹ M)⁆ ≠ ⊥ := commutator_conjSub_ne_bot hKv' hKM₁
  have h12 : conjSub u⁻¹ M ≠ M := conjSub_ne_of_eq_or_eq hu' hLu (hSu M hM hKM)
  have h23 : conjSub v⁻¹ (conjSub u⁻¹ M) ≠ conjSub u⁻¹ M :=
    conjSub_ne_of_eq_or_eq hv' hLv (hSv _ hM₁c hKM₁)
  have h31 : conjSub (u * v)⁻¹ M ≠ M := conjSub_ne_of_eq_or_eq hw' hLw (hSw M hM hKM)
  have hM₂eq : conjSub v⁻¹ (conjSub u⁻¹ M) = conjSub (u * v)⁻¹ M := by
    rw [mul_inv_rev, conjSub_mul]
  rw [← hM₂eq] at h31
  exact false_of_three (hSw M hM hKM) (hSw _ hM₁c hKM₁) (hSw _ hM₂c hKM₂) h12.symm h23.symm h31

end CFSG.GH74.GLS.EvenCore
