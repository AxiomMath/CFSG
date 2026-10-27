module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionNormalizer

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open
open scoped commutatorElement
open CFSG.ComponentClassification.AschbacherComponentInvolution
open CFSG.ComponentClassification.AschbacherComponentAction

private theorem normalizer_le_normalizer_centralizer {X : Type*} [Group X] (H : Subgroup X) :
    Subgroup.normalizer (H : Set X) ≤
      Subgroup.normalizer ((Subgroup.centralizer (H : Set X)) : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc h hh
    have hy : g⁻¹ * h * g ∈ H :=
      (hg (g⁻¹ * h * g)).mpr (by
        rw [show g * (g⁻¹ * h * g) * g⁻¹ = h from by group]
        exact hh)
    calc
      h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc (g⁻¹ * h * g) hy]
      _ = (g * c * g⁻¹) * h := by group
  · intro hc h hh
    have hy : g * h * g⁻¹ ∈ H := (hg h).mp hh
    calc
      h * c = g⁻¹ * ((g * h * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * h * g⁻¹)) * g := by rw [hc (g * h * g⁻¹) hy]
      _ = c * h := by group

private theorem layer_eq_sup_centralizer {X : Type*} [Group X] [Finite X] (L : Subgroup X)
    (hL : IsComponentOf L ⊤) :
    CFSG.ComponentClassification.Layer.subgroup X =
      L ⊔ (Subgroup.centralizer (L : Set X) ⊓
        CFSG.ComponentClassification.Layer.subgroup X) := by
  apply le_antisymm
  · rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
    apply sSup_le
    intro M hM
    by_cases hML : M = L
    · rw [hML]
      exact le_sup_left
    · have hMcomm : ⁅M, L⁆ = ⊥ :=
        CFSG.ComponentClassification.LocalComponents.commute_of_ne M L hM hL hML
      have hMC : M ≤ Subgroup.centralizer (L : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMcomm
      exact (le_inf hMC (CFSG.ComponentClassification.Layer.component_le hM)).trans le_sup_right
  · exact sup_le (CFSG.ComponentClassification.Layer.component_le hL) inf_le_right

private theorem commutator_mul_mul_comm_eq {X : Type*} [Group X] (x₁ y₁ x₂ y₂ : X)
    (h₁ : Commute x₁ y₂) (h₂ : Commute x₂ y₁)
    (h₃ : Commute x₁ ⁅y₁, y₂⁆) (h₄ : Commute x₂ ⁅y₁, y₂⁆)
    (h₅ : Commute ⁅y₁, y₂⁆ ⁅x₁, x₂⁆) :
    ⁅x₁ * y₁, x₂ * y₂⁆ = ⁅x₁, x₂⁆ * ⁅y₁, y₂⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul x₁ y₁ (x₂ * y₂),
    commutatorElement_mul_right_eq_mul_conj y₁ x₂ y₂,
    commutatorElement_mul_right_eq_mul_conj x₁ x₂ y₂,
    h₂.symm.commutator_eq, h₁.commutator_eq, one_mul, mul_one]
  rw [h₄.mul_inv_cancel, mul_inv_cancel_right, h₃.mul_inv_cancel, h₅.eq]

private theorem commutator_mul_eq_of_central {X : Type*} [Group X] (x₁ z₁ x₂ z₂ : X)
    (h₁ : Commute z₁ x₂) (h₂ : Commute z₁ z₂) (h₃ : Commute x₁ z₂) :
    ⁅x₁ * z₁, x₂ * z₂⁆ = ⁅x₁, x₂⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul x₁ z₁ (x₂ * z₂),
    commutatorElement_mul_right_eq_mul_conj z₁ x₂ z₂,
    commutatorElement_mul_right_eq_mul_conj x₁ x₂ z₂,
    h₂.commutator_eq, h₁.commutator_eq, h₃.commutator_eq]
  group

private theorem le_sup_of_perfect_fixed {X : Type*} [Group X] (L C' E : Subgroup X) (a : X)
    [Group.IsPerfect E]
    (hLC : ⁅L, C'⁆ = ⊥) (hE : E ≤ L ⊔ C')
    (hEfix : E ≤ Subgroup.centralizer ({a} : Set X))
    (haL : a ∈ Subgroup.normalizer (L : Set X))
    (haC' : a ∈ Subgroup.normalizer (C' : Set X)) :
    E ≤ (L ⊓ Subgroup.centralizer ({a} : Set X)) ⊔
        (C' ⊓ Subgroup.centralizer ({a} : Set X)) := by
  let C := Subgroup.centralizer ({a} : Set X)
  let P := L ⊓ C
  let Q := C' ⊓ C
  have hC'NL : C' ≤ Subgroup.normalizer (L : Set X) := by
    have h' : ⁅C', L⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hLC
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h').trans
      (Subgroup.centralizer_le_normalizer (L : Set X))
  have hcomm : ∀ l ∈ L, ∀ c ∈ C', l * c = c * l := fun l hl c hc =>
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLC hl) c hc).symm
  have hcommutator_mem : ∀ e₁ ∈ E, ∀ e₂ ∈ E, ⁅e₁, e₂⁆ ∈ P ⊔ Q := by
    intro e₁ he₁ e₂ he₂
    obtain ⟨m₁, hm₁, c₁, hc₁, hcoord₁⟩ :=
      CFSG.ComponentClassification.NormalizedProduct.coordinates L C' hC'NL e₁ (hE he₁)
    obtain ⟨m₂, hm₂, c₂, hc₂, hcoord₂⟩ :=
      CFSG.ComponentClassification.NormalizedProduct.coordinates L C' hC'NL e₂ (hE he₂)
    have hae₁ : a * e₁ * a⁻¹ = e₁ := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEfix he₁), mul_inv_cancel_right]
    have hae₂ : a * e₂ * a⁻¹ = e₂ := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEfix he₂), mul_inv_cancel_right]
    have ham₁ : a * m₁ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haL m₁).mp hm₁
    have ham₂ : a * m₂ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haL m₂).mp hm₂
    have hac₁ : a * c₁ * a⁻¹ ∈ C' := (Subgroup.mem_normalizer_iff.mp haC' c₁).mp hc₁
    have hac₂ : a * c₂ * a⁻¹ ∈ C' := (Subgroup.mem_normalizer_iff.mp haC' c₂).mp hc₂
    have hprod₁ : (a * m₁ * a⁻¹) * (a * c₁ * a⁻¹) = m₁ * c₁ := by
      calc
        (a * m₁ * a⁻¹) * (a * c₁ * a⁻¹) = a * (m₁ * c₁) * a⁻¹ := by group
        _ = a * e₁ * a⁻¹ := by rw [hcoord₁]
        _ = e₁ := hae₁
        _ = m₁ * c₁ := hcoord₁.symm
    have hprod₂ : (a * m₂ * a⁻¹) * (a * c₂ * a⁻¹) = m₂ * c₂ := by
      calc
        (a * m₂ * a⁻¹) * (a * c₂ * a⁻¹) = a * (m₂ * c₂) * a⁻¹ := by group
        _ = a * e₂ * a⁻¹ := by rw [hcoord₂]
        _ = e₂ := hae₂
        _ = m₂ * c₂ := hcoord₂.symm
    set z₁ : X := m₁⁻¹ * (a * m₁ * a⁻¹) with hz₁def
    set z₂ : X := m₂⁻¹ * (a * m₂ * a⁻¹) with hz₂def
    have hz₁L : z₁ ∈ L := by
      rw [hz₁def]
      exact L.mul_mem (L.inv_mem hm₁) ham₁
    have hz₂L : z₂ ∈ L := by
      rw [hz₂def]
      exact L.mul_mem (L.inv_mem hm₂) ham₂
    have hz₁C' : z₁ ∈ C' := by
      have h₁ : z₁ * (a * c₁ * a⁻¹) = c₁ := by
        rw [hz₁def]
        have h := congrArg (fun x => m₁⁻¹ * x) hprod₁
        rw [inv_mul_cancel_left] at h
        simpa only [mul_assoc] using h
      have hz₁eq : z₁ = c₁ * (a * c₁ * a⁻¹)⁻¹ := by
        have h := congrArg (fun x => x * (a * c₁ * a⁻¹)⁻¹) h₁
        rw [mul_assoc, mul_inv_cancel, mul_one] at h
        exact h
      rw [hz₁eq]
      exact C'.mul_mem hc₁ (C'.inv_mem hac₁)
    have hz₂C' : z₂ ∈ C' := by
      have h₁ : z₂ * (a * c₂ * a⁻¹) = c₂ := by
        rw [hz₂def]
        have h := congrArg (fun x => m₂⁻¹ * x) hprod₂
        rw [inv_mul_cancel_left] at h
        simpa only [mul_assoc] using h
      have hz₂eq : z₂ = c₂ * (a * c₂ * a⁻¹)⁻¹ := by
        have h := congrArg (fun x => x * (a * c₂ * a⁻¹)⁻¹) h₁
        rw [mul_assoc, mul_inv_cancel, mul_one] at h
        exact h
      rw [hz₂eq]
      exact C'.mul_mem hc₂ (C'.inv_mem hac₂)
    have ham₁' : a * m₁ * a⁻¹ = m₁ * z₁ := by rw [hz₁def]; group
    have ham₂' : a * m₂ * a⁻¹ = m₂ * z₂ := by rw [hz₂def]; group
    have hac₁' : a * c₁ * a⁻¹ = z₁⁻¹ * c₁ := by
      have h := congrArg (fun x => (a * m₁ * a⁻¹)⁻¹ * x) hprod₁
      rw [inv_mul_cancel_left] at h
      rw [h, ham₁']
      group
    have hac₂' : a * c₂ * a⁻¹ = z₂⁻¹ * c₂ := by
      have h := congrArg (fun x => (a * m₂ * a⁻¹)⁻¹ * x) hprod₂
      rw [inv_mul_cancel_left] at h
      rw [h, ham₂']
      group
    have hm12L : ⁅m₁, m₂⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem hm₁ hm₂) (L.inv_mem hm₁)) (L.inv_mem hm₂)
    have hc12C' : ⁅c₁, c₂⁆ ∈ C' := by
      rw [commutatorElement_def]
      exact C'.mul_mem (C'.mul_mem (C'.mul_mem hc₁ hc₂) (C'.inv_mem hc₁)) (C'.inv_mem hc₂)
    have hm12C : ⁅m₁, m₂⁆ ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hconj : a * ⁅m₁, m₂⁆ * a⁻¹ = ⁅m₁, m₂⁆ := by
        rw [conjugate_commutatorElement, ham₁', ham₂']
        exact commutator_mul_eq_of_central m₁ z₁ m₂ z₂
          (hcomm m₂ hm₂ z₁ hz₁C').symm
          (hcomm z₂ hz₂L z₁ hz₁C').symm
          (hcomm m₁ hm₁ z₂ hz₂C')
      have h := congrArg (fun x => x * a) hconj
      rw [mul_assoc, inv_mul_cancel, mul_one] at h
      exact h.symm
    have hc12C : ⁅c₁, c₂⁆ ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hconj : a * ⁅c₁, c₂⁆ * a⁻¹ = ⁅c₁, c₂⁆ := by
        have hz12 : ⁅z₁⁻¹, z₂⁻¹⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (hcomm z₂⁻¹ (L.inv_mem hz₂L) z₁⁻¹ (C'.inv_mem hz₁C')).symm
        have hCM : Commute ⁅c₁, c₂⁆ ⁅z₁⁻¹, z₂⁻¹⁆ := by
          rw [hz12]
          exact Commute.one_right _
        rw [conjugate_commutatorElement, hac₁', hac₂',
          commutator_mul_mul_comm_eq z₁⁻¹ c₁ z₂⁻¹ c₂
            (hcomm z₁⁻¹ (L.inv_mem hz₁L) c₂ hc₂)
            (hcomm z₂⁻¹ (L.inv_mem hz₂L) c₁ hc₁)
            (hcomm z₁⁻¹ (L.inv_mem hz₁L) ⁅c₁, c₂⁆ hc12C')
            (hcomm z₂⁻¹ (L.inv_mem hz₂L) ⁅c₁, c₂⁆ hc12C')
            hCM,
          hz12, one_mul]
      have h := congrArg (fun x => x * a) hconj
      rw [mul_assoc, inv_mul_cancel, mul_one] at h
      exact h.symm
    have hm12P : ⁅m₁, m₂⁆ ∈ P := ⟨hm12L, hm12C⟩
    have hc12Q : ⁅c₁, c₂⁆ ∈ Q := ⟨hc12C', hc12C⟩
    have hkey : ⁅e₁, e₂⁆ = ⁅m₁, m₂⁆ * ⁅c₁, c₂⁆ := by
      rw [← hcoord₁, ← hcoord₂]
      exact commutator_mul_mul_comm_eq m₁ c₁ m₂ c₂
        (hcomm m₁ hm₁ c₂ hc₂)
        (hcomm m₂ hm₂ c₁ hc₁)
        (hcomm m₁ hm₁ ⁅c₁, c₂⁆ hc12C')
        (hcomm m₂ hm₂ ⁅c₁, c₂⁆ hc12C')
        (hcomm ⁅m₁, m₂⁆ hm12L ⁅c₁, c₂⁆ hc12C').symm
    rw [hkey]
    exact Subgroup.mul_mem_sup hm12P hc12Q
  rw [← Subgroup.commutator_eq_self (H := E)]
  exact Subgroup.commutator_le.mpr hcommutator_mem

@[expose] def diagDerived {X : Type} [Group X] (L : Subgroup X) (a : X) : Subgroup X :=
  ⁅⁅L, zpowers a⁆ ⊓ centralizer ({a} : Set X), ⁅L, zpowers a⁆ ⊓ centralizer ({a} : Set X)⁆

theorem component_dichotomy {X : Type} [Group X] [Finite X] {a : X} (ha : orderOf a = 2)
    {E : Subgroup X} (hEC : E ≤ centralizer ({a} : Set X))
    (hEn : (E.subgroupOf (centralizer ({a} : Set X))).Normal)
    (hE : IsComponentOf (E.subgroupOf (centralizer ({a} : Set X))) ⊤)
    (hEΛ : E ≤ CFSG.ComponentClassification.Layer.subgroup X) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (hEL : ⁅E, L⁆ ≠ ⊥) :
    (a ∉ normalizer (L : Set X) ∧ E = diagDerived L a) ∨
      (a ∈ normalizer (L : Set X) ∧ E ≤ L) := by
  by_cases haL : a ∈ normalizer (L : Set X)
  · right
    refine ⟨haL, ?_⟩
    let C := Subgroup.centralizer ({a} : Set X)
    let Λ := CFSG.ComponentClassification.Layer.subgroup X
    let C' := Subgroup.centralizer (L : Set X) ⊓ Λ
    let P := L ⊓ C
    let Q := C' ⊓ C
    have hquasiE : IsQuasisimple E :=
      ((CFSG.ComponentClassification.OrdinaryComponentTransport.subgroupOf_iff E C hEC).mp hE).2
    let : Group.IsPerfect E := ⟨hquasiE.1⟩
    have hENL : E ≤ Subgroup.normalizer (L : Set X) :=
      involution_component_normalizes a ha E hEC hE L hL
    have hCE : C ≤ Subgroup.normalizer (E : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hEC).mp hEn
    have hΛeq : Λ = L ⊔ C' := layer_eq_sup_centralizer L hL
    have hLC : ⁅L, C'⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_left
    have haΛ : a ∈ Subgroup.normalizer (Λ : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr
        (CFSG.ComponentClassification.Layer.normal X)]
      exact Subgroup.mem_top a
    have haC' : a ∈ Subgroup.normalizer (C' : Set X) :=
      (Subgroup.inf_normalizer_le_normalizer_inf
        (H := Subgroup.centralizer (L : Set X)) (K := Λ))
        ⟨normalizer_le_normalizer_centralizer L haL, haΛ⟩
    have hEPQ : E ≤ (L ⊓ C) ⊔ (C' ⊓ C) :=
      le_sup_of_perfect_fixed L C' E a hLC (hEΛ.trans hΛeq.le) hEC haL haC'
    have hPE : P ≤ Subgroup.normalizer (E : Set X) := inf_le_right.trans hCE
    have hQE : Q ≤ Subgroup.normalizer (E : Set X) := inf_le_right.trans hCE
    have hQP : ⁅Q, P⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (by rw [Subgroup.commutator_comm C' L]; exact hLC.le))
    have hQNP : Q ≤ Subgroup.normalizer (P : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQP).trans
        (Subgroup.centralizer_le_normalizer (P : Set X))
    have hEC'N : E ≤ Subgroup.normalizer (C' : Set X) :=
      (le_inf (hENL.trans (normalizer_le_normalizer_centralizer L))
        (hEΛ.trans Subgroup.le_normalizer)).trans
        (Subgroup.inf_normalizer_le_normalizer_inf
          (H := Subgroup.centralizer (L : Set X)) (K := Λ))
    rcases normalized_quasisimple_le_or_commutes E L P hquasiE hPE inf_le_left hENL with
      hcontained | hEP
    · exact hcontained
    · rcases normalized_quasisimple_le_or_commutes E C' Q hquasiE hQE inf_le_left hEC'N with
        hEC'' | hEQ
      · have hle : ⁅E, L⁆ ≤ ⊥ := by
          calc
            ⁅E, L⁆ ≤ ⁅C', L⁆ := Subgroup.commutator_mono hEC'' le_rfl
            _ = ⁅L, C'⁆ := Subgroup.commutator_comm C' L
            _ = ⊥ := hLC
        exact absurd (le_bot_iff.mp hle) hEL
      · exfalso
        have hEcenter : E ≤ Subgroup.centralizer (E : Set X) := by
          intro e he
          rw [Subgroup.mem_centralizer_iff]
          intro f hf
          obtain ⟨p, hp, q, hq, hpq⟩ :=
            CFSG.ComponentClassification.NormalizedProduct.coordinates P Q hQNP e (hEPQ he)
          have hfp : p * f = f * p :=
            Subgroup.mem_centralizer_iff.mp
              (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hEP hf) p hp
          have hfq : q * f = f * q :=
            Subgroup.mem_centralizer_iff.mp
              (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hEQ hf) q hq
          have hpqf : Commute (p * q) f := Commute.mul_left hfp hfq
          rw [← hpq]
          exact hpqf.symm
        have hbot : E = ⊥ := by
          rw [← Subgroup.commutator_eq_self (H := E)]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hEcenter
        exact (Subgroup.nontrivial_iff_ne_bot E).mp
          (CFSG.ComponentClassification.Quasisimple.nontrivial hquasiE) hbot
  · left
    refine ⟨haL, ?_⟩
    have hmoved : rightComponent L a ≠ L := fun h =>
      haL ((rightComponent_eq_iff_normalizer L a).mp h)
    rcases moved_component_alternative a ha E L hEC hE hL hmoved with hbot | hdiag
    · exact absurd hbot hEL
    · simpa only [diagDerived] using hdiag

end CFSG.EvenSporadicStandard.Co3Std.CentT
