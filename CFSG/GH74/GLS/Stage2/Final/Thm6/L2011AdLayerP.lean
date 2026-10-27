module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Commutators

variable {G : Type*} [Group G]

theorem commutator_commutator_eq_one_of_commutators_mem_center {a b y : G}
    (ha : ⁅a, y⁆ ∈ center G) (hb : ⁅b, y⁆ ∈ center G) : ⁅⁅a, b⁆, y⁆ = 1 := by
  have hleft : ∀ {z a b : G}, z ∈ center G → ⁅z * a, b⁆ = ⁅a, b⁆ := by
    intro z a b hz
    have h := mem_center_iff.1 hz
    rw [commutatorElement_def, commutatorElement_def]
    calc z * a * b * (z * a)⁻¹ * b⁻¹ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by group
      _ = (a * b * a⁻¹) * z * z⁻¹ * b⁻¹ := by rw [← h (a * b * a⁻¹)]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  have hright : ∀ {z a b : G}, z ∈ center G → ⁅a, z * b⁆ = ⁅a, b⁆ := by
    intro z a b hz
    rw [← commutatorElement_inv, hleft hz, commutatorElement_inv]
  have hc : ⁅y, a⁆ ∈ center G := by
    rw [← commutatorElement_inv]
    exact inv_mem ha
  have hd : ⁅y, b⁆ ∈ center G := by
    rw [← commutatorElement_inv]
    exact inv_mem hb
  have e1 : y * a * y⁻¹ = ⁅y, a⁆ * a := by rw [commutatorElement_def]; group
  have e2 : y * b * y⁻¹ = ⁅y, b⁆ * b := by rw [commutatorElement_def]; group
  have hconj : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  have h : y * ⁅a, b⁆ * y⁻¹ = ⁅a, b⁆ := by
    rw [hconj, e1, e2, hleft hc, hright hd]
  rw [commutatorElement_eq_one_iff_mul_comm]
  calc ⁅a, b⁆ * y = (y * ⁅a, b⁆ * y⁻¹) * y := by rw [h]
    _ = y * ⁅a, b⁆ := by group

end Commutators

section Layer

variable {X : Type*} [Group X] [Finite X]

theorem commutator_centralizer_layer_le {x : X} (hx : x ∈ layer X) :
    ⁅layer X ⊓ centralizer ({x} : Set X), layer X ⊓ centralizer ({x} : Set X)⁆ ≤
      ⨆ Q : ComponentIndex X, Q.1 ⊓ centralizer ({x} : Set X) := by
  rw [commutator_le]
  rintro a ⟨haE, haC⟩ b ⟨hbE, hbC⟩
  obtain ⟨y, rfl⟩ := exists_layerMul_eq haE
  obtain ⟨y', rfl⟩ := exists_layerMul_eq hbE
  obtain ⟨w, rfl⟩ := exists_layerMul_eq hx
  have hcoord : ∀ z : ∀ K : ComponentIndex X, K.1,
      layerMul X z ∈ centralizer ({layerMul X w} : Set X) → ∀ Q, ⁅z Q, w Q⁆ ∈ center Q.1 := by
    intro z hz Q
    have hker : ⁅z, w⁆ ∈ (layerMul X).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mem_centralizer_singleton_iff.mp hz
    exact layerMul_ker_le hker Q (Set.mem_univ Q)
  have hy := hcoord y haC
  have hy' := hcoord y' hbC
  have hcomm : ⁅layerMul X y, layerMul X y'⁆ = layerMul X (fun Q => ⁅y Q, y' Q⁆) := by
    rw [← map_commutatorElement]
    rfl
  rw [hcomm]
  refine layerMul_mem _ fun Q => ?_
  refine mem_iSup_of_mem Q ⟨(⁅y Q, y' Q⁆).2, ?_⟩
  have h1 := commutator_commutator_eq_one_of_commutators_mem_center (hy Q) (hy' Q)
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  have h2 : Commute ((⁅y Q, y' Q⁆ : Q.1) : X) (w Q : X) := congrArg Subtype.val h1
  have h3 := (commute_layerMul_iff w Q (⁅y Q, y' Q⁆ : Q.1).2).mpr h2
  exact mem_centralizer_singleton_iff.mpr h3.eq

end Layer

theorem exists_component_ge_of_component_centralizer {X : Type} [Group X] [Finite X] {x : X}
    (hx : x ∈ layer X) {K : Subgroup X} (hKE : K ≤ layer X)
    (hKC : K ≤ centralizer ({x} : Set X))
    (hK : IsComponent (K.subgroupOf (centralizer ({x} : Set X)))) :
    ∃ Q : Subgroup X, IsComponent Q ∧ K ≤ Q := by
  by_contra hno
  have hKq : IsQuasisimple K := isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKC) hK.1
  have hperf : ⁅K, K⁆ = K := isPerfect_iff.mp hKq.1
  have hnt : Nontrivial K := isQuasisimple_nontrivial hKq
  have hKP : K ≤ ⨆ Q : ComponentIndex X, Q.1 ⊓ centralizer ({x} : Set X) :=
    calc K = ⁅K, K⁆ := hperf.symm
      _ ≤ ⁅layer X ⊓ centralizer ({x} : Set X), layer X ⊓ centralizer ({x} : Set X)⁆ :=
        commutator_mono (le_inf hKE hKC) (le_inf hKE hKC)
      _ ≤ _ := commutator_centralizer_layer_le hx
  have hcent : ∀ Q : ComponentIndex X,
      Q.1 ⊓ centralizer ({x} : Set X) ≤ centralizer (K : Set X) := by
    intro Q
    rcases component_subnormal_subgroup hK (Q.2.2.subgroupOf (K := centralizer ({x} : Set X)))
      with h | h
    · exact (hno ⟨Q.1, Q.2, le_of_subgroupOf_le hKC h⟩).elim
    · exact le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (commutator_inf_eq_bot_of_subgroupOf hKC h))
  have hKK : ⁅K, K⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hKP.trans (iSup_le hcent))
  rw [hperf] at hKK
  exact (nontrivial_iff_ne_bot K).mp hnt hKK

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
