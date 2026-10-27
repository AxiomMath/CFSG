module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BridgeParts
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Lift55Aux
import CFSG.GH74.GLS.Stage2.Local.P34Perf

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

namespace Lift55Aux

variable {M : Type} [Group M] [Finite M]

theorem card_components_le_four_of_no_three
    (h3 : ∀ J₁ J₂ J₃ : Subgroup M, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False) :
    Nat.card {K : Subgroup M // IsComponent K} ≤ 4 := by
  classical
  have : Fintype {K : Subgroup M // IsComponent K} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  by_contra hlt
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    (Fintype.two_lt_card_iff (α := {K : Subgroup M // IsComponent K})).1 (by omega)
  exact h3 a.1 b.1 c.1 a.2 b.2 c.2 (fun h => hab (Subtype.ext h)) (fun h => hac (Subtype.ext h))
    (fun h => hbc (Subtype.ext h))

theorem fittingSubgroup_le_pCore_two (hO : pPrimeCore 2 M = ⊥) :
    fittingSubgroup M ≤ pCore 2 M :=
  le_sSup ⟨fittingSubgroup_normal,
    isPGroup_of_nilpotent_normal _ fittingSubgroup_normal inferInstance hO⟩

end Lift55Aux

theorem exists_component_moved {M : Type} [Group M] [Finite M] (hSch : P34.GHSchreier)
    (hO : pPrimeCore 2 M = ⊥)
    (hGH : ∀ J : Subgroup M, IsComponent J → GHList (↥J ⧸ center ↥J))
    (h3 : ∀ J₁ J₂ J₃ : Subgroup M, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False)
    {g : M} (hgO : pCore 2 M ≤ centralizer ({g} : Set M))
    {L W : Subgroup M} (hLsn : L.IsSubnormal) (hgL : g ∈ normalizer (L : Set M))
    (hWL : W ≤ L) (hgW : g ∈ normalizer (W : Set M)) [hWn : (W.subgroupOf L).Normal]
    [IsSimpleGroup (↥L ⧸ W.subgroupOf L)] (hnab : ∃ a b : ↥L ⧸ W.subgroupOf L, a * b ≠ b * a)
    (hmove : ∃ l ∈ L, ⁅l, g⁆ ∉ W) :
    ∃ J : Subgroup M, IsComponent J ∧ J ≤ L ∧ ¬ J ≤ W ∧ ¬ J ≤ centralizer ({g} : Set M) := by
  classical
  let φ : ↥L →* ↥L ⧸ W.subgroupOf L := QuotientGroup.mk' (W.subgroupOf L)
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : φ.ker = W.subgroupOf L := QuotientGroup.ker_mk' _
  have hsimp : ∀ H : Subgroup (↥L ⧸ W.subgroupOf L), H.Normal → H = ⊥ ∨ H = ⊤ :=
    fun H _ => IsSimpleGroup.eq_bot_or_eq_top_of_normal H
  have hconjW : ∀ x ∈ L, ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    intro x hx w hw
    have h := hWn.conj_mem ⟨w, hWL hw⟩ (by rw [mem_subgroupOf]; exact hw) ⟨x, hx⟩
    rw [mem_subgroupOf] at h
    simpa using h
  have hbot : ∀ K : Subgroup M, K ≤ L → (K.subgroupOf L).map φ = ⊥ → K ≤ W := by
    intro K hKL h
    rw [Subgroup.map_eq_bot_iff, hker] at h
    exact CFSG.LocalCores.le_of_subgroupOf_le hKL h
  have hgZ : zpowers g ≤ normalizer (L : Set M) := zpowers_le.mpr hgL
  have hUL : ⁅L, zpowers g⁆ ≤ L := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp hgZ
  have hLU : L ≤ normalizer ((⁅L, zpowers g⁆ : Subgroup M) : Set M) :=
    normalizer_commutator_ge_left L (zpowers g)
  have hgU : g ∈ normalizer ((⁅L, zpowers g⁆ : Subgroup M) : Set M) :=
    normalizer_commutator_ge_right L (zpowers g) (mem_zpowers g)
  have hUtop : ((⁅L, zpowers g⁆ : Subgroup M).subgroupOf L).map φ = ⊤ := by
    have hLtop : (L.subgroupOf L).map φ = ⊤ := by
      rw [subgroupOf_self]
      exact map_top_of_surjective φ hφs
    rcases hsimp _ (Lift55Aux.map_subgroupOf_normal φ hLtop hLU) with h | h
    · obtain ⟨l, hl, hlg⟩ := hmove
      exact absurd (hbot _ hUL h (commutator_mem_commutator hl (mem_zpowers g))) hlg
    · exact h
  have hFg : fittingSubgroup M ≤ centralizer ({g} : Set M) :=
    (Lift55Aux.fittingSubgroup_le_pCore_two hO).trans hgO
  have hUF : ⁅⁅L, zpowers g⁆, fittingSubgroup M⁆ = ⊥ :=
    Lift55Aux.commutator_commutator_zpowers_eq_bot le_normalizer_of_normal hFg
  obtain ⟨L₁, ⟨hL₁U, hLL₁, hgL₁, hL₁top⟩, hL₁⟩ :=
    Lift55Aux.exists_perfect_of_commutator_closed
      (fun X => X ≤ ⁅L, zpowers g⁆ ∧ L ≤ normalizer (X : Set M) ∧ g ∈ normalizer (X : Set M) ∧
        (X.subgroupOf L).map φ = ⊤)
      (fun X ⟨hXU, hLX, hgX, hXtop⟩ => ⟨(commutator_le_self X).trans hXU,
        fun x hx => Lift55Aux.mem_normalizer_commutator (hLX hx) (hLX hx),
        Lift55Aux.mem_normalizer_commutator hgX hgX, by
          rw [Lift55Aux.commutator_subgroupOf_of_le (hXU.trans hUL) (hXU.trans hUL),
            map_commutator, hXtop]
          exact Lift55Aux.commutator_top_eq_top hnab⟩)
      ⟨le_rfl, hLU, hgU, hUtop⟩
  have hL₁L : L₁ ≤ L := hL₁U.trans hUL
  have hL₁perf : Group.IsPerfect ↥L₁ := isPerfect_iff.mpr hL₁
  have hcard := Lift55Aux.card_components_le_four_of_no_three h3
  have hnorm : ∀ K : Subgroup M, IsComponent K → L₁ ≤ normalizer (K : Set M) := by
    intro K hK a ha
    have h1 := P34.perfect_normalizes_component hcard hL₁ hK
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => h1 a ha x hx, fun hx => ?_⟩
    have h2 := h1 a⁻¹ (inv_mem ha) _ hx
    simpa [mul_assoc] using h2
  have hL₁F : ⁅L₁, fittingSubgroup M⁆ = ⊥ :=
    le_bot_iff.mp (hUF ▸ commutator_mono hL₁U le_rfl)
  have hL₁E : L₁ ≤ layer M :=
    CFSG.LocalAnalysis.ComponentInitial.unique_perfect_component_normalizer_enters_layer hL₁perf
      hL₁F hnorm (fun K hK => hSch _ hK.1.2.1 hK.1.2.2 (hGH K hK))
  have hL₁sn : L₁.IsSubnormal :=
    IsSubnormal.step L₁ L hL₁L hLsn (normal_subgroupOf_of_le_normalizer hLL₁)
  by_cases hex : ∃ J : Subgroup M, IsComponent J ∧ J ≤ L₁ ∧ ¬ J ≤ W
  ·
    obtain ⟨J, hJ, hJL₁, hJW⟩ := hex
    have hJL : J ≤ L := hJL₁.trans hL₁L
    refine ⟨J, hJ, hJL, hJW, fun hJg => ?_⟩
    have hJtop : (J.subgroupOf L).map φ = ⊤ := by
      rcases hsimp _ (Lift55Aux.map_subgroupOf_normal φ hL₁top (hnorm J hJ)) with h | h
      · exact absurd (hbot J hJL h) hJW
      · exact h
    obtain ⟨l, hl, hlg⟩ := hmove
    apply hlg
    have hlm : φ ⟨l, hl⟩ ∈ (J.subgroupOf L).map φ := hJtop ▸ mem_top _
    obtain ⟨j, hj, hjl⟩ := hlm
    rw [SetLike.mem_coe, mem_subgroupOf] at hj
    have hw : (j : M)⁻¹ * l ∈ W := by
      have h1 : j⁻¹ * ⟨l, hl⟩ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hjl, inv_mul_cancel]
      rw [hker, mem_subgroupOf] at h1
      simpa using h1
    have hjg : Commute (j : M) g := mem_centralizer_singleton_iff.mp (hJg hj)
    have hwg : ⁅(j : M)⁻¹ * l, g⁆ ∈ W := by
      have h1 : g * ((j : M)⁻¹ * l)⁻¹ * g⁻¹ ∈ W :=
        (mem_normalizer_iff.mp hgW _).mp (inv_mem hw)
      have h2 := mul_mem hw h1
      rw [commutatorElement_def]
      simpa [mul_assoc] using h2
    have hj' : g * (j : M)⁻¹ * g⁻¹ = (j : M)⁻¹ := by
      rw [← hjg.inv_left.eq, mul_inv_cancel_right]
    have hcomm : ⁅l, g⁆ = (j : M) * ⁅(j : M)⁻¹ * l, g⁆ * (j : M)⁻¹ := by
      calc ⁅l, g⁆ = (j : M) * ⁅(j : M)⁻¹ * l, g⁆ * (g * (j : M)⁻¹ * g⁻¹) := by
            rw [commutatorElement_def, commutatorElement_def]
            group
        _ = (j : M) * ⁅(j : M)⁻¹ * l, g⁆ * (j : M)⁻¹ := by rw [hj']
    rw [hcomm]
    exact hconjW _ j.2 _ hwg
  ·
    exfalso
    push Not at hex
    have hCA : centralizer (L₁ : Set M) ≤ normalizer ((L₁ ⊓ W : Subgroup M) : Set M) := by
      intro c hc
      have hc' : ∀ y ∈ L₁, y * c = c * y := fun y hy => (mem_centralizer_iff.mp hc) y hy
      rw [mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        have h1 : c * a * c⁻¹ = a := by rw [← hc' a (mem_inf.mp ha).1, mul_inv_cancel_right]
        rw [h1]
        exact ha
      · intro ha
        have h2 := hc' _ (mem_inf.mp ha).1
        have h3 : a = c * a * c⁻¹ :=
          mul_left_cancel (h2.symm.trans (inv_mul_cancel_right (c * a) c)).symm
        rw [h3]
        exact ha
    have hEAC : layer M ≤ (L₁ ⊓ W) ⊔ centralizer (L₁ : Set M) := by
      refine sSup_le fun J hJ => ?_
      rcases CFSG.LocalCores.component_subnormal_subgroup hJ hL₁sn with h | h
      · exact le_sup_of_le_left (le_inf h (hex J hJ h))
      · exact le_sup_of_le_right (commutator_eq_bot_iff_le_centralizer.mp h)
    have hL₁W : L₁ ≤ W := by
      calc L₁ = ⁅L₁, L₁⁆ := hL₁.symm
        _ ≤ ⁅L₁, (L₁ ⊓ W) ⊔ centralizer (L₁ : Set M)⁆ :=
            commutator_mono le_rfl (hL₁E.trans hEAC)
        _ ≤ ⁅L₁, L₁ ⊓ W⁆ := Lift55Aux.commutator_sup_le_of_le_centralizer le_rfl hCA
        _ ≤ W := by
            rw [commutator_le]
            intro x hx a ha
            rw [commutatorElement_def]
            exact mul_mem (hconjW x (hL₁L hx) a (mem_inf.mp ha).2)
              (inv_mem (mem_inf.mp ha).2)
    have hL₁bot : (L₁.subgroupOf L).map φ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hker]
      intro x hx
      rw [mem_subgroupOf] at hx ⊢
      exact hL₁W hx
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥L ⧸ W.subgroupOf L)
    have hqm : q ∈ (L₁.subgroupOf L).map φ := hL₁top ▸ mem_top q
    rw [hL₁bot, mem_bot] at hqm
    exact hq hqm

theorem lift55_thm : Lift55 := by
  intro hSch M _ _ p _ _ hO hGH h3 g _ hgO L W hLsn _ hgL hWL hgW hWn hs hnab hmove
  exact exists_component_moved hSch hO hGH h3 hgO hLsn hgL hWL hgW hnab hmove

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
