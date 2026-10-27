module

public import CFSG.ClassicalInvolution.Q3.TL4OddSecE2
public import CFSG.ClassicalInvolution.Q3.TL4OddKey

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Quiet

variable {G : Type} [Group G] [Finite G]

theorem quiet_of_inO2_sub {H : Subgroup G} (hH : IsSubnormal H ⊤) {τ : G} (hτ : τ ∈ H)
    (h2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H)))
    (L : Subgroup (G ⧸ componentClassificationOddCore G)) (hL : CFSG.IsComponent L) :
    ∀ y ∈ L, QuotientGroup.mk' (componentClassificationOddCore G) τ * y =
      y * QuotientGroup.mk' (componentClassificationOddCore G) τ := by
  set N := componentClassificationOddCore G with hN
  set M := classicalInvolutionOddCore ↥H with hM
  by_contra hcon
  push Not at hcon
  obtain ⟨χ, hχ, hχmk, hχR⟩ := exists_oddQuot_embedding hH
  set x : ↥H ⧸ M := QuotientGroup.mk' M ⟨τ, hτ⟩ with hx
  have hχx : χ x = QuotientGroup.mk' N τ := hχmk ⟨τ, hτ⟩
  have hHm : H.IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hH
      Subgroup.IsSubnormal.top
  have hRm : χ.range.IsSubnormal := by
    rw [hχR]
    exact hHm.map (QuotientGroup.mk'_surjective N)
  have hτR : QuotientGroup.mk' N τ ∈ χ.range := ⟨x, hχx⟩
  have hle : L ≤ χ.range := by
    rcases CFSG.LocalCores.component_subnormal_subgroup hL hRm with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hne⟩ := hcon
      apply hne
      have hc := Subgroup.commutator_mem_commutator hy hτR
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc.symm
  have hL₂ : CFSG.IsComponent (L.comap χ) := by
    set χ' : (↥H ⧸ M) ≃* ↥χ.range := MonoidHom.ofInjective hχ with hχ'
    have h1 := CFSG.LocalCores.isComponent_map_mulEquiv χ'.symm
      (CFSG.LocalCores.component_overgroup hL hle)
    have h2 : (L.subgroupOf χ.range).map χ'.symm.toMonoidHom = L.comap χ := by
      ext z
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf,
        Subgroup.mem_comap]
      rfl
    rwa [h2] at h1
  obtain ⟨P, hPn, hP2, hxP⟩ := h2
  have hcomm := commute_of_mem_normal_isPGroup hL₂ hPn hP2 hxP
  obtain ⟨y, hy, hne⟩ := hcon
  obtain ⟨w, rfl⟩ := hle hy
  apply hne
  have h3 := congrArg χ (hcomm w hy)
  rwa [map_mul, map_mul, hχx] at h3

end Quiet

section Datum

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem mem_centralizerModOdd_of_act (hd : TightDatum R S t) {u : Y}
    (hut : u ∈ Subgroup.centralizer ({t} : Set Y))
    (huK : (⟨u, hut⟩ : Subgroup.centralizer ({t} : Set Y)) ∈ hd.act.ker) :
    u ∈ centralizerModOdd ⊤ R := by
  have hN : u ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer hut
  have hcomm : ∀ r ∈ R, ⁅u, r⁆ ∈ oddCoreImg R := (hd.act_eq_one_iff hut).mp huK
  refine ⟨trivial, hN, ?_, hcomm⟩
  rw [Subgroup.mem_normalizer_iff]
  intro o
  constructor
  · intro ho
    exact conj_mem_oddCoreImg hN ho
  · intro ho
    have h := conj_mem_oddCoreImg (Subgroup.inv_mem _ hN) ho
    have e : u⁻¹ * (u * o * u⁻¹) * u⁻¹⁻¹ = o := by group
    rwa [e] at h

end Datum

end CFSG.ClassicalInvolution.Q3.TL4
