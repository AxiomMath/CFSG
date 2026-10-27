module

public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1b
public import CFSG.ClassicalInvolution.Q3.Q3NFMain
public import CFSG.ClassicalInvolution.Q3.Q3T8AF01
public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge
public import CFSG.ClassicalInvolution.Q3.Q3T8L274A

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3T8.AF
open scoped commutatorElement

section Triangle


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_triangle {K : Subgroup G} {z : G} (hs : Q3.Disc3.AscStand3 Ω K)
    (hz : IsUniqueInvolution K z)
    (hfr : ∃ A₀ : Subgroup G, Q3NL.FuzzyFrame3 Ω A₀) :
    ∃ (A B : Subgroup G) (tA tB : G), A ∈ omegaNbr Ω K ∧ B ∈ omegaNbr Ω K ∧
      B ∈ omegaNbr Ω A ∧ IsUniqueInvolution A tA ∧ IsUniqueInvolution B tB ∧
        tB ∉ Subgroup.closure ({z, tA} : Set G) := by
  have hΩ : HypOmegaMod Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp
  obtain ⟨A₀, J, x, hJ, hA, hAe, hAc, hAt⟩ := hfr
  have hzA : ∀ i, x i ∈ A₀ := fun i => hA ▸ Subgroup.subset_closure ⟨i, rfl⟩
  have hsq : ∀ i, x i * x i = 1 := fun i => (hJ i).2.isCentralInvolution.sq
  have hcomm : ∀ i j, x i * x j = x j * x i := fun i j =>
    DeltaClosure.comm_of_mem_elemAbelian hAe (hzA i) (hzA j)
  obtain ⟨hdist, hind⟩ := Q3NF.fuzzy_independent hsq hcomm (hA ▸ hAc)
  have hui : ∀ i, IsUniqueInvolution (J i) (x i) := by
    intro i
    obtain ⟨w, hw⟩ := hΩ.exists_uniqueInvolution (hJ i).1
    have hxw : x i = w :=
      (hw.unique (x i) (hJ i).2.mem (hsq i)).resolve_left (hJ i).2.ne_one
    exact hxw ▸ hw
  obtain ⟨g, hg⟩ := hs.trans (J 0) (hJ 0).1
  set h : G := g⁻¹ with hh
  have hK0 : conjSub h (J 0) = K := by
    rw [← hg, hh, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hMΩ : ∀ i, conjSub h (J i) ∈ Ω := fun i => hΩ.conjInvariant h _ (hJ i).1
  have hMu : ∀ i, IsUniqueInvolution (conjSub h (J i)) (h * x i * h⁻¹) := fun i => (hui i).conj h
  have hy0 : h * x 0 * h⁻¹ = z := by
    have := hMu 0
    rw [hK0] at this
    exact this.eq hz
  have hyd : ∀ i j : Fin 3, i ≠ j → h * x i * h⁻¹ ≠ h * x j * h⁻¹ := fun i j hij e =>
    hdist i j hij (mul_left_cancel (mul_right_cancel e))
  have hadj : ∀ i j : Fin 3, i ≠ j → conjSub h (J j) ∈ omegaNbr Ω (conjSub h (J i)) := by
    intro i j hij
    have hne : conjSub h (J j) ≠ conjSub h (J i) := fun e =>
      hyd i j hij ((hMu i).eq (e ▸ hMu j))
    exact Q3T6D.mem_omegaNbr_of_trivialOnQuotGen hΩ (hMΩ i) (hMu i) (hMΩ j) hne
      (trivialOnQuot_conjSub (hAt j (hzA i)) h)
  have hKA : conjSub h (J 1) ∈ omegaNbr Ω K := hK0 ▸ hadj 0 1 (by decide)
  have hKB : conjSub h (J 2) ∈ omegaNbr Ω K := hK0 ▸ hadj 0 2 (by decide)
  have hAB : conjSub h (J 2) ∈ omegaNbr Ω (conjSub h (J 1)) := hadj 1 2 (by decide)
  refine ⟨conjSub h (J 1), conjSub h (J 2), h * x 1 * h⁻¹, h * x 2 * h⁻¹, hKA, hKB, hAB,
    hMu 1, hMu 2, fun hmem => ?_⟩
  have hzt : z * (h * x 1 * h⁻¹) = (h * x 1 * h⁻¹) * z := by
    rw [← hy0]
    calc h * x 0 * h⁻¹ * (h * x 1 * h⁻¹) = h * (x 0 * x 1) * h⁻¹ := by group
      _ = h * (x 1 * x 0) * h⁻¹ := by rw [hcomm 0 1]
      _ = h * x 1 * h⁻¹ * (h * x 0 * h⁻¹) := by group
  rw [← hy0] at hmem
  rcases T3CII.closure_pair_cases (hy0 ▸ (hMu 0).sq) (hMu 1).sq (hy0 ▸ hzt) hmem with e | e | e | e
  · exact (hMu 2).ne_one e
  · exact hyd 2 0 (by decide) e
  · exact hyd 2 1 (by decide) e
  · apply hind
    have e' : h * (x 0 * x 1) * h⁻¹ = h * x 2 * h⁻¹ := by
      rw [e]
      group
    exact mul_left_cancel (mul_right_cancel e')

end Triangle

section Comp


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem comm_mem_oddCoreOf_of_components {ι : Type}
    (D : Q3.LieSystemData3 ι (Q3T7.layerQuot3 Ω z) (Q3T7.layerFam3 Ω z)) {M N : Subgroup G}
    {i j : ι} (hij : i ≠ j) {R : Subgroup (D.kind i).G} {R' : Subgroup (D.kind j).G}
    (hM : M ∈ Q3NL.tqMembers3 Ω z) (hN : N ∈ Q3NL.tqMembers3 Ω z)
    (hMR : Layer.layerImg3 Ω z M = R.map (D.hom i))
    (hNR : Layer.layerImg3 Ω z N = R'.map (D.hom j)) :
    ∀ a ∈ Q3NL.exactCore3 z M, ∀ b ∈ Q3NL.exactCore3 z N,
      ⁅a, b⁆ ∈ oddCoreOf (Q3NL.exactLayer3 Ω z) := by
  intro a ha b hb
  have haY : a ∈ Q3NL.exactLayer3 Ω z := Q3NL.exactCore3_le_exactLayer3 hM ha
  have hbY : b ∈ Q3NL.exactLayer3 Ω z := Q3NL.exactCore3_le_exactLayer3 hN hb
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω z)) with hπ
  have hπa : π ⟨a, haY⟩ ∈ Layer.layerImg3 Ω z M :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)
  have hπb : π ⟨b, hbY⟩ ∈ Layer.layerImg3 Ω z N :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hb)
  rw [hMR] at hπa
  rw [hNR] at hπb
  obtain ⟨r, -, hr⟩ := hπa
  obtain ⟨r', -, hr'⟩ := hπb
  have hc : π ⟨a, haY⟩ * π ⟨b, hbY⟩ = π ⟨b, hbY⟩ * π ⟨a, haY⟩ := by
    rw [← hr, ← hr']
    exact D.commute i j hij r r'
  have h1 : π ⁅(⟨a, haY⟩ : ↥(Q3NL.exactLayer3 Ω z)), ⟨b, hbY⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨_, h2, by simp [commutatorElement_def]⟩

end Comp

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
