module

public import CFSG.ClassicalInvolution.Q3.Q3T6YGood
public import CFSG.ClassicalInvolution.Q3.Q3T6BSym
public import CFSG.ClassicalInvolution.Q3.Q3T6YNontriv
public import CFSG.ClassicalInvolution.Q3.Q3T6BOuter

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6B
  CFSG.ClassicalInvolution.Q3.Q3T6X
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem symOuterOn_of_bal368 (h368 : Bal368 F) (S : Set F) : SymOuterOn F S := by
  classical
  intro X Y x y hX hY _ _ hxY hout
  by_contra hy
  have hxy : x * y = y * x := Mem3.comm_of_mem_normalizer hY hxY
  have hs : Swap X x y :=
    ⟨hX, hY.mul_self, hxy.symm, fun he => hy (AscHypOmega.mem_normalizer_of_conjSub_eq he)⟩
  obtain ⟨R, hR⟩ := hs.exists_swapSylow
  obtain ⟨e, he, f, hf, he2, hf2, hfe⟩ := hR.exists_anticomm hs
  have hxx := hX.mul_self
  have hc := hR.comm_conj he
  have hex : e * x = x * e := hX.mul_comm_of_mem he.2
  have hdx : x * diag y e = diag y e * x :=
    diag_comm_x hex (hs.twin.mul_comm_of_mem (conj_mem_conjSub he.2))
  have hd2 : diag y e * diag y e = 1 := diag_mul_self hxx hs.comm he2 hc
  obtain ⟨Y', hY', hxY', hout', hdtriv⟩ := exists_good_member' hs hR hY hxY hout he hf he2 hf2 hfe
  have hdN : diag y e ∈ Subgroup.normalizer (Y' : Set F) := mem_normalizer_of_trivial hd2 hdtriv
  obtain ⟨κ, hκY, hκx, hκd⟩ :=
    exists_inverting_commuting hY' hxx hd2 hdx hxY' hdN hout' hdtriv
  obtain ⟨g, hg, hgx⟩ := exists_conj_diag_eq_y hs hR he hf he2 hfe hκd hκx
  have hδ : g⁻¹ * y * g⁻¹⁻¹ = diag y e := by
    calc g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * (g * diag y e * g⁻¹) * g⁻¹⁻¹ := by rw [hg]
      _ = diag y e := by group
  have hI : Mem3 (conjSub g⁻¹ Y') (diag y e) := by
    have h1 := hY'.conj g⁻¹
    rwa [hδ] at h1
  have hdyN : diag y e * y ∈ Subgroup.normalizer (Y' : Set F) :=
    Subgroup.mul_mem _ hdN (Subgroup.le_normalizer hY'.mem)
  have hxI : x ∈ Subgroup.normalizer (conjSub g⁻¹ Y' : Set F) := by
    apply AscHypOmega.mem_normalizer_of_conjSub_eq
    have h1 : x * g⁻¹ = g⁻¹ * (diag y e * y) := by rw [← hgx]; group
    calc conjSub x (conjSub g⁻¹ Y') = conjSub (x * g⁻¹) Y' := (conjSub_mul _ _ _).symm
      _ = conjSub (g⁻¹ * (diag y e * y)) Y' := by rw [h1]
      _ = conjSub g⁻¹ (conjSub (diag y e * y) Y') := conjSub_mul _ _ _
      _ = conjSub g⁻¹ Y' := by rw [conjSub_eq_of_mem_normalizer hdyN]
  have hxtriv : ∀ i ∈ conjSub g⁻¹ Y', ⁅x, i⁆ ∈ oddCoreOf (conjSub g⁻¹ Y') := by
    intro i hi
    have hk : g * i * g⁻¹ ∈ Y' := by
      have := mem_conjSub_iff.mp hi
      simpa using this
    rw [AscFusion.oddCoreOf_conjSub', mem_conjSub_iff]
    have h1 : g * ⁅x, i⁆ * g⁻¹ = ⁅diag y e * y, g * i * g⁻¹⁆ := by
      rw [← hgx]
      simp only [commutatorElement_def]
      group
    have h2 : ⁅diag y e * y, g * i * g⁻¹⁆ = ⁅diag y e, g * i * g⁻¹⁆ := by
      have hyk : y * (g * i * g⁻¹) = (g * i * g⁻¹) * y := (hY'.mul_comm_of_mem hk).symm
      simp only [commutatorElement_def]
      calc diag y e * y * (g * i * g⁻¹) * (diag y e * y)⁻¹ * (g * i * g⁻¹)⁻¹
          = diag y e * (y * (g * i * g⁻¹) * y⁻¹) * (diag y e)⁻¹ * (g * i * g⁻¹)⁻¹ := by group
        _ = diag y e * (g * i * g⁻¹) * (diag y e)⁻¹ * (g * i * g⁻¹)⁻¹ := by
          rw [hyk]
          group
    have h3 : (g⁻¹)⁻¹ * ⁅x, i⁆ * g⁻¹ = g * ⁅x, i⁆ * g⁻¹ := by rw [inv_inv]
    rw [h3, h1, h2]
    exact hdtriv _ hk
  have hne : diag y e ≠ x := (SwapSylow.diag_ne hs hR he he2).2.1
  have hdX : diag y e ∈ Subgroup.normalizer (X : Set F) := SwapSylow.diag_mem_normalizer hs he.2
  have hcomm := h368 hI hX hne hxI hxtriv hdX f hf.2
  have hdf : ⁅diag y e, f⁆ = x := by
    have h1 : ⁅f, diag y e⁆ = x := by
      rw [commutatorElement_def, diag_conj hs hR he hf he2 hfe]
      group
    rw [← commutatorElement_inv, h1]
    exact inv_eq_of_mul_eq_one_right hxx
  rw [hdf] at hcomm
  exact not_mem_oddCoreOf_of_orderOf_two hX.orderOf_eq_two hcomm

theorem fusion3MinOn_of_bal368 (h368 : Bal368 F) {S : Set F} (htriv : DiagInputTrivOn F S) :
    Fusion3MinOn F S :=
  fusion3MinOn_of_parts (symOuterOn_of_bal368 h368 S) htriv (diagInputNontrivOn S)

end CFSG.ClassicalInvolution.Q3.Q3T6Y
