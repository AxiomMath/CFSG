module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
import CFSG.ClassicalInvolution.Asc77.AscT3CLateSwapEng
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfg

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

private theorem Std20.late_toF (d : Std20 p f K K' J S R R' W V z t) :
    Std20F K K' J S R R' W V z t :=
  { d with
    hyp := d.late_hΩ
    late_ne_inv := d.late_ne_inv
    late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.branch.odd d.hyp d.viol.star d.viol.hzJ
    late_card2 := fun hU hK hR =>
      Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp hU hK hR }

theorem Std20.late_exists_swap (d : Std20 p f K K' J S R R' W V z t) :
    ∃ u ∈ (S : Subgroup G), conjSub u K = K' := by
  exact d.late_toF.late_exists_swap

theorem Std20.late_swap_data (d : Std20 p f K K' J S R R' W V z t) {u : G}
    (hu : u ∈ (S : Subgroup G)) (huK : conjSub u K = K') :
    conjSub u K' = K ∧ conjSub u R = R' ∧ conjSub u W = W ∧ conjSub u (S : Subgroup G) = S := by
  exact d.late_toF.late_swap_data hu huK

end Std

section Cmo

variable {G : Type} [Group G]

theorem late_cmo_conj_mem {H L : Subgroup G} {x : G} (hx : x ∈ centralizerModOdd H L) (n : G) :
    n * x * n⁻¹ ∈ centralizerModOdd (conjSub n H) (conjSub n L) := by
  obtain ⟨hxH, hxL, hxO, hxc⟩ : x ∈ H ∧ x ∈ Subgroup.normalizer (L : Set G) ∧
      x ∈ Subgroup.normalizer (oddCoreOf L : Set G) ∧ ∀ l ∈ L, ⁅x, l⁆ ∈ oddCoreOf L := hx
  have hcn : ∀ A : Subgroup G, x ∈ Subgroup.normalizer (A : Set G) →
      n * x * n⁻¹ ∈ Subgroup.normalizer ((conjSub n A : Subgroup G) : Set G) := fun A hA => by
    rw [mem_normalizer_iff_conjSub_eq] at hA ⊢
    calc conjSub (n * x * n⁻¹) (conjSub n A)
        = conjSub n (conjSub x (conjSub n⁻¹ (conjSub n A))) := by rw [conjSub_mul, conjSub_mul]
      _ = conjSub n A := by rw [conjSub_inv_conjSub, hA]
  refine ⟨conj_mem_conjSub hxH, hcn L hxL, ?_, fun l' hl' => ?_⟩
  · rw [Thompson.oddCoreOf_conjSub_eq]
    exact hcn _ hxO
  · rw [mem_conjSub_iff] at hl'
    rw [Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
    have h := hxc _ hl'
    have e : n⁻¹ * ⁅n * x * n⁻¹, l'⁆ * n = ⁅x, n⁻¹ * l' * n⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact h

end Cmo

end CFSG.ClassicalInvolution.Asc77.T3CII
