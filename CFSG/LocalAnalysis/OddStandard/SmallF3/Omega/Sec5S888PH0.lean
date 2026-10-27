module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Core
public import Certificates.Data.ExceptionalSL3

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

structure PlaneSetup {H X : Type} [Group H] [Group X] (z : H) (K : Fin 4 → Subgroup H)
    (α : H →* X) : Prop where
  quad : Sec5B517Quad K z
  surj : Function.Surjective α
  ker : α.ker = zpowers z

structure PocketHyp {H : Type} [Group H] [Finite H] (z : H) (K : Fin 4 → Subgroup H)
    (T : Subgroup H) : Prop where
  quad : Sec5B517Quad K z
  sylow : ∃ T' : Sylow 2 H, (T' : Subgroup H) = T
  le_T : Sec5B517Q8 quad ≤ T
  T_le_N : T ≤ normalizer (Sec5B517Q8 quad : Set H)
  perm : ∀ x ∈ normalizer (Sec5B517Q8 quad : Set H), ∀ i, ∃ j, CFSG.conjugate (K i) x = K j
  trans : ∀ i j, ∃ x ∈ normalizer (Sec5B517Q8 quad : Set H), CFSG.conjugate (K i) x = K j
  closed : ∀ q ∈ Sec5B517Q8 quad, ∀ x : H, x⁻¹ * q * x ∈ normalizer (Sec5B517Q8 quad : Set H) →
    x⁻¹ * q * x ∈ Sec5B517Q8 quad
  centS : ∀ s ∈ T, (∀ q ∈ Sec5B517Q8 quad, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) →
    s ∈ Sec5B517Q8 quad

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H}

@[expose] def planeV (hq : Sec5B517Quad K z) (α : H →* X) : Subgroup X :=
  (Sec5B517Q8 hq).map α

@[expose] def planeW (hq : Sec5B517Quad K z) (α : H →* X) (i : Fin 4) : Subgroup X :=
  (Sec5B517Q8 hq ⊓ K i).map α

private def sec5s888ph0_gen : SL23 :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩

private lemma sec5s888ph0_gen_ne_one : sec5s888ph0_gen ≠ 1 := by decide +kernel

private lemma sec5s888ph0_gen_order : orderOf sec5s888ph0_gen = 3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · exact sec5s888ph0_gen_ne_one

theorem Sec5B517Quad.exists_order_three (hq : Sec5B517Quad K z) (i : Fin 4) :
    ∃ u ∈ K i, orderOf u = 3 := by
  obtain ⟨e⟩ := hq.iso i
  refine ⟨((e.symm sec5s888ph0_gen : ↥(K i)) : H), (e.symm sec5s888ph0_gen).2, ?_⟩
  calc orderOf (((e.symm sec5s888ph0_gen : ↥(K i)) : H))
      = orderOf (e.symm sec5s888ph0_gen : ↥(K i)) := Subgroup.orderOf_coe _
    _ = orderOf sec5s888ph0_gen := (e.symm).orderOf_eq sec5s888ph0_gen
    _ = 3 := sec5s888ph0_gen_order

@[expose] noncomputable def elt3 (hq : Sec5B517Quad K z) (i : Fin 4) : H :=
  Classical.choose (hq.exists_order_three i)

theorem elt3_mem (hq : Sec5B517Quad K z) (i : Fin 4) : elt3 hq i ∈ K i :=
  (Classical.choose_spec (hq.exists_order_three i)).1

theorem elt3_order (hq : Sec5B517Quad K z) (i : Fin 4) : orderOf (elt3 hq i) = 3 :=
  (Classical.choose_spec (hq.exists_order_three i)).2

@[expose] noncomputable def planeRho (hq : Sec5B517Quad K z) (α : H →* X) (i : Fin 4) : X :=
  α (elt3 hq i)

end CFSG.OddStandard.SmallF3.Omega
