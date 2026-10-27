module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.OutU43Main

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Monster.B.Co2 CFSG.LieType.Multipliers.U43 CFSG.Sporadic.SmallOddCore

section AutModel


theorem psi_x_mem : psi xElt ∈ P := by
  rw [P_eq_closure]
  exact subset_closure (Set.mem_insert _ _)

theorem psi_y_mem : psi yElt ∈ P := by
  rw [P_eq_closure]
  exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem inj_of_comm {x : Equiv.Perm (Fin 820)} (hx : x ∈ R)
    (hcomm : ∀ p ∈ P, x * p = p * x) : x = 1 := by
  obtain ⟨g, hg, k, hk, rfl⟩ := mem_R_iff.1 hx
  have hcard := card_comm_gens hk
  have hne : Nonempty {g : P // CommGens k g} :=
    ⟨⟨⟨g, hg⟩, hcomm _ psi_x_mem, hcomm _ psi_y_mem⟩⟩
  by_cases hk0 : k = 0
  · subst hk0
    have hcard1 : Nat.card {g : P // CommGens 0 g} = 1 := by simpa using hcard
    rw [Nat.card_eq_one_iff_unique] at hcard1
    obtain ⟨hsub, -⟩ := hcard1
    have h1 : CommGens 0 1 := by simp [CommGens, tP_zero]
    have := hsub.elim ⟨⟨g, hg⟩, hcomm _ psi_x_mem, hcomm _ psi_y_mem⟩ ⟨⟨1, P.one_mem⟩, h1⟩
    have hg1 : g = 1 := congrArg (fun z : {g : P // CommGens 0 g} => (z.1 : Equiv.Perm (Fin 820)))
      this
    rw [hg1, tP_zero, mul_one]
  · have hcard0 : Nat.card {g : P // CommGens k g} = 0 := by simpa [hk0] using hcard
    exact absurd hcard0 (Nat.card_pos_iff.2 ⟨hne, inferInstance⟩).ne'

@[expose] noncomputable def kappaAut (x : R) : MulAut P where
  toFun p := ⟨x * p * x⁻¹, conj_mem_P x.2 p.2⟩
  invFun p := ⟨x⁻¹ * p * x, by simpa using conj_mem_P (R.inv_mem x.2) p.2⟩
  left_inv p := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv p := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' p q := by
    apply Subtype.ext
    simp [mul_assoc]

@[expose] noncomputable def kappa : R →* MulAut P where
  toFun := kappaAut
  map_one' := by
    apply MulEquiv.ext
    intro p
    apply Subtype.ext
    simp [kappaAut]
  map_mul' x y := by
    apply MulEquiv.ext
    intro p
    apply Subtype.ext
    simp [kappaAut, mul_assoc]

theorem kappa_injective : Function.Injective kappa := by
  intro x y hxy
  have hc : ∀ p ∈ P, ((y : Equiv.Perm (Fin 820))⁻¹ * (x : Equiv.Perm (Fin 820))) * p =
      p * ((y : Equiv.Perm (Fin 820))⁻¹ * (x : Equiv.Perm (Fin 820))) := by
    intro p hp
    have h1 := congrArg (fun β : MulAut P => ((β ⟨p, hp⟩ : P) : Equiv.Perm (Fin 820))) hxy
    simp only [kappa, kappaAut, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, Subgroup.coe_inv] at h1
    calc ((y : Equiv.Perm (Fin 820))⁻¹ * (x : Equiv.Perm (Fin 820))) * p
        = (y : Equiv.Perm (Fin 820))⁻¹ * ((x : Equiv.Perm (Fin 820)) * p *
          (x : Equiv.Perm (Fin 820))⁻¹) * (x : Equiv.Perm (Fin 820)) := by group
      _ = (y : Equiv.Perm (Fin 820))⁻¹ * ((y : Equiv.Perm (Fin 820)) * p *
          (y : Equiv.Perm (Fin 820))⁻¹) * (x : Equiv.Perm (Fin 820)) := by rw [h1]
      _ = p * ((y : Equiv.Perm (Fin 820))⁻¹ * (x : Equiv.Perm (Fin 820))) := by group
  have hmem : (y : Equiv.Perm (Fin 820))⁻¹ * (x : Equiv.Perm (Fin 820)) ∈ R :=
    R.mul_mem (R.inv_mem y.2) x.2
  have h2 := inj_of_comm hmem hc
  exact Subtype.ext (inv_mul_eq_one.1 h2).symm

theorem card_mulAut_P : Nat.card (MulAut P) = 8 * Nat.card P := by
  rw [← Nat.card_congr (MulAut.congr psiEquiv).toEquiv,
    CFSG.EvenSporadicStandard.RuStd.S2.card_mulAut_u43, Nat.card_congr psiEquiv.toEquiv]

theorem kappa_bijective : Function.Bijective kappa := by
  have hfin : Finite (MulAut P) := by
    apply Nat.finite_of_card_ne_zero
    rw [card_mulAut_P]
    exact (Nat.mul_pos (by norm_num) Nat.card_pos).ne'
  exact kappa_injective.bijective_of_nat_card_le (by rw [card_mulAut_P, card_R])

theorem autModel : AutModel P R where
  le := P_le_R
  conj_mem := fun _ hx _ hp => conj_mem_P hx hp
  surj := fun α => by
    obtain ⟨x, hx⟩ := kappa_bijective.2 α
    refine ⟨x, x.2, fun p => ?_⟩
    have := congrArg (fun β : MulAut P => ((β p : P) : Equiv.Perm (Fin 820))) hx
    simpa [kappa, kappaAut] using this.symm
  inj := fun _ hx hc => inj_of_comm hx hc

end AutModel

end CFSG.EvenSporadicStandard.M24Std.CU43
