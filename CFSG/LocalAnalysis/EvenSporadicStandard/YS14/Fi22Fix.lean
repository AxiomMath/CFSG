module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi22E16
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.KGen
public import CFSG.Monster.B.Fischer.Fi22Model
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCover

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.EvenSporadicStandard.Solomon78

section Fi22


theorem involutionFixesElem_fi22P : InvolutionFixesElem ↥fi22P 16 := by
  intro α hα1 hα2
  obtain ⟨r, rfl⟩ := fi22RAut.surjective α
  have hr1 : r ≠ 1 := fun h => hα1 (by rw [h, map_one])
  have hr2 : r * r = 1 := fi22RAut.injective (by rw [map_mul, hα2, map_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf (r : Equiv.Perm (Fin 3510)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [← sq] at hr2; exact hr2) hr1
  obtain ⟨k, hk, c, hc, hcr⟩ := fi22R_involution_conj r.2 ho
  obtain ⟨E, hEP, hE2, hEc, hEt, hE16⟩ := fi22_e16_witness k hk
  set t : Equiv.Perm (Fin 3510) := fi22ExtRep k with ht
  set τ : Equiv.Perm (Fin 3510) := (r : Equiv.Perm (Fin 3510)) with hτ
  have hτc : τ = c⁻¹ * t * c := by
    rw [← hcr]; group
  have hN := fi22R_le_normalizer
  have hcinv : c⁻¹ ∈ fi22R := fi22R.inv_mem hc
  let E' : Subgroup (Equiv.Perm (Fin 3510)) := E.map (MulAut.conj c⁻¹).toMonoidHom
  have hmemE' : ∀ x, x ∈ E' ↔ ∃ y ∈ E, c⁻¹ * y * c = x := by
    intro x
    simp only [E', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hE'P : E' ≤ fi22P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmemE' x).1 hx
    have := (Subgroup.mem_normalizer_iff.1 (hN hcinv) y).1 (hEP hy)
    simpa using this
  refine ⟨E'.subgroupOf fi22P, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := (hmemE' _).1 hx
    apply Subtype.ext
    rw [fi22RAut_apply, fi22ConjHom_apply]
    have hyt : y * t = t * y := hEt y hy
    show τ * (x : Equiv.Perm (Fin 3510)) * τ⁻¹ = x
    rw [← hyx, hτc]
    calc c⁻¹ * t * c * (c⁻¹ * y * c) * (c⁻¹ * t * c)⁻¹ = c⁻¹ * (t * y * t⁻¹) * c := by group
      _ = c⁻¹ * y * c := by rw [← hyt]; group
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := (hmemE' _).1 hx
    apply Subtype.ext
    show (x : Equiv.Perm (Fin 3510)) * x = 1
    rw [← hyx]
    calc c⁻¹ * y * c * (c⁻¹ * y * c) = c⁻¹ * (y * y) * c := by group
      _ = 1 := by rw [hE2 y hy]; group
  · intro x hx x' hx'
    rw [Subgroup.mem_subgroupOf] at hx hx'
    obtain ⟨y, hy, hyx⟩ := (hmemE' _).1 hx
    obtain ⟨y', hy', hyx'⟩ := (hmemE' _).1 hx'
    apply Subtype.ext
    show (x : Equiv.Perm (Fin 3510)) * x' = x' * x
    rw [← hyx, ← hyx']
    calc c⁻¹ * y * c * (c⁻¹ * y' * c) = c⁻¹ * (y * y') * c := by group
      _ = c⁻¹ * (y' * y) * c := by rw [hEc y hy y' hy']
      _ = c⁻¹ * y' * c * (c⁻¹ * y * c) := by group
  · have h1 : Nat.card ↥(E'.subgroupOf fi22P) = Nat.card E' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'P).toEquiv
    have h2 : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
    rw [h1, h2]
    exact hE16

theorem involutionFixesElem_native_fi22 :
    InvolutionFixesElem CFSG.Blueprint.NativeSporadic.Fi22 16 :=
  @CFSG.EvenSporadicStandard.Induction.Fi.involutionFixesElem_of_mulEquiv ↥fi22P
    CFSG.Blueprint.NativeSporadic.Fi22 _ Units.instGroup fi22PermEquiv.symm 16
    involutionFixesElem_fi22P

theorem involutionFixesElem_fi22 :
    InvolutionFixesElem (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) 16 :=
  involutionFixesElem_native_fi22

end Fi22

end CFSG.EvenSporadicStandard.YS14
