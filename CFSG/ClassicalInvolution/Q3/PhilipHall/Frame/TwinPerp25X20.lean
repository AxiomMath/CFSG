module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X17
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X18

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Asc77.CX (TwinGroup DiagTriv DiagRel TwinIso centTG fixSubgroup)
open scoped MatrixGroups

section Rigid

theorem mulEquiv_eq_of_pow4 {H H' : Type} [Group H] [Group H'] (e : H ≃* SL(2, ZMod 3))
    (f g : H ≃* H') (h : ∀ k : H, k ^ 4 = 1 → f k = g k) : f = g := by
  let θ : H ≃* H := f.trans g.symm
  have hθ : ∀ k : H, k ^ 4 = 1 → θ k = k := fun k hk => by
    show g.symm (f k) = k
    rw [h k hk]
    exact g.symm_apply_apply k
  let θS : SL(2, ZMod 3) →* SL(2, ZMod 3) := (e.symm.trans (θ.trans e)).toMonoidHom
  have hfix : ∀ s : SL(2, ZMod 3), s ^ 4 = 1 → θS s = s := fun s hs => by
    show e (θ (e.symm s)) = s
    have h4 : (e.symm s) ^ 4 = 1 := by rw [← map_pow, hs, map_one]
    rw [hθ _ h4]
    exact e.apply_symm_apply s
  have hid := sl23_hom_eq_id_of_fix θS hfix
  ext k
  have h1 : θ k = k := by
    have := hid (e k)
    have h2 : e (θ k) = e k := by simpa [θS] using this
    exact e.injective h2
  have h3 : g.symm (f k) = k := h1
  calc f k = g (g.symm (f k)) := (g.apply_symm_apply (f k)).symm
    _ = g k := by rw [h3]

end Rigid


section LI

variable {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] {E E' : Type}
  {e : E → Y} {e' : E' → Y} {f : E → Y'} {f' : E' → Y'} {zb : Y} {zb' : Y'}
  {P : Subgroup (MulAut Y)} {P' : Subgroup (MulAut Y')}

theorem lift_preserved_le (hom5 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Om5StabDiag)
    (hcent5 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C25W.Cent5)
    (T : TwinLift e e' zb P) (T' : TwinLift f f' zb' P') {β : MulAut Y} {β' : MulAut Y'}
    (hA : T.A ≤ Goldschmidt75.perfRes (fixSubgroup β)) (hA' : T.A' ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hB : T'.A ≤ Goldschmidt75.perfRes (fixSubgroup β')) (hB' : T'.A' ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (h5' : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 (centTG T'.A T'.A' β' hB hB'))
    (ψ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β')))
    (hψ : ∀ r : E', ((ψ ⟨e' r, hA' (T.he' r)⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β'))) : Y') = f' r) :
    (T.A.subgroupOf (Goldschmidt75.perfRes (fixSubgroup β))).map ψ.toMonoidHom ≤
      T'.A.subgroupOf (Goldschmidt75.perfRes (fixSubgroup β')) := by
  classical
  rintro _ ⟨x, hx, rfl⟩
  have hxA : (x : Y) ∈ T.A := hx
  have hcomm : ∀ r : E', ((ψ x : ↥(Goldschmidt75.perfRes (fixSubgroup β'))) : Y') * f' r =
      f' r * ((ψ x : ↥(Goldschmidt75.perfRes (fixSubgroup β'))) : Y') := by
    intro r
    have h1 : (x : Y) * e' r = e' r * (x : Y) := T.hCA _ hxA r
    have h2 : x * (⟨e' r, hA' (T.he' r)⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β))) =
        ⟨e' r, hA' (T.he' r)⟩ * x := Subtype.ext h1
    have h3 := congrArg ψ h2
    rw [map_mul, map_mul] at h3
    have h4 := congrArg (fun m : ↥(Goldschmidt75.perfRes (fixSubgroup β')) => (m : Y')) h3
    simp only [Subgroup.coe_mul] at h4
    rw [hψ r] at h4
    exact h4
  obtain ⟨hN, hCenter⟩ := T'.hC _ hcomm
  have hmem := CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X.cq_abstract hom5 hcent5
    (centTG T'.A T'.A' β' hB hB') h5' T'.eA (c := ψ x)
    (fun a ha => by
      have ha' : Subtype.val a ∈ T'.A := ha
      exact hN _ ha')
    (fun a ha => Subtype.ext (hCenter _ ha))
    (fun a ha a' ha' => Subtype.ext ((T'.hC (Subtype.val a) (fun r => T'.hCA _ ha r)).2 _ ha'))
  exact hmem

theorem lift_preserved_le' (hom5 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Om5StabDiag)
    (hcent5 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C25W.Cent5)
    (T : TwinLift e e' zb P) (T' : TwinLift f f' zb' P') {β : MulAut Y} {β' : MulAut Y'}
    (hA : T.A ≤ Goldschmidt75.perfRes (fixSubgroup β)) (hA' : T.A' ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hB : T'.A ≤ Goldschmidt75.perfRes (fixSubgroup β')) (hB' : T'.A' ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (h5' : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 (centTG T'.A T'.A' β' hB hB'))
    (ψ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β')))
    (hψ : ∀ r : E, ((ψ ⟨e r, hA (T.he r)⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β'))) : Y') = f r) :
    (T.A'.subgroupOf (Goldschmidt75.perfRes (fixSubgroup β))).map ψ.toMonoidHom ≤
      T'.A'.subgroupOf (Goldschmidt75.perfRes (fixSubgroup β')) := by
  classical
  rintro _ ⟨x, hx, rfl⟩
  have hxA : (x : Y) ∈ T.A' := hx
  have hcomm : ∀ r : E, ((ψ x : ↥(Goldschmidt75.perfRes (fixSubgroup β'))) : Y') * f r =
      f r * ((ψ x : ↥(Goldschmidt75.perfRes (fixSubgroup β'))) : Y') := by
    intro r
    have h1 : (x : Y) * e r = e r * (x : Y) := T.hCA' _ hxA r
    have h2 : x * (⟨e r, hA (T.he r)⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β))) =
        ⟨e r, hA (T.he r)⟩ * x := Subtype.ext h1
    have h3 := congrArg ψ h2
    rw [map_mul, map_mul] at h3
    have h4 := congrArg (fun m : ↥(Goldschmidt75.perfRes (fixSubgroup β')) => (m : Y')) h3
    simp only [Subgroup.coe_mul] at h4
    rw [hψ r] at h4
    exact h4
  obtain ⟨hN, hCenter⟩ := T'.hC' _ hcomm
  have hmem := CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X.cq_abstract hom5 hcent5
    (twinSwap (centTG T'.A T'.A' β' hB hB')) (isOm5_twinSwap h5') T'.eA' (c := ψ x)
    (fun a ha => by
      have ha' : Subtype.val a ∈ T'.A' := ha
      exact hN _ ha')
    (fun a ha => Subtype.ext (hCenter _ ha))
    (fun a ha a' ha' => Subtype.ext ((T'.hC' (Subtype.val a) (fun r => T'.hCA' _ ha r)).2 _ ha'))
  exact hmem

end LI

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
