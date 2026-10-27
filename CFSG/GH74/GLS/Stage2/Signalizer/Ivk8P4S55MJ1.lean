module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Weak
public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MN1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MNoP
public import Certificates.Certificate5253
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MOut
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.PairJ2Cert
public import CFSG.Sporadic.Schreier.PairJ3Cert

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

theorem j1P_center_eq_bot :
    center ↥j1P = ⊥ := by
  have hs : IsSimpleGroup ↥j1P := isSimpleGroup_j1P
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥j1P) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ x y : ↥j1P, x * y = y * x := fun x y =>
      Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top y) x
    let _ : CommGroup ↥j1P := { (inferInstance : Group ↥j1P) with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := ↥j1P)
    rw [card_j1P] at hp
    exact absurd hp (by norm_num)

theorem j1_mulAut_card_le :
    Nat.card (MulAut ↥j1P) ≤ 2 * Nat.card ↥j1P := by
  have : Finite NativeSporadic.J1 := Finite.of_equiv _ j1PermEquiv.symm.toEquiv
  have h1 := mulAut_card_le_of_outer (k := 1) (at_j1_schreier.1).le j1PermEquiv
  rw [Nat.card_congr j1PermEquiv.toEquiv] at h1
  omega

theorem noN1_J1
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .J1) {p : ℕ} {b : MulAut Y}
    {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥j1P := (e : Y ≃* NativeSporadic.J1).trans j1PermEquiv
  exact noN1_of_noP e' j1P_center_eq_bot j1_mulAut_card_le (k := 3)
    (by rw [card_j1P]; norm_num) (by rw [card_j1P]; norm_num)
    Certificates.certificate5253.2.2.2.2.2.2.2.1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
