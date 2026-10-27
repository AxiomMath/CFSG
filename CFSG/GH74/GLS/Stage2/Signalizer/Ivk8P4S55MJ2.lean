module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Weak
public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MN1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MNoP
public import Certificates.Certificate5253
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.Schreier.PairJ2Faithful
public import CFSG.Sporadic.Schreier.PairJ3Cert

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem j2P_center_eq_bot :
    center ↥j2P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : (z : Equiv.Perm (Fin 315)) ∈
      Subgroup.centralizer (j2P : Set (Equiv.Perm (Fin 315))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
  rw [j2_centralizer_eq_bot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

theorem j2_mulAut_card_le :
    Nat.card (MulAut ↥j2P) ≤ 2 * Nat.card ↥j2P := by
  obtain ⟨-, -, -, -, h⟩ := ctuc_j2_full_automorphism_permutation_model
  rw [h, card_j2P]

theorem noN1_J2
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .J2) {p : ℕ} {b : MulAut Y}
    {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥j2P := (e : Y ≃* NativeSporadic.J2).trans j2PermEquiv
  exact noN1_of_noP e' j2P_center_eq_bot j2_mulAut_card_le (k := 7)
    (by rw [card_j2P]; norm_num) (by rw [card_j2P]; norm_num)
    Certificates.certificate5253.2.2.2.2.2.2.2.2.1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
