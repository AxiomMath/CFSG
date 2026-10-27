module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Weak
public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MN1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MNoP
public import Certificates.Certificate5253
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.Schreier.PairJ3Faithful
public import CFSG.Sporadic.Schreier.PairJ2Cert

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem j3P_center_eq_bot :
    center ↥j3P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : (z : Equiv.Perm (Fin 6156)) ∈
      Subgroup.centralizer (j3P : Set (Equiv.Perm (Fin 6156))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
  rw [j3_centralizer_eq_bot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

theorem j3_mulAut_card_le :
    Nat.card (MulAut ↥j3P) ≤ 2 * Nat.card ↥j3P := by
  have h := j3_autModel
  have hinj : Function.Injective (fun α : MulAut ↥j3P => (⟨h.elt α, h.elt_mem α⟩ : ↥j3R)) := by
    intro α β hαβ
    exact h.hom_injective (congrArg Subtype.val hαβ)
  calc Nat.card (MulAut ↥j3P) ≤ Nat.card ↥j3R := Nat.card_le_card_of_injective _ hinj
    _ ≤ 2 * Nat.card ↥j3P := by
      rw [ctuc_j3_normalizing_involution_permutation_model.2.2.2.2.2.2.2.2.1, card_j3P]

theorem noN1_J3
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .J3) {p : ℕ} {b : MulAut Y}
    {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥j3P := (e : Y ≃* NativeSporadic.J3).trans j3PermEquiv
  exact noN1_of_noP e' j3P_center_eq_bot j3_mulAut_card_le (k := 7)
    (by rw [card_j3P]; norm_num) (by rw [card_j3P]; norm_num)
    Certificates.certificate5253.2.2.2.2.1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
