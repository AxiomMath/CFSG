module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Weak
public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MN1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MNoP
public import Certificates.Certificate5253
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12L34
public import Certificates.Certificate5247
public import CFSG.Sporadic.Schreier.PairJ2Cert
public import CFSG.Sporadic.Schreier.PairJ3Cert

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem center_S_eq_bot_L34 :
    Subgroup.center ↥CFSG.ComponentClassification.PSL3Four.S = ⊥ := by
  open CFSG.ComponentClassification.PSL3Four in
  rw [eq_bot_iff]
  intro z hz
  open CFSG.ComponentClassification.PSL3Four in
  have h1 : conjAutS (⟨(z : Equiv.Perm (Fin 42)), S_le_R z.2⟩ : ↥R) = 1 := by
    refine MulEquiv.ext fun t => Subtype.ext ?_
    rw [conjAutS_apply]
    have := Subgroup.mem_center_iff.mp hz t
    have h2 : (t : Equiv.Perm (Fin 42)) * z = z * t := congrArg Subtype.val this
    show _ = (t : Equiv.Perm (Fin 42))
    calc (z : Equiv.Perm (Fin 42)) * t * (z : Equiv.Perm (Fin 42))⁻¹
        = ((z : Equiv.Perm (Fin 42)) * t) * (z : Equiv.Perm (Fin 42))⁻¹ := rfl
      _ = (t * z) * (z : Equiv.Perm (Fin 42))⁻¹ := by rw [h2]
      _ = t := by group
  open CFSG.ComponentClassification.PSL3Four in
  have h2 : (⟨(z : Equiv.Perm (Fin 42)), S_le_R z.2⟩ : ↥R) = 1 :=
    conjAutS_injective (by rw [h1, map_one])
  have h3 : (z : Equiv.Perm (Fin 42)) = 1 := congrArg Subtype.val h2
  exact Subgroup.mem_bot.mpr (Subtype.ext h3)

theorem noN1_L34
    {Y : Type} [Group Y] (hY : LieModel Y .PSL 3 2 2) {p : ℕ} {b : MulAut Y}
    {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hY
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hI : ((CFSG.ComponentClassification.PSL3Four.S).subgroupOf
      CFSG.ComponentClassification.PSL3Four.R).map
        ((Cls3.conjIso.trans (MulAut.congr e.symm)).toMonoidHom) = innSub Y := by
    have h1 : ((Cls3.conjIso.trans (MulAut.congr e.symm)).toMonoidHom) =
        (MulAut.congr e.symm).toMonoidHom.comp Cls3.conjIso.toMonoidHom := rfl
    rw [h1, ← Subgroup.map_map, Cls3.map_SR_eq_innSub, map_innSub e.symm]
  have hcY : Subgroup.center Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : e z ∈ Subgroup.center ↥CFSG.ComponentClassification.PSL3Four.S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      have := congrArg e (hz (e.symm g))
      simpa using this
    rw [center_S_eq_bot_L34, Subgroup.mem_bot] at hz'
    exact e.injective (by simpa using hz')
  exact noN1_of_noP_aut CFSG.ComponentClassification.PSL3Four.S_le_R
    (Cls3.conjIso.trans (MulAut.congr e.symm)) hI hcY (k := 6)
    (by rw [CFSG.ComponentClassification.PSL3Four.card_S]; norm_num)
    (by rw [CFSG.ComponentClassification.PSL3Four.card_S]; norm_num)
    Certificates.certificate5253.2.2.1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
