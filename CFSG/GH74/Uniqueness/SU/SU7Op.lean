module

public import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Gen

open Subgroup CFSG

theorem op_eq_ker {X : Type*} [Group X] [Finite X] (ψ : X →* alternatingGroup (Fin 5))
    (hψ : Function.Surjective ψ) (hO : pPrimeCore 2 X ≤ ψ.ker)
    (h2 : IsPGroup 2 ↥(ψ.ker.map (QuotientGroup.mk' (pPrimeCore 2 X)))) :
    Op_p'p 2 X = ψ.ker := by
  classical
  apply le_antisymm
  · let ψb : X ⧸ pPrimeCore 2 X →* alternatingGroup (Fin 5) :=
      QuotientGroup.lift (pPrimeCore 2 X) ψ hO
    have hψbsurj : Function.Surjective ψb := fun a => by
      obtain ⟨x, rfl⟩ := hψ a
      exact ⟨QuotientGroup.mk x, rfl⟩
    intro w hw
    have hmk : QuotientGroup.mk' (pPrimeCore 2 X) w ∈ pCore 2 (X ⧸ pPrimeCore 2 X) := hw
    have hNn : ((pCore 2 (X ⧸ pPrimeCore 2 X)).map ψb).Normal :=
      Subgroup.Normal.map pCore_normal ψb hψbsurj
    have hNp : IsPGroup 2 ↥((pCore 2 (X ⧸ pPrimeCore 2 X)).map ψb) := pCore_isPGroup.map ψb
    have hbot := eq_bot_of_normal_isPGroup_alt5 hNn hNp
    have hmem : ψb (QuotientGroup.mk' (pPrimeCore 2 X) w) ∈
        (pCore 2 (X ⧸ pPrimeCore 2 X)).map ψb := Subgroup.mem_map_of_mem _ hmk
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  · intro w hw
    have hnorm : (ψ.ker.map (QuotientGroup.mk' (pPrimeCore 2 X))).Normal :=
      Subgroup.Normal.map ψ.normal_ker _ (QuotientGroup.mk'_surjective _)
    have hle : ψ.ker.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤
        pCore 2 (X ⧸ pPrimeCore 2 X) := le_sSup ⟨hnorm, h2⟩
    exact hle (Subgroup.mem_map_of_mem _ hw)

end CFSG.GH74.Uniqueness.SU.SU7.Gen
