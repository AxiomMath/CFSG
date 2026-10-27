module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDPhi
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

namespace Sec5CDAbs

variable {L B : Subgroup G} {r : G} {i : Fin 6} {fr : NFrame Q (Fin 6) 1}
  {φc : ↥L →* omegaGroup hQ} (h : Sec5CDAbs L B r i fr φc)

include h

theorem phi_ones {t : G} (htL : t ∈ L) (htB : t ∈ B)
    (hπ : (φc ⟨t, htL⟩ : OGroup Q) = piOrth Q) :
    sec5c_phi L B r i fr φc (fun _ => 1) = t := by
  have he : IsEvenVec (fun _ : Fin 6 => (1 : ZMod 2)) := by
    refine (sec5c_isEvenVec_iff _).mpr ?_
    rw [sec5c_supp_one, Finset.card_univ, Fintype.card_fin]
    decide
  rw [h.phi_even he, sec5c_supp_one]
  have hu := h.liftL_unique (b := ⟨t, htL⟩) htB
  rw [hπ, fr.piOrth_eq_signChange_univ] at hu
  exact congrArg Subtype.val hu

theorem mem_B_of_comm {z : G} (hzL : z ∈ L) (hzz : z * z = 1)
    (hc : ∀ b ∈ B, b * z = z * b) : z ∈ B := by
  have hg : (φc ⟨z, hzL⟩ : OGroup Q) ∈ ffB0 fr := by
    refine sec5c_cent_B0 hQ h.dim h.sgn fr (φc ⟨z, hzL⟩).2 fun b hb => ?_
    obtain ⟨c, hcB, hcφ⟩ := h.B_onto b hb
    subst hcφ
    have hcomm : (⟨z, hzL⟩ : ↥L) * c = c * ⟨z, hzL⟩ := Subtype.ext (hc c hcB).symm
    have h1 := congrArg (fun x : ↥L => (φc x : OGroup Q)) hcomm
    simpa only [map_mul, Subgroup.coe_mul] using h1
  obtain ⟨c, hcB, hcφ⟩ := h.B_onto _ hg
  have hcc : c * c = 1 := Subtype.ext (h.B_sq _ hcB)
  have hzz' : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 := Subtype.ext hzz
  have hceq := h.cover.eq_of_mul_self_eq_one hcc hzz' (Subtype.ext hcφ)
  have hcz : (c : G) = z := congrArg Subtype.val hceq
  rw [← hcz]
  exact hcB

theorem weight_of_invType {v : Fin 6 → ZMod 2} (hv : IsEvenVec v)
    (hvL : sec5c_phi L B r i fr φc v ∈ L)
    (hinv : invType (φc ⟨sec5c_phi L B r i fr φc v, hvL⟩ : OGroup Q) = (4, 1)) :
    vecWeight v = 4 := by
  have hJ : Even (sec5c_supp v).card := (sec5c_isEvenVec_iff v).mp hv
  have hlift : (⟨sec5c_phi L B r i fr φc v, hvL⟩ : ↥L) =
      sec5c_liftL L B φc (fr.signChange (sec5c_supp v)) := Subtype.ext (h.phi_even hv)
  have hmap : (φc ⟨sec5c_phi L B r i fr φc v, hvL⟩ : OGroup Q) =
      fr.signChange (sec5c_supp v) := by
    rw [hlift]
    exact h.map_liftL (signChange_mem_ffB0 fr hJ)
  rw [hmap, fr.invType_signChange hQ _ hJ] at hinv
  rw [sec5c_vecWeight]
  exact congrArg Prod.fst hinv

end Sec5CDAbs

end CFSG.OddStandard.SmallF3.Omega
