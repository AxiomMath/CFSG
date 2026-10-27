module

public import CFSG.GF2Type.SmithTypeE.LMod.RhoT6
public import Certificates.Certificate38608

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open CFSG.LargeExtraspecial.SMod20 (V eq_of_decode_eq)

theorem tvArrInj_holds : chkTvArrInj = true :=
  Certificates.certificate38608

theorem tvCols_injective {a b : ℕ} (ha : a < 1953)
    (hb : b < 1953) (h : tvCols a = tvCols b) : a = b := by
  have hchk := tvArrInj_holds
  simp only [chkTvArrInj, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hchk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hchk b hb a hlt (by rw [tvArr_get ha, tvArr_get hb]; exact h)
  · exact hchk a ha b hlt (by rw [tvArr_get ha, tvArr_get hb]; exact h.symm)

section Faith

theorem array_eq_of_getElem!_eq {x y : Array ℕ} (hs : x.size = y.size)
    (h : ∀ m < x.size, x[m]! = y[m]!) : x = y := by
  apply Array.ext hs
  intro m hm1 hm2
  exact (getElem!_pos x m hm1).symm.trans ((h m hm1).trans (getElem!_pos y m hm2))

theorem tvEquiv_injective {a b : ℕ} (ha : a < 1953) (hb : b < 1953) (h : tvEquiv a = tvEquiv b) :
    a = b := by
  refine tvCols_injective ha hb
    (array_eq_of_getElem!_eq (by rw [size_tvCols, size_tvCols]) fun m hm => ?_)
  have hm20 : m < 20 := by rwa [size_tvCols] at hm
  have h1 := congrArg (fun L : V ≃ₗ[ZMod 2] V => L (Pi.single ⟨m, hm20⟩ 1)) h
  simp only [tvEquiv_single ha, tvEquiv_single hb] at h1
  exact eq_of_decode_eq (tvInv_parts ha m hm20).1 (tvInv_parts hb m hm20).1 h1

end Faith

section Rho

theorem rhoMod_injective : Function.Injective (rhoMod : T6 →* (V ≃ₗ[ZMod 2] V)) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  refine Subtype.ext (Equiv.ext fun k => ?_)
  have h := rhoMod_conj_tvEquiv g k
  rw [hg, one_mul, inv_one, mul_one] at h
  exact (Fin.ext (tvEquiv_injective k.2 ((g : Equiv.Perm (Fin 1953)) k).2 h)).symm

end Rho

end CFSG.GF2Type.SmithTypeE.LMod
