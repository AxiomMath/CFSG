module

public import Certificates.Data.Kernel.Ivk8CentralN
public import CFSG.Certificates.Kernel.Ivk8TwoNSound
public import CFSG.Certificates.Kernel.Spor.MulHSound

public section

namespace CFSG.KC.Ivk8N

open CFSG.KC.Enum CFSG.KC.YoshQ CFSG.Sporadic.Th.Native Certificates.Ivk8Two CFSG.KS.MulH

variable {n w : Nat}

theorem centralOKT_tabN (d : Dims n w) (gs : List Nat) (wd : List Int) :
    centralOKT n (gs.map (tabN n w)) wd = centralOKN n w gs wd := by
  unfold centralOKT centralOKN invOKN
  simp only [map_invT_tabN d, evalT_tabN' d, List.all_map, Function.comp_def, invT_tabN' d,
    invOK_tabN d, compT_tabN' d, tblEq_tabN' d]

theorem tabT_unpack (X : Nat) : tabT (CFSG.KS.Raw.unpack n w X) = tabN n w X := by
  apply Array.ext (by simp [tabT, tabN, CFSG.KS.Raw.unpack])
  intro i h1 _
  have hi : i < n := by simpa [tabT, CFSG.KS.Raw.unpack] using h1
  simp only [tabT, tabN, Array.getElem_map, Array.getElem_ofFn, CFSG.KS.Raw.unpack]
  rw [pg_mod hi]

theorem beq_tabN (d : Dims n w) (x y : Nat) : (tabN n w x == tabN n w y) = eqN n w x y := by
  apply Bool.eq_iff_iff.2
  unfold eqN
  simp only [beq_iff_eq, Nat.beq_eq]
  constructor
  · intro h
    exact (tabN_inj_iff (n := n) d.w_pos d.w_le).1 fun i _ => by rw [h]
  · intro h
    unfold tabN
    rw [h]

theorem map_eq_compT' {P T : Table} (hT : T.size = n) :
    T.map (fun t => P[t.toNat]!) = compT n P T := by
  apply Array.ext (by simp [compT, hT])
  intro i h1 _
  simp only [Array.getElem_map, compT, Array.getElem_ofFn]
  rw [getElem!_pos T i (by simpa using h1)]

end CFSG.KC.Ivk8N

end
