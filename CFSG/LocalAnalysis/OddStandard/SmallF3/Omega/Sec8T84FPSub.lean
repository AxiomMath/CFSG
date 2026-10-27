module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPModel

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.Asc82NormA6 (Facts)
open Certificates.T84P (Elt mulE oneE P0l Vl F0l Jl)

theorem sec8t84_oneE_F0l (G : Certificates.T84P.Facts) : oneE ∈ F0l := by
  obtain ⟨-, hlen, -, hmul, hsq, -⟩ := G.vf.2.1
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos (by omega : 0 < F0l.length)
  simpa [hsq x hx] using hmul x hx x hx

theorem sec8t84_oneE_Jl (G : Certificates.T84P.Facts) : oneE ∈ Jl := by
  have hV : oneE ∈ Vl := by
    obtain ⟨-, hlen, -, hmul, hsq, -⟩ := G.vf.1
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos (by omega : 0 < Vl.length)
    simpa [hsq x hx] using hmul x hx x hx
  have h11 : mulE oneE oneE = oneE := by simp [mulE, oneE]
  have h : mulE oneE oneE ∈ Jl := List.mem_dedup.mpr
    (List.mem_flatMap.mpr ⟨oneE, hV, List.mem_map.mpr ⟨oneE, sec8t84_oneE_F0l G, rfl⟩⟩)
  rwa [h11] at h

@[expose] def sec8t84FPP0 (F : Facts) (G : Certificates.T84P.Facts) :
    Subgroup (Sec8T84FPM0 F) :=
  sec8t84FPOfList F P0l G.p0.2.2.1 G.p0.2.2.2.2

@[expose] def sec8t84FPF0 (F : Facts) (G : Certificates.T84P.Facts) :
    Subgroup (Sec8T84FPM0 F) :=
  sec8t84FPOfList F F0l (sec8t84_oneE_F0l G) G.vf.2.1.2.2.2.1

@[expose] def sec8t84FPJ0 (F : Facts) (G : Certificates.T84P.Facts) :
    Subgroup (Sec8T84FPM0 F) :=
  sec8t84FPOfList F Jl (sec8t84_oneE_Jl G) G.j.2.2.2

end CFSG.OddStandard.SmallF3.Omega
