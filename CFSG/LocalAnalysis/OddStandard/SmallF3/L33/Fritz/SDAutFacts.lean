module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDDihedral
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralH8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDCore

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDAutFacts

open CFSG Subgroup Equiv CFSG.ComponentClassification.HSFLit
open CFSG.ComponentClassification.HSDihedral
open CFSG.ComponentClassification.HSDihedral.H8 (autPair_H8)
open CFSG.OddStandard.SmallF3.L33.KD.SD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

omit [Finite X] in
theorem map_ker (A : SDData t L) : A.ψ.ker.map A.T.subtype = A.K := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, (A.ψ_eq_one_iff g).mp (MonoidHom.mem_ker.mp hg)⟩
  · intro hx
    exact ⟨⟨x, hx.1⟩, MonoidHom.mem_ker.mpr ((A.ψ_eq_one_iff _).mpr hx.2), rfl⟩

@[expose] noncomputable def datum (A : SDData t L) : LocalDatum X (Perm (ZMod 8)) where
  t := t
  S := A.T
  D := A.R
  ψ := A.ψ
  orderOf_t := A.orderOf_t
  sylow := ⟨A.syl, rfl⟩
  D_le := inf_le_left
  conj_mem_D := fun s hs d hd => conj_mem_R_of_mem_T hs hd
  eq_one_of_mem_D := fun d hd h1 =>
    A.eq_of_ψ_eq hd (one_mem _) (h1.trans (map_one A.ψ).symm)
  t_mem_ker := fun ht => (A.mem_K_iff ht).mp A.t_mem_K
  t_not_mem_D := fun ht => A.config.not_mem (A.R_le_L ht)
  isCyclic_ker :=
    ((A.ψ.ker.equivMapOfInjective A.T.subtype A.T.subtype_injective).trans
      (MulEquiv.subgroupCongr (map_ker A))).isCyclic.mpr A.isCyclic_K
  dihedral := ⟨4, by norm_num, SDDihedral.nonempty_mulEquiv_R A⟩

theorem Dbar_datum (A : SDData t L) : (datum A).Dbar = R8 := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact A.ψ_mem_R8' hg
  · intro σ hσ
    obtain ⟨r, hr, hrσ⟩ := A.exists_mem_R_ψ_eq hσ
    exact ⟨⟨r, hr.1⟩, hr, hrσ⟩

theorem autFacts_datum (A : SDData t L) : AutFacts (datum A) := by
  refine (datum A).autFacts_of_autPair ?_
  rw [Dbar_datum]
  exact autPair_H8 A.R8_le_range A.range_le_H8

end CFSG.OddStandard.SmallF3.L33.KD.SDAutFacts
