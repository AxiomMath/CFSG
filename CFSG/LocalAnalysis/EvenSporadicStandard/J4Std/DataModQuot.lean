module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModMap
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open Subgroup CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

theorem quotData_J :
    QuotData (⊤ : Subgroup J) (Eg uJ 11) := by
  have hF := j4Facts
  have hmem : ∀ g : ↥Hj, starHom g ∈ CFSG.Blueprint.NativeSporadic.M24 := fun g => by
    rw [← range_starHom_eq]
    exact ⟨g, rfl⟩
  let f0 : ↥Hj →* ↥CFSG.Blueprint.NativeSporadic.M24 := starHom.codRestrict _ hmem
  have hf0 : Function.Surjective f0 := by
    intro m
    obtain ⟨g, hg⟩ : (m : Equiv.Perm (Fin 24)) ∈ starHom.range := by
      rw [range_starHom_eq]
      exact m.2
    exact ⟨g, Subtype.ext hg⟩
  have hf0ker : f0.ker = (Eg uJ 11).subgroupOf Hj := by
    rw [← ker_starHom]
    ext g
    simp only [MonoidHom.mem_ker, f0]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  exact quotData_of_Hloc_eq (Hloc_top_eq hF) f0 hf0 hf0ker

end CFSG.EvenSporadicStandard.J4Std.DataMod

namespace CFSG.EvenSporadicStandard.J4Std

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem quotData_J4
    {G : Type} [Group G]
    (ι : J →* G) (hι : Function.Injective ι) : QuotData ι.range ((Eg uJ 11).map ι) :=
  DataMod.quotData_map ι hι _ DataMod.quotData_J

end CFSG.EvenSporadicStandard.J4Std
