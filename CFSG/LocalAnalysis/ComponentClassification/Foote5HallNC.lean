module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.ComponentClassification.Foote5.HallNC

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] (C : Subgroup G)

@[expose] def Nc : Subgroup G := normalizer (C : Set G)

@[expose] def Cn : Subgroup (Nc C) := C.subgroupOf (Nc C)

instance Cn_normal : (Cn C).Normal := Subgroup.normal_in_normalizer

end CFSG.ComponentClassification.Foote5.HallNC
