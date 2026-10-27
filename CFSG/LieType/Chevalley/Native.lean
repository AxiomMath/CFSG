module

public import CFSG.LieType.Chevalley.RootOps.CommAll
public import CFSG.LieType.Chevalley.Canonical
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable (τ : Tag) (K : Type) [Field K]

@[expose] noncomputable def nativeRootSubgroups : RootSubgroups τ K :=
  (rootOperatorFamily τ).toRootSubgroups K fun i β hβ hne =>
    commContained_simpleRoot τ K i β hβ hne

theorem nativeRootSubgroups_X :
    (nativeRootSubgroups τ K).X = (rootOperatorFamily τ).rootSubgroup K :=
  rfl

@[expose] noncomputable def nativeData [Finite K] :
    RootGroupData (rootCombinatorics τ) (adjointGroup τ K) :=
  (nativeRootSubgroups τ K).toRootGroupData

@[expose] noncomputable def nrep (w : WeylGroup τ) : adjointGroup τ K :=
  ⟨canonicalRep (coxeterSystem τ) K w, canonicalRep_mem_adjointGroup (coxeterSystem τ) K w⟩

theorem nrep_eq_prod {ω : List (Fin τ.rank)} (hω : (coxeterSystem τ).IsReduced ω) :
    nrep τ K ((coxeterSystem τ).wordProd ω) = (ω.map (weylElement τ K)).prod := by
  apply Subtype.ext
  change canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) = _
  rw [canonicalRep_wordProd hω, Subgroup.val_list_prod, List.map_map]
  rfl

theorem nrep_mem_monomialGroup (w : WeylGroup τ) : nrep τ K w ∈ monomialGroup τ K := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [nrep_eq_prod τ K hω]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact weylElement_mem_monomialGroup i

theorem weylHom_nrep [Finite K] (w : WeylGroup τ) :
    weylHom τ K ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩ = w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  have hprod : (⟨nrep τ K ((coxeterSystem τ).wordProd ω), nrep_mem_monomialGroup τ K _⟩ :
      monomialGroup τ K) =
      (ω.map fun i => (⟨weylElement τ K i, weylElement_mem_monomialGroup i⟩ :
        monomialGroup τ K)).prod := by
    apply Subtype.ext
    change nrep τ K ((coxeterSystem τ).wordProd ω) = _
    rw [nrep_eq_prod τ K hω, Subgroup.val_list_prod, List.map_map]
    rfl
  rw [hprod, map_list_prod, List.map_map]
  change _ = (ω.map (coxeterSystem τ).simple).prod
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact weylHom_weylElement i

@[expose] noncomputable def Uminus (w : WeylGroup τ) : Subgroup (adjointGroup τ K) :=
  ⨆ (α : Root τ) (_ : 0 < height α.1 ∧ height (w • α).1 < 0), (nativeRootSubgroups τ K).X α

@[expose] noncomputable def Uplus (w : WeylGroup τ) : Subgroup (adjointGroup τ K) :=
  ⨆ (α : Root τ) (_ : 0 < height α.1 ∧ 0 < height (w • α).1), (nativeRootSubgroups τ K).X α

end CFSG.LieType.Chevalley
