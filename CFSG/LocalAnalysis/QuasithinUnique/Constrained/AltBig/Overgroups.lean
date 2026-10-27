module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Sylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenMain

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement

theorem core_even_overgroup {m : ℕ} (hm : 10 ≤ m) (hmev : Even m)
    {T X K : Subgroup ↥(alternatingGroup (Fin m))} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hTX : T ≤ X) (hKX : K ≤ X) (hsub : IsSubnormal K X)
    (hK : CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) :
    ∃ n, n ≤ m ∧ Nonempty (↥K ≃* alternatingGroup (Fin n)) := by
  classical
  have hα : Even (Fintype.card (Fin m)) := by simpa using hmev
  obtain ⟨p, hp⟩ := exists_contained_of_sylow hα hT
  have hYA : X.map (alternatingGroup (Fin m)).subtype ≤ alternatingGroup (Fin m) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hKY : K.map (alternatingGroup (Fin m)).subtype ≤ X.map (alternatingGroup (Fin m)).subtype :=
    Subgroup.map_mono hKX
  have hB : p.Contained (X.map (alternatingGroup (Fin m)).subtype) := fun x y h1 h2 =>
    Subgroup.map_mono hTX (hp x y h1 h2)
  have hsub' : IsSubnormal (K.map (alternatingGroup (Fin m)).subtype)
      (X.map (alternatingGroup (Fin m)).subtype) :=
    CFSG.Quasithin.A3.subnormal_map (alternatingGroup (Fin m)).subtype hsub
  have hcard : 10 ≤ Fintype.card (Fin m) := by simpa using hm
  have hKe : ↥(K.map (alternatingGroup (Fin m)).subtype) ≃* ↥K :=
    (Subgroup.equivMapOfInjective K (alternatingGroup (Fin m)).subtype
      (alternatingGroup (Fin m)).subtype_injective).symm
  rcases hK with hq | h3
  · have hq' : CFSG.Open.IsQuasisimple ↥(K.map (alternatingGroup (Fin m)).subtype) :=
      open_isQuasisimple_of_mulEquiv hKe.symm hq
    have hcomp : IsComponentOf (K.map (alternatingGroup (Fin m)).subtype)
        (X.map (alternatingGroup (Fin m)).subtype) := ⟨hKY, hsub', hq'⟩
    obtain ⟨k, -, -, hkm, ⟨ek⟩⟩ := structure_component p hcard hYA hB hcomp
    refine ⟨k, by simpa using hkm, ⟨hKe.symm.trans ek⟩⟩
  · exfalso
    have hc : Nat.card ↥(K.map (alternatingGroup (Fin m)).subtype) = 3 := by
      rw [Nat.card_congr hKe.toEquiv]
      exact h3
    exact no_three_subnormal p (by simpa using (by omega : 6 ≤ m)) hB hKY hsub' hc

end CFSG.QuasithinUnique.L246C127.AltBig

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace L246C127

theorem alt_overgroups_even {Γ : Type} [Group Γ] [Finite Γ] (L T X K : Subgroup Γ) {m : ℕ}
    (hm : 10 ≤ m) (hmev : Even m) (hL : Nonempty (↥L ≃* alternatingGroup (Fin m)))
    (hT : IsSylowTwoOf T L) (hTX : T ≤ X) (hXL : X ≤ L) (hKX : K ≤ X)
    (hsub : IsSubnormal K X) (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) :
    ∃ n, n ≤ m ∧ IsAlt n ↥K := by
  obtain ⟨ψ⟩ := hL
  have hKL : K ≤ L := hKX.trans hXL
  have hTL : T ≤ L := hT.1
  have hsub1 : IsSubnormal (K.subgroupOf L) (X.subgroupOf L) :=
    A3.subnormal_comap L.subtype hsub
  have hsub2 : IsSubnormal ((K.subgroupOf L).map ψ.toMonoidHom) ((X.subgroupOf L).map ψ.toMonoidHom) :=
    A3.subnormal_map ψ.toMonoidHom hsub1
  have hT2 := isSylowTwoOf_top_map_subgroupOf ψ hT
  have hTX2 : (T.subgroupOf L).map ψ.toMonoidHom ≤ (X.subgroupOf L).map ψ.toMonoidHom :=
    Subgroup.map_mono (fun t ht => hTX ht)
  have hKX2 : (K.subgroupOf L).map ψ.toMonoidHom ≤ (X.subgroupOf L).map ψ.toMonoidHom :=
    Subgroup.map_mono (fun t ht => hKX ht)
  have eK : ↥((K.subgroupOf L).map ψ.toMonoidHom) ≃* ↥K :=
    (Subgroup.equivMapOfInjective (K.subgroupOf L) ψ.toMonoidHom ψ.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hKL)
  have hK2 : CFSG.Open.IsQuasisimple ↥((K.subgroupOf L).map ψ.toMonoidHom) ∨
      Nat.card ↥((K.subgroupOf L).map ψ.toMonoidHom) = 3 := by
    rcases hK with hq | h3
    · exact Or.inl (AltBig.open_isQuasisimple_of_mulEquiv eK.symm (B1Red.isQuasisimple_to_open hq))
    · exact Or.inr (by rw [Nat.card_congr eK.toEquiv]; exact h3)
  obtain ⟨n, hnm, ⟨e⟩⟩ := AltBig.core_even_overgroup hm hmev hT2 hTX2 hKX2 hsub2 hK2
  exact ⟨n, hnm, ⟨eK.symm.trans e⟩⟩

end L246C127

end CFSG.QuasithinUnique
