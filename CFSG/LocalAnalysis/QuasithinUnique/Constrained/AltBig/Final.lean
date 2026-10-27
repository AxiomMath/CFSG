module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127KBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Sylow

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement

theorem isQuasisimple_alt {n : ℕ} (h5 : 5 ≤ n) :
    CFSG.Open.IsQuasisimple (alternatingGroup (Fin n)) := by
  have h5' : 5 ≤ Nat.card (Fin n) := by simpa using h5
  have hs : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup h5'
  refine ⟨?_, ?_⟩
  · have := commutator_alternatingGroup_eq_top h5'
    exact this
  · have hc : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
      alternatingGroup.center_eq_bot (by omega)
    exact (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)).2 hs

theorem nat_card_alt_three : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem alt_equiv_inj {n k : ℕ} (hn : 5 ≤ n) (hk : 5 ≤ k)
    (e : alternatingGroup (Fin n) ≃* alternatingGroup (Fin k)) : n = k := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hc := Nat.card_congr e.toEquiv
  rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at hc
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hc
  have h1 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h2 : 2 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hfac : n.factorial = k.factorial := by omega
  exact (Nat.factorial_inj (by omega)).1 hfac

theorem core_even {m n : ℕ} (hm : 10 ≤ m) (hmev : Even m) (hn3 : 3 ≤ n) (hnodd : Odd n)
    {T K : Subgroup ↥(alternatingGroup (Fin m))} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (φ : ↥K ≃* alternatingGroup (Fin n)) (hsub : IsSubnormal K (K ⊔ T)) : False := by
  classical
  have hα : Even (Fintype.card (Fin m)) := by simpa using hmev
  obtain ⟨p, hp⟩ := exists_contained_of_sylow hα hT
  have hYA : (K ⊔ T).map (alternatingGroup (Fin m)).subtype ≤ alternatingGroup (Fin m) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hKY : K.map (alternatingGroup (Fin m)).subtype ≤
      (K ⊔ T).map (alternatingGroup (Fin m)).subtype := Subgroup.map_mono le_sup_left
  have hB : p.Contained ((K ⊔ T).map (alternatingGroup (Fin m)).subtype) := fun x y h1 h2 =>
    Subgroup.map_mono le_sup_right (hp x y h1 h2)
  have hsub' : IsSubnormal (K.map (alternatingGroup (Fin m)).subtype)
      ((K ⊔ T).map (alternatingGroup (Fin m)).subtype) :=
    CFSG.Quasithin.A3.subnormal_map (alternatingGroup (Fin m)).subtype hsub
  have hcard : 10 ≤ Fintype.card (Fin m) := by simpa using hm
  have hKn : ↥(K.map (alternatingGroup (Fin m)).subtype) ≃* alternatingGroup (Fin n) :=
    (Subgroup.equivMapOfInjective K (alternatingGroup (Fin m)).subtype
      (alternatingGroup (Fin m)).subtype_injective).symm.trans φ
  rcases (show n = 3 ∨ 5 ≤ n by obtain ⟨r, hr⟩ := hnodd; omega) with h3 | h5
  · subst h3
    have hc : Nat.card ↥(K.map (alternatingGroup (Fin m)).subtype) = 3 := by
      rw [Nat.card_congr hKn.toEquiv]
      exact nat_card_alt_three
    exact no_three_subnormal p (by simpa using (by omega : 6 ≤ m)) hB hKY hsub' hc
  · have hq : CFSG.Open.IsQuasisimple ↥(K.map (alternatingGroup (Fin m)).subtype) :=
      open_isQuasisimple_of_mulEquiv hKn.symm (isQuasisimple_alt h5)
    have hcomp : IsComponentOf (K.map (alternatingGroup (Fin m)).subtype)
        ((K ⊔ T).map (alternatingGroup (Fin m)).subtype) := ⟨hKY, hsub', hq⟩
    obtain ⟨k, hkev, hk5, -, ⟨ek⟩⟩ := structure_component p hcard hYA hB hcomp
    have hnk : n = k := alt_equiv_inj h5 hk5 (hKn.symm.trans ek)
    subst hnk
    exact (Nat.not_even_iff_odd.2 hnodd) hkev

end CFSG.QuasithinUnique.L246C127.AltBig

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace L246C127

theorem altEvenExcludedBig : AltEvenExcludedBig := by
  intro Γ _ _ L K T m n hmev hm10 hnodd hn3 hnm ⟨ψ⟩ hKL ⟨φ⟩ hT hsub
  have hTL : T ≤ L := hT.1
  have hsub1 : IsSubnormal (K.subgroupOf L) (K.subgroupOf L ⊔ T.subgroupOf L) := by
    have h1 := A3.subnormal_comap L.subtype hsub
    have e : (K ⊔ T).comap L.subtype = K.subgroupOf L ⊔ T.subgroupOf L :=
      (Subgroup.comap_sup_eq_of_le_range L.subtype (by rw [Subgroup.range_subtype]; exact hKL)
        (by rw [Subgroup.range_subtype]; exact hTL)).symm
    rw [e] at h1
    exact h1
  have hsub2 : IsSubnormal ((K.subgroupOf L).map ψ.toMonoidHom)
      ((K.subgroupOf L).map ψ.toMonoidHom ⊔ (T.subgroupOf L).map ψ.toMonoidHom) := by
    have := A3.subnormal_map ψ.toMonoidHom hsub1
    rwa [Subgroup.map_sup] at this
  have hT2 := isSylowTwoOf_top_map_subgroupOf ψ hT
  have eK : ↥((K.subgroupOf L).map ψ.toMonoidHom) ≃* alternatingGroup (Fin n) :=
    ((Subgroup.equivMapOfInjective (K.subgroupOf L) ψ.toMonoidHom ψ.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hKL)).trans φ
  exact AltBig.core_even hm10 hmev hn3 hnodd hT2 eK hsub2

end L246C127

end CFSG.QuasithinUnique
