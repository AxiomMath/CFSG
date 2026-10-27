module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFInvolution
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFPermEF

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace Janko

variable {G : Type*} [Group G] {z : G} (hz : orderOf z = 2)
  (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))
include hH

theorem E_inf_F_eq :
    E e ⊓ F e = (liftOddSubgroup e JankoF.EFbar).map (centralizer ({z} : Set G)).subtype := by
  rw [E, F, ← map_inf_eq _ _ _ (centralizer _).subtype_injective]
  congr 1
  ext x
  rw [mem_inf, hH.mem_liftOddSubgroup_iff e JankoF.odd_card_Ebar,
    hH.mem_liftOddSubgroup_iff e JankoF.odd_card_EFbar, mem_comap, JankoF.EFbar, mem_inf]
  tauto

theorem card_EF : Nat.card (E e ⊓ F e : Subgroup G) = 9 := by
  rw [E_inf_F_eq hH e, card_map_of_injective (centralizer _).subtype_injective,
    hH.card_liftOddSubgroup e JankoF.odd_card_EFbar, JankoF.card_EFbar]

omit hH in
private theorem map_comap_inf_F (Y : Subgroup (alternatingGroup (Fin 9))) :
    (Y.comap (proj e)).map (centralizer ({z} : Set G)).subtype ⊓ F e =
      ((Y ⊓ Fbar).comap (proj e)).map (centralizer ({z} : Set G)).subtype := by
  rw [F, comap_inf, map_inf_eq _ _ _ (centralizer _).subtype_injective]

include hz in
theorem centralizer_EF :
    centralizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ F e = (E e ⊓ F e) ⊔ zpowers z := by
  have hodd := JankoF.odd_card_EFbar
  have hlhs : centralizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ F e =
      (JankoF.EFbar.comap (proj e)).map (centralizer ({z} : Set G)).subtype := by
    have hC : centralizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) =
        ((centralizer (JankoF.EFbar : Set (alternatingGroup (Fin 9)))).comap (proj e)).map
          (centralizer ({z} : Set G)).subtype := by
      rw [E_inf_F_eq hH e, centralizer_map_inf_eq_map_subtype,
        hH.centralizer_liftOddSubgroup e hodd]
    have h1 : centralizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ F e =
        centralizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) ⊓ F e := by
      rw [inf_assoc, inf_eq_right.mpr (F_le e)]
    rw [h1, hC, map_comap_inf_F e, JankoF.centralizer_EFbar]
  rw [hlhs]
  have hcard : Nat.card ((JankoF.EFbar.comap (proj e)).map
      (centralizer ({z} : Set G)).subtype) = 18 := by
    rw [card_map_of_injective (centralizer _).subtype_injective, hH.card_comap_proj e,
      JankoF.card_EFbar]
  have : Finite ((JankoF.EFbar.comap (proj e)).map (centralizer ({z} : Set G)).subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hzc : z ∈ centralizer ((E e ⊓ F e : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (F_le e hh.2)
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rw [E_inf_F_eq hH e]
    refine sup_le (map_mono (hH.liftOddSubgroup_le_comap e hodd)) (zpowers_le.mpr ?_)
    exact (JankoF.coe_mem_map_comap_iff e ⟨z, JankoF.self_mem_centralizer⟩).mpr
      (by rw [JankoF.proj_mk_eq_one]; exact one_mem _)
  · rw [hcard, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (zpowers_le.mpr (centralizer_le_normalizer _ hzc))
      (disjoint_of_coprime_natCard (by rw [card_EF hH e, Nat.card_zpowers, hz]; norm_num)),
      card_EF hH e, Nat.card_zpowers, hz]

include hz in
theorem normalizer_EF :
    normalizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ F e = (E e ⊓ F e) ⊔ zpowers (ℓ e) := by
  have hodd := JankoF.odd_card_EFbar
  have hlhs : normalizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ F e =
      ((normalizer (JankoF.EFbar : Set (alternatingGroup (Fin 9))) ⊓ Fbar).comap (proj e)).map
        (centralizer ({z} : Set G)).subtype := by
    have hN : normalizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) =
        ((normalizer (JankoF.EFbar : Set (alternatingGroup (Fin 9)))).comap (proj e)).map
          (centralizer ({z} : Set G)).subtype := by
      rw [E_inf_F_eq hH e, normalizer_map_inf_eq_map_subtype,
        hH.normalizer_liftOddSubgroup e hodd]
    have h1 : normalizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ F e =
        normalizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) ⊓ F e := by
      rw [inf_assoc, inf_eq_right.mpr (F_le e)]
    rw [h1, hN, map_comap_inf_F e]
  have hcard : Nat.card (normalizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ F e : Subgroup G) =
      72 := by
    rw [hlhs, card_map_of_injective (centralizer _).subtype_injective, hH.card_comap_proj e,
      JankoF.card_normalizer_EFbar]
  have : Finite (normalizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ F e : Subgroup G) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hℓN : ℓ e ∈ normalizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ F e := by
    rw [hlhs]
    exact (JankoF.coe_mem_map_comap_iff e _).mpr (by
      rw [proj_someLift]
      exact ⟨JankoF.ℓbar_mem_normalizer_EFbar, JankoF.ℓbar_mem_Fbar⟩)
  have hle : (E e ⊓ F e) ⊔ zpowers (ℓ e) ≤
      normalizer ((E e ⊓ F e : Subgroup G) : Set G) ⊓ F e :=
    sup_le (le_inf le_normalizer inf_le_right) (zpowers_le.mpr hℓN)
  have hdisj : Disjoint (E e ⊓ F e) (zpowers (ℓ e)) := disjoint_of_coprime_natCard (by
    rw [card_EF hH e, Nat.card_zpowers, orderOf_ℓ hz hH e]
    norm_num)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (zpowers_le.mpr hℓN.1) hdisj, card_EF hH e, Nat.card_zpowers, orderOf_ℓ hz hH e]

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
