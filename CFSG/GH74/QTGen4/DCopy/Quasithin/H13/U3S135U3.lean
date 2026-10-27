module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15U
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S135Gen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3SixAction

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem u3_centralizer_not_le_F4
    (h1332 : Stmt13_3_2_F4) (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G} {z : G}
    (hH : QTH13 G T L) (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) (hF : QTU3InternalFrame T L V z)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  have : CFSG.IsElementaryAbelian 2 V := hF.2.2.1
  obtain ⟨v₀, hv₀, hv₀1, hM⟩ := exists_centralizer_not_le_F4 h12213 hH (hyp1223_of_F4 h1332 hH hV)
  obtain ⟨l, hl, hlv⟩ :=
    (u3_six_action_profile_producer_F4 h1332 G T L V z hH hU3 hF).1 v₀ hv₀ hv₀1 v hv hv1
  exact not_centralizer_le_of_conj (inv_mem (le_normalizer hl)) (by rw [inv_inv]; exact hlv) hM

theorem u3_g1_not_le_F4
    (h1332 : Stmt13_3_2_F4) (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    (hH : QTH13 G T L) (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) :
    ¬ A6.g1 T V ≤ normalizer (L : Set G) := by
  obtain ⟨z, hF⟩ := u3_frame_of_irrPlus_F4 h1332 hH hU3 hV
  have hVz : V ⊓ centralizer (T : Set G) = zpowers z := hF.2.2.2.2.2.2.2.2.2.2.2.1
  have hz2 : orderOf z = 2 := hF.2.2.2.2.2.2.2.2.2.2.2.2
  have hV1 : fsuV1 T V = zpowers z := (fsuV1_eq hF).trans hVz
  have hzV : z ∈ V := by
    have : z ∈ V ⊓ centralizer (T : Set G) := by rw [hVz]; exact mem_zpowers z
    exact this.1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  intro hle
  apply u3_centralizer_not_le_F4 h1332 h12213 hH hU3 hV hF hzV hz1
  refine (centralizer_le_normalizer_zpowers z).trans ?_
  rw [← hV1]
  exact hle

end CFSG.Quasithin.H13.U3
