module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovCfg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Mathieu
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4J3

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.OddStandard CFSG.GH74.Generic.S45 CFSG.GH74.GLS.IVK

theorem ivk93cov_empty_of_small_centralizers {P : (X : Type) → [Group X] → Prop}
    (hsmall : ∀ (L : Type) [Group L] [Finite L], P L → ∀ y : L, y * y = 1 → y ≠ 1 →
      Nat.card ↥(centralizer ({y} : Set L)) < 40320) :
    Ivk93CovEmpty P :=
  ivk93cov_empty_of_cfg fun J _ _ hJ x _ _ _ hc =>
    hc.false_of_card_cent_lt (hsmall J hJ x hc.mul_self_eq_one hc.ne_one)

theorem ivk93cov_m11 :
    Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .M11) := by
  refine ivk93cov_empty_of_small_centralizers ?_
  intro L _ _ hL y hy2 hy1
  obtain ⟨e⟩ := hL
  have e' : L ≃* NativeSporadic.M11 := e
  obtain ⟨p, hp, hcard⟩ := mathieu_card_cent_mem m11_innerRecordsValid e' hy2 hy1
  have hshape : recordShape m11Records = [(165, 48)] := rfl
  rw [hshape] at hp
  have hp2 : p.2 = 48 := by simp at hp; rw [hp]
  rw [hcard, hp2]
  norm_num

theorem ivk93cov_m22 :
    Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .M22) := by
  refine ivk93cov_empty_of_small_centralizers ?_
  intro L _ _ hL y hy2 hy1
  obtain ⟨e⟩ := hL
  have e' : L ≃* NativeSporadic.M22 := e
  obtain ⟨p, hp, hcard⟩ := mathieu_card_cent_mem m22_innerRecordsValid e' hy2 hy1
  have hshape : recordShape m22Records = [(1155, 384)] := rfl
  rw [hshape] at hp
  have hp2 : p.2 = 384 := by simp at hp; rw [hp]
  rw [hcard, hp2]
  norm_num

theorem ivk93cov_m23 :
    Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .M23) := by
  refine ivk93cov_empty_of_small_centralizers ?_
  intro L _ _ hL y hy2 hy1
  obtain ⟨e⟩ := hL
  have e' : L ≃* NativeSporadic.M23 := e
  obtain ⟨p, hp, hcard⟩ := mathieu_card_cent_mem m23_innerRecordsValid e' hy2 hy1
  have hshape : recordShape m23Records = [(3795, 2688)] := rfl
  rw [hshape] at hp
  have hp2 : p.2 = 2688 := by simp at hp; rw [hp]
  rw [hcard, hp2]
  norm_num

theorem ivk93cov_j3 :
    Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .J3) := by
  refine ivk93cov_empty_of_small_centralizers ?_
  intro L _ _ hL y hy2 hy1
  obtain ⟨e⟩ := hL
  let e' : L ≃* ↥j3P := e.trans j3PermEquiv
  have hord : orderOf ((e' y : ↥j3P) : Equiv.Perm (Fin 6156)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨-, hcard⟩ := j3_inner_centralizer_data _ (e' y).2 hord
  rw [GHInv.card_centralizer_eq_centralizerIn j3P e' y, hcard]
  norm_num

end CFSG.GH74.GLS.IVK.Proofs2
