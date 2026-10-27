module

public import CFSG.GH74.KGroups.L34Tables
public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

theorem ki3
    : CFSG.GH74.Uniqueness.SU.K.KI3 := by
  intro H _ _ _hGH _hO hL x hx hx2
  classical
  have hN : (CFSG.generalizedFitting H).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic).2
  obtain ⟨e⟩ := equiv_of_lieModel hL
  obtain ⟨hsolv, hcore, hcard⟩ := ki3_model (CFSG.generalizedFitting H)
    (CFSG.centralizer_generalizedFitting_le H) e x hx hx2
  refine ⟨hsolv, hcore, ?_⟩
  unfold CFSG.GH74.Uniqueness.SU.SU4.IsSylowIn
  set N : Subgroup H := CFSG.generalizedFitting H with hNdef
  have hle : Subgroup.centralizer ({x} : Set H) ⊓ N ≤ N := inf_le_right
  have hp : IsPGroup 2 ↥(Subgroup.centralizer ({x} : Set H) ⊓ N) :=
    IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)
  have hnN : Nat.card ↥N = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({x} : Set H) ⊓ N) (K := N)
  rw [inf_eq_left.2 hle, hcard, hnN] at h1
  have h2 : (Subgroup.centralizer ({x} : Set H) ⊓ N).relIndex N = 315 := by omega
  exact ⟨hle, hp, by rw [h2]; exact ⟨157, by norm_num⟩⟩

end CFSG.GH74.KGroups.L34
