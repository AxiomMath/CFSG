module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4M23

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.IVK


theorem m23_centralizer_perfect_card {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y)
    {F : Type} [Group F] (eN : ↥N ≃* F) (e : F ≃* ↥NativeSporadic.M23)
    {t : Y} (htN : t ∈ N) (ht : orderOf t = 2) :
    Group.IsPerfect ↥(N ⊓ Subgroup.centralizer ({t} : Set Y)) ∧
      Nat.card ↥(N ⊓ Subgroup.centralizer ({t} : Set Y)) = 2688 := by
  let φ : ↥N ≃* ↥NativeSporadic.M23 := eN.trans e
  let s : ↥N := ⟨t, htN⟩
  have hs2 : orderOf s = 2 := (Subgroup.orderOf_coe s).symm.trans ht
  have hφs : orderOf (φ s) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hs2
  have hord : orderOf ((φ s : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hφs
  obtain ⟨hperf0, hcard0⟩ := m23_inv_centralizer_data _ (φ s).2 hord
  have hperfS : Group.IsPerfect ↥(Subgroup.centralizer ({s} : Set ↥N)) :=
    GHInv.isPerfect_centralizer_of_equiv NativeSporadic.M23 φ s hperf0
  have hcardS : Nat.card ↥(Subgroup.centralizer ({s} : Set ↥N)) = 2688 := by
    rw [GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M23 φ s]
    exact hcard0
  let ε := GHInv.centralizerSubtypeEquiv N s
  refine ⟨Group.IsPerfect.ofSurjective (f := ε.toMonoidHom) ε.surjective, ?_⟩
  exact (Nat.card_congr ε.toEquiv).symm.trans hcardS

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
