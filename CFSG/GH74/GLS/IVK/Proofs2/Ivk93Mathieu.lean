module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Mathieu

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.OddStandard
  CFSG.GH74.GLS.IVK

theorem ivk93_empty_of_small_centralizers {P : (X : Type) → [Group X] → Prop}
    (hsmall : ∀ (L : Type) [Group L] [Finite L], P L → ∀ y : L, y * y = 1 → y ≠ 1 →
      Nat.card ↥(centralizer ({y} : Set L)) < 7200) :
    Ivk93Empty P :=
  ivk93_empty_of_cfg fun J _ _ hJ x _ _ _ _ hc =>
    hc.false_of_pair_card (hsmall J hJ x hc.mul_self_eq_one hc.ne_one)

theorem mathieu_card_cent_mem {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {recs : List (InnerClassRecord n)} (hvalid : InnerClassRecordsValid G recs) {L : Type} [Group L]
    (e : L ≃* ↥G) {y : L} (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ p ∈ recordShape recs, Nat.card ↥(centralizer ({y} : Set L)) = p.2 := by
  have hord : orderOf ((e y : ↥G) : Equiv.Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨p, hp, hcard⟩ := mathieu_inv_card_mem hvalid _ (e y).2 hord
  exact ⟨p, hp, by rw [GHInv.card_centralizer_eq_centralizerIn G e y, hcard]⟩

theorem ivk93_m11 :
    Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .M11) := by
  refine ivk93_empty_of_small_centralizers ?_
  intro L _ _ hL y hy2 hy1
  obtain ⟨e⟩ := hL
  have e' : L ≃* NativeSporadic.M11 := e
  obtain ⟨p, hp, hcard⟩ := mathieu_card_cent_mem m11_innerRecordsValid e' hy2 hy1
  have hshape : recordShape m11Records = [(165, 48)] := rfl
  rw [hshape] at hp
  have hp2 : p.2 = 48 := by simp at hp; rw [hp]
  rw [hcard, hp2]
  norm_num

theorem ivk93_m22 :
    Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .M22) := by
  refine ivk93_empty_of_small_centralizers ?_
  intro L _ _ hL y hy2 hy1
  obtain ⟨e⟩ := hL
  have e' : L ≃* NativeSporadic.M22 := e
  obtain ⟨p, hp, hcard⟩ := mathieu_card_cent_mem m22_innerRecordsValid e' hy2 hy1
  have hshape : recordShape m22Records = [(1155, 384)] := rfl
  rw [hshape] at hp
  have hp2 : p.2 = 384 := by simp at hp; rw [hp]
  rw [hcard, hp2]
  norm_num

theorem ivk93_m23 :
    Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .M23) := by
  refine ivk93_empty_of_small_centralizers ?_
  intro L _ _ hL y hy2 hy1
  obtain ⟨e⟩ := hL
  have e' : L ≃* NativeSporadic.M23 := e
  obtain ⟨p, hp, hcard⟩ := mathieu_card_cent_mem m23_innerRecordsValid e' hy2 hy1
  have hshape : recordShape m23Records = [(3795, 2688)] := rfl
  rw [hshape] at hp
  have hp2 : p.2 = 2688 := by simp at hp; rw [hp]
  rw [hcard, hp2]
  norm_num

end CFSG.GH74.GLS.IVK.Proofs2
