module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Ord
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4M23

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.OddStandard
  CFSG.GH74.GLS.IVK

theorem ivk95_empty_of_perfect_centralizers {P : (X : Type) → [Group X] → Prop}
    (hperf : ∀ (L : Type) [Group L] [Finite L], P L → ∀ y : L, y * y = 1 → y ≠ 1 →
      Group.IsPerfect ↥(centralizer ({y} : Set L)) ∧
        (Nat.card ↥(centralizer ({y} : Set L)) = 1920 ∨
          Nat.card ↥(centralizer ({y} : Set L)) = 2688)) :
    Ivk95Empty P :=
  ivk95_empty_of_cfg fun J _ _ hJ z hz =>
    hz.false_of_perfect (hperf J hJ z hz.mul_self_eq_one hz.ne_one).1
      (hperf J hJ z hz.mul_self_eq_one hz.ne_one).2

theorem mathieu_inv_card_mem {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {recs : List (InnerClassRecord n)} (hvalid : InnerClassRecordsValid G recs) :
    ∀ u ∈ G, orderOf u = 2 → ∃ p ∈ recordShape recs, Nat.card (centralizerIn G u) = p.2 := by
  obtain ⟨hrecs, -, hcover⟩ := hvalid
  intro u hu hu2
  obtain ⟨r, hr, hur⟩ := hcover u hu hu2
  refine ⟨(r.classSize, r.centralizerOrder), List.mem_map_of_mem hr, ?_⟩
  rw [GHInv.card_centralizerIn_eq_of_mem_conjClass G hur]
  exact (hrecs r hr).2.2.2.1

theorem ivk95_m11 :
    Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .M11) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.M11 := e
  obtain ⟨p, hp, hcard⟩ := mathieu_inv_card_mem m11_innerRecordsValid
    ((e' z : NativeSporadic.M11) : Equiv.Perm (Fin 11)) (e' z).2
    (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hz.ord)
  have hshape : recordShape m11Records = [(165, 48)] := rfl
  rw [hshape] at hp
  have hp2 : p.2 = 48 := by simp at hp; rw [hp]
  have hC : Nat.card ↥(centralizer ({z} : Set J)) = 48 := by
    rw [GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M11 e' z, hcard, hp2]
  exact hz.false_of_card_cent_dvd (N := 48) (by rw [hC])
    (fun q hq => not_sl2_dvd_of_lt (by norm_num) (by norm_num) q hq)

theorem ivk95_m22 :
    Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .M22) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.M22 := e
  obtain ⟨p, hp, hcard⟩ := mathieu_inv_card_mem m22_innerRecordsValid
    ((e' z : NativeSporadic.M22) : Equiv.Perm (Fin 22)) (e' z).2
    (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hz.ord)
  have hshape : recordShape m22Records = [(1155, 384)] := rfl
  rw [hshape] at hp
  have hp2 : p.2 = 384 := by simp at hp; rw [hp]
  have hC : Nat.card ↥(centralizer ({z} : Set J)) = 384 := by
    rw [GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M22 e' z, hcard, hp2]
  exact hz.false_of_card_cent_dvd (N := 384) (by rw [hC]) (fun q hq => not_sl2_dvd_384 q hq)

theorem ivk95_m23 :
    Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .M23) := by
  refine ivk95_empty_of_perfect_centralizers ?_
  intro L _ _ hL y hy2 hy1
  obtain ⟨e⟩ := hL
  have e' : L ≃* NativeSporadic.M23 := e
  have hord : orderOf ((e' y : NativeSporadic.M23) : Equiv.Perm (Fin 23)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨hperf, hcard⟩ := m23_inv_centralizer_data _ (e' y).2 hord
  refine ⟨GHInv.isPerfect_centralizer_of_equiv NativeSporadic.M23 e' y hperf, Or.inr ?_⟩
  rw [GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M23 e' y]
  exact hcard

end CFSG.GH74.GLS.IVK.Proofs2
