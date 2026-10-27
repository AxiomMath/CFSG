module

public import CFSG.Sporadic.Recognition.PresentedWords
public import Certificates.Data.ChengHeldONRels

public section

namespace CFSG.OddStandard.ChengHeld.ONSylow

open CFSG.CosetTable CFSG.Sporadic.Recognition.PresentedWords

abbrev ONPres : Type := PG 8 onRels

theorem range_pgHom {G : Type*} [Group G] (x : Fin 8 → G) (hx : ∀ w ∈ onRels, wprod x w = 1) :
    (pgHom x hx).range = Subgroup.closure (Set.range x) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext i
  simp [pgHom_of]

theorem exists_mulEquiv_closure {G : Type*} [Group G] [Finite ONPres]
    (hP : Nat.card ONPres ≤ 512) (x : Fin 8 → G) (hx : ∀ w ∈ onRels, wprod x w = 1)
    (hc : 512 ≤ Nat.card (Subgroup.closure (Set.range x))) :
    Nonempty (ONPres ≃* Subgroup.closure (Set.range x)) := by
  have hr := range_pgHom x hx
  have hs : Function.Surjective (pgHom x hx).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have hle : Nat.card (pgHom x hx).range ≤ Nat.card ONPres := Nat.card_le_card_of_surjective _ hs
  rw [← hr] at hc
  have hb : Function.Bijective (pgHom x hx).rangeRestrict :=
    hs.bijective_of_nat_card_le (hP.trans hc)
  exact ⟨(MulEquiv.ofBijective _ hb).trans (MulEquiv.subgroupCongr hr)⟩

theorem range_eight {G : Type*} (t pi tau mu lam ze xi z : G) :
    Set.range ![t, pi, tau, mu, lam, ze, xi, z] = ({t, pi, tau, mu, lam, ze, xi, z} : Set G) := by
  ext g
  simp
  tauto

end CFSG.OddStandard.ChengHeld.ONSylow
