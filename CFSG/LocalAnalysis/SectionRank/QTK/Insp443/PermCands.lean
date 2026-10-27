module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermKit

public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

variable {n : ℕ}

theorem closure_map_tabPerm {bs : List Table} (hb : EBasis (permB n bs)) :
    Subgroup.closure {g | g ∈ bs.map (tabPerm n)} = eSub hb := by
  rw [eSub_eq_closure hb]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_range]
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, List.getElem_mem i.2, rfl⟩

theorem exists_index_of_mem_candPerms {cands : List (List Table)} {cg : List (Perm (Fin n))}
    (h : cg ∈ candPerms n cands) :
    ∃ k < cands.length, cg = (cands.getD k []).map (tabPerm n) := by
  unfold candPerms at h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk]⟩

theorem eq_eSub_of_map_eq_closure {H : Subgroup (Perm (Fin n))} {U : Subgroup H}
    {bs : List Table} (hb : EBasis (permB n bs))
    (h : U.map H.subtype = Subgroup.closure {g | g ∈ bs.map (tabPerm n)}) :
    ∃ hbH : ∀ i, permB n bs i ∈ H, U = eSub (liftB_basis hbH hb) := by
  rw [closure_map_tabPerm hb] at h
  have hbH : ∀ i, permB n bs i ∈ H := fun i => by
    have h1 : permB n bs i ∈ U.map H.subtype := by rw [h]; exact mem_eSub hb i
    obtain ⟨x, -, hx⟩ := h1
    rw [← hx]
    exact x.2
  refine ⟨hbH, Subgroup.map_injective H.subtype_injective ?_⟩
  rw [h, eSub_liftB_map hbH hb]

theorem eq_or_eq_of_le_of_card {G : Type*} [Group G] [Finite G] {U V W : Subgroup G}
    (hUV : U ≤ V) (hVW : V ≤ W) (hc : Nat.card W = 2 * Nat.card U) : V = U ∨ V = W := by
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hUV
  obtain ⟨b, hb⟩ := Subgroup.card_dvd_of_le hVW
  have hU0 : 0 < Nat.card U := Nat.card_pos
  have hab : a * b = 2 := by
    rw [hb, ha, mul_assoc] at hc
    have := Nat.eq_of_mul_eq_mul_left hU0 (hc.trans (mul_comm 2 _))
    linarith
  have ha2 : a ∣ 2 := ⟨b, hab.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp ha2 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hUV (by rw [ha, mul_one])).symm
  · right
    have hb1 : b = 1 := by omega
    exact Subgroup.eq_of_le_of_card_ge hVW (by rw [hb, hb1, mul_one])

end CFSG.SectionRank.QTK.Insp443.PermKit

end
