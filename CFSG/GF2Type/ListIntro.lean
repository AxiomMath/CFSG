module

public import CFSG.RankThree.GF2n.Statements

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n

variable {G : Type} [Group G]

theorem gf2TypeList_of_psl {n : ℕ} (hn : 3 ≤ n) (h : LieModel G .PSL n 2 1) : GF2TypeList G :=
  Or.inl ⟨n, hn, h⟩

theorem gf2TypeList_of_psu {n : ℕ} (hn : 4 ≤ n) (h : LieModel G .PSU n 2 1) : GF2TypeList G :=
  Or.inr (Or.inl ⟨n, hn, h⟩)

theorem gf2TypeList_of_omegaPlus {n : ℕ} (hn : 4 ≤ n) (h : LieModel G .POmegaPlus n 2 1) :
    GF2TypeList G :=
  Or.inr (Or.inr (Or.inl ⟨.POmegaPlus, n, by simp, hn, h⟩))

theorem gf2TypeList_of_omegaMinus {n : ℕ} (hn : 4 ≤ n) (h : LieModel G .POmegaMinus n 2 1) :
    GF2TypeList G :=
  Or.inr (Or.inr (Or.inl ⟨.POmegaMinus, n, by simp, hn, h⟩))

theorem gf2TypeList_of_exceptional {s : StatedLieTag}
    (hs : s ∈ ({.trialityD4, .E6, .twistedE6, .E7, .E8} : Set StatedLieTag))
    (h : LieModel G s 0 2 1) : GF2TypeList G :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, h⟩)))

theorem gf2TypeList_of_psl_two {p f m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hm : 3 ≤ m)
    (hq : p ^ f = 2 ^ m - 1 ∨ p ^ f = 2 ^ m + 1) (h : LieModel G .PSL 2 p f) : GF2TypeList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, m, hp, hp2, hf, hm, hq, h⟩))))

theorem gf2TypeList_of_three {s : StatedLieTag} {n : ℕ}
    (hs : (s, n) ∈ ({(.PSL, 3), (.PSU, 3), (.PSL, 4), (.PSU, 4), (.G2, 0), (.POmegaPlus, 4)} :
      Set (StatedLieTag × ℕ))) (h : LieModel G s n 3 1) : GF2TypeList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, n, hs, h⟩)))))

theorem gf2TypeList_of_alternating {k : ℕ} (hk : k ∈ ({6, 8, 9} : Set ℕ))
    (h : Nonempty (G ≃* alternatingGroup (Fin k))) : GF2TypeList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, h⟩))))))

theorem gf2TypeList_of_sporadic {s : TauCeti.SporadicName}
    (hs : s ∈ ({.M11, .M12, .M24, .J2, .J3, .J4, .Co2, .Co1, .HS, .Suz, .He, .Fi24Prime, .HN, .Th,
      .B, .M} : Set TauCeti.SporadicName)) (h : NativeSporadic.IsSporadic G s) : GF2TypeList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hs, h⟩))))))

end CFSG.GF2Type
