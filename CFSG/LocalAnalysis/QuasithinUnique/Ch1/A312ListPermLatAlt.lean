module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

open CFSG.QuasithinUnique.Unc25K1.Six

section Check

variable {G : Type} [Group G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R] {enc : G → R}

section Sound

variable [Finite G]

theorem LatCert.isSylowTwoOf_top (h : IsEnc enc) (c : LatCert G) (hc : c.check enc = true)
    {k m : ℕ} (hk : c.sizes.headD 0 = 2 ^ k) (hm : c.msize = 2 ^ k * m) (hodd : ¬ 2 ∣ m) :
    CFSG.QuasithinUnique.IsSylowTwoOf
      ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf (Subgroup.closure {g | g ∈ c.mGens}))
      (⊤ : Subgroup ↥(Subgroup.closure {g | g ∈ c.mGens})) := by
  simp only [LatCert.check, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hcl, hcov⟩, hreps⟩, hjoins⟩, hsz⟩, htle⟩ := hc
  have hTM := c.t_le_m h hcl htle
  have hT := c.card_t h hcl hsz
  have hM := c.card_m h hcl hsz
  have hU : Nat.card ↥((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ c.mGens})) = 2 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hT, hk]
  refine ⟨le_top, IsPGroup.of_card hU, ?_⟩
  have hidx := Subgroup.card_mul_index
    ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf (Subgroup.closure {g | g ∈ c.mGens}))
  rw [hU, hM, hm] at hidx
  have hidx' : ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ c.mGens})).index = m :=
    Nat.eq_of_mul_eq_mul_left (by positivity) hidx
  have e : (((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ c.mGens})).subgroupOf
        (⊤ : Subgroup ↥(Subgroup.closure {g | g ∈ c.mGens}))).index =
      ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
        (Subgroup.closure {g | g ∈ c.mGens})).index :=
    Subgroup.relIndex_top_right _
  rw [e, hidx']
  exact hodd

end Sound

theorem solvable_subgroupOf_two_three {G : Type*} [Group G] [Finite G] {L M : Subgroup G}
    (hLM : L ≤ M) {a b : ℕ} (hcard : Nat.card L = 2 ^ a * 3 ^ b) :
    Group.IsSolvable ↥(L.subgroupOf M) := by
  have : Nat.card ↥(L.subgroupOf M) = 2 ^ a * 3 ^ b := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcard]
  exact isSolvable_of_card_two_three this

end Check

end CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
