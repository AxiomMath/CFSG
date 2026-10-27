module

public import CFSG.CGT.Timmesfeld75.Sec66Loc
public import CFSG.CGT.Timmesfeld75.Sec66Count

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} {m : ℕ}

theorem Sec6Ctx.sec66_loc_card (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ 3 m)
    {y g : G} (hyD : y ∈ classD T) (hyy : y * y = 1) (hS3 : Sec3 T (conjSubgroup y T))
    (hg : g ∈ T ⊔ conjSubgroup y T)
    (hfix : conjSubgroup y (conjSubgroup g T) = conjSubgroup g T)
    (hyS : y ∉ conjSubgroup g T) :
    Nat.card ↥(conjSubgroup g T ⊓ Subgroup.centralizer ({y} : Set G)) = (2 ^ m) ^ 2 ∧
      Nat.card ↥(conjSubgroup g T ⊓ cfgM T (conjSubgroup y T) ⊓
        Subgroup.centralizer ({y} : Set G)) ≤ 2 ^ m := by
  have hyN : y ∈ Subgroup.normalizer ((conjSubgroup g T : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSubgroup_eq.2 hfix
  have hLq : Nat.card ↥(normIn T T₁) = (2 ^ m) ^ 2 := by
    rw [hc.card_normIn]
  have hCU : Nat.card ↥(conjSubgroup g T ⊓ Subgroup.centralizer ({y} : Set G)) =
      (2 ^ m) ^ 2 := by
    rcases hc.card_centralizer_conj h63 hyD hyN hyS with h | ⟨h16, -, -⟩
    · rw [h, hLq]
    · exact absurd h16 hc.card_ne_sixteen_three
  refine ⟨hCU, ?_⟩
  have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact hyy
  have hUab : IsElemAbelian 2 (conjSubgroup g T) :=
    isElemAbelian_conjSubgroup hc.hy.pair.wc.1 g
  have h23 := card_commSub_mul_card_centralizer hUab hy2 hyN
  rw [card_conjSubgroup, hCU, hc.hT] at h23
  have hcomm : Nat.card ↥(commSub y (conjSubgroup g T)) = 2 ^ m := by
    have hpos : 0 < (2 ^ m) ^ 2 := by positivity
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h23]
    ring
  obtain ⟨-, hB⟩ := hc.card_normIn_le_sq_aux h62 h63 hyD hyy hS3 hg hfix hyS
  rw [← hcomm]
  exact Subgroup.card_le_of_le hB

end CFSG.CGT.Timmesfeld75
