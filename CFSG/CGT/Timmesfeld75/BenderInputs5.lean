module

public import CFSG.CGT.Timmesfeld75.BenderWC
import CFSG.CGT.Timmesfeld75.BenderInputsBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.BenderSuzuki

private theorem isPGroup_two_zpowers_aux {K : Type*} [Group K] {b : K} (hb : b * b = 1) :
    IsPGroup 2 (Subgroup.zpowers b) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hb
  rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hb2]

theorem benderWCInput_of_repo : BenderWCInput := by
  intro K _ _ hK T hT _ g hg
  by_contra hne
  obtain ⟨⟨s, hs⟩, hs1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  have hsmem : s ∈ T ⊓ Subgroup.normalizer (conjSubgroup g T : Set K) := hs
  have hsT : s ∈ T := (Subgroup.mem_inf.1 hsmem).1
  have hsN : s ∈ Subgroup.normalizer (conjSubgroup g T : Set K) := (Subgroup.mem_inf.1 hsmem).2
  have hs2 : s * s = 1 := by rw [← pow_two]; exact hT.1.2 s hsT
  obtain ⟨Q, hTQ⟩ := (isPGroup_two_of_isElemAbelian hT.1).exists_le_sylow
  have hsQ : s ∈ Q := hTQ hsT
  have hTg : IsPGroup 2 (conjSubgroup g T) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hT.1 g)
  have hP : IsPGroup 2 (Subgroup.zpowers s ⊔ conjSubgroup g T : Subgroup K) :=
    (isPGroup_two_zpowers_aux hs2).to_sup_of_normal_right' hTg
      (Subgroup.zpowers_le.2 hsN)
  obtain ⟨Q', hPQ'⟩ := hP.exists_le_sylow
  have hsQ' : s ∈ Q' := hPQ' (Subgroup.mem_sup_left (Subgroup.mem_zpowers s))
  have hTgQ' : conjSubgroup g T ≤ (Q' : Subgroup K) := le_trans le_sup_right hPQ'
  have hQ'N : (Q' : Subgroup K) ≤ Subgroup.normalizer (Q : Set K) := fun y hy =>
    centralizer_le_normalizer_of_isBenderGroup hK Q hsQ hs2 hs1
      (Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q' hsQ'
          hs2 y hy)
  have hQ'Q : (Q' : Subgroup K) ≤ (Q : Subgroup K) :=
    le_of_isPGroup_of_le_normalizer Q'.isPGroup' Q hQ'N
  have hle : conjSubgroup g T ≤ Subgroup.centralizer ({s} : Set K) := fun y hy => by
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q hsQ hs2 y
      (hQ'Q (hTgQ' hy))
  exact hg ((hT.2 s hsT hs1).2 g hle)

end CFSG.CGT.Timmesfeld75
