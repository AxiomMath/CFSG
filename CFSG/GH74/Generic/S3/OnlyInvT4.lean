module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.S3.OnlyInvT1

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

section Orders

variable {L : Type} [Group L] [Finite L] {A : Subgroup L} {K₀ : Type} [Group K₀]
  {p f : ℕ}

theorem IsL3Cover.sixteen_dvd_card_sub (hc : IsL3Cover ↥A K₀ p f) : 16 ∣ Nat.card L :=
  hc.sixteen_dvd.trans (hc.card_dvd.trans (Subgroup.card_subgroup_dvd_card A))

theorem l3Cover_false_of_ree
    (hc : IsL3Cover ↥A K₀ p f) {f₀ : ℕ}
    (h : LieModel L .twistedG2 0 3 f₀) : False := by
  obtain ⟨k, -, hk⟩ := card_of_lieModel_twistedG2 h
  have := hc.sixteen_dvd_card_sub
  rw [hk] at this
  exact not_sixteen_dvd_ordRee k this

theorem l3Cover_false_of_J1 (hc : IsL3Cover ↥A K₀ p f)
    (h : NativeSporadic.IsSporadic L .J1) : False := by
  have h16 := hc.sixteen_dvd_card_sub
  rw [card_of_isSporadic_J1 h] at h16
  norm_num at h16

theorem l3Cover_lt_of_proper (hA : A ≠ ⊤) (hc : IsL3Cover ↥A K₀ p f) {tL : StatedLieTag}
    {p' f' : ℕ} (htL : tL = .PSL ∨ tL = .PSU) (hp' : p'.Prime) (hp2' : p' ≠ 2)
    (hq' : 5 ≤ p' ^ f') (hL : LieModel L tL 3 p' f') : p ^ f < p' ^ f' := by
  by_contra hcon
  have hle : p' ^ f' ≤ p ^ f := by omega
  obtain ⟨t, ht, hK⟩ := hc.model
  have hlt := card_lt_four_mul ht htL hc.ne_two hc.big hp' hp2' hq' hle hK hL
  have h1 : Nat.card K₀ ≤ Nat.card A := hc.card_le
  have hs : IsSimpleGroup L := by
    rcases htL with rfl | rfl
    · exact isSimpleGroup_of_lieModel_L3' (Or.inl hL)
    · exact isSimpleGroup_of_lieModel_L3' (Or.inr hL)
  have h6 := card_le_six_of_lt_four_mul hs hA (by omega)
  have h124 := (l3_card_bounds htL hp' hp2' hq' hL).1
  omega

end Orders

end CFSG.GH74.Generic.S3
