module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartCQ

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup PartC

theorem card_Hz_eq {G : Type} [Group G] [Finite G] (z : G) :
    Nat.card ↥(Hz z) = Nat.card (Qbar z) * Nat.card ↥(Fz z) := by
  have hFH : Fz z ≤ Hz z := Subgroup.map_subtype_le _
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Fz z).subgroupOf (Hz z))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFH).toEquiv] at h
  exact h

theorem two_pow_nine_dvd_card_Hz {G : Type} [Group G] [Finite G] {z : G} {Z A : Subgroup G}
    (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) (hAut : AutStmt)
    (hset : HSSetting G z) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ Hz z) {V : Subgroup G}
    (hV : HSV z (T : Subgroup G) V) : 2 ^ 9 ∣ Nat.card ↥(Hz z) := by
  have hC : 64 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G)) := by
    rw [← hV.card_W]
    exact Subgroup.card_dvd_of_le (W_le_centralizer hD hz hF2 hV)
  have hGN : 168 * 64 ∣ Nat.card G := by
    refine dvd_trans (Nat.mul_dvd_mul_left 168 hC) ?_
    rw [← (hAut hset hV).2.1]
    exact Subgroup.card_subgroup_dvd_card _
  have h9 : 9 ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
      (dvd_trans (by norm_num) hGN)
  have hT : 2 ^ 9 ∣ Nat.card ↥(T : Subgroup G) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Sylow.card_eq_multiplicity T]
    exact pow_dvd_pow 2 h9
  exact dvd_trans hT (Subgroup.card_dvd_of_le hTH)

theorem hsPartC_of_inputs (hEmb : EmbedStmt) (hAut : AutStmt) (hBL : BurnsideStmt)
    (hSix : SixStmt) : HSPartC := by
  intro G _ _ z hset hti hwide
  obtain ⟨T, hTH, hE, hW⟩ := hwide
  have hV := hBL hset hti T hTH hE hW
  obtain ⟨ι, hι, hO2, a, ha, hP1, hK4⟩ := hsQ_hypotheses hEmb hAut hset hti hV
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset'
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  rcases hSix ι hι hO2 a ha hP1 hK4 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exfalso
    have hQ : Nat.card (Qbar z) = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    have hF : Nat.card ↥(Fz z) = 64 := by
      rw [Width.card_Fz hD hz]
      norm_num
    have h9 := two_pow_nine_dvd_card_Hz hD hz hF2 hAut hset T hTH hV
    rw [card_Hz_eq, hQ, hF] at h9
    exact absurd h9 (by norm_num)
  · refine ⟨e.toMonoidHom.comp (qmk z), e.surjective.comp (qmk_surjective z), ?_⟩
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, qmk_eq_one_iff, Subgroup.mem_subgroupOf]

end CFSG.GF2Type.Aschbacher1976Full.HS
