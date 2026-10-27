module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBFixS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBSetup

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace BCtx_F4

variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx_F4 T M L V g D)

include c in
theorem card_inf_centralizer_le_four {u : G} (hu : u ∈ Subgroup.normalizer (V : Set G))
    (hu2 : u * u = 1) (hu1 : u ∉ Subgroup.centralizer (V : Set G)) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := c.h.toHyp611.isElemAbelian
  have hA : IsElemAbelian 2 (Subgroup.zpowers u) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : u ^ (↑(2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_two]; exact hu2
    rw [this, one_zpow]
  have hAN : Subgroup.zpowers u ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr hu
  have hAM : Subgroup.zpowers u ≤ M := hAN.trans (c.hl.h621 G T M L V c.h).2
  have hle : autI hV (Subgroup.zpowers u) ≤ autI hV M := autI_mono hV hAM
  have hne : autI hV (Subgroup.zpowers u) ≠ ⊥ :=
    fun h => hu1 ((autI_eq_bot_iff hV hAN).mp h (Subgroup.mem_zpowers u))
  have hp : IsPGroup 2 (autI hV (Subgroup.zpowers u)) :=
    isPGroup_of_isElemAbelian2 (isElemAbelian2_autI hV hA hAN)
  have h1 := mParam_le_rkIdx_fixV hle hp hne
  have h2 : mParam (autI hV M) = 2 := ((c.hl.h6110 G T M L V 2 c.h.toHyp611Nat).2.1 hV).2
  rw [h2] at h1
  have hFcard : Nat.card (fixV (autI hV (Subgroup.zpowers u))) =
      Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) := by
    rw [card_fixV_autI hV hAN, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hidx := Subgroup.index_mul_card (fixV (autI hV (Subgroup.zpowers u)))
  have hV16 : Nat.card (IntMod V hV) = 16 := KData.card_V c.h
  rw [hV16, hFcard] at hidx
  have hne0 : (fixV (autI hV (Subgroup.zpowers u))).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : 2 ^ 2 ∣ (fixV (autI hV (Subgroup.zpowers u))).index :=
    (padicValNat_dvd_iff_le hne0).mpr h1
  have h5 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) h4
  have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) := Nat.card_pos
  generalize (fixV (autI hV (Subgroup.zpowers u))).index = i at *
  generalize Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) = n at *
  nlinarith

include c in
theorem exists_comm_of_involution {u : G} (hu : u ∈ Subgroup.normalizer (V : Set G))
    (hu2 : u * u = 1) (hu1 : u ∉ Subgroup.centralizer (V : Set G)) :
    ∀ x ∈ V ⊓ Subgroup.centralizer ({u} : Set G), ∃ v ∈ V, x = v * u * v⁻¹ * u⁻¹ := by
  refine exists_comm_of_card_le_F4 c.h.toHyp611.isElemAbelian hu hu2 ?_
  have h4 := c.card_inf_centralizer_le_four hu hu2 hu1
  rw [KData.card_V c.h]
  nlinarith

end BCtx_F4

end CFSG.Quasithin.H13.GM22
