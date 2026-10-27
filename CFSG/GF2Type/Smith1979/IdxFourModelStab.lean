module

public import CFSG.GF2Type.Smith1979.IdxFourModelOrbit
public import CFSG.GF2Type.Smith1979.IdxFourModelOrder

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour.Orb

@[expose] def w0 : V12 := vecOf 3

@[expose] def a0V : V12 := vecOf 15

theorem inO378_w0 : inO378 w0 := by
  unfold inO378 w0
  rw [codeOf_vecOf (by norm_num)]
  decide +kernel

theorem inO1701_a0V : inO1701 a0V := by
  unfold inO1701 a0V
  rw [codeOf_vecOf (by norm_num)]
  decide +kernel

@[expose] def stabIn (H : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (v : V12) : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  H ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) v

theorem mem_stabIn {H : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {v : V12} {g : V12 ≃ₗ[ZMod 2] V12} :
    g ∈ stabIn H v ↔ g ∈ H ∧ g v = v := by
  simp [stabIn, MulAction.mem_stabilizer_iff]

theorem card_subgroupOf_eq {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card ↥(K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.card_map_of_injective H.subtype_injective (K := K.subgroupOf H),
    Subgroup.subgroupOf_map_subtype, inf_comm]

theorem card_stabIn_mul_ncard {H : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {v : V12} {S : Set V12}
    (hS : MulAction.orbit ↥H v = S) : Nat.card (stabIn H v) * S.ncard = Nat.card H := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥H v)
  rw [MulAction.index_stabilizer, hS, ← MulAction.stabilizer_subgroupOf,
    card_subgroupOf_eq] at h1
  exact h1

theorem orbit_eq_inO378 :
    MulAction.orbit ↥M0 w0 = {x | inO378 x} := by
  ext x
  constructor
  · rintro ⟨⟨U, hU⟩, rfl⟩
    exact inO378_invariant hU inO378_w0
  · intro hx
    obtain ⟨U, hU, hUx⟩ := inO378_trans inO378_w0 hx
    exact ⟨⟨U, hU⟩, hUx⟩

theorem orbit_eq_inO1701 :
    MulAction.orbit ↥M0 a0V = {x | inO1701 x} := by
  ext x
  constructor
  · rintro ⟨⟨U, hU⟩, rfl⟩
    exact inO1701_invariant hU inO1701_a0V
  · intro hx
    obtain ⟨U, hU, hUx⟩ := inO1701_trans inO1701_a0V hx
    exact ⟨⟨U, hU⟩, hUx⟩

theorem orbit_E0_eq_inO378 :
    MulAction.orbit ↥E0 w0 = {x | inO378 x} := by
  ext x
  constructor
  · rintro ⟨⟨U, hU⟩, rfl⟩
    exact inO378_invariant (E0_le_M0 hU) inO378_w0
  · intro hx
    obtain ⟨U, hU, hUx⟩ := inO378_trans_E0 inO378_w0 hx
    exact ⟨⟨U, hU⟩, hUx⟩

theorem ncard_inO378 : {x : V12 | inO378 x}.ncard = 378 := by
  rw [← Nat.card_coe_set_eq]
  exact card_inO378

theorem ncard_inO1701 : {x : V12 | inO1701 x}.ncard = 1701 := by
  rw [← Nat.card_coe_set_eq]
  exact card_inO1701

theorem card_stabIn_M0_w0 :
    Nat.card (stabIn M0 w0) = 103680 := by
  have h := card_stabIn_mul_ncard (H := M0) orbit_eq_inO378
  rw [ncard_inO378, card_M0] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 378) (h.trans (by norm_num))

theorem card_stabIn_E0_w0 :
    Nat.card (stabIn E0 w0) = 25920 := by
  have h := card_stabIn_mul_ncard (H := E0) orbit_E0_eq_inO378
  rw [ncard_inO378, card_E0] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 378) (h.trans (by norm_num))

theorem card_stabIn_M0_a0 :
    Nat.card (stabIn M0 a0V) = 23040 := by
  have h := card_stabIn_mul_ncard (H := M0) orbit_eq_inO1701
  rw [ncard_inO1701, card_M0] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1701) (h.trans (by norm_num))

end CFSG.GF2Type.Smith1979.IdxFour
