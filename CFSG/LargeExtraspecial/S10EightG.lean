module

public import CFSG.LargeExtraspecial.S10EightF
public import CFSG.LargeExtraspecial.S10EightE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace DirDec

variable {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb)
include D

theorem pi_spec (hCE : CentralExtInput.{u}) {X : Hyp10 S g t} {F : Frame X}
    (hFY : (D.piY F).range = Γ₂) {d : S.O} (hd : d ∈ ⁅Yb, Yb⁆) (hd1 : d ≠ 1) :
    (F.π ⟨d, D.le_Rbar_right ((D.mem_commutator_iff).mp hd).1⟩).1 = 1 ∧
      F.π ⟨d, D.le_Rbar_right ((D.mem_commutator_iff).mp hd).1⟩ ^ 3 = 1 ∧
      F.π ⟨d, D.le_Rbar_right ((D.mem_commutator_iff).mp hd).1⟩ ≠ 1 := by
  have hdY := ((D.mem_commutator_iff).mp hd).1
  have hd3 := ((D.mem_commutator_iff).mp hd).2
  refine ⟨mem_Γ₂.mp (hFY ▸ ⟨⟨d, hdY⟩, rfl⟩), ?_, fun h => hd1 ?_⟩
  · rw [← map_pow]
    have : (⟨d, D.le_Rbar_right hdY⟩ : Rbar S g t) ^ 3 = 1 := Subtype.ext hd3
    rw [this, map_one]
  · have := D.piY_injective hCE F (a₁ := ⟨d, hdY⟩) (a₂ := 1)
      (by rw [DirDec.piY_apply, map_one]; exact h)
    exact congrArg Subtype.val this

end DirDec

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem timmesfeld_10_8_one (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {τ : S.O}
    (hτ : τ ∈ S.Lbar g ⊓ Xb) (hτ1 : τ ≠ 1) :
    (Rbar S g τ = (S.Lbar g ⊓ Xb) ⊔ Yb ∨ Hyp10 S g τ) ∧ IsOp 3 (Rbar S g τ) ⁅Yb, Yb⁆ := by
  rcases D.Rbar_eq_or_hyp10 hCE hP hτ hτ1 with ⟨-, h, -⟩ | Y
  · exact ⟨Or.inl h, h ▸ D.isOp_sup⟩
  · obtain ⟨Xτ, Yτ, Dτ, heq⟩ := D.exists_dirDec_of_hyp10 hCE hτ Y
    exact ⟨Or.inr Y, heq ▸ Dτ.isOp_commutator hCE Y⟩

theorem mem_Xb_of_commute (hCE : CentralExtInput.{u}) {d : S.O} (hd : d ∈ ⁅Yb, Yb⁆)
    (hd1 : d ≠ 1) {l : S.O} (hl : l ∈ S.Lbar g) (hc : l * d = d * l) : l ∈ Xb := by
  obtain ⟨F, hFY, hFX, -⟩ := D.exists_frame hCE
  obtain ⟨hπd1, hπd3, hπdne⟩ := D.dec.pi_spec hCE hFY hd hd1
  have hlR := Lbar_le_Rbar X.ht hl
  rw [hFX]
  refine (F.mem_pre).mpr ⟨hlR, mem_Γ₁.mpr ?_⟩
  by_contra h2
  apply not_comm_of_stab _ _ (F.π_mem_stabA hl) h2 hπd1 hπd3 hπdne
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hc

theorem map_commutator_eq (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {k : S.M} {τ : S.O}
    (hτ : τ ∈ S.Lbar g ⊓ Xb) (hτ1 : τ ≠ 1) (hτk : τ ∈ (S.Lbar g ⊓ Xb).map (cK S k)) :
    ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆ := by
  rw [mem_map_cK_iff] at hτk
  set σ := (S.ρ k)⁻¹ * τ * S.ρ k with hσ
  have hσ1 : σ ≠ 1 := fun h => hτ1 (by
    calc τ = S.ρ k * σ * (S.ρ k)⁻¹ := by rw [hσ]; group
      _ = 1 := by rw [h]; group)
  have hτσ : τ = S.ρ k * σ * (S.ρ k)⁻¹ := by rw [hσ]; group
  have h1 := (D.timmesfeld_10_8_one hCE hP hτk hσ1).2.map_conj (S.ρ k)
  have h2 := (D.timmesfeld_10_8_one hCE hP hτ hτ1).2
  have hR : Rbar S g τ = (Rbar S g σ).map (cK S k) := by rw [hτσ]; exact Rbar_conj k σ
  rw [← hR] at h1
  exact h1.eq h2

theorem timmesfeld_10_8_two (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {k : S.M}
    (hle : (S.Lbar g ⊓ Xb).map (cK S k) ≤ S.Lbar g) :
    (S.Lbar g ⊓ Xb).map (cK S k) = S.Lbar g ⊓ Xb := by
  set E := S.Lbar g ⊓ Xb with hE
  set E' := E.map (cK S k) with hE'
  have hcard : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective (cK_injective k)
  have hEN : E ≤ normalizer (E' : Set S.O) := by
    intro e he
    rw [mem_normalizer_iff]
    intro x
    have hc : ∀ {x : S.O}, x ∈ S.Lbar g → e * x * e⁻¹ = x := fun {x} hx => by
      rw [S4.Lbar_comm S X.haQ he.1 hx, mul_inv_cancel_right]
    constructor
    · intro hx
      rw [hc (hle hx)]
      exact hx
    · intro hx
      have h1 : x ∈ S.Lbar g := by
        have := hle hx
        have e1 : e⁻¹ * (e * x * e⁻¹) * e = x := by group
        rw [← e1]
        exact mul_mem (mul_mem (inv_mem he.1) this) he.1
      rw [hc h1] at hx
      exact hx
  have h1 := card_sup_mul_card_inf hEN
  have h2 : Nat.card (E ⊔ E' : Subgroup S.O) ≤ Nat.card (S.Lbar g) :=
    Subgroup.card_le_of_le (sup_le inf_le_left hle)
  have h3 := D.two_mul_card_Ebar hCE
  have h4 : 2 ≤ Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
    have := Subgroup.card_le_of_le ((zpowers_le).mpr X.t_mem_Abar)
    rwa [Nat.card_zpowers, X.orderOf_t] at this
  have h5 := X.card_Lbar_eq
  have hpos : 0 < Nat.card E := Nat.card_pos
  have h6 : 2 ≤ Nat.card (E ⊓ E' : Subgroup S.O) := by
    rw [hcard] at h1
    nlinarith
  obtain ⟨⟨τ, hτ⟩, hτ1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot (E ⊓ E')).mp (by omega))
  have hτ1 : τ ≠ 1 := fun h => hτ1' (Subtype.ext h)
  have hY := D.map_commutator_eq hCE hP hτ.1 hτ1 hτ.2
  obtain ⟨⟨d, hdY'⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp D.dec.commutator_ne_bot
  have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
  have hle' : E' ≤ E := by
    intro x hx
    refine ⟨hle hx, D.mem_Xb_of_commute hCE hdY' hd1 (hle hx) ?_⟩
    have hdk : d ∈ ⁅Yb, Yb⁆.map (cK S k) := by rw [hY]; exact hdY'
    rw [mem_map_cK_iff] at hx hdk
    have hc := D.dec.comm _ hx.2 _ ((D.dec.mem_commutator_iff).mp hdk).1
    calc x * d = S.ρ k * (((S.ρ k)⁻¹ * x * S.ρ k) * ((S.ρ k)⁻¹ * d * S.ρ k)) *
          (S.ρ k)⁻¹ := by group
      _ = S.ρ k * (((S.ρ k)⁻¹ * d * S.ρ k) * ((S.ρ k)⁻¹ * x * S.ρ k)) * (S.ρ k)⁻¹ := by
          rw [hc]
      _ = d * x := by group
  exact Subgroup.eq_of_le_of_card_ge hle' hcard.symm.le

end Dec108

end CFSG.LargeExtraspecial.S10
