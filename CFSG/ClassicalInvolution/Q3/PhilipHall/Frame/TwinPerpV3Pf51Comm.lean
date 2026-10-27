module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnTransportLift

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped MatrixGroups

namespace Pf51Comm

theorem sl2_card_pow_four : Nat.card {g : SL(2, ZMod 3) // g ^ 4 = 1} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem sl2_centralizes_pow_four : ∀ c : SL(2, ZMod 3),
    (∀ g : SL(2, ZMod 3), g ^ 4 = 1 → c * g = g * c) → c = 1 ∨ (c ^ 2 = 1 ∧ c ≠ 1) := by
  decide +kernel

theorem sl2_involution_central : ∀ a b : SL(2, ZMod 3), a ^ 2 = 1 → b * a = a * b := by
  decide +kernel

theorem quaternion_pow_four : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by
  decide +kernel

theorem quaternion_card : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem mem_iff_pow_four {Y : Type} [Group Y] [Finite Y] {J L : Subgroup Y} (hJL : J ≤ L)
    (hq8 : Nonempty (↥J ≃* QuaternionGroup 2)) (e : ↥L ≃* SL(2, ZMod 3)) :
    ∀ g ∈ L, g ∈ J ↔ g ^ 4 = 1 := by
  obtain ⟨q⟩ := hq8
  have hJ4 : ∀ j : J, j ^ 4 = 1 := fun j => q.injective (by
    rw [map_pow, quaternion_pow_four, map_one])
  have hf : ∀ j : J, (Subgroup.inclusion hJL j) ^ 4 = 1 := fun j => by
    rw [← map_pow, hJ4, map_one]
  let f : J → {g : L // g ^ 4 = 1} := fun j => ⟨Subgroup.inclusion hJL j, hf j⟩
  have hfi : Function.Injective f := fun a b h =>
    (Subgroup.inclusion_injective hJL) (congrArg Subtype.val h)
  have key : ∀ g : L, (e g) ^ 4 = 1 ↔ g ^ 4 = 1 := fun g => by
    rw [← map_pow]
    exact e.map_eq_one_iff
  have hcard : Nat.card {g : L // g ^ 4 = 1} = Nat.card J := by
    rw [Nat.card_congr q.toEquiv, quaternion_card,
      Nat.card_congr (e.toEquiv.subtypeEquiv (p := fun g : L => g ^ 4 = 1)
        (q := fun g : SL(2, ZMod 3) => g ^ 4 = 1) (fun g => (key g).symm))]
    exact sl2_card_pow_four
  have hbij : Function.Bijective f :=
    hfi.bijective_of_nat_card_le (by rw [hcard])
  intro g hg
  constructor
  · intro hgJ
    have h2 := congrArg Subtype.val (hf ⟨g, hgJ⟩)
    simpa using h2
  · intro hg4
    have hg4' : (⟨g, hg⟩ : L) ^ 4 = 1 := Subtype.ext (by simpa using hg4)
    obtain ⟨j, hj⟩ := hbij.2 ⟨⟨g, hg⟩, hg4'⟩
    have h3 : (j : Y) = g := congrArg (fun z : {g : L // g ^ 4 = 1} => ((z.1 : L) : Y)) hj
    exact h3 ▸ j.2

end Pf51Comm

open Pf51Comm in
theorem centralizes_lift_of_centralizes {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}
    (hΩ : HypOmegaGen Ω) {J L : Subgroup Y} {t x : Y} (hJ : J ∈ Ω) (hz : IsUniqueInvolution J t)
    (hJ2 : IsPGroup 2 ↥J) (hq8 : Nonempty (↥J ≃* QuaternionGroup 2)) (hL : IsClassicalMember3 L t)
    (hJL : J ≤ L)
    (hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (hxt : x * t = t * x) (hxJ : ∀ j ∈ J, x * j = j * x) :
    ∀ l ∈ L, x * l = l * x := by
  classical
  have hOL : classicalInvolutionOddCore ↥L = ⊥ := by
    have h1 := Balance.oddCoreIn_le_of_isSubnormal hL.subnormal
    rw [TwinConnT.oddCoreIn_eq_bot_of_classicalOddCore hO, le_bot_iff] at h1
    exact TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn h1
  obtain ⟨e⟩ := hL.nonempty_equiv_sl2 hOL
  have hxt' : x * t * x⁻¹ = t := by rw [hxt]; group
  have hxL : conjSub x L = L := by
    have h1 := hL.conj x
    rw [hxt'] at h1
    refine TwinConnT.liftUnique_in hΩ hJ hz ?_ hJL h1 hL hO
    intro j hj
    have hj' : x * j * x⁻¹ = j := by rw [hxJ j hj]; group
    have h2 := conj_mem_conjSub (n := x) (hJL hj)
    rwa [hj'] at h2
  have hJeq := mem_iff_pow_four hJL hq8 e
  have hxl : ∀ l ∈ L, x * l * x⁻¹ ∈ L := fun l hl => hxL ▸ conj_mem_conjSub hl
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hL.orderOf_eq_two] at this
  have htL : (⟨t, hL.mem⟩ : L) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
  have hCt : ∀ c ∈ L, (∀ j ∈ J, c * j = j * c) → c = 1 ∨ c = t := by
    intro c hc hcJ
    have h := sl2_centralizes_pow_four (e ⟨c, hc⟩) (fun g hg4 => by
      have hg4' : (e.symm g) ^ 4 = 1 := by
        rw [← e.symm.map_one, ← map_pow]
        exact congrArg e.symm hg4
      have hmem := (hJeq _ (e.symm g).2).mpr (by simpa using congrArg Subtype.val hg4')
      have hcomm := hcJ _ hmem
      have hcomm' : (⟨c, hc⟩ : L) * e.symm g = e.symm g * ⟨c, hc⟩ := Subtype.ext hcomm
      have := congrArg e hcomm'
      simpa using this)
    rcases h with h | ⟨h2, h1⟩
    · left
      have := e.injective (h.trans e.map_one.symm)
      simpa using congrArg Subtype.val this
    · right
      have ht2 : (e ⟨t, hL.mem⟩) ^ 2 = 1 := by rw [← map_pow, htL, map_one]
      have ht1 : e ⟨t, hL.mem⟩ ≠ 1 := fun h' => hL.ne_one (by
        have := e.injective (h'.trans e.map_one.symm)
        simpa using congrArg Subtype.val this)
      have := Q3T.sl2_involution_unique _ _ h2 h1 ht2 ht1
      simpa using congrArg Subtype.val (e.injective this)
  have hle : L ≤ Subgroup.centralizer ({x} : Set Y) := by
    refine Q3T.le_of_forall_oddPrimePow_mem hL fun l hl p k hp hp2 hlp => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hl' := hxl l hl
    have hc : l⁻¹ * (y * l * y⁻¹) ∈ L := L.mul_mem (L.inv_mem hl) hl'
    have hcJ : ∀ j ∈ J, (l⁻¹ * (y * l * y⁻¹)) * j = j * (l⁻¹ * (y * l * y⁻¹)) := by
      intro j hj
      have hj1 : l * j * l⁻¹ ∈ J := by
        refine (hJeq _ (L.mul_mem (L.mul_mem hl (hJL hj)) (L.inv_mem hl))).mpr ?_
        have hj4 : j ^ 4 = 1 := by
          exact (hJeq j (hJL hj)).mp hj
        rw [conj_pow, hj4]
        group
      have h1 : y * j = j * y := hxJ j hj
      have h2 : y * (l * j * l⁻¹) = (l * j * l⁻¹) * y := hxJ _ hj1
      have hxj' : y⁻¹ * j = j * y⁻¹ := (Commute.inv_left (show Commute y j from h1)).eq
      calc l⁻¹ * (y * l * y⁻¹) * j = l⁻¹ * y * l * (y⁻¹ * j) := by group
        _ = l⁻¹ * y * (l * j * l⁻¹) * l * y⁻¹ := by rw [hxj']; group
        _ = l⁻¹ * (y * (l * j * l⁻¹)) * l * y⁻¹ := by group
        _ = l⁻¹ * ((l * j * l⁻¹) * y) * l * y⁻¹ := by rw [h2]
        _ = j * (l⁻¹ * (y * l * y⁻¹)) := by group
    rcases hCt _ hc hcJ with h | h
    · calc y * l = y * l * y⁻¹ * y := by group
        _ = l * y := by
          have : y * l * y⁻¹ = l := by
            have := congrArg (l * ·) h
            simpa using this
          rw [this]
    · exfalso
      have hl'eq : y * l * y⁻¹ = l * t := by
        have := congrArg (l * ·) h
        simpa using this
      have hcomm : t * l = l * t := by
        have h0 := sl2_involution_central (e ⟨t, hL.mem⟩) (e ⟨l, hl⟩) (by
          rw [← map_pow, htL, map_one])
        have h1 : (⟨l, hl⟩ : L) * ⟨t, hL.mem⟩ = ⟨t, hL.mem⟩ * ⟨l, hl⟩ :=
          e.injective (by rw [map_mul, map_mul]; exact h0)
        exact (congrArg Subtype.val h1).symm
      have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
      have htp : t ^ (p ^ k) = t := by
        obtain ⟨m, hm⟩ := hodd
        rw [hm, pow_succ, pow_mul, ht2, one_pow, one_mul]
      have h1 : (y * l * y⁻¹) ^ (p ^ k) = 1 := by
        rw [conj_pow, hlp]; group
      rw [hl'eq, Commute.mul_pow (show Commute l t from hcomm.symm), hlp, one_mul, htp] at h1
      exact hL.ne_one h1
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (hle hl)) x (Set.mem_singleton x)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
