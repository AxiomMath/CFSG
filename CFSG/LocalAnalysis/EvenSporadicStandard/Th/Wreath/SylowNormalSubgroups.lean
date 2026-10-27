module

public import CFSG.GroupTheory.PGroupNormalCommutator
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowBoundsCount

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L S A B Aa : Subgroup G} {z b : G}

omit [Finite G] in
private theorem map_conj_inv_le_and_normal {h : G} {S Y : Subgroup G}
    (hYS : Y ≤ S.map (MulAut.conj h).toMonoidHom)
    (hYn : ∀ s ∈ S.map (MulAut.conj h).toMonoidHom, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    (Y.map (MulAut.conj h⁻¹).toMonoidHom ≤ S) ∧
      (∀ s ∈ S, ∀ y ∈ Y.map (MulAut.conj h⁻¹).toMonoidHom,
        s * y * s⁻¹ ∈ Y.map (MulAut.conj h⁻¹).toMonoidHom) := by
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hYS hy
    have hEq : (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom s) = s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rwa [hEq]
  · intro s hs y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hs' : (MulAut.conj h).toMonoidHom s ∈ S.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hs
    have hc := hYn ((MulAut.conj h).toMonoidHom s) hs' y₀ hy₀
    refine ⟨(MulAut.conj h).toMonoidHom s * y₀ * ((MulAut.conj h).toMonoidHom s)⁻¹, hc, ?_⟩
    have hEq : (MulAut.conj h⁻¹).toMonoidHom
        ((MulAut.conj h).toMonoidHom s * y₀ * ((MulAut.conj h).toMonoidHom s)⁻¹)
        = s * (MulAut.conj h⁻¹).toMonoidHom y₀ * s⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rwa [hEq]

omit [Finite G] in
private theorem map_conj_inf_centralizer (h : G) (S Y : Subgroup G) :
    (S.map (MulAut.conj h).toMonoidHom ⊓ centralizer (Y : Set G)).map
        (MulAut.conj h⁻¹).toMonoidHom
      = S ⊓ centralizer (Y.map (MulAut.conj h⁻¹).toMonoidHom : Set G) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hz.1
    refine ⟨?_, ?_⟩
    · have hEq : (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom s) = s := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      rwa [hEq]
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro y hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      have hc : y₀ * (MulAut.conj h).toMonoidHom s = (MulAut.conj h).toMonoidHom s * y₀ :=
        Subgroup.mem_centralizer_iff.1 hz.2 y₀ hy₀
      have hc' : y₀ * (h * s * h⁻¹) = (h * s * h⁻¹) * y₀ := by
        simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hc
      have hEq : (MulAut.conj h⁻¹).toMonoidHom y₀ *
            (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom s)
          = (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom s) *
            (MulAut.conj h⁻¹).toMonoidHom y₀ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        calc h⁻¹ * y₀ * h * (h⁻¹ * (h * s * h⁻¹) * h)
            = h⁻¹ * (y₀ * (h * s * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * s * h⁻¹) * y₀) * h := by rw [hc']
          _ = h⁻¹ * (h * s * h⁻¹) * h * (h⁻¹ * y₀ * h) := by group
      exact hEq
  · intro hx
    refine ⟨(MulAut.conj h).toMonoidHom x, ⟨?_, ?_⟩, ?_⟩
    · exact ⟨x, hx.1, rfl⟩
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro y hy
      have hy' : (MulAut.conj h⁻¹).toMonoidHom y ∈ Y.map (MulAut.conj h⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy
      have hc : (MulAut.conj h⁻¹).toMonoidHom y * x = x * (MulAut.conj h⁻¹).toMonoidHom y :=
        Subgroup.mem_centralizer_iff.1 hx.2 ((MulAut.conj h⁻¹).toMonoidHom y) hy'
      have hc' : (h⁻¹ * y * h) * x = x * (h⁻¹ * y * h) := by
        simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hc
      have hEq : y * (MulAut.conj h).toMonoidHom x = (MulAut.conj h).toMonoidHom x * y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        calc y * (h * x * h⁻¹) = h * ((h⁻¹ * y * h) * x) * h⁻¹ := by group
          _ = h * (x * (h⁻¹ * y * h)) * h⁻¹ := by rw [hc']
          _ = (h * x * h⁻¹) * y := by group
      exact hEq
    · have hEq : (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom x) = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      rwa [hEq]

theorem ThLocalIn.A_le_of_normal (W : ThLocalIn L S A B z) {Y : Subgroup G} (hYS : Y ≤ S)
    (hYn : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) (hY : 16 ≤ Nat.card Y) : A ≤ Y := by
  obtain ⟨Y₀, hY₀Y, hY₀card, hY₀n⟩ :=
    CFSG.GroupTheory.exists_le_normal_card_eq (p := 2) W.pgroup hYS hYn (k := 4)
      (by simpa using hY)
  have hY₀S : Y₀ ≤ S := hY₀Y.trans hYS
  have hY₀A : Y₀ ≤ A := by
    intro y hy
    rw [W.mem_A_iff]
    refine ⟨hY₀S hy, ?_⟩
    intro s₁ h₁ s₂ h₂ s₃ h₃ s₄ h₄
    exact CFSG.GroupTheory.commutator_four_eq_one_of_card_le W.pgroup hY₀S hY₀n
      (by rw [hY₀card]) y hy s₁ h₁ s₂ h₂ s₃ h₃ s₄ h₄
  have hAeq : Y₀ = A :=
    Subgroup.eq_of_le_of_card_ge hY₀A (by rw [W.A_card, hY₀card]; norm_num)
  rwa [← hAeq]

theorem ThLocalIn.inf_centralizer_le_B_of_normal (W : ThLocalIn L S A B z) {Y : Subgroup G}
    (hYS : Y ≤ S) (hYn : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) (hY : 16 ≤ Nat.card Y) :
    S ⊓ centralizer (Y : Set G) ≤ B := by
  have hAY : A ≤ Y := W.A_le_of_normal hYS hYn hY
  intro x hx
  exact (W.mem_B_iff x (W.S_le hx.1)).2 fun a ha =>
    ((mem_centralizer_iff.1 hx.2) a (hAY ha)).symm

theorem ThLocalIn.card_inf_centralizer_le_of_normal (W : ThLocalIn L S A B z) {Y : Subgroup G}
    (hYS : Y ≤ S) (hYn : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) (hY : 16 ≤ Nat.card Y) :
    Nat.card ↥(S ⊓ centralizer (Y : Set G)) ≤ 2 ^ 9 :=
  (Subgroup.card_le_of_le (W.inf_centralizer_le_B_of_normal hYS hYn hY)).trans_eq W.B_card

theorem ThLocalIn.card_inf_centralizer_le_of_normal_map (W : ThLocalIn L S A B z) (h : G)
    {Y : Subgroup G} (hYS : Y ≤ S.map (MulAut.conj h).toMonoidHom)
    (hYn : ∀ s ∈ S.map (MulAut.conj h).toMonoidHom, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y)
    (hY : 16 ≤ Nat.card Y) :
    Nat.card ↥(S.map (MulAut.conj h).toMonoidHom ⊓ centralizer (Y : Set G)) ≤ 2 ^ 9 := by
  let Y' : Subgroup G := Y.map (MulAut.conj h⁻¹).toMonoidHom
  obtain ⟨hY'S, hY'n⟩ := map_conj_inv_le_and_normal hYS hYn
  have hY' : 16 ≤ Nat.card Y' := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
    exact hY
  have hmap := map_conj_inf_centralizer (h := h) (S := S) (Y := Y)
  calc Nat.card ↥(S.map (MulAut.conj h).toMonoidHom ⊓ centralizer (Y : Set G))
      = Nat.card ↥((S.map (MulAut.conj h).toMonoidHom ⊓ centralizer (Y : Set G)).map
          (MulAut.conj h⁻¹).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).symm
    _ = Nat.card ↥(S ⊓ centralizer (Y' : Set G)) := by rw [hmap]
    _ ≤ 2 ^ 9 := W.card_inf_centralizer_le_of_normal hY'S hY'n hY'

theorem ThLocalIn2.card_le_of_normal_elementary (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    {Y : Subgroup G} (hYS : Y ≤ S) (hYn : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) (hY : 16 ≤ Nat.card Y)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) (hsq : ∀ y ∈ Y, y ^ 2 = 1) :
    Y ≤ B ∧ Nat.card Y ≤ 32 := by
  have hAY : A ≤ Y := W.A_le_of_normal hYS hYn hY
  have hYB : Y ≤ B := by
    intro y hy
    exact (W.mem_B_iff y (W.S_le (hYS hy))).2 fun a ha => hcomm y hy a (hAY ha)
  constructor
  · exact hYB
  · have hYinfB : Y ⊓ B = Y := inf_of_le_left hYB
    have hle := W2.card_inf_B_le W Y
    rw [hYinfB] at hle
    have hK : Y ⊓ Aa ≤ A := W2.inf_Aa_le_A_of_sq W hsq
    have hKcard : Nat.card ↥(Y ⊓ Aa) ≤ 16 :=
      (Subgroup.card_le_of_le hK).trans_eq W.A_card
    calc Nat.card Y ≤ 2 * Nat.card ↥(Y ⊓ Aa) := hle
      _ ≤ 2 * 16 := Nat.mul_le_mul_left 2 hKcard
      _ = 32 := by norm_num

theorem ThLocalIn2.card_le_of_normal_elementary_map (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (h : G) {Y : Subgroup G}
    (hYS : Y ≤ S.map (MulAut.conj h).toMonoidHom)
    (hYn : ∀ s ∈ S.map (MulAut.conj h).toMonoidHom, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) (hY : 16 ≤ Nat.card Y)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) (hsq : ∀ y ∈ Y, y ^ 2 = 1) : Nat.card Y ≤ 32 := by
  let Y' : Subgroup G := Y.map (MulAut.conj h⁻¹).toMonoidHom
  obtain ⟨hY'S, hY'n⟩ := map_conj_inv_le_and_normal hYS hYn
  have hY' : 16 ≤ Nat.card Y' := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
    exact hY
  have hcomm' : ∀ x ∈ Y', ∀ y ∈ Y', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hEq : (MulAut.conj h⁻¹).toMonoidHom x * (MulAut.conj h⁻¹).toMonoidHom y
        = (MulAut.conj h⁻¹).toMonoidHom y * (MulAut.conj h⁻¹).toMonoidHom x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc h⁻¹ * x * h * (h⁻¹ * y * h) = h⁻¹ * (x * y) * h := by group
        _ = h⁻¹ * (y * x) * h := by rw [hcomm x hx y hy]
        _ = h⁻¹ * y * h * (h⁻¹ * x * h) := by group
    exact hEq
  have hsq' : ∀ y ∈ Y', y ^ 2 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hEq : (MulAut.conj h⁻¹).toMonoidHom y * (MulAut.conj h⁻¹).toMonoidHom y = 1 := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc h⁻¹ * y * h * (h⁻¹ * y * h) = h⁻¹ * (y * y) * h := by group
        _ = h⁻¹ * y ^ 2 * h := by rw [pow_two]
        _ = 1 := by rw [hsq y hy]; group
    simpa [sq] using hEq
  have hres := (W2.card_le_of_normal_elementary W hY'S hY'n hY' hcomm' hsq').2
  rwa [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective] at hres

end CFSG.EvenSporadicStandard.ThStd
