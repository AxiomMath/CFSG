module

import CFSG.CGT.Foote82.Lemma61
public import CFSG.CGT.Foote82.T66.CaseIIDim
public import CFSG.CGT.Foote82.T66.CaseIIU

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

theorem card_eq_mul_of_surjective {W M : Type*} [AddCommGroup W] [AddCommGroup M] [Finite W]
    (β : W →+ M) (hβ : Function.Surjective β) :
    Nat.card W = Nat.card M * Nat.card β.ker := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup β.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective β hβ).toEquiv]

theorem le_six_of_card_alt_le {n : ℕ} (h : Nat.card ↥(alternatingGroup (Fin n)) ≤ 360) : n ≤ 6 := by
  by_contra hn
  push Not at hn
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h2 : 2 * Nat.card ↥(alternatingGroup (Fin n)) = Nat.factorial n := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  have h3 : Nat.factorial 7 ≤ Nat.factorial n := Nat.factorial_le hn
  have h4 : Nat.factorial 7 = 5040 := by decide
  omega

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem L_fix_Vz {l : GLV V} (hl : l ∈ L) {w : V} (hw : w ∈ commSpace (Subgroup.zpowers z) ⊤) :
    l w = w := by
  have h := c.std.extremal.setup.toSetup6.lemma61 (Subgroup.mem_zpowers z)
  exact h.1 l hl w hw

theorem VL_le_V₀ : commSpace L ⊤ ≤ commSpace (HH G L v) ⊤ := commSpace_mono c.L_le_H le_rfl

theorem finrank_V₀ (hs : CaseIISplit) : Module.finrank (ZMod 2) ↥(commSpace (HH G L v) ⊤) = 6 := by
  obtain ⟨β, hβ, -⟩ := c.exists_beta hs
  have h1 : Nat.card ↥(commSpace (HH G L v) ⊤) = 64 := by
    rw [Nat.card_congr (Equiv.ofBijective β hβ)]
    simp [Nat.card_fun]
  have h2 := card_eq_two_pow_finrank ↥(commSpace (HH G L v) ⊤)
  rw [h1] at h2
  have : (64 : ℕ) = 2 ^ 6 := by norm_num
  rw [this] at h2
  exact (Nat.pow_right_injective le_rfl h2).symm

theorem finrank_V₀z (hs : CaseIISplit) :
    Module.finrank (ZMod 2) ↥((commSpace (HH G L v) ⊤).map (subOne z)) = 1 := by
  rw [c.finrank_map_V₀ hs c.z_mem]
  exact c.data.ψ_z

theorem finrank_VL_le (hs : CaseIISplit) :
    Module.finrank (ZMod 2) ↥(commSpace L ⊤) ≤
      5 + Module.finrank (ZMod 2) ↥(fixedSpace L ⊓ commSpace L ⊤) := by
  have h4 := c.finrank_V₀z hs
  set W := commSpace L ⊤
  set Z := (commSpace (HH G L v) ⊤).map (subOne z)
  have hZfix : Z ≤ fixedSpace L := by
    rintro _ ⟨w, -, rfl⟩ l hl
    refine c.L_fix_Vz hl ?_
    rw [commSpace_zpowers_top_eq_range c.z_mul_z]
    exact LinearMap.mem_range_self _ w
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W Z
  have h2 : Module.finrank (ZMod 2) ↥(W ⊔ Z) ≤ 6 := by
    rw [← c.finrank_V₀ hs]
    exact Submodule.finrank_mono (sup_le c.VL_le_V₀ (c.map_V₀_le c.z_mem))
  have h3 : Module.finrank (ZMod 2) ↥(W ⊓ Z) ≤ Module.finrank (ZMod 2) ↥(fixedSpace L ⊓ W) :=
    Submodule.finrank_mono fun w hw => ⟨hZfix hw.2, hw.1⟩
  omega

theorem card_VL_le (hs : CaseIISplit) :
    Nat.card ↥(commSpace L ⊤) ≤ 32 * Nat.card ↥(fixedSpace L ⊓ commSpace L ⊤) := by
  rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank]
  have h := c.finrank_VL_le hs
  calc 2 ^ Module.finrank (ZMod 2) ↥(commSpace L ⊤)
      ≤ 2 ^ (5 + Module.finrank (ZMod 2) ↥(fixedSpace L ⊓ commSpace L ⊤)) :=
        Nat.pow_le_pow_right (by norm_num) h
    _ = 32 * 2 ^ Module.finrank (ZMod 2) ↥(fixedSpace L ⊓ commSpace L ⊤) := by
        rw [pow_add]; norm_num

theorem card_ker_eq {M : Type*} [AddCommGroup M] (β : ↥(commSpace L ⊤) →+ M)
    (hβk : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup) :
    Nat.card β.ker = Nat.card ↥(fixedSpace L ⊓ commSpace L ⊤) := by
  rw [hβk]
  refine Nat.card_congr
    { toFun := fun w => ⟨(w : ↥(commSpace L ⊤)), w.2, (w : ↥(commSpace L ⊤)).2⟩
      invFun := fun w => ⟨⟨w, w.2.2⟩, w.2.1⟩
      left_inv := fun w => rfl
      right_inv := fun w => rfl }

theorem card_le_of_witness (hs : CaseIISplit) {X M : Type} [Group X] [AddCommGroup M]
    {R : X → M → M → Prop} (h : TildeVWitness L X M R) : Nat.card M ≤ 32 := by
  obtain ⟨-, -, β, hβs, hβk, -⟩ := h
  have h1 := card_eq_mul_of_surjective β hβs
  rw [c.card_ker_eq β hβk] at h1
  have h2 := c.card_VL_le hs
  have hpos : 0 < Nat.card ↥(fixedSpace L ⊓ commSpace L ⊤) := Nat.card_pos
  rw [h1] at h2
  exact Nat.le_of_mul_le_mul_right h2 hpos

theorem isAltNaturalModule (hs : CaseIISplit) : IsAltNaturalModule L 6 := by
  have hL := c.card_L
  rcases c.std.extremal.fmod with ⟨n, hn, h⟩ | h | h | h | h | h
  ·
    obtain ⟨α, hα, -⟩ := id h
    have hle : Nat.card ↥(alternatingGroup (Fin n)) ≤ 360 := by
      rw [← hL]
      exact Nat.card_le_card_of_surjective α hα
    have hn6 : n = 6 := le_antisymm (le_six_of_card_alt_le hle) hn
    subst hn6
    exact h
  ·
    exfalso
    obtain ⟨⟨α, hα⟩, -⟩ := h
    have hle := Nat.card_le_card_of_surjective α hα
    rw [hL, nat_card_alternatingGroup, Nat.card_fin] at hle
    have : Nat.factorial 7 / 2 = 2520 := by decide
    omega
  · exfalso
    have := c.card_le_of_witness hs h
    simp [Nat.card_fun] at this
  · exfalso
    have := c.card_le_of_witness hs h
    simp [Nat.card_fun] at this
  · exfalso
    have := c.card_le_of_witness hs h
    simp [Nat.card_fun] at this
  ·
    exfalso
    obtain ⟨-, h6⟩ := h
    have hq := Submodule.finrank_quotient_add_finrank
      ((fixedSpace L).comap (commSpace L ⊤).subtype)
    have hc : Module.finrank (ZMod 2) ↥((fixedSpace L).comap (commSpace L ⊤).subtype) =
        Module.finrank (ZMod 2) ↥(fixedSpace L ⊓ commSpace L ⊤) := by
      refine LinearEquiv.finrank_eq
        { toFun := fun w => ⟨(w : ↥(commSpace L ⊤)), w.2, (w : ↥(commSpace L ⊤)).2⟩
          invFun := fun w => ⟨⟨w, w.2.2⟩, w.2.1⟩
          left_inv := fun w => rfl
          right_inv := fun w => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
    have h5 := c.finrank_VL_le hs
    change Module.finrank (ZMod 2)
      (↥(commSpace L ⊤) ⧸ (fixedSpace L).comap (commSpace L ⊤).subtype) = 6 at h6
    omega

end Ctx

end CaseII

end CFSG.CGT.Foote82
