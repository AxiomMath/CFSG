module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
public import CFSG.GH74.Generic.BProg.B2.PumpupTableL3
import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Inner

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableSp4

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.ComponentClassification.CatFactsSp4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.Generic.BProg.B2.PumpupTableBasic CFSG.GH74.Generic.BProg.B2.PumpupTableTwoInv
  CFSG.GH74.Generic.BProg.B2.PumpupTableL3 CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
open scoped MatrixGroups

theorem stated_of_lieModel_psp {X : Type} [Group X] {n p f : ℕ} (h : LieModel X .PSp n p f) :
    StatedClassicalModel X .PSp n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

section Certified


theorem false_of_sl2_component {N : Type} [Group N] [Finite N] {H L : Subgroup N} {t : N}
    (hs : ShapeInCent H t L) {F : Type} [Field F] [Finite F] (hk : ringChar F ≠ 2)
    (e : ↥L ≃* SL(2, F)) : False := by
  obtain ⟨a, haL, b, hbL, ha2, hb2, ha1, hb1, hab⟩ := hasTwoInvolutions_of_shapeInCent hs
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hk
  have hsq : ∀ x : ↥L, (x : N) * x = 1 → (x : N) ≠ 1 →
      ((e x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    intro x hx2 hx1
    refine CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (e x) ?_ ?_
    · rw [← map_pow, pow_two]
      have : x * x = 1 := Subtype.ext hx2
      rw [this, map_one]
    · intro h1
      apply hx1
      have : x = 1 := e.injective (by rw [h1, map_one])
      rw [this]; rfl
  have ea := hsq ⟨a, haL⟩ ha2 ha1
  have eb := hsq ⟨b, hbL⟩ hb2 hb1
  have : e ⟨a, haL⟩ = e ⟨b, hbL⟩ := Subtype.ext (ea.trans eb.symm)
  exact hab (congrArg Subtype.val (e.injective this))

theorem pumpupIn_sp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) : PumpupEmptyIn (fun X _ => LieModel X .PSp 2 p f) := by
  intro N _ _ H t L hs htH hH
  obtain ⟨hadm, F, _, _, hF, ⟨ψ⟩⟩ := stated_of_lieModel_psp hH
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hk : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  have hot : orderOf (⟨t, htH⟩ : ↥H) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hs.inv
  have hvu : orderOf (ψ ⟨t, htH⟩) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hot
  obtain ⟨φ, hφ⟩ := exists_model_conj hodd hvu
  set Φ : ↥H ≃* StatedProj (StatedSp 2 F) := ψ.trans φ with hΦ
  have hB := isCompIn_centralizer_subgroupOf htH hs.comp
  have hcomp : IsPComponent 2 ((L.subgroupOf H).subgroupOf
      (centralizer {(⟨t, htH⟩ : ↥H)})) := isPComponent_two_of_isComponent hB.2
  have hmap := isPComponent_map_subgroupOf 2 Φ hB.1 hcomp
  have hMX : (L.subgroupOf H).map Φ.toMonoidHom ≤ centralizer {Φ ⟨t, htH⟩} := by
    rw [← CFSG.ComponentClassification.CatFactsSp4.map_centralizer_singleton]
    exact Subgroup.map_mono hB.1
  rw [CFSG.ComponentClassification.CatFactsSp4.map_centralizer_singleton] at hmap
  let eM : ↥L ≃* ↥((L.subgroupOf H).map Φ.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hLH).symm.trans
      ((L.subgroupOf H).equivMapOfInjective Φ.toMonoidHom Φ.injective)
  have hΦt : Φ ⟨t, htH⟩ = φ (ψ ⟨t, htH⟩) := rfl
  rcases hφ with h | h
  · rw [← hΦt] at h
    rw [h] at hmap hMX
    obtain ⟨hE | hE, -⟩ := pComponent_centralizer_u1 hodd hMX hmap
    · exact false_of_sl2_component hs hk
        (eM.trans ((MulEquiv.subgroupCongr hE).trans (E1Equiv h2).symm))
    · exact false_of_sl2_component hs hk
        (eM.trans ((MulEquiv.subgroupCongr hE).trans (E2Equiv h2).symm))
  · rw [← hΦt] at h
    rw [h] at hmap hMX
    obtain ⟨hL, h5⟩ := pComponent_centralizer_u2 hodd hMX hmap
    exact false_of_psl2_component hs hp hp2 (lieModel_psl2_of_equiv hp hf (by omega) hF
      (eM.trans ((MulEquiv.subgroupCongr hL).trans (LEquiv F).symm)))

end Certified

end CFSG.GH74.Generic.BProg.B2.PumpupTableSp4
