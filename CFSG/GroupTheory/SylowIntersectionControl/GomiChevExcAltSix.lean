module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcAut
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcAltSixData
public import CFSG.GroupTheory.PCoreOfInvolution
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsA6
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsA6Perm

public section

namespace CFSG.GroupTheory

open Equiv CFSG.Open CFSG.ABGLocalTools Subgroup CFSG.QuasithinUnique.Setup.X3E

private theorem pCoreOf_eqLocus_ne_bot_of_conjNormal {g : Perm (Fin 6)}
    (hβ2 : (MulAut.conjNormal g : MulAut S6) * MulAut.conjNormal g = 1)
    (hβout : ∀ k : S6, (MulAut.conjNormal g : MulAut S6) ≠ MulAut.conj k) :
    pCoreOf 2 ((MulAut.conjNormal g : MulAut S6).toMonoidHom.eqLocus (MonoidHom.id S6)) ≠ ⊥ := by
  have hgg : g * g = 1 := by
    apply CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.conjNormal_injective_alt6
    rw [map_mul, map_one, hβ2]
  have hs : Perm.sign g = -1 := by
    by_contra hs
    have hs1 : Perm.sign g = 1 := (Int.units_eq_one_or (Perm.sign g)).resolve_right hs
    exact hβout ⟨g, Perm.mem_alternatingGroup.2 hs1⟩
      (MulAut.conjNormal_val (h := ⟨g, Perm.mem_alternatingGroup.2 hs1⟩))
  obtain ⟨t, hts, ht1, ht2, htg, hc⟩ :=
    GomiExcAltSix.exists_commuting_conj_of_odd_involution hgg hs
  refine pCoreOf_ne_bot_of_commute_conj (t := ⟨t, Perm.mem_alternatingGroup.2 hts⟩) ?_ ?_ ?_ ?_
  · refine Subtype.ext ?_
    change g * t * g⁻¹ = t
    rw [← htg]
    group
  · exact fun h => ht1 (by simpa using Subtype.ext_iff.mp h)
  · exact Subtype.ext (by simp [ht2])
  · intro x hx
    refine Subtype.ext ?_
    have hx' : g * (x : Perm (Fin 6)) * g⁻¹ = (x : Perm (Fin 6)) := by
      have h := congrArg Subtype.val hx
      simpa [MulAut.conjNormal_apply] using h
    have hxg : (x : Perm (Fin 6)) * g = g * (x : Perm (Fin 6)) := by
      calc (x : Perm (Fin 6)) * g = (g * (x : Perm (Fin 6)) * g⁻¹) * g := by rw [hx']
        _ = g * (x : Perm (Fin 6)) := by group
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hc (x : Perm (Fin 6)) hxg

private theorem not_mem_map_conj_alt6PairStab {β : MulAut S6} {g k : S6}
    (hg : ((g * β gx * g⁻¹ : S6) : Perm (Fin 6)) = c[0, 1, 2] * c[3, 4, 5]) :
    β (k * gx * k⁻¹) ∉
      GomiExcAltSix.alt6PairStab.map (MulAut.conj k).toMonoidHom := by
  intro hβy
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hβy
  have hβgx : ((β gx : S6) : Perm (Fin 6)) =
      (g : Perm (Fin 6))⁻¹ * (c[0, 1, 2] * c[3, 4, 5]) * (g : Perm (Fin 6)) := by
    have h := hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [← h]
    group
  let w : Perm (Fin 6) :=
    (k : Perm (Fin 6))⁻¹ * (β k : Perm (Fin 6)) * (g : Perm (Fin 6))⁻¹
  have hβy' : ((β (k * gx * k⁻¹) : S6) : Perm (Fin 6)) =
      (β k : Perm (Fin 6)) * ((g : Perm (Fin 6))⁻¹ * (c[0, 1, 2] * c[3, 4, 5]) *
        (g : Perm (Fin 6))) * ((β k : Perm (Fin 6)))⁻¹ := by
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hβgx]
  have hkey : ((k⁻¹ * β (k * gx * k⁻¹) * k : S6) : Perm (Fin 6)) =
      w * (c[0, 1, 2] * c[3, 4, 5]) * w⁻¹ := by
    rw [show ((k⁻¹ * β (k * gx * k⁻¹) * k : S6) : Perm (Fin 6)) =
        (k : Perm (Fin 6))⁻¹ * ((β (k * gx * k⁻¹) : S6) : Perm (Fin 6)) *
          (k : Perm (Fin 6)) from rfl, hβy']
    show (k : Perm (Fin 6))⁻¹ * ((β k : Perm (Fin 6)) *
      ((g : Perm (Fin 6))⁻¹ * (c[0, 1, 2] * c[3, 4, 5]) * (g : Perm (Fin 6))) *
      ((β k : Perm (Fin 6)))⁻¹) * (k : Perm (Fin 6)) =
        w * (c[0, 1, 2] * c[3, 4, 5]) * w⁻¹
    rw [show w = (k : Perm (Fin 6))⁻¹ * (β k : Perm (Fin 6)) *
      (g : Perm (Fin 6))⁻¹ from rfl]
    group
  have hc33 : (c[0, 1, 2] * c[3, 4, 5] : Perm (Fin 6)) ^ 3 = 1 := by decide
  have hcube : ((k⁻¹ * β (k * gx * k⁻¹) * k : S6) : Perm (Fin 6)) ^ 3 = 1 := by
    rw [hkey, conj_pow, hc33, mul_one, mul_inv_cancel]
  have h4 := GomiExcAltSix.apply_four_of_mem_alt6PairStab (k⁻¹ * β (k * gx * k⁻¹) * k) hβy hcube
  have hfix : (c[0, 1, 2] * c[3, 4, 5] : Perm (Fin 6)) (w⁻¹ 4) = w⁻¹ 4 := by
    have h := h4
    rw [hkey] at h
    have h2 : w (((c[0, 1, 2] * c[3, 4, 5]) : Perm (Fin 6)) (w⁻¹ 4)) = 4 := by
      simpa [Perm.mul_apply] using h
    exact w.injective (by rw [h2]; simp)
  exact GomiExcAltSix.c33_apply_ne (w⁻¹ 4) hfix

private theorem false_of_outer_alt6 {β : MulAut S6} {g : S6}
    (hg : ((g * β gx * g⁻¹ : S6) : Perm (Fin 6)) = c[0, 1, 2] * c[3, 4, 5])
    {U : Subgroup S6} (hU : IsSylowOf 2 U ⊤)
    (hA : ∀ A : Subgroup S6, IsGomiAtom ⊤ U A → A ⊔ A.map β.toMonoidHom ≠ ⊤) : False := by
  obtain ⟨k, -, hconj⟩ := GomiExcAltSix.isSylowOf_R0.exists_mem_conj hU
  have hUeq : U = R0.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    exact hconj x
  let B : Subgroup S6 := GomiExcAltSix.alt6PairStab.map (MulAut.conj k).toMonoidHom
  have hBatom : IsGomiAtom ⊤ U B := by
    rw [hUeq]
    exact (isGomiAtom_top_map_mulEquiv_iff (MulAut.conj k) R0
      GomiExcAltSix.alt6PairStab).2 GomiExcAltSix.isGomiAtom_R0_alt6PairStab
  have hBcard : Nat.card B = 24 := by
    rw [show B = GomiExcAltSix.alt6PairStab.map (MulAut.conj k).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective,
      GomiExcAltSix.card_alt6PairStab]
  have hyB : k * gx * k⁻¹ ∈ B := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom
      GomiExcAltSix.gx_mem_alt6PairStab
    simpa [B, MulAut.conj_apply] using h
  have hylt : B < B ⊔ B.map β.toMonoidHom := by
    refine lt_of_le_of_ne le_sup_left fun hEq => ?_
    have hmem : β (k * gx * k⁻¹) ∈ B ⊔ B.map β.toMonoidHom :=
      Subgroup.mem_sup_right (Subgroup.mem_map_of_mem β.toMonoidHom hyB)
    rw [← hEq] at hmem
    exact not_mem_map_conj_alt6PairStab (β := β) (k := k) hg hmem
  exact hA B hBatom (GomiExcAltSix.eq_top_of_card_eq_24_of_lt hBcard hylt)

theorem gomiExcAutFixed_alt6 : GomiExcAutFixed (alternatingGroup (Fin 6)) := by
  intro β U hβ2 hβout hU _hβU hA
  rcases CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.mulAut_alt6_cases β with
    ⟨g, rfl⟩ | ⟨g, hg⟩
  · exact pCoreOf_eqLocus_ne_bot_of_conjNormal hβ2 hβout
  · exact (false_of_outer_alt6 hg hU hA).elim

end CFSG.GroupTheory
