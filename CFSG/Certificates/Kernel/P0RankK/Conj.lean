
module

public import CFSG.Monster.B.TwoA.Sp8.P0RankBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix CFSG.Open
open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank
open CFSG.KC.BvecLoop

theorem sCoord_conj_uE_bvec (lam : ℕ) (x : Lgrp) {σ : ℕ} (hσ : σ < 2 ^ 16)
    (hx : sCoord x = Multiplicative.ofAdd (bvec 16 σ)) :
    sCoord ⟨uE lam * x * (uE lam)⁻¹, conj_mem_Lgrp (uE_mem_P0 lam) x.2⟩ =
      Multiplicative.ofAdd (bvec 16 (actK p0Data.aCols lam σ)) := by
  have h := sCoord_conj ⟨uE lam, uE_mem_P0 lam⟩ x
  rw [uCoord_uE, hx, toAdd_ofAdd, toAdd_ofAdd] at h
  rw [bvec_actK_aCols lam hσ]
  exact h

theorem conj_layers {E : Subgroup Dfull} (hE : E ≤ PLam lam0) (hEA : IsElemAbelian 2 E)
    (lam : ℕ) : ∃ E' : Subgroup Dfull, E' ≤ PLam lam0 ∧ IsElemAbelian 2 E' ∧
      Nat.card E' = Nat.card E ∧ layerD E' = (layerD E).image (actK p0Data.aCols lam) := by
  classical
  set g : Dfull := uE lam with hgdef
  have hg : g ∈ P0 := uE_mem_P0 lam
  have hP0 : P0 = PLam lam0 := rfl
  let f : Dfull →* Dfull := (MulAut.conj g).toMonoidHom
  have hf : ∀ y, f y = g * y * g⁻¹ := fun y => rfl
  have hfinj : Function.Injective f := (MulAut.conj g).injective
  refine ⟨E.map f, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← hP0]
    rw [hf]
    exact P0.mul_mem (P0.mul_mem hg (hE hy)) (P0.inv_mem hg)
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨z, hz, hzb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : Dfull) * b = b * a
      have hyz : y * z = z * y := congrArg Subtype.val (hEA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      rw [← hya, ← hzb, ← map_mul, ← map_mul, hyz]
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hEA.2 y hy, map_one]
  · exact Subgroup.card_map_of_injective hfinj
  · ext σ'
    simp only [layerD, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hσ', x', hx'E, hx'⟩
      obtain ⟨y, hyE, hyx⟩ := Subgroup.mem_map.1 hx'E
      have hyL : y ∈ Lgrp := by
        have h := conj_mem_Lgrp (P0.inv_mem hg) x'.2
        have hy : g⁻¹ * (x' : Dfull) * g⁻¹⁻¹ = y := by
          rw [← hyx, hf, inv_inv]
          group
        rwa [hy] at h
      let Y : Lgrp := ⟨y, hyL⟩
      obtain ⟨σ, hσ, hb⟩ := exists_bvec 16 (sCoord Y).toAdd
      have hY : sCoord Y = Multiplicative.ofAdd (bvec 16 σ) := by rw [hb, ofAdd_toAdd]
      refine ⟨σ, ⟨hσ, Y, hyE, hY⟩, ?_⟩
      have hx'eq : x' = ⟨uE lam * Y * (uE lam)⁻¹, conj_mem_Lgrp (uE_mem_P0 lam) Y.2⟩ :=
        Subtype.ext (by rw [← hyx, hf])
      have h := sCoord_conj_uE_bvec lam Y hσ hY
      rw [← hx'eq, hx'] at h
      exact bvec_inj (actK_aCols_lt lam hσ) hσ' (Multiplicative.ofAdd.injective h).symm
    · rintro ⟨σ, ⟨hσ, x, hxE, hx⟩, rfl⟩
      refine ⟨actK_aCols_lt lam hσ,
        ⟨uE lam * x * (uE lam)⁻¹, conj_mem_Lgrp (uE_mem_P0 lam) x.2⟩,
        Subgroup.mem_map.2 ⟨x, hxE, rfl⟩, sCoord_conj_uE_bvec lam x hσ hx⟩

end CFSG.Monster.B.TwoA.Sp8.WordRel
