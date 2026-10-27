module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftImageNat

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization
open Projectivization

universe v

section SL2

variable {F : Type*} [Field F]

theorem exists_sl2_firstCol {u : Fin 2 → F} (hu : u ≠ 0) :
    ∃ A : SL(2, F), A • (Pi.single 0 1 : Fin 2 → F) = u := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := by
      intro h1
      apply hu
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    refine ⟨⟨!![0, -(u 1)⁻¹; u 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    change (!![0, -(u 1)⁻¹; u 1, 0] : Matrix (Fin 2) (Fin 2) F).mulVec
      (Pi.single 0 1 : Fin 2 → F) = u
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply, h0]
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    change (!![u 0, 0; u 1, (u 0)⁻¹] : Matrix (Fin 2) (Fin 2) F).mulVec
      (Pi.single 0 1 : Fin 2 → F) = u
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_sl2_smul_eq {u v : Fin 2 → F} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ y : SL(2, F), y • u = v := by
  obtain ⟨A, hA⟩ := exists_sl2_firstCol hu
  obtain ⟨B, hB⟩ := exists_sl2_firstCol hv
  refine ⟨B * A⁻¹, ?_⟩
  rw [mul_smul, ← hA, inv_smul_smul, hB]

end SL2

section Natural

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

theorem natural_span (ctx : FamilyCtx H T n F r Lc) (hnat : NaturalFamily H F r Lc)
    (hU : ∀ i, IsSylowTwoOf (T ⊓ Lc i) (Lc i)) :
    Submodule.span (ZMod 2) {w : V | ∃ k ∈ oddGen H, ∃ y ∈ fixGL (⨆ i, T ⊓ Lc i), w = k y} = ⊤ := by
  classical
  set Y := fixGL (⨆ i, T ⊓ Lc i) with hY
  set M := Submodule.span (ZMod 2) {w : V | ∃ k ∈ oddGen H, ∃ y ∈ Y, w = k y} with hM
  have hgen : ∀ k ∈ oddGen H, ∀ y ∈ Y, k y ∈ M := fun k hk y hy =>
    Submodule.subset_span ⟨k, hk, y, hy, rfl⟩
  have hYM : ∀ y ∈ Y, y ∈ M := fun y hy => hgen 1 (Subgroup.one_mem _) y hy
  have hYM' : Y ≤ M := fun y hy => hYM y hy
  have hLK : ∀ i, Lc i ≤ oddGen H := fun i => by
    rw [ctx.layer.K_eq]
    exact le_iSup Lc i
  have hDK : (⨆ i, T ⊓ Lc i) ≤ oddGen H := iSup_le fun j => inf_le_right.trans (hLK j)
  have hIM : ∀ i, commGL (Lc i) ⊤ ≤ M := by
    intro i u hu
    obtain ⟨θ, β, x, hcompat, hline⟩ := natural_coords hnat (hU i)
    have hlift := natural_lines_lift ctx hnat (hU i) θ β x hcompat hline
    set w := β (Submodule.Quotient.mk ⟨u, hu⟩ :
      ↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) with hw
    by_cases hw0 : w = 0
    · have hz : (⟨u, hu⟩ : ↥(commGL (Lc i) ⊤)) ∈ fixIn (Lc i) (commGL (Lc i) ⊤) := by
        have hq : (Submodule.Quotient.mk ⟨u, hu⟩ :
            ↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) = 0 :=
          β.injective (by rw [← hw, hw0, map_zero])
        exact (Submodule.Quotient.mk_eq_zero _).1 hq
      exact hYM u (mem_fixGL_prod ctx hu (fun l hl => hz l hl.2))
    · obtain ⟨y, hy⟩ := exists_sl2_smul_eq hw0 (smul_single_ne_zero x)
      have hyl : y • w ∈ rootLine x := by
        rw [hy]
        exact smul_single_mem_rootLine x
      obtain ⟨v, hvfix, hvβ⟩ := hlift (y • w) hyl
      set k : ↥(Lc i) := θ.symm y⁻¹ with hk
      have hkv : (k : V ≃ₗ[ZMod 2] V) (v : V) ∈ commGL (Lc i) ⊤ :=
        blockB_apply_mem_I ctx (Lc_le_blockB ctx i k.2) v.2
      have hcomp := hcompat k v ⟨(k : V ≃ₗ[ZMod 2] V) (v : V), hkv⟩ rfl
      have hθk : θ k = y⁻¹ := by simp [hk]
      have hβkv : β (Submodule.Quotient.mk ⟨(k : V ≃ₗ[ZMod 2] V) (v : V), hkv⟩) = w := by
        rw [hcomp, hθk, hvβ]
        show y⁻¹ • (y • w) = w
        rw [inv_smul_smul]
      have hdiff : (⟨(k : V ≃ₗ[ZMod 2] V) (v : V), hkv⟩ - ⟨u, hu⟩ : ↥(commGL (Lc i) ⊤)) ∈
          fixIn (Lc i) (commGL (Lc i) ⊤) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
        exact β.injective (hβkv.trans hw)
      have hzY : (k : V ≃ₗ[ZMod 2] V) (v : V) - u ∈ Y := by
        have hzI : (k : V ≃ₗ[ZMod 2] V) (v : V) - u ∈ commGL (Lc i) ⊤ :=
          Submodule.sub_mem _ hkv hu
        exact mem_fixGL_prod ctx hzI (fun l hl => hdiff l hl.2)
      have hvY : (v : V) ∈ Y := mem_fixGL_prod ctx v.2 hvfix
      have h1 : (k : V ≃ₗ[ZMod 2] V) (v : V) ∈ M := hgen k (hLK i k.2) v hvY
      have h2 := M.sub_mem h1 (hYM _ hzY)
      simpa using h2
  have hV := V_sum ctx
  refine top_le_iff.1 ?_
  rw [← hV]
  exact sup_le (iSup_le hIM) ((fixSub_anti _ hDK).trans hYM')

end Natural

end CFSG.QuasithinUnique.Setup.Lift
