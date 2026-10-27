module

public import CFSG.GH74.GLS.Stage4.T6Irr

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

@[expose] def bSub (F : Type) [Field F] : Subgroup (SL2 F) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    intro x y hx hy
    have hx' : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hx
    have hy' : (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hy
    show ((x * y : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx', hy']
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    have hx' : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hx
    show ((x⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hx']

theorem mem_bSub {F : Type} [Field F] {x : SL2 F} :
    x ∈ bSub F ↔ (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := Iff.rfl

theorem t6_normalizes_uSub {F : Type} [Field F] {g : SL2 F}
    (hg : ∀ x ∈ uSub F, g * x * g⁻¹ ∈ uSub F) : g ∈ bSub F := by
  have h := (hg (sl2U 1) (sl2U_mem_uSub 1)).2.2
  have h2 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination -h
  exact mem_bSub.2 (pow_eq_zero_iff two_ne_zero |>.1 h2)

@[expose] def bElt {F : Type} [Field F] (t : Fˣ) (b : F) : SL2 F :=
  ⟨!![(t : F), b; 0, ((t⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

theorem bElt_mem {F : Type} [Field F] (t : Fˣ) (b : F) : bElt t b ∈ bSub F := rfl

theorem bElt_bijective (F : Type) [Field F] :
    Function.Bijective (fun p : Fˣ × F => (⟨bElt p.1 p.2, bElt_mem p.1 p.2⟩ : bSub F)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨t, b⟩ ⟨t', b'⟩ h
    have h00 := congrArg (fun x : bSub F => ((x : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0) h
    have h01 := congrArg (fun x : bSub F => ((x : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp only [bElt] at h00 h01
    exact Prod.ext (Units.ext h00) h01
  · rintro ⟨g, hg⟩
    have hdet := t2A_det g
    rw [mem_bSub.1 hg, mul_zero, sub_zero] at hdet
    refine ⟨(⟨(g : Matrix (Fin 2) (Fin 2) F) 0 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1, hdet, by
      rw [mul_comm]; exact hdet⟩, (g : Matrix (Fin 2) (Fin 2) F) 0 1), ?_⟩
    apply Subtype.ext
    apply t2A_ext <;> simp [bElt, mem_bSub.1 hg]

theorem t6_card_bSub (F : Type) [Field F] [Finite F] :
    Nat.card ↥(bSub F) = Nat.card F * (Nat.card F - 1) := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (bElt_bijective F)), Nat.card_prod, Nat.card_units,
    mul_comm]

theorem t6_card_normalizer_dvd {G : Type} [Group G] {F : Type} [Field F] [Finite F] {φ : SL2 F →* G}
    (hφ : Function.Injective φ) :
    Nat.card ↥(Subgroup.normalizer (((uSub F).map φ : Subgroup G) : Set G) ⊓ φ.range) ∣
      Nat.card F * (Nat.card F - 1) := by
  have hNr : Subgroup.normalizer (((uSub F).map φ : Subgroup G) : Set G) ⊓ φ.range ≤ φ.range :=
    inf_le_right
  have hle : (Subgroup.normalizer (((uSub F).map φ : Subgroup G) : Set G) ⊓ φ.range).comap φ ≤
      bSub F := by
    intro g hg
    apply t6_normalizes_uSub
    intro x hx
    have hn : φ g ∈ Subgroup.normalizer (((uSub F).map φ : Subgroup G) : Set G) :=
      (Subgroup.mem_comap.1 hg).1
    have hmem : φ (g * x * g⁻¹) ∈ (uSub F).map φ := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_set_normalizer_iff.1 hn (φ x)).1 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = g * x * g⁻¹ := hφ hyx
    rwa [← this]
  have hcard : Nat.card ↥(Subgroup.normalizer (((uSub F).map φ : Subgroup G) : Set G) ⊓ φ.range) =
      Nat.card ↥((Subgroup.normalizer (((uSub F).map φ : Subgroup G) : Set G) ⊓ φ.range).comap φ) := by
    rw [← Subgroup.card_map_of_injective hφ, t6_map_comap hNr]
  rw [hcard, ← t6_card_bSub F]
  exact Subgroup.card_dvd_of_le hle

end CFSG.GH74.GLS.Stage4.Rest.T6
