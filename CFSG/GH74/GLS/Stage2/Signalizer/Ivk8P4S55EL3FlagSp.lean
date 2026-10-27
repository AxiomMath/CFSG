module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.Flag

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Fl3

open Subgroup Matrix Module CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def fix (R : Subgroup SL(3, F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
  add_mem' := fun {a b} ha hb g hg => by rw [mulVec_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => mulVec_zero _
  smul_mem' := fun c a ha g hg => by rw [mulVec_smul, ha g hg]

@[expose] def aug (R : Subgroup SL(3, F)) : Submodule F (Fin 3 → F) :=
  Submodule.span F {w | ∃ g ∈ R, ∃ v : Fin 3 → F,
    w = ((g : Matrix (Fin 3) (Fin 3) F) - 1) *ᵥ v}

@[expose] def fixT (R : Subgroup SL(3, F)) : Submodule F (Fin 3 → F) where
  carrier := {w | ∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w = w}
  add_mem' := fun {a b} ha hb g hg => by rw [mulVec_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => mulVec_zero _
  smul_mem' := fun c a ha g hg => by rw [mulVec_smul, ha g hg]

theorem sub_one_mulVec_mem_aug {R : Subgroup SL(3, F)} {g : SL(3, F)} (hg : g ∈ R)
    (v : Fin 3 → F) : ((g : Matrix (Fin 3) (Fin 3) F) - 1) *ᵥ v ∈ aug R :=
  Submodule.subset_span ⟨g, hg, v, rfl⟩

theorem mulVec_mem_fix {R : Subgroup SL(3, F)} {g : SL(3, F)}
    (hg : g ∈ normalizer (R : Set SL(3, F))) {v : Fin 3 → F} (hv : v ∈ fix R) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ fix R := by
  intro h hh
  have hk : g⁻¹ * h * g ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) h).mp hh
    simpa using this
  have hv' := hv _ hk
  calc (h : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
      = ((h * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
        rw [Matrix.SpecialLinearGroup.coe_mul h g, mulVec_mulVec]
    _ = ((g * (g⁻¹ * h * g) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
        rw [← mul_assoc, mul_inv_cancel_left]
    _ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (((g⁻¹ * h * g : SL(3, F)) :
          Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
        rw [Matrix.SpecialLinearGroup.coe_mul g (g⁻¹ * h * g), mulVec_mulVec]
    _ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by rw [hv']

theorem mulVec_mem_aug {R : Subgroup SL(3, F)} {g : SL(3, F)}
    (hg : g ∈ normalizer (R : Set SL(3, F))) {w : Fin 3 → F} (hw : w ∈ aug R) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ aug R := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, hh, v, rfl⟩ := hx
    have hk : g * h * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg h).mp hh
    have hkg : ((g * h * g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * (h : Matrix _ _ F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul (g * h * g⁻¹) g,
        ← Matrix.SpecialLinearGroup.coe_mul g h, mul_assoc (g * h), inv_mul_cancel, mul_one]
    have : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (((h : Matrix (Fin 3) (Fin 3) F) - 1) *ᵥ v) =
        (((g * h * g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1) *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
      rw [mulVec_mulVec, mulVec_mulVec, sub_mul, hkg, one_mul, mul_sub, mul_one]
    rw [this]
    exact sub_one_mulVec_mem_aug hk _
  | zero => simp
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx

theorem aug_ne_bot {R : Subgroup SL(3, F)} (hR : R ≠ ⊥) : aug R ≠ ⊥ := by
  intro hbot
  apply hR
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hall : ∀ v : Fin 3 → F, ((g : Matrix (Fin 3) (Fin 3) F) - 1) *ᵥ v = 0 := by
    intro v
    have := sub_one_mulVec_mem_aug hg v
    rwa [hbot, Submodule.mem_bot] at this
  apply Subtype.ext
  ext i j
  have h := congrFun (hall (Pi.single j 1)) i
  rw [sub_mulVec, one_mulVec] at h
  have h' : (g : Matrix (Fin 3) (Fin 3) F) i j = (1 : Matrix (Fin 3) (Fin 3) F) i j := by
    have := sub_eq_zero.mp h
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  simpa using h'

@[expose] noncomputable def augRep (R : Subgroup SL(3, F)) : ↥R →* Module.End F (aug R) where
  toFun g := (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) F)).restrict
    (fun w hw => mulVec_mem_aug (Subgroup.le_normalizer g.2) hw)
  map_one' := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [LinearMap.coe_restrict_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    show (((g * h : ↥R) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ (w : Fin 3 → F) =
      ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ (w : Fin 3 → F))
    rw [mulVec_mulVec]
    rfl

theorem fix_inf_aug_ne_bot {p : ℕ} [Fact p.Prime] [CharP F p] [Finite F] {R : Subgroup SL(3, F)}
    (hRp : IsPGroup p R) (hR : R ≠ ⊥) : fix R ⊓ aug R ≠ ⊥ := by
  have : Nontrivial (aug R) := Submodule.nontrivial_iff_ne_bot.mpr (aug_ne_bot hR)
  have hP : IsPGroup p ↥(⊤ : Subgroup ↥R) := hRp.of_equiv Subgroup.topEquiv.symm
  obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero (augRep R) p (⊤ : Subgroup ↥R) hP
  intro hbot
  have hmem : (v : Fin 3 → F) ∈ fix R ⊓ aug R := by
    refine ⟨?_, v.2⟩
    intro g hg
    exact congrArg Subtype.val (hv ⟨g, hg⟩ (Subgroup.mem_top _))
  rw [hbot, Submodule.mem_bot] at hmem
  exact hv0 (Subtype.ext hmem)

@[expose] def dotB : LinearMap.BilinForm F (Fin 3 → F) := dotProductBilin F F

theorem dotBilin_apply (u v : Fin 3 → F) : dotB u v = u ⬝ᵥ v := rfl

theorem dotBilin_nondegenerate : (dotB (F := F)).Nondegenerate := by
  constructor
  · intro x hx
    ext i
    have := hx (Pi.single i 1)
    simpa [dotBilin_apply, dotProduct_single] using this
  · intro y hy
    ext i
    have := hy (Pi.single i 1)
    simpa [dotBilin_apply, single_dotProduct] using this

theorem sub_one_mulVec_dotProduct (M : Matrix (Fin 3) (Fin 3) F) (v w : Fin 3 → F) :
    ((M - 1) *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Mᵀ *ᵥ w - w) := by
  have h : ((M - 1) *ᵥ v) ⬝ᵥ w = v ⬝ᵥ ((M - 1)ᵀ *ᵥ w) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    exact dotProduct_comm _ _
  rw [h, Matrix.transpose_sub, Matrix.transpose_one, sub_mulVec, one_mulVec]

theorem orthogonal_aug (R : Subgroup SL(3, F)) : dotB.orthogonal (aug R) = fixT R := by
  ext w
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h g hg
    have key : ∀ i : Fin 3, ((g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w - w) i = 0 := by
      intro i
      have h1 := h _ (sub_one_mulVec_mem_aug hg (Pi.single i 1))
      rw [dotBilin_apply, sub_one_mulVec_dotProduct] at h1
      simpa [dotProduct_single, single_dotProduct] using h1
    have := funext key
    exact sub_eq_zero.mp this
  · intro hw n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, v, rfl⟩ := hx
      rw [dotBilin_apply, sub_one_mulVec_dotProduct, hw g hg, sub_self, dotProduct_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

theorem finrank_aug_add_finrank_fixT [Finite F] (R : Subgroup SL(3, F)) :
    finrank F (aug R) + finrank F (fixT R) = 3 := by
  have h := LinearMap.BilinForm.finrank_orthogonal dotBilin_nondegenerate (aug R)
  rw [orthogonal_aug, finrank_fin_fun] at h
  have := Submodule.finrank_le (aug R)
  rw [finrank_fin_fun] at this
  omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Fl3
