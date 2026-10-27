module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniData
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinComp
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.ClassicalInvolution.Phan
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S267Z.SL3 (blk mem_blk)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K] {h : UnitaryFieldData ℓ f K} [Fact ℓ.Prime]
  [CharP K ℓ] {σ : K ≃+* K} {f₀ : ℕ}

instance instCharPFixed : CharP ↥(semilinearFixedSubfield σ) ℓ := Subfield.charP _ ℓ

theorem bar_coe_fixed (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀))
    (x : ↥(semilinearFixedSubfield σ)) :
    h.bar (x : K) =
      ((unitaryInvolution (↥(semilinearFixedSubfield σ)) ℓ f₀ x : ↥(semilinearFixedSubfield σ)) :
        K) := by
  rw [unitaryInvolution_apply, SubmonoidClass.coe_pow, hbar _ x.2]

variable (h) in
@[expose] noncomputable def embSU (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀)) :
    Su (↥(semilinearFixedSubfield σ)) ℓ f₀ 3 →* ↥(SG h) where
  toFun A := ⟨Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype A, by
    obtain ⟨hdet, hu⟩ := mem_SUid.1 A.2
    refine mem_gramSU.2 ⟨?_, ?_⟩
    · have hmap : ((Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
          (A : GL (Fin 3) ↥(semilinearFixedSubfield σ)) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K).map h.bar =
          (((A : GL (Fin 3) ↥(semilinearFixedSubfield σ)) :
            Matrix (Fin 3) (Fin 3) ↥(semilinearFixedSubfield σ)).map
              (unitaryInvolution (↥(semilinearFixedSubfield σ)) ℓ f₀)).map
            (semilinearFixedSubfield σ).subtype := by
        ext i j
        exact bar_coe_fixed hbar _
      rw [hmap, Units.val_one, Matrix.mul_one]
      change ((((A : GL (Fin 3) ↥(semilinearFixedSubfield σ)) :
            Matrix (Fin 3) (Fin 3) ↥(semilinearFixedSubfield σ)).map
              (unitaryInvolution (↥(semilinearFixedSubfield σ)) ℓ f₀)).map
            (semilinearFixedSubfield σ).subtype)ᵀ *
          ((A : GL (Fin 3) ↥(semilinearFixedSubfield σ)) :
            Matrix (Fin 3) (Fin 3) ↥(semilinearFixedSubfield σ)).map
              (semilinearFixedSubfield σ).subtype = 1
      rw [← Matrix.transpose_map, ← Matrix.map_mul]
      have hu' : (((A : GL (Fin 3) ↥(semilinearFixedSubfield σ)) :
          Matrix (Fin 3) (Fin 3) ↥(semilinearFixedSubfield σ)).map
            (unitaryInvolution (↥(semilinearFixedSubfield σ)) ℓ f₀))ᵀ *
          ((A : GL (Fin 3) ↥(semilinearFixedSubfield σ)) :
            Matrix (Fin 3) (Fin 3) ↥(semilinearFixedSubfield σ)) = 1 := hu
      rw [hu', Matrix.map_one _ (map_zero _) (map_one _)]
    · change (((A : GL (Fin 3) ↥(semilinearFixedSubfield σ)) :
          Matrix (Fin 3) (Fin 3) ↥(semilinearFixedSubfield σ)).map
            (semilinearFixedSubfield σ).subtype).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' A B := by
    apply Subtype.ext
    simp

theorem coe_embSU (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀))
    (A : Su (↥(semilinearFixedSubfield σ)) ℓ f₀ 3) (i j : Fin 3) :
    (((embSU h hbar A : ↥(SG h)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      ((((A : GL (Fin 3) ↥(semilinearFixedSubfield σ)) :
        Matrix (Fin 3) (Fin 3) ↥(semilinearFixedSubfield σ)) i j : ↥(semilinearFixedSubfield σ)) :
          K) :=
  rfl

theorem embSU_injective (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀)) :
    Function.Injective (embSU h hbar) := by
  intro A B hAB
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrArg (fun g : ↥(SG h) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) hAB
  exact this

section Block

variable (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀))
include hbar

variable (h) in
noncomputable abbrev blockZ : Subgroup ↥(SG h) :=
  (coordBlockSU (↥(semilinearFixedSubfield σ)) ℓ f₀ blk).map (embSU h hbar)

theorem blockZ_le_blockU : blockZ h hbar ≤ blockU h blk := by
  rintro _ ⟨A, hA, rfl⟩
  rw [mem_blockU_iff]
  intro i j hij
  rw [coe_embSU, (mem_coordBlockSU_iff.1 hA) i j hij]
  split_ifs <;> simp

theorem fixed_of_mem_blockZ {g : ↥(SG h)} (hg : g ∈ blockZ h hbar) (i j : Fin 3) :
    σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j := by
  obtain ⟨A, -, rfl⟩ := hg
  rw [coe_embSU]
  exact ((((A : GL (Fin 3) ↥(semilinearFixedSubfield σ)) :
    Matrix (Fin 3) (Fin 3) ↥(semilinearFixedSubfield σ)) i j).2)

theorem mem_blockZ_of_fixed {g : ↥(SG h)} (hg : g ∈ blockU h blk)
    (hfix : ∀ i j, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) : g ∈ blockZ h hbar := by
  set K₀ := semilinearFixedSubfield σ with hK₀
  set gm : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hgm
  let M₀ : Matrix (Fin 3) (Fin 3) K₀ := Matrix.of fun i j => ⟨gm i j, hfix i j⟩
  have hmap : M₀.map K₀.subtype = gm := by
    ext i j
    rfl
  obtain ⟨hgu, hgd⟩ := mem_gramSU.1 g.2
  have hdet : M₀.det = 1 := by
    apply Subtype.val_injective
    change K₀.subtype M₀.det = K₀.subtype 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, map_one]
    exact hgd
  let A : GL (Fin 3) K₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero M₀ (by rw [hdet]; exact one_ne_zero)
  have hAm : (A : Matrix (Fin 3) (Fin 3) K₀) = M₀ := rfl
  have hA : A ∈ SUid (unitaryInvolution K₀ ℓ f₀) 3 := by
    rw [mem_SUid, hAm]
    refine ⟨hdet, ?_⟩
    apply Matrix.map_injective (f := K₀.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul, conjTr, Matrix.transpose_map, Matrix.map_map, hmap,
      Matrix.map_one _ (map_zero _) (map_one _)]
    have hbarm : (M₀.map (fun x => K₀.subtype (unitaryInvolution K₀ ℓ f₀ x))) = gm.map h.bar := by
      ext i j
      exact (bar_coe_fixed hbar _).symm
    rw [show (K₀.subtype ∘ unitaryInvolution K₀ ℓ f₀) =
        fun x => K₀.subtype (unitaryInvolution K₀ ℓ f₀ x) from rfl, hbarm]
    rw [Units.val_one, Matrix.mul_one] at hgu
    exact hgu
  have hblk : (⟨A, hA⟩ : Su K₀ ℓ f₀ 3) ∈ coordBlockSU K₀ ℓ f₀ blk := by
    rw [mem_coordBlockSU_iff]
    intro i j hij
    apply Subtype.val_injective
    have := mem_blockU_iff.1 hg i j hij
    change gm i j = _ at this
    change gm i j = ((if i = j then 1 else 0 : K₀) : K)
    rw [this]
    split_ifs <;> rfl
  refine ⟨⟨A, hA⟩, hblk, ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem isQuasisimple_blockZ
    (hK0 : Nat.card (semilinearFixedSubfield σ) = (ℓ ^ f₀) ^ 2) (hq0 : 5 ≤ ℓ ^ f₀) :
    CFSG.Open.IsQuasisimple ↥(blockZ h hbar) :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.equivMapOfInjective _ _ (embSU_injective hbar)).symm
    (isQuasisimple_coordBlockSU hK0 hq0 (by decide))

end Block

section Fix

variable (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀))
include hbar

theorem primeFormFieldSU_eq_of_mem_blockZ {g : ↥(SG h)} (hg : g ∈ blockZ h hbar) :
    primeFormFieldSU h (isPrimeFormGram_one (n := 3)) σ g = g := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [primeFormFieldSU_apply]
  exact fixed_of_mem_blockZ hbar hg i j

theorem JU_inf_fixSubgroup_eq :
    JU h ⊓ fixSubgroup (fieldAut h σ) = (blockZ h hbar).map (projU h) := by
  apply le_antisymm
  · rintro x ⟨⟨g, hg, rfl⟩, hfix⟩
    have hfix' : fieldAut h σ (projU h g) = projU h g := hfix
    rw [fieldAut_projU] at hfix'
    replace hfix := hfix'
    obtain ⟨c, hc⟩ := exists_scalar_of_projU_eq hfix
    have hg' := mem_blockU_iff.1 hg
    have h00 := congrFun (congrFun hc 0) 0
    rw [mul_diagonal, primeFormFieldSU_apply, hg' 0 0 (Or.inl (by simp [mem_blk])), if_pos rfl,
      map_one, one_mul] at h00
    refine ⟨g, mem_blockZ_of_fixed hbar hg fun i j => ?_, rfl⟩
    have hij := congrFun (congrFun hc i) j
    rw [mul_diagonal, primeFormFieldSU_apply, ← h00, mul_one] at hij
    exact hij.symm
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨g, blockZ_le_blockU hbar hg, rfl⟩, ?_⟩
    show fieldAut h σ (projU h g) = projU h g
    rw [fieldAut_projU, primeFormFieldSU_eq_of_mem_blockZ hbar hg]

theorem glaPLayer_JU_inf_fixSubgroup_ne_bot
    (hK0 : Nat.card (semilinearFixedSubfield σ) = (ℓ ^ f₀) ^ 2) (hq0 : 5 ≤ ℓ ^ f₀) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζn : h.bar ζ * ζ = 1)
    (hζσ : σ ζ = ζ) :
    GLAPLayer p (JU h ⊓ fixSubgroup (fieldAut h σ)) ≠ ⊥ := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  rw [JU_inf_fixSubgroup_eq hbar]
  set L := (blockZ h hbar).map (projU h) with hL
  have hLe : ↥(blockZ h hbar) ≃* ↥L := mapProjUEquiv zero_not_mem_blk _ (blockZ_le_blockU hbar)
  have hqs : CFSG.Open.IsQuasisimple ↥L :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv hLe.symm
      (isQuasisimple_blockZ hbar hK0 hq0)
  have hx : diagU h ![1, ζ, ζ⁻¹] (norm_diagBlk hζn) (prod_diagBlk hζ0) ∈ blockZ h hbar :=
    mem_blockZ_of_fixed hbar (diagU_blk_mem_blockU hζn hζ0) fun i j => by
      rw [coe_diagU]
      by_cases hij : i = j
      · subst hij
        fin_cases i <;> simp [hζσ, map_inv₀]
      · rw [diagonal_apply_ne _ hij, map_zero]
  have hy : swapBlk h ∈ blockZ h hbar :=
    mem_blockZ_of_fixed hbar swapBlk_mem_blockU fun i j => by
      rw [coe_swapBlk]
      fin_cases i <;> fin_cases j <;> simp [swapMat]
  have hdvd : p ∣ Nat.card (↥(blockZ h hbar) ⧸ Subgroup.center ↥(blockZ h hbar)) :=
    CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute hp hx hy
      (diagU_blk_pow hp hp2 hζ hζn) (diagU_blk_mul_swapBlk_ne hp hp2 hζ hζn)
  have hdvd' : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.natCard_quotient_center_congr hLe]
    exact hdvd
  have hN : (L.subgroupOf L).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple hp le_rfl hN hqs
    hdvd'

end Fix

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
