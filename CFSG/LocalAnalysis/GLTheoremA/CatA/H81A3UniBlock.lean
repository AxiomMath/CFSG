module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinBlock
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.UniA3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.GLTheoremA.H81.LinA3 CFSG.ClassicalInvolution.Phan
open scoped commutatorElement

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

abbrev SG : Subgroup (GL (Fin 4) K) := gramSU h (idGram K 4)

abbrev PS : Type := primeFormP h (idGram K 4)

noncomputable abbrev projU : ↥(SG h) →* PS h := QuotientGroup.mk' _

@[expose] def toSLU : ↥(SG h) →* SpecialLinearGroup (Fin 4) K where
  toFun g := ⟨((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), (mem_gramSU.1 g.2).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def blockU (I : Finset (Fin 4)) : Subgroup ↥(SG h) :=
  (coordBlockSL K I).comap (toSLU h)

@[expose] noncomputable def diagU (d : Fin 4 → K) (hn : ∀ i, h.bar (d i) * d i = 1)
    (hd : ∏ i, d i = 1) : ↥(SG h) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal d)
      (by rw [det_diagonal, hd]; exact one_ne_zero), mem_gramSU.2 ⟨by
    change ((diagonal d).map h.bar)ᵀ * ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      diagonal d = ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    rw [Units.val_one, diagonal_map (map_zero _), diagonal_transpose, Matrix.mul_one,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hn i, by
    change (diagonal d).det = 1
    rw [det_diagonal, hd]⟩⟩

variable {h}

theorem idGram_eq : idGram K 4 = 1 := Units.val_one

theorem coe_toSLU (g : ↥(SG h)) :
    ((toSLU h g : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  rfl

variable (h) in
theorem toSLU_injective : Function.Injective (toSLU h) := fun a b hab =>
  Subtype.ext (Units.ext (congrArg (fun x : SpecialLinearGroup (Fin 4) K =>
    (x : Matrix (Fin 4) (Fin 4) K)) hab))

theorem mem_blockU_iff {I : Finset (Fin 4)} {g : ↥(SG h)} :
    g ∈ blockU h I ↔ ∀ i j, (i ∉ I ∨ j ∉ I) →
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = if i = j then 1 else 0 :=
  mem_coordBlockSL_iff

theorem coe_diagU (d : Fin 4 → K) (hn : ∀ i, h.bar (d i) * d i = 1) (hd : ∏ i, d i = 1) :
    (((diagU h d hn hd : ↥(SG h)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal d :=
  rfl

theorem toSLU_diagU (d : Fin 4 → K) (hn : ∀ i, h.bar (d i) * d i = 1) (hd : ∏ i, d i = 1) :
    toSLU h (diagU h d hn hd) = diagSL d hd :=
  rfl

theorem mem_centralizer_iff_toSLU {x g : ↥(SG h)} :
    g ∈ Subgroup.centralizer ({x} : Set ↥(SG h)) ↔
      toSLU h g ∈ Subgroup.centralizer ({toSLU h x} : Set (SpecialLinearGroup (Fin 4) K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
    ← map_mul, (toSLU_injective h).eq_iff]

variable {d : Fin 4 → K} {hn : ∀ i, h.bar (d i) * d i = 1} {hd : ∏ i, d i = 1}

theorem blockU_le_centralizer {I : Finset (Fin 4)} (hI : ∀ i ∈ I, ∀ j ∈ I, d i = d j) :
    blockU h I ≤ Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h)) := by
  intro g hg
  rw [mem_centralizer_iff_toSLU, toSLU_diagU]
  exact coordBlockSL_le_centralizer_diagSL' hI hg

theorem toSLU_mem_cent {g : ↥(SG h)}
    (hg : g ∈ Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h))) :
    toSLU h g ∈ cent d hd := by
  rw [mem_centralizer_iff_toSLU, toSLU_diagU] at hg
  exact hg

variable (hd0 : ∀ j, j ≠ 0 → d 0 ≠ d j)
include hd0

theorem commutator_centralizer_le_blockU :
    ⁅Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h)),
      Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h))⁆ ≤ blockU h blockJ := by
  rw [Subgroup.commutator_le]
  intro g hg k hk
  change toSLU h ⁅g, k⁆ ∈ coordBlockSL K blockJ
  rw [map_commutatorElement]
  exact commutator_centralizer_le_coordBlockSL hd0
    (Subgroup.commutator_mem_commutator (toSLU_mem_cent hg) (toSLU_mem_cent hk))

theorem blockU_normal (hJ : ∀ i j, i ≠ 0 → j ≠ 0 → d i = d j) :
    ((blockU h blockJ).subgroupOf
      (Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h)))).Normal := by
  refine ⟨fun n hnm g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hnm ⊢
  change toSLU h ((g : ↥(SG h)) * n * (g : ↥(SG h))⁻¹) ∈ coordBlockSL K blockJ
  rw [map_mul, map_mul, map_inv]
  have hN := coordBlockSL_normal (hd := hd) hd0 hJ
  have h1 : (⟨toSLU h n, coordBlockSL_le_centralizer_diagSL hJ hnm⟩ : cent d hd) ∈
      (coordBlockSL K blockJ).subgroupOf (cent d hd) := hnm
  exact hN.conj_mem _ h1 ⟨toSLU h g, toSLU_mem_cent g.2⟩

omit hd0

section Su

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

variable (h) in
theorem suid_eq_gramSU : SUid (unitaryInvolution K ℓ f) 4 = SG h := by
  ext B
  rw [CFSG.LieType.Universal.Unitary.mem_SUid, mem_gramSU, idGram_eq, Matrix.mul_one, conjTr]
  have hmap : (B : Matrix (Fin 4) (Fin 4) K).map (unitaryInvolution K ℓ f) =
      (B : Matrix (Fin 4) (Fin 4) K).map h.bar := by
    ext i j
    rw [map_apply, map_apply, unitaryInvolution_apply, UnitaryFieldData.bar_apply]
  rw [hmap]
  exact And.comm

variable (h) in
@[expose] noncomputable def suEquiv : Su K ℓ f 4 ≃* ↥(SG h) :=
  MulEquiv.subgroupCongr (suid_eq_gramSU h)

theorem blockU_eq_map (I : Finset (Fin 4)) :
    blockU h I = (coordBlockSU K ℓ f I).map (suEquiv h).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_blockU_iff, mem_coordBlockSU_iff]
  rfl

theorem isQuasisimple_blockU (hK : Nat.card K = (ℓ ^ f) ^ 2) (hq : 5 ≤ ℓ ^ f)
    {I : Finset (Fin 4)} (hI : 2 ≤ I.card) : CFSG.Open.IsQuasisimple ↥(blockU h I) := by
  rw [blockU_eq_map]
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.equivMapOfInjective _ _ (suEquiv h).injective).symm
    (isQuasisimple_coordBlockSU hK hq hI)

end Su

end CFSG.LocalAnalysis.GLTheoremA.H81.UniA3
