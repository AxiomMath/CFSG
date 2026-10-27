module

public import CFSG.LocalAnalysis.ComponentClassification.GS82L34G1
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigCtx
public import CFSG.GH74.GLS.C3.Layer1.Defs
public import CFSG.GH74.GLS.Stage2.Final.LayerLiftN
public import CFSG.GH74.Generic.BProg.B1.PilotS1ThreeFacts
public import CFSG.GH74.Generic.BProg.B1.PilotS3Facts
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TFrameL
public import CFSG.Sporadic.ThSchreier.Max3Action
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUg
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerOut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCUb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILi
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUk
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUl
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4ProdU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4SteinU
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigQuot
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NoPump
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7OS1U
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3g
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB10
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0Defs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIRed
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Final
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalB
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82SecondCentral
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Lift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBSections
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3B
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecLinearHigh
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPair
public import CFSG.LocalAnalysis.ComponentClassification.TBLitAssembly
public import CFSG.LocalAnalysis.OddStandard.Solomon75Inputs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Defs
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.ThSchreier.Max3ActionBase1
public import CFSG.Sporadic.ThSchreier.Rigidity
public import Certificates.Certificate10091Base

public section

namespace CFSG.ComponentClassification.GSThmB.L34DP

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

@[expose] noncomputable def blockImage : Subgroup (projectiveSL 4 (ZMod 7)) :=
  closure (Set.range fun p : SL(2, ZMod 7) × SL(2, ZMod 7) => proj 4 (ZMod 7) (blk p.1 p.2))

local notation "e4" => (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)
local notation "e4s" => (Equiv.symm (finSumFinEquiv (m := 2) (n := 2)))
local notation "M4" => Matrix (Fin 4) (Fin 4) (ZMod 7)
local notation "M2" => Matrix (Fin 2) (Fin 2) (ZMod 7)
local notation "π" => proj 4 (ZMod 7)
local notation "G4" => projectiveSL 4 (ZMod 7)

theorem slext {n : ℕ} {A B : SL(n, ZMod 7)}
    (h : (A : Matrix (Fin n) (Fin n) (ZMod 7)) = (B : Matrix (Fin n) (Fin n) (ZMod 7))) :
    A = B := Subtype.ext h

theorem coe_blk (a b : SL(2, ZMod 7)) :
    ((blk a b : SL(4, ZMod 7)) : M4) = reindex e4 e4 (fromBlocks (a : M2) 0 0 (b : M2)) := by
  rfl

theorem reindex_mul_reindex (A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 7)) :
    reindex e4 e4 A * reindex e4 e4 B = reindex e4 e4 (A * B) := by
  simp only [reindex_apply, submatrix_mul_equiv]

theorem blk_mul (a b a' b' : SL(2, ZMod 7)) : blk (a * a') (b * b') = blk a b * blk a' b' := by
  apply slext
  show (blk (a * a') (b * b') : M4) = (blk a b : M4) * (blk a' b' : M4)
  rw [coe_blk, coe_blk, coe_blk, reindex_mul_reindex, fromBlocks_multiply]
  simp

theorem blk_one : blk 1 1 = 1 := by
  apply slext
  simp only [coe_blk, SpecialLinearGroup.coe_one, fromBlocks_one]
  simp [reindex_apply]

@[expose] noncomputable def blkHom : SL(2, ZMod 7) × SL(2, ZMod 7) →* SL(4, ZMod 7) where
  toFun p := blk p.1 p.2
  map_one' := blk_one
  map_mul' p q := blk_mul p.1 p.2 q.1 q.2

theorem blockImage_eq : blockImage = ((proj 4 (ZMod 7)).comp blkHom).range := by
  rw [blockImage]
  have : (Set.range fun p : SL(2, ZMod 7) × SL(2, ZMod 7) => proj 4 (ZMod 7) (blk p.1 p.2)) =
      (((proj 4 (ZMod 7)).comp blkHom).range : Set G4) := by
    rw [MonoidHom.coe_range]; rfl
  rw [this, closure_eq]

theorem mem_blockImage {x : G4} : x ∈ blockImage ↔ ∃ a b, π (blk a b) = x := by
  rw [blockImage_eq, MonoidHom.mem_range]
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨a, b, rfl⟩; exact ⟨(a, b), rfl⟩

theorem reindex_symm_reindex (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 7)) :
    reindex e4s e4s (reindex e4 e4 A) = A := by
  simp [reindex_apply]

theorem coe_dSL_blocks : (dSL : M4) = reindex e4 e4 (fromBlocks (-1) 0 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem zmod7_zero_of_neg {x : ZMod 7} (h : -x = x) : x = 0 := by revert x; decide
theorem zmod7_zero_of_neg' {x : ZMod 7} (h : x = -x) : x = 0 := by revert x; decide

theorem blk_comm_dSL (a b : SL(2, ZMod 7)) : blk a b * dSL = dSL * blk a b := by
  apply slext
  show (blk a b : M4) * (dSL : M4) = (dSL : M4) * (blk a b : M4)
  rw [coe_blk, coe_dSL_blocks, reindex_mul_reindex, reindex_mul_reindex, fromBlocks_multiply,
    fromBlocks_multiply]
  simp

theorem exists_blocks_of_comm {g : SL(4, ZMod 7)} (h : g * dSL = dSL * g) :
    ∃ A B : M2, (g : M4) = reindex e4 e4 (fromBlocks A 0 0 B) := by
  have h' : (g : M4) * (dSL : M4) = (dSL : M4) * (g : M4) := by
    have := congrArg (fun x : SL(4, ZMod 7) => (x : M4)) h
    exact this
  rw [coe_dSL] at h'
  have hij : ∀ i j, (g : M4) i j * ![-1, -1, 1, 1] j = ![-1, -1, 1, 1] i * (g : M4) i j := by
    intro i j
    have := congrFun (congrFun h' i) j
    rwa [mul_diagonal, diagonal_mul] at this
  refine ⟨toBlocks₁₁ (reindex e4s e4s (g : M4)),
    toBlocks₂₂ (reindex e4s e4s (g : M4)), ?_⟩
  ext i j
  have hh := hij i j
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (simp at hh; first
        | exact (zmod7_zero_of_neg hh).trans rfl
        | exact (zmod7_zero_of_neg' hh).trans rfl
        | exact (zmod7_zero_of_neg hh.symm).trans rfl
        | exact (zmod7_zero_of_neg' hh.symm).trans rfl)

theorem mem_cent_iff {g : SL(4, ZMod 7)} : g ∈ centralizer {dSL} ↔ g * dSL = dSL * g :=
  mem_centralizer_singleton_iff

@[expose] noncomputable def topDet (g : M4) : ZMod 7 := det (toBlocks₁₁ (reindex e4s e4s g))

theorem topDet_blocks (A B : M2) : topDet (reindex e4 e4 (fromBlocks A 0 0 B)) = det A := by
  rw [topDet, reindex_symm_reindex, toBlocks_fromBlocks₁₁]

@[expose] noncomputable def topDetHom : centralizer ({dSL} : Set (SL(4, ZMod 7))) →* ZMod 7 where
  toFun g := topDet (g : SL(4, ZMod 7))
  map_one' := by
    show topDet (((1 : SL(4, ZMod 7)) : M4)) = 1
    have : ((1 : SL(4, ZMod 7)) : M4) = reindex e4 e4 (fromBlocks 1 0 0 1) := by
      rw [fromBlocks_one]; simp [reindex_apply]
    rw [this, topDet_blocks, det_one]
  map_mul' g h := by
    obtain ⟨A, B, hA⟩ := exists_blocks_of_comm (mem_cent_iff.1 g.2)
    obtain ⟨A', B', hA'⟩ := exists_blocks_of_comm (mem_cent_iff.1 h.2)
    show topDet (((g : SL(4, ZMod 7)) * (h : SL(4, ZMod 7)) : SL(4, ZMod 7)) : M4) =
      topDet ((g : SL(4, ZMod 7)) : M4) * topDet ((h : SL(4, ZMod 7)) : M4)
    have : (((g : SL(4, ZMod 7)) * (h : SL(4, ZMod 7)) : SL(4, ZMod 7)) : M4) =
        ((g : SL(4, ZMod 7)) : M4) * ((h : SL(4, ZMod 7)) : M4) := rfl
    rw [this, hA, hA', reindex_mul_reindex, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [topDet_blocks, topDet_blocks, topDet_blocks, det_mul]

theorem exists_blk_of_topDet {g : SL(4, ZMod 7)} (h : g * dSL = dSL * g) (ht : topDet g = 1) :
    ∃ a b, blk a b = g := by
  obtain ⟨A, B, hA⟩ := exists_blocks_of_comm h
  have hdet : det A * det B = 1 := by
    have := g.2
    rw [hA, det_reindex_self, det_fromBlocks_zero₂₁] at this
    exact this
  rw [hA, topDet_blocks] at ht
  have hB : det B = 1 := by rw [ht, one_mul] at hdet; exact hdet
  refine ⟨⟨A, ht⟩, ⟨B, hB⟩, ?_⟩
  apply slext
  exact (coe_blk _ _).trans hA.symm

section Abstract

variable {H : Type*} [Group H] {Z : Subgroup H}

theorem commutator_mul_central_left {g k z : H} (hz : z ∈ center H) : ⁅g * z, k⁆ = ⁅g, k⁆ := by
  have h1 : z * k * z⁻¹ = k := by rw [← (mem_center_iff.1 hz k), mul_inv_cancel_right]
  calc ⁅g * z, k⁆ = g * (z * k * z⁻¹) * g⁻¹ * k⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅g, k⁆ := by rw [h1, commutatorElement_def]

theorem commutator_mul_central_right {g k z : H} (hz : z ∈ center H) : ⁅g, k * z⁆ = ⁅g, k⁆ := by
  have h1 : z * g⁻¹ * z⁻¹ = g⁻¹ := by rw [← (mem_center_iff.1 hz g⁻¹), mul_inv_cancel_right]
  calc ⁅g, k * z⁆ = g * k * (z * g⁻¹ * z⁻¹) * k⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅g, k⁆ := by rw [h1, commutatorElement_def]

theorem conj_eq_mul_central {d g : H} :
    d⁻¹ * g * d = g * ((d * g)⁻¹ * (g * d)) := by group

theorem commutator_comm_of_central (hZ : Z ≤ center H) {d g h : H}
    (hg : (d * g)⁻¹ * (g * d) ∈ Z) (hh : (d * h)⁻¹ * (h * d) ∈ Z) :
    ⁅g, h⁆ * d = d * ⁅g, h⁆ := by
  have key : d⁻¹ * ⁅g, h⁆ * d = ⁅g, h⁆ := by
    calc d⁻¹ * ⁅g, h⁆ * d = ⁅d⁻¹ * g * d, d⁻¹ * h * d⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅g, h⁆ := by
          rw [conj_eq_mul_central, conj_eq_mul_central, commutator_mul_central_left (hZ hg),
            commutator_mul_central_right (hZ hh)]
  calc ⁅g, h⁆ * d = d * (d⁻¹ * ⁅g, h⁆ * d) := by group
    _ = d * ⁅g, h⁆ := by rw [key]

theorem conj_comm_of_central (hZ : Z ≤ center H) {d g h : H}
    (hh : (d * h)⁻¹ * (h * d) ∈ Z) (hg : g * d = d * g) :
    (h * g * h⁻¹) * d = d * (h * g * h⁻¹) := by
  set z := (d * h)⁻¹ * (h * d) with hzdef
  have hzc := hZ hh
  have hw : h⁻¹ * d * h = d * z⁻¹ := by rw [hzdef]; group
  have hwg : (h⁻¹ * d * h) * g = g * (h⁻¹ * d * h) := by
    rw [hw, mul_assoc, (mem_center_iff.1 (inv_mem hzc) g).symm, ← mul_assoc, ← hg, mul_assoc]
  calc (h * g * h⁻¹) * d = h * (g * (h⁻¹ * d * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * d * h) * g) * h⁻¹ := by rw [hwg]
    _ = d * (h * g * h⁻¹) := by group

end Abstract

theorem proj_mem_Cd {g : SL(4, ZMod 7)} :
    π g ∈ centralizer ({π dSL} : Set G4) ↔ (dSL * g)⁻¹ * (g * dSL) ∈ scalars 4 (ZMod 7) := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, eq_comm, proj_eq_proj_iff]

@[expose] noncomputable def X1 : Subgroup G4 := (centralizer ({dSL} : Set (SL(4, ZMod 7)))).map π

theorem commutator_Cd_le :
    ⁅centralizer ({π dSL} : Set G4), centralizer ({π dSL} : Set G4)⁆ ≤ X1 := by
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl⟩ := proj_surjective 4 (ZMod 7) x
  obtain ⟨h, rfl⟩ := proj_surjective 4 (ZMod 7) y
  rw [← map_commutatorElement]
  exact mem_map_of_mem _ (mem_cent_iff.2 (commutator_comm_of_central
    (scalars_le_center 4 (ZMod 7)) (proj_mem_Cd.1 hx) (proj_mem_Cd.1 hy)))

theorem conj_mem_X1 {x k : G4} (hx : x ∈ centralizer ({π dSL} : Set G4)) (hk : k ∈ X1) :
    x * k * x⁻¹ ∈ X1 := by
  obtain ⟨g, hg, rfl⟩ := hk
  obtain ⟨h, rfl⟩ := proj_surjective 4 (ZMod 7) x
  rw [← map_inv, ← map_mul, ← map_mul]
  exact mem_map_of_mem _ (mem_cent_iff.2 (conj_comm_of_central
    (scalars_le_center 4 (ZMod 7)) (proj_mem_Cd.1 hx) (mem_cent_iff.1 hg)))

theorem map_commutator_eq_one {K M : Type*} [Group K] [CommMonoid M] (f : K →* M) (a b : K) :
    f ⁅a, b⁆ = 1 := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul]
  calc f a * f b * f a⁻¹ * f b⁻¹ = f (a * a⁻¹) * f (b * b⁻¹) := by
        rw [map_mul, map_mul]; ac_rfl
    _ = 1 := by simp

theorem commutator_X1_le : ⁅X1, X1⁆ ≤ blockImage := by
  rw [commutator_le]
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
  rw [← map_commutatorElement]
  have hc : ⁅g, h⁆ ∈ centralizer ({dSL} : Set (SL(4, ZMod 7))) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have ht : topDet ((⁅g, h⁆ : SL(4, ZMod 7)) : M4) = 1 := by
    have := map_commutator_eq_one topDetHom ⟨g, hg⟩ ⟨h, hh⟩
    exact this
  obtain ⟨a, b, hab⟩ := exists_blk_of_topDet (mem_cent_iff.1 hc) ht
  exact mem_blockImage.2 ⟨a, b, by rw [hab]⟩

@[expose] noncomputable def beta1 : SL(2, ZMod 7) →* G4 := (proj 4 (ZMod 7)).comp (blkHom.comp (MonoidHom.inl _ _))

@[expose] noncomputable def beta2 : SL(2, ZMod 7) →* G4 := (proj 4 (ZMod 7)).comp (blkHom.comp (MonoidHom.inr _ _))

theorem beta1_apply (a : SL(2, ZMod 7)) : beta1 a = π (blk a 1) := by rfl
theorem beta2_apply (b : SL(2, ZMod 7)) : beta2 b = π (blk 1 b) := by rfl

theorem blk_one_right_eq_one {a : SL(2, ZMod 7)} (h : blk a 1 ∈ scalars 4 (ZMod 7)) : a = 1 := by
  obtain ⟨c, -, hA⟩ := mem_scalars.1 h
  have h33 : ((blk a 1 : SL(4, ZMod 7)) : M4) 3 3 = 1 := by
    rw [coe_blk]; simp [reindex_apply]; rfl
  have hc : (c : ZMod 7) = 1 := by
    rw [hA] at h33; simpa using h33
  have hM : ((blk a 1 : SL(4, ZMod 7)) : M4) = 1 := by rw [hA, hc]; simp
  have ha : (a : M2) = toBlocks₁₁ (reindex e4s e4s ((blk a 1 : SL(4, ZMod 7)) : M4)) := by
    rw [coe_blk, reindex_symm_reindex, toBlocks_fromBlocks₁₁]
  apply Subtype.ext
  rw [ha, hM]
  ext i j
  simp [toBlocks₁₁, reindex_apply, one_apply]

theorem blk_one_left_eq_one {b : SL(2, ZMod 7)} (h : blk 1 b ∈ scalars 4 (ZMod 7)) : b = 1 := by
  obtain ⟨c, -, hA⟩ := mem_scalars.1 h
  have h00 : ((blk 1 b : SL(4, ZMod 7)) : M4) 0 0 = 1 := by
    rw [coe_blk]; simp [reindex_apply]; rfl
  have hc : (c : ZMod 7) = 1 := by
    rw [hA] at h00; simpa using h00
  have hM : ((blk 1 b : SL(4, ZMod 7)) : M4) = 1 := by rw [hA, hc]; simp
  have hb : (b : M2) = toBlocks₂₂ (reindex e4s e4s ((blk 1 b : SL(4, ZMod 7)) : M4)) := by
    rw [coe_blk, reindex_symm_reindex, toBlocks_fromBlocks₂₂]
  apply Subtype.ext
  rw [hb, hM]
  ext i j
  simp [toBlocks₂₂, reindex_apply, one_apply]

theorem beta1_injective : Function.Injective beta1 := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [beta1_apply, proj_eq_one_iff] at ha
  exact blk_one_right_eq_one ha

theorem beta2_injective : Function.Injective beta2 := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [beta2_apply, proj_eq_one_iff] at ha
  exact blk_one_left_eq_one ha

@[expose] noncomputable def B1 : Subgroup G4 := beta1.range
@[expose] noncomputable def B2 : Subgroup G4 := beta2.range

@[expose] noncomputable def equivB1 : ↥B1 ≃* SL(2, ZMod 7) := (MonoidHom.ofInjective beta1_injective).symm
@[expose] noncomputable def equivB2 : ↥B2 ≃* SL(2, ZMod 7) := (MonoidHom.ofInjective beta2_injective).symm

theorem card_zmod7 : Nat.card (ZMod 7) = 7 := Nat.card_zmod 7

instance : Group.IsPerfect SL(2, ZMod 7) :=
  (GH74.Generic.BProg.B1.PilotS3.isQuasisimple_sl2 (F := ZMod 7) (by rw [card_zmod7]; norm_num)).1

theorem B1_perfect : ⁅B1, B1⁆ = B1 := by
  haveI : Group.IsPerfect B1 := Group.IsPerfect.range beta1
  exact Subgroup.commutator_eq_self

theorem B2_perfect : ⁅B2, B2⁆ = B2 := by
  haveI : Group.IsPerfect B2 := Group.IsPerfect.range beta2
  exact Subgroup.commutator_eq_self

theorem proj_blk_mem_X1 (a b : SL(2, ZMod 7)) : π (blk a b) ∈ X1 :=
  mem_map_of_mem _ (mem_cent_iff.2 (blk_comm_dSL a b))

theorem B1_le_X1 : B1 ≤ X1 := by
  rintro _ ⟨a, rfl⟩; rw [beta1_apply]; exact proj_blk_mem_X1 a 1

theorem B2_le_X1 : B2 ≤ X1 := by
  rintro _ ⟨a, rfl⟩; rw [beta2_apply]; exact proj_blk_mem_X1 1 a

theorem proj_blk_eq (a b : SL(2, ZMod 7)) : π (blk a b) = beta1 a * beta2 b := by
  rw [beta1_apply, beta2_apply, ← map_mul, ← blk_mul, mul_one, one_mul]

theorem beta_comm (a b : SL(2, ZMod 7)) : beta1 a * beta2 b = beta2 b * beta1 a := by
  rw [beta1_apply, beta2_apply, ← map_mul, ← map_mul, ← blk_mul, ← blk_mul, mul_one, one_mul,
    mul_one, one_mul]

theorem blockImage_le_sup : blockImage ≤ B1 ⊔ B2 := by
  rw [blockImage, closure_le]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  show π (blk a b) ∈ B1 ⊔ B2
  rw [proj_blk_eq]
  exact mul_mem (mem_sup_left ⟨a, rfl⟩) (mem_sup_right ⟨b, rfl⟩)

theorem B1_le_blockImage : B1 ≤ blockImage := by
  rintro _ ⟨a, rfl⟩; exact mem_blockImage.2 ⟨a, 1, (beta1_apply a).symm⟩

theorem B2_le_blockImage : B2 ≤ blockImage := by
  rintro _ ⟨a, rfl⟩; exact mem_blockImage.2 ⟨1, a, (beta2_apply a).symm⟩

theorem blockImage_eq_commutator : blockImage = ⁅X1, X1⁆ := by
  refine le_antisymm ?_ commutator_X1_le
  refine blockImage_le_sup.trans (sup_le ?_ ?_)
  · rw [← B1_perfect]; exact commutator_mono B1_le_X1 B1_le_X1
  · rw [← B2_perfect]; exact commutator_mono B2_le_X1 B2_le_X1

theorem conj_mem_blockImage {x b : G4} (hx : x ∈ centralizer ({π dSL} : Set G4))
    (hb : b ∈ blockImage) : x * b * x⁻¹ ∈ blockImage := by
  rw [blockImage_eq_commutator] at hb ⊢
  have hle : X1.map (MulAut.conj x).toMonoidHom ≤ X1 := by
    rintro _ ⟨k, hk, rfl⟩
    exact conj_mem_X1 hx hk
  have := mem_map_of_mem (MulAut.conj x).toMonoidHom hb
  rw [map_commutator] at this
  exact commutator_mono hle hle this

theorem blockImage_le_Cd : blockImage ≤ centralizer ({π dSL} : Set G4) := by
  rw [blockImage, closure_le]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  show π (blk a b) ∈ centralizer ({π dSL} : Set G4)
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, blk_comm_dSL]

theorem conj_mem_B1 {x b : G4} (hx : x ∈ blockImage) (hb : b ∈ B1) : x * b * x⁻¹ ∈ B1 := by
  obtain ⟨p, q, rfl⟩ := mem_blockImage.1 hx
  obtain ⟨a, rfl⟩ := hb
  refine ⟨p * a * p⁻¹, ?_⟩
  rw [proj_blk_eq, _root_.mul_inv_rev, map_mul, map_mul, map_inv,
    mul_assoc (beta1 p) (beta2 q) (beta1 a), ← beta_comm a q]
  group

theorem conj_mem_B2 {x b : G4} (hx : x ∈ blockImage) (hb : b ∈ B2) : x * b * x⁻¹ ∈ B2 := by
  obtain ⟨p, q, rfl⟩ := mem_blockImage.1 hx
  obtain ⟨a, rfl⟩ := hb
  refine ⟨q * a * q⁻¹, ?_⟩
  rw [proj_blk_eq, beta_comm p q, _root_.mul_inv_rev, map_mul, map_mul, map_inv,
    mul_assoc (beta2 q) (beta1 p) (beta2 a), beta_comm p a]
  group

theorem subnormal_of_chain {X : Type*} [Group X] {B S C : Subgroup X} (hBS : B ≤ S) (hSC : S ≤ C)
    (hB : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B) (hS : ∀ c ∈ C, ∀ s ∈ S, c * s * c⁻¹ ∈ S) :
    (B.subgroupOf C).IsSubnormal := by
  have hSn : (S.subgroupOf C).Normal :=
    ⟨fun n hn g => mem_subgroupOf.2 (hS g.1 g.2 n.1 (mem_subgroupOf.1 hn))⟩
  refine IsSubnormal.step _ (S.subgroupOf C) (subgroupOf_mono C hBS) hSn.isSubnormal
    ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
  exact hB ((g : C) : X) (mem_subgroupOf.1 g.2) _ hn

theorem isPCompIn_of_subnormal_sl2 {X : Type*} [Group X] [Finite X] {B C : Subgroup X}
    (hBC : B ≤ C) (hsub : (B.subgroupOf C).IsSubnormal) (e : ↥B ≃* SL(2, ZMod 7)) :
    GH74.GLS.IsPCompIn 2 C B := by
  refine ⟨hBC, ?_⟩
  set M := B.subgroupOf C with hM
  have e' : ↥M ≃* SL(2, ZMod 7) := (subgroupOfEquivOfLe hBC).trans e
  have hq : IsQuasisimple ↥M :=
    GH74.Generic.BProg.B1.PilotS3.isQuasisimple_of_equiv_sl2 (by rw [card_zmod7]; norm_num) e'
  have hinf := GH74.Generic.BProg.B1.PilotS1.inf_pPrimeCore_eq_one_of_sl2 (H := ↥C) (M := M)
    (by rw [card_zmod7]; decide) (by rw [card_zmod7]; norm_num) e'
  have hinj : ∀ z ∈ M, z ∈ (QuotientGroup.mk' (pPrimeCore 2 ↥C)).ker → z = 1 := fun z hz hzk =>
    hinf z hz (by rwa [QuotientGroup.ker_mk'] at hzk)
  refine ⟨M.map (QuotientGroup.mk' (pPrimeCore 2 ↥C)), ⟨?_, ?_⟩, hsub, rfl, ?_⟩
  · exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (CFSG.ClassicalInvolution.Models.Transfer.mulEquivMap hinj)).1 hq
  · exact hsub.map (QuotientGroup.mk'_surjective _)
  · intro J hJ _ hmap
    refine hJ.not_ge fun m hm => ?_
    have hm' : QuotientGroup.mk' (pPrimeCore 2 ↥C) m ∈ J.map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) := by
      rw [hmap]; exact ⟨m, hm, rfl⟩
    obtain ⟨j, hj, hjm⟩ := hm'
    have hjM : j ∈ M := hJ.le hj
    have h1 : j⁻¹ * m = 1 := by
      apply hinj _ (M.mul_mem (M.inv_mem hjM) hm)
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjm, inv_mul_cancel]
    have : m = j := by rw [← mul_one j, ← h1]; group
    rw [this]; exact hj

local notation "Cd" => centralizer ({proj 4 (ZMod 7) dSL} : Set (projectiveSL 4 (ZMod 7)))

theorem isPCompIn_B1 : GH74.GLS.IsPCompIn 2 Cd B1 :=
  isPCompIn_of_subnormal_sl2 (B1_le_blockImage.trans blockImage_le_Cd)
    (subnormal_of_chain B1_le_blockImage blockImage_le_Cd (fun _ hs _ hb => conj_mem_B1 hs hb)
      (fun _ hc _ hs => conj_mem_blockImage hc hs)) equivB1

theorem isPCompIn_B2 : GH74.GLS.IsPCompIn 2 Cd B2 :=
  isPCompIn_of_subnormal_sl2 (B2_le_blockImage.trans blockImage_le_Cd)
    (subnormal_of_chain B2_le_blockImage blockImage_le_Cd (fun _ hs _ hb => conj_mem_B2 hs hb)
      (fun _ hc _ hs => conj_mem_blockImage hc hs)) equivB2

theorem le_blockImage_of_isPCompIn {L : Subgroup G4} (hL : GH74.GLS.IsPCompIn 2 Cd L) :
    L ≤ blockImage := by
  obtain ⟨hLC, hcomp⟩ := hL
  have hperf := GH74.GLS.Stage2.Final.LayerLiftN.isPerfect_of_isPComponent hcomp
  have hLL : ⁅L, L⁆ = L := by
    have := congrArg (Subgroup.map (Subgroup.subtype Cd)) hperf
    rwa [map_commutator, subgroupOf_map_subtype, inf_of_le_left hLC] at this
  have hX : L ≤ X1 := by
    rw [← hLL]; exact (commutator_mono hLC hLC).trans commutator_Cd_le
  rw [← hLL]
  exact (commutator_mono hX hX).trans commutator_X1_le

theorem pLayer_Cd : GH74.GLS.pLayerOf 2 Cd = blockImage := by
  apply le_antisymm
  · exact sSup_le fun L hL => le_blockImage_of_isPCompIn hL
  · refine blockImage_le_sup.trans (sup_le ?_ ?_)
    · exact le_sSup isPCompIn_B1
    · exact le_sSup isPCompIn_B2

@[expose] def upU : SL(2, ZMod 7) := ⟨!![1, 1; 0, 1], by rw [det_fin_two_of]; decide⟩

theorem sl2_mul_self_of_comm (p : SL(2, ZMod 7)) (h : ∀ a, p * a = a * p) : p * p = 1 := by
  have hu : (p : M2) * (upU : M2) = (upU : M2) * (p : M2) :=
    congrArg (fun x : SL(2, ZMod 7) => (x : M2)) (h upU)
  have hl : (p : M2) * (lowL : M2) = (lowL : M2) * (p : M2) :=
    congrArg (fun x : SL(2, ZMod 7) => (x : M2)) (h lowL)
  have hU : (upU : M2) = !![1, 1; 0, 1] := by rfl
  have hL : (lowL : M2) = !![1, 0; 1, 1] := by rfl
  have hp : (p : M2) = !![(p : M2) 0 0, (p : M2) 0 1; (p : M2) 1 0, (p : M2) 1 1] :=
    eta_fin_two _
  have hdet : (p : M2) 0 0 * (p : M2) 1 1 - (p : M2) 0 1 * (p : M2) 1 0 = 1 := by
    rw [← det_fin_two]; exact p.2
  rw [hU] at hu
  rw [hL] at hl
  have e1 := congrFun (congrFun hu 0) 0
  have e2 := congrFun (congrFun hu 0) 1
  have e3 := congrFun (congrFun hl 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have hz : (p : M2) 1 0 = 0 := e1
  have hy : (p : M2) 0 1 = 0 := e3
  have hw : (p : M2) 1 1 = (p : M2) 0 0 := by linear_combination -e2
  have hx : (p : M2) 0 0 * (p : M2) 0 0 = 1 := by
    rw [hw, hy, hz] at hdet; linear_combination hdet
  apply Subtype.ext
  show (p : M2) * (p : M2) = 1
  rw [hp, hz, hy, hw, mul_fin_two, one_fin_two]
  simp [hx]

theorem sq_eq_one_of_comm {p q : SL(2, ZMod 7)}
    (h1 : ∀ a, π (blk p q) * beta1 a = beta1 a * π (blk p q))
    (h2 : ∀ b, π (blk p q) * beta2 b = beta2 b * π (blk p q)) : π (blk p q) ^ 2 = 1 := by
  have hp : ∀ a, p * a = a * p := by
    intro a
    have := h1 a
    rw [proj_blk_eq] at this
    have key : (beta1 p * beta1 a) * beta2 q = (beta1 a * beta1 p) * beta2 q := by
      calc (beta1 p * beta1 a) * beta2 q = beta1 p * (beta1 a * beta2 q) := by group
        _ = beta1 p * (beta2 q * beta1 a) := by rw [beta_comm a q]
        _ = beta1 p * beta2 q * beta1 a := by group
        _ = beta1 a * (beta1 p * beta2 q) := this
        _ = (beta1 a * beta1 p) * beta2 q := by group
    apply beta1_injective
    rw [map_mul, map_mul]
    exact mul_right_cancel key
  have hq : ∀ b, q * b = b * q := by
    intro b
    have := h2 b
    rw [proj_blk_eq] at this
    have key : beta1 p * (beta2 q * beta2 b) = beta1 p * (beta2 b * beta2 q) := by
      calc beta1 p * (beta2 q * beta2 b) = beta1 p * beta2 q * beta2 b := by group
        _ = beta2 b * (beta1 p * beta2 q) := this
        _ = (beta2 b * beta1 p) * beta2 q := by group
        _ = (beta1 p * beta2 b) * beta2 q := by rw [beta_comm p b]
        _ = beta1 p * (beta2 b * beta2 q) := by group
    apply beta2_injective
    rw [map_mul, map_mul]
    exact mul_left_cancel key
  rw [pow_two, ← map_mul, ← blk_mul, sl2_mul_self_of_comm p hp, sl2_mul_self_of_comm q hq, blk_one,
    map_one]

theorem comm_of_mem_pPrimeCore {n : ↥blockImage} (hn : n ∈ pPrimeCore 2 ↥blockImage)
    {B : Subgroup G4} (hB : B ≤ blockImage) (e : ↥B ≃* SL(2, ZMod 7))
    (hBn : ∀ x b : G4, x ∈ blockImage → b ∈ B → x * b * x⁻¹ ∈ B) {b : G4} (hb : b ∈ B) :
    (n : G4) * b = b * (n : G4) := by
  set b' : ↥blockImage := ⟨b, hB hb⟩
  have e' : ↥(B.subgroupOf blockImage) ≃* SL(2, ZMod 7) := (subgroupOfEquivOfLe hB).trans e
  have hinf := GH74.Generic.BProg.B1.PilotS1.inf_pPrimeCore_eq_one_of_sl2 (H := ↥blockImage)
    (M := B.subgroupOf blockImage) (by rw [card_zmod7]; decide) (by rw [card_zmod7]; norm_num) e'
  have hc1 : ⁅n, b'⁆ ∈ pPrimeCore 2 ↥blockImage := by
    have : ⁅n, b'⁆ = n * (b' * n⁻¹ * b'⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem hn ((CFSG.pPrimeCore_normal (p := 2) (G := ↥blockImage)).conj_mem _ (inv_mem hn) b')
  have hc2 : ⁅n, b'⁆ ∈ B.subgroupOf blockImage := by
    rw [mem_subgroupOf, commutatorElement_def]
    exact mul_mem (hBn _ _ n.2 hb) (inv_mem hb)
  have := commutatorElement_eq_one_iff_mul_comm.1 (hinf _ hc2 hc1)
  exact congrArg Subtype.val this

theorem pPrimeCore_blockImage : pPrimeCore 2 ↥blockImage = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [mem_bot]
  have hcomm1 : ∀ a, (n : G4) * beta1 a = beta1 a * (n : G4) := fun a =>
    comm_of_mem_pPrimeCore hn B1_le_blockImage equivB1 (fun _ _ hx hb => conj_mem_B1 hx hb) ⟨a, rfl⟩
  have hcomm2 : ∀ a, (n : G4) * beta2 a = beta2 a * (n : G4) := fun a =>
    comm_of_mem_pPrimeCore hn B2_le_blockImage equivB2 (fun _ _ hx hb => conj_mem_B2 hx hb) ⟨a, rfl⟩
  obtain ⟨p, q, hpq⟩ := mem_blockImage.1 n.2
  rw [← hpq] at hcomm1 hcomm2
  have hsq := sq_eq_one_of_comm hcomm1 hcomm2
  have hn2 : n ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ← hpq, hsq]; rfl)
  have hodd := GH74.Generic.BProg.B1.PilotS3.odd_orderOf_of_mem_pPrimeCore hn
  have hdvd := orderOf_dvd_of_pow_eq_one hn2
  have : orderOf n = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 this

theorem g1_layer :
    GH74.GLS.pLayerOf 2 (centralizer ({proj 4 (ZMod 7) dSL} : Set (projectiveSL 4 (ZMod 7)))) =
      blockImage ∧ pPrimeCore 2 ↥blockImage = ⊥ :=
  ⟨pLayer_Cd, pPrimeCore_blockImage⟩

theorem proj_mem_cent {d g : SL(4, ZMod 7)} :
    π g ∈ centralizer ({π d} : Set G4) ↔ (d * g)⁻¹ * (g * d) ∈ scalars 4 (ZMod 7) := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, eq_comm, proj_eq_proj_iff]

theorem commutator_cent_le (d : SL(4, ZMod 7)) :
    ⁅centralizer ({π d} : Set G4), centralizer ({π d} : Set G4)⁆ ≤
      (centralizer ({d} : Set (SL(4, ZMod 7)))).map π := by
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl⟩ := proj_surjective 4 (ZMod 7) x
  obtain ⟨h, rfl⟩ := proj_surjective 4 (ZMod 7) y
  rw [← map_commutatorElement]
  exact mem_map_of_mem _ (mem_centralizer_singleton_iff.2 (commutator_comm_of_central
    (scalars_le_center 4 (ZMod 7)) (proj_mem_cent.1 hx) (proj_mem_cent.1 hy)))

theorem pLayer_le_commutator (d : SL(4, ZMod 7)) :
    GH74.GLS.pLayerOf 2 (centralizer ({π d} : Set G4)) ≤
      (⁅centralizer ({d} : Set (SL(4, ZMod 7))), centralizer ({d} : Set (SL(4, ZMod 7)))⁆).map π := by
  refine sSup_le fun L hL => ?_
  obtain ⟨hLC, hcomp⟩ := hL
  have hperf := GH74.GLS.Stage2.Final.LayerLiftN.isPerfect_of_isPComponent hcomp
  have hLL : ⁅L, L⁆ = L := by
    have := congrArg (Subgroup.map (Subgroup.subtype (centralizer ({π d} : Set G4)))) hperf
    rwa [map_commutator, subgroupOf_map_subtype, inf_of_le_left hLC] at this
  have hX : L ≤ (centralizer ({d} : Set (SL(4, ZMod 7)))).map π := by
    rw [← hLL]; exact (commutator_mono hLC hLC).trans (commutator_cent_le d)
  rw [← hLL, map_commutator]
  exact commutator_mono hX hX

instance fact_not_isSquare_neg_one : Fact (¬ IsSquare (-1 : ZMod 7)) := ⟨by decide⟩

abbrev K49 : Type := QuadraticAlgebra (ZMod 7) (-1) 0

@[expose] noncomputable def rhoM (A : M4) (hA : A * A = -1) : K49 →+* M4 where
  toFun z := z.re • (1 : M4) + z.im • A
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, add_mul, mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hA, smul_smul]
    module
  map_zero' := by simp
  map_add' z w := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, add_smul]; abel

@[expose] def VA (A : M4) (_hA : A * A = -1) : Type := Fin 4 → ZMod 7

section VA

variable (A : M4) (hA : A * A = -1)

noncomputable instance : AddCommGroup (VA A hA) := inferInstanceAs (AddCommGroup (Fin 4 → ZMod 7))
instance : Finite (VA A hA) := inferInstanceAs (Finite (Fin 4 → ZMod 7))

noncomputable instance : Module K49 (VA A hA) where
  smul z v := Matrix.mulVec (rhoM A hA z) v
  one_smul v := (congrArg (fun M : M4 => M *ᵥ (v : Fin 4 → ZMod 7)) (map_one (rhoM A hA))).trans
    (one_mulVec _)
  mul_smul z w v := (congrArg (fun M : M4 => M *ᵥ (v : Fin 4 → ZMod 7))
    (map_mul (rhoM A hA) z w)).trans (mulVec_mulVec _ _ _).symm
  smul_zero z := mulVec_zero _
  smul_add z v w := mulVec_add _ _ _
  add_smul z w v := (congrArg (fun M : M4 => M *ᵥ (v : Fin 4 → ZMod 7))
    (map_add (rhoM A hA) z w)).trans (add_mulVec _ _ _)
  zero_smul v := (congrArg (fun M : M4 => M *ᵥ (v : Fin 4 → ZMod 7))
    (map_zero (rhoM A hA))).trans (zero_mulVec _)

theorem card_K49 : Nat.card K49 = 49 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-1 : ZMod 7) 0), Nat.card_prod, card_zmod7]

theorem finrank_VA : Module.finrank K49 (VA A hA) = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := K49) (V := VA A hA)
  have hV : Nat.card (VA A hA) = 7 ^ 4 := by
    show Nat.card (Fin 4 → ZMod 7) = _
    rw [Nat.card_fun, card_zmod7, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [card_K49] at h
  have h2 : (49 : ℕ) ^ Module.finrank K49 (VA A hA) = 49 ^ 2 := by
    rw [← h, hV]; norm_num
  exact Nat.pow_right_injective (by norm_num) h2

end VA

theorem rhoM_apply (A : M4) (hA : A * A = -1) (z : K49) :
    rhoM A hA z = z.re • (1 : M4) + z.im • A := by rfl

section Det

variable (A' : SL(4, ZMod 7)) (hA : (A' : M4) * (A' : M4) = -1)

theorem comm_rhoM {g : M4} (hg : g * (A' : M4) = (A' : M4) * g) (z : K49) :
    g * rhoM (A' : M4) hA z = rhoM (A' : M4) hA z * g := by
  rw [rhoM_apply]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, hg]

@[expose] noncomputable def gLin (g : centralizer ({A'} : Set (SL(4, ZMod 7)))) :
    VA (A' : M4) hA →ₗ[K49] VA (A' : M4) hA where
  toFun v := ((g : SL(4, ZMod 7)) : M4) *ᵥ (v : Fin 4 → ZMod 7)
  map_add' v w := mulVec_add _ _ _
  map_smul' z v := (mulVec_mulVec _ _ _).trans ((congrArg (· *ᵥ (v : Fin 4 → ZMod 7))
    (comm_rhoM A' hA (congrArg (fun x : SL(4, ZMod 7) => (x : M4))
      (mem_centralizer_singleton_iff.1 g.2)) z)).trans (mulVec_mulVec _ _ _).symm)

@[expose] noncomputable def psiHom :
    centralizer ({A'} : Set (SL(4, ZMod 7))) →* Module.End K49 (VA (A' : M4) hA) where
  toFun g := gLin A' hA g
  map_one' := LinearMap.ext fun v => one_mulVec (v : Fin 4 → ZMod 7)
  map_mul' g h := LinearMap.ext fun v => (mulVec_mulVec (v : Fin 4 → ZMod 7) _ _).symm

@[expose] noncomputable def detK : centralizer ({A'} : Set (SL(4, ZMod 7))) →* K49 :=
  LinearMap.det.comp (psiHom A' hA)

theorem detK_of_eq_smul (k : centralizer ({A'} : Set (SL(4, ZMod 7)))) {c : ZMod 7}
    (hc : c * c = 1) (hk : ((k : SL(4, ZMod 7)) : M4) = c • (A' : M4)) : detK A' hA k = -1 := by
  have hrho : rhoM (A' : M4) hA ⟨0, c⟩ = c • (A' : M4) := by
    rw [rhoM_apply]; simp
  have hpsi : psiHom A' hA k = (⟨0, c⟩ : K49) • LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    exact congrArg (· *ᵥ (v : Fin 4 → ZMod 7)) (hk.trans hrho.symm)
  show LinearMap.det (psiHom A' hA k) = -1
  rw [hpsi, LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_VA]
  ext <;> simp [pow_two, hc, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem detK_commutator {k : SL(4, ZMod 7)}
    (hk : k ∈ ⁅centralizer ({A'} : Set (SL(4, ZMod 7))), centralizer ({A'} : Set (SL(4, ZMod 7)))⁆) :
    ∃ hk' : k ∈ centralizer ({A'} : Set (SL(4, ZMod 7))), detK A' hA ⟨k, hk'⟩ = 1 := by
  have hle : ⁅centralizer ({A'} : Set (SL(4, ZMod 7))), centralizer ({A'} : Set (SL(4, ZMod 7)))⁆ ≤
      (detK A' hA).ker.map (Subgroup.subtype _) := by
    rw [commutator_le]
    intro g hg h hh
    refine ⟨⁅⟨g, hg⟩, ⟨h, hh⟩⁆, map_commutator_eq_one _ _ _, ?_⟩
    rw [map_commutatorElement]
    rfl
  obtain ⟨k', hk'1, rfl⟩ := hle hk
  exact ⟨k'.2, hk'1⟩

theorem neg_one_ne_one_K49 : (-1 : K49) ≠ 1 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp at this
  revert this; decide

end Det

theorem scalars_cases {s : SL(4, ZMod 7)} (hs : s ∈ scalars 4 (ZMod 7)) :
    (s : M4) = 1 ∨ (s : M4) = -1 := by
  obtain ⟨c, hc4, hs⟩ := mem_scalars.1 hs
  have hc : (c : ZMod 7) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]
  have : ∀ x : ZMod 7, x ^ 4 = 1 → x = 1 ∨ x = -1 := by decide
  rcases this _ hc with h | h
  · left; rw [hs, h, map_one]
  · right; rw [hs, h, map_neg, map_one]

theorem not_mem_pLayer_of_sq_neg (A' : SL(4, ZMod 7)) (hA : (A' : M4) * (A' : M4) = -1) :
    π A' ∉ GH74.GLS.pLayerOf 2 (centralizer ({π A'} : Set G4)) := by
  intro hL
  obtain ⟨k, hk, hkA⟩ := pLayer_le_commutator A' hL
  obtain ⟨hk', h1⟩ := detK_commutator A' hA hk
  have hs := proj_eq_proj_iff.1 hkA
  have hA_eq : (A' : M4) = (k : M4) * ((k⁻¹ * A' : SL(4, ZMod 7)) : M4) := by
    have : A' = k * (k⁻¹ * A') := by group
    exact congrArg (fun x : SL(4, ZMod 7) => (x : M4)) this
  rcases scalars_cases hs with h | h
  · rw [h, Matrix.mul_one] at hA_eq
    have := detK_of_eq_smul A' hA ⟨k, hk'⟩ (c := 1) (by decide) (by rw [one_smul]; exact hA_eq.symm)
    exact neg_one_ne_one_K49 (this.symm.trans h1)
  · rw [h, Matrix.mul_neg, Matrix.mul_one] at hA_eq
    have := detK_of_eq_smul A' hA ⟨k, hk'⟩ (c := -1) (by decide)
      (by rw [neg_one_smul, hA_eq, neg_neg])
    exact neg_one_ne_one_K49 (this.symm.trans h1)

theorem X1_one_eq :
    CFSG.ComponentClassification.CatFactsL4U4.HBlocks.X1 (1 : ZMod 7) = -(dSL : M4) := by
  rw [coe_dSL]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem exists_conj_of_sq_one (A : SL(4, ZMod 7)) (hA : (A : M4) * (A : M4) = 1)
    (h1 : (A : M4) ≠ 1) (hm1 : (A : M4) ≠ -1) : ∃ Q : SL(4, ZMod 7), A * Q = Q * dSL := by
  have h2 : (2 : ZMod 7) ≠ 0 := by decide
  obtain ⟨P, hP⟩ := CFSG.ComponentClassification.CatFactsL4U4.TBlocks.exists_frame_t2_L4 h2
    (X := -(A : M4)) (by rw [neg_mul_neg, hA]) (by rw [det_neg]; simp [A.2]; decide)
    (fun h => hm1 (by rw [← neg_neg (A : M4), h])) (fun h => h1 (neg_inj.1 h))
  rw [X1_one_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at hP
  have hd : (P : M4).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit P)).ne_zero
  refine ⟨⟨(P : M4) * diagonal ![((P : M4).det)⁻¹, 1, 1, 1], ?_⟩, ?_⟩
  · rw [det_mul, det_diagonal, Fin.prod_univ_four]
    simp [hd]
  · apply slext
    show (A : M4) * ((P : M4) * diagonal ![((P : M4).det)⁻¹, 1, 1, 1]) =
      ((P : M4) * diagonal ![((P : M4).det)⁻¹, 1, 1, 1]) * (dSL : M4)
    rw [← Matrix.mul_assoc, hP, Matrix.mul_assoc, Matrix.mul_assoc, coe_dSL, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 2
    ext i
    fin_cases i <;> simp

theorem g1_class (i : projectiveSL 4 (ZMod 7)) (hi : orderOf i = 2)
    (hL : i ∈ GH74.GLS.pLayerOf 2 (centralizer ({i} : Set (projectiveSL 4 (ZMod 7))))) :
    ∃ g, g * i * g⁻¹ = proj 4 (ZMod 7) dSL := by
  obtain ⟨A, rfl⟩ := proj_surjective 4 (ZMod 7) i
  have hA2 : A * A ∈ scalars 4 (ZMod 7) := by
    rw [← proj_eq_one_iff, map_mul, ← pow_two, ← hi, pow_orderOf_eq_one]
  have hne : π A ≠ 1 := by
    intro h; rw [h, orderOf_one] at hi; norm_num at hi
  have h1 : (A : M4) ≠ 1 := fun h => hne (by rw [show A = 1 from slext h]; exact map_one _)
  have hm1 : (A : M4) ≠ -1 := fun h => hne (proj_eq_one_iff.2 (mem_scalars.2
    ⟨-1, by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_one_sq, one_pow], by rw [h]; simp [← diagonal_neg]⟩))
  rcases scalars_cases hA2 with h | h
  · obtain ⟨Q, hQ⟩ := exists_conj_of_sq_one A h h1 hm1
    refine ⟨π Q⁻¹, ?_⟩
    rw [map_inv, inv_inv, ← map_inv, ← map_mul, ← map_mul, mul_assoc, hQ, ← mul_assoc,
      inv_mul_cancel, one_mul]
  · exact absurd hL (not_mem_pLayer_of_sq_neg A h)

end CFSG.ComponentClassification.GSThmB.L34DP

