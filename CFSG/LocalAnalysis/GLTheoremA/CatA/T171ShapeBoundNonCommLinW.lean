module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundNonCommLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenBaseW
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOmGen
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.PrimaryConjScalar
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.FixedCommutingProduct
open Polynomial
open scoped commutatorElement

variable {N n : ℕ} {K : Type} [Field K] [Finite K]

theorem specialFactor_of_isComponentOf
    {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G} {d b : G}
    (hw : WSetup p L J A d b)
    (hJ : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)))
    (hn : Nat.card K = 2 ^ n)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    (D : GL (Fin N) K)
    (hD : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
    (hDp : D ^ p = 1)
    (hDind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)) :
    ∃ h : {h : primaryFactors (glA D : Module.End K (Fin N → K)) // IsGoodFactor D h},
      ((J.subgroupOf L).map (piCenterQuot θ)).map
          (CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K).symm.toMonoidHom =
        (specialFactor D h.1.1).map (proj N K) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card]; exact hn)
  haveI := hchar
  have hpk : (p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    intro hdvd
    have h2p : p = 2 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hw.prime).1 hdvd).symm
    exact hw.odd h2p
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hw.idiag hw.d_mem
  have hJc : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    (CFSG.Assembly.isComponentOf_iff_open).2 hJ
  have hcomp := componentDescent_component θ hdN hDind hJc
  set e := CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K with he
  have hφ : MulAut.congr e.symm (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩) =
      conjAut N K D := projConj_recipe D hD
  have hfix : (fixedSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)).map
        e.symm.toMonoidHom = fixedSubgroup (conjAut N K D) := by
    rw [← hφ]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩ y = y := hy
      change (MulAut.congr e.symm (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩))
        (e.symm y) = e.symm y
      simp only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
        MulEquiv.apply_symm_apply]
      rw [hy']
    · intro hx
      refine ⟨e x, ?_, by simp⟩
      have hx' : (MulAut.congr e.symm (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩))
          x = x := hx
      change TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩ (e x) = e x
      simpa only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
        MulEquiv.apply_symm_apply] using congrArg e hx'
  have hmap : ((J.subgroupOf L).map (piCenterQuot θ)).map e.symm.toMonoidHom =
      (J.subgroupOf L).map (e.symm.toMonoidHom.comp (piCenterQuot θ)) := by
    rw [Subgroup.map_map]
  have hK : CFSG.Open.IsComponentOf
      ((J.subgroupOf L).map (e.symm.toMonoidHom.comp (piCenterQuot θ)))
      (fixedSubgroup (conjAut N K D)) := by
    rw [← hmap, ← hfix]
    exact CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv e.symm
      ((CFSG.Assembly.isComponentOf_iff_open).1 hcomp)
  have hDp' : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : Kˣ) := by
    simpa using hDp
  obtain ⟨h, hh⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components
    (p := p) hpk hDp' _ hK
  rw [Subgroup.map_map]
  exact ⟨h, hh⟩

section Private

variable {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G} {d b : G}
variable {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K)}
variable {hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
  (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ,
  LargeEvenInduces θ (conjRel a) φ}
variable {hS : (Set.univ : Set (GL (Fin N) K)) ⊆ Subgroup.normalizer
  (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))}
variable {hw : WSetup p L J A d b}
variable {hJ : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G))}
variable {M : LiftMap (L := L) (A := A) (S := Set.univ) θ hact hS}

private lemma exists_rescaled_lift
    (hc : ∃ c : Kˣ, (M.mat ⟨d, hw.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p)) :
    ∃ (c : Kˣ) (D Mb : GL (Fin N) K)
      (hDnorm : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
      (hBnorm : Mb ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))),
      D = Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ * M.mat ⟨d, hw.d_mem⟩ ∧
      Mb = M.mat ⟨b, hw.b_mem⟩ ∧
      D ^ p = 1 ∧
      LargeEvenInduces θ (conjRel d)
        (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hDnorm⟩) ∧
      LargeEvenInduces θ (conjRel b)
        (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨Mb, hBnorm⟩) := by
  classical
  obtain ⟨c, hc⟩ := hc
  let mat := M.mat
  let hmat := M.mem
  let hind := M.ind
  let s : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹
  let D : GL (Fin N) K := s * mat ⟨d, hw.d_mem⟩
  let Mb : GL (Fin N) K := mat ⟨b, hw.b_mem⟩
  have hs : s ∈ LargeEvenScalars (Fin N) K := by
    rw [largeEvenScalars_def]
    exact ⟨c⁻¹, rfl⟩
  have hDnorm : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) :=
    Subgroup.mul_mem _ (TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs)
      (hS (hmat ⟨d, hw.d_mem⟩))
  have hBnorm : Mb ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) :=
    hS (hmat ⟨b, hw.b_mem⟩)
  have hsMd : s * mat ⟨d, hw.d_mem⟩ = mat ⟨d, hw.d_mem⟩ * s :=
    (Subgroup.mem_center_iff.mp
      (TableB.scalars_le_center hs) (mat ⟨d, hw.d_mem⟩)).symm
  have hDpow : D ^ p = 1 := by
    have hsp : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) ((c⁻¹ : Kˣ) ^ p) :=
      (map_pow (Matrix.GeneralLinearGroup.scalar (Fin N)) c⁻¹ p).symm
    rw [show D = s * mat ⟨d, hw.d_mem⟩ from rfl,
      Commute.mul_pow hsMd p, hsp, hc, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hDind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hDnorm⟩) := by
    have hsub : (⟨D, hDnorm⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) =
        (⟨s, TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) *
        ⟨mat ⟨d, hw.d_mem⟩, hS (hmat ⟨d, hw.d_mem⟩)⟩ := Subtype.ext rfl
    have hscalar : TableB.projConj (LargeEvenSLGroup (Fin N) K)
        (⟨s, TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) = 1 :=
      TableB.projConj_of_scalar (LargeEvenSLGroup (Fin N) K) hs
    rw [hsub, map_mul, hscalar, one_mul]
    exact hind ⟨d, hw.d_mem⟩
  have hBind : LargeEvenInduces θ (conjRel b)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨Mb, hBnorm⟩) :=
    hind ⟨b, hw.b_mem⟩
  exact ⟨c, D, Mb, hDnorm, hBnorm, rfl, rfl, hDpow, hDind, hBind⟩

private lemma conj_scalar_of_ne
    (hN : 3 ≤ N) (c : Kˣ) {D Mb : GL (Fin N) K}
    (hD_eq : D = Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ * M.mat ⟨d, hw.d_mem⟩)
    (hMb_eq : Mb = M.mat ⟨b, hw.b_mem⟩)
    (hDpow : D ^ p = 1)
    (hnc : M.mat ⟨b, hw.b_mem⟩ * M.mat ⟨d, hw.d_mem⟩ ≠
      M.mat ⟨d, hw.d_mem⟩ * M.mat ⟨b, hw.b_mem⟩) :
    ∃ ζ : Kˣ, Mb * D * Mb⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D ∧
      ζ ≠ 1 ∧ (ζ : K) ^ p = 1 := by
  classical
  have hker := linKernelScalar_of_three_le (K := K) (N := N) hN
  let s : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹
  have hs : s ∈ LargeEvenScalars (Fin N) K := by
    rw [largeEvenScalars_def]
    exact ⟨c⁻¹, rfl⟩
  have hsc : ∀ y : GL (Fin N) K, y * s = s * y := fun y =>
    Subgroup.mem_center_iff.mp (TableB.scalars_le_center hs) y
  have hbase := LiftMap.commutator_mem_scalars_of_wSetup (L := L) (A := A) M hw
    ⟨b, hw.b_mem⟩ hker
  have heq : Mb * D * Mb⁻¹ * D⁻¹ =
      s * (M.mat ⟨b, hw.b_mem⟩ * M.mat ⟨d, hw.d_mem⟩ * (M.mat ⟨b, hw.b_mem⟩)⁻¹ *
        (M.mat ⟨d, hw.d_mem⟩)⁻¹) * s⁻¹ := by
    rw [hD_eq, hMb_eq]
    calc (M.mat ⟨b, hw.b_mem⟩ * (s * M.mat ⟨d, hw.d_mem⟩)) *
          (M.mat ⟨b, hw.b_mem⟩)⁻¹ * (s * M.mat ⟨d, hw.d_mem⟩)⁻¹
        = M.mat ⟨b, hw.b_mem⟩ * (s * M.mat ⟨d, hw.d_mem⟩) *
            (M.mat ⟨b, hw.b_mem⟩)⁻¹ * ((M.mat ⟨d, hw.d_mem⟩)⁻¹ * s⁻¹) := by
          rw [mul_inv_rev]
      _ = M.mat ⟨b, hw.b_mem⟩ * s * M.mat ⟨d, hw.d_mem⟩ *
            (M.mat ⟨b, hw.b_mem⟩)⁻¹ * (M.mat ⟨d, hw.d_mem⟩)⁻¹ * s⁻¹ := by group
      _ = s * M.mat ⟨b, hw.b_mem⟩ * M.mat ⟨d, hw.d_mem⟩ *
            (M.mat ⟨b, hw.b_mem⟩)⁻¹ * (M.mat ⟨d, hw.d_mem⟩)⁻¹ * s⁻¹ := by
          rw [hsc (M.mat ⟨b, hw.b_mem⟩)]
      _ = s * (M.mat ⟨b, hw.b_mem⟩ * M.mat ⟨d, hw.d_mem⟩ *
            (M.mat ⟨b, hw.b_mem⟩)⁻¹ * (M.mat ⟨d, hw.d_mem⟩)⁻¹) * s⁻¹ := by group
  have hcommut : Mb * D * Mb⁻¹ * D⁻¹ ∈ LargeEvenScalars (Fin N) K := by
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hbase) (Subgroup.inv_mem _ hs)
  obtain ⟨ζ, hζ⟩ := by
    rw [largeEvenScalars_def, MonoidHom.mem_range] at hcommut
    exact hcommut
  have hconj : Mb * D * Mb⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D := by
    calc Mb * D * Mb⁻¹ = (Mb * D * Mb⁻¹ * D⁻¹) * D := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D := by rw [← hζ]
  have hζ1 : ζ ≠ 1 := by
    intro h1
    apply hnc
    have hMD : Mb * D = D * Mb := by
      calc Mb * D = (Mb * D * Mb⁻¹) * Mb := by group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D) * Mb := by rw [hconj]
        _ = D * Mb := by rw [h1, map_one, one_mul]
    have h1' : Mb * (s * M.mat ⟨d, hw.d_mem⟩) =
        (s * M.mat ⟨d, hw.d_mem⟩) * Mb := by
      rw [← hD_eq]
      exact hMD
    have h3 : Mb * (s * M.mat ⟨d, hw.d_mem⟩) =
        s * (Mb * M.mat ⟨d, hw.d_mem⟩) := by
      calc Mb * (s * M.mat ⟨d, hw.d_mem⟩) = (Mb * s) * M.mat ⟨d, hw.d_mem⟩ :=
            (mul_assoc _ _ _).symm
        _ = (s * Mb) * M.mat ⟨d, hw.d_mem⟩ := by rw [← hsc Mb]
        _ = s * (Mb * M.mat ⟨d, hw.d_mem⟩) := mul_assoc _ _ _
    have h4 : (s * M.mat ⟨d, hw.d_mem⟩) * Mb =
        s * (M.mat ⟨d, hw.d_mem⟩ * Mb) := mul_assoc _ _ _
    rw [h3, h4] at h1'
    rw [hMb_eq] at h1'
    exact mul_left_cancel h1'
  have hζp : (ζ : K) ^ p = 1 := by
    have hcommζD : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) ζ) D := by
      rw [Commute]
      exact (Subgroup.mem_center_iff.mp
        (TableB.scalars_le_center (show Matrix.GeneralLinearGroup.scalar (Fin N) ζ ∈
          LargeEvenScalars (Fin N) K from ⟨ζ, rfl⟩)) D).symm
    have h1 : (Mb * D * Mb⁻¹) ^ p = 1 := by
      rw [show Mb * D * Mb⁻¹ = (MulAut.conj Mb) D from (MulAut.conj_apply Mb D).symm,
        ← map_pow, hDpow, map_one]
    rw [hconj, Commute.mul_pow hcommζD p, hDpow, mul_one] at h1
    haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    have hinj := Matrix.GeneralLinearGroup.scalar_injective (n := Fin N) (R := K)
    have h2 : (ζ : Kˣ) ^ p = 1 := by
      apply hinj
      rw [map_pow, h1, map_one]
    simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Kˣ => (u : K)) h2
  exact ⟨ζ, hconj, hζ1, hζp⟩

private lemma projective_special_factor_preserved
    {D Mb : GL (Fin N) K} {f : K[X]}
    (hJeq : ((J.subgroupOf L).map (piCenterQuot θ)).map
        (CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K).symm.toMonoidHom =
      (specialFactor D f).map (proj N K))
    (hBnorm : Mb ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
    (hBind : LargeEvenInduces θ (conjRel b)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨Mb, hBnorm⟩))
    (hbL : b ∈ Subgroup.normalizer (L : Set G))
    (hbJ : b ∈ Subgroup.normalizer (J : Set G)) :
    ∀ a ∈ specialFactor D f, ∃ b' ∈ specialFactor D f,
      (proj N K) (slConjugation N K Mb a) = (proj N K) b' := by
  classical
  let e := CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K
  let φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) :=
    TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨Mb, hBnorm⟩
  let PJ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) :=
    (J.subgroupOf L).map (piCenterQuot θ)
  let K₀ : Subgroup (projectiveSL N K) := (specialFactor D f).map (proj N K)
  have hJ' : PJ.map e.symm.toMonoidHom = K₀ := hJeq
  have hPJle : PJ.map φ.toMonoidHom ≤ PJ := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
    have hjJ : (j : G) ∈ J := (Subgroup.mem_subgroupOf).mp hj
    have hmemL : b⁻¹ * (j : G) * b ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbL) (j : G)).mp j.2
      simpa using this
    have hmemJ : b⁻¹ * (j : G) * b ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbJ) (j : G)).mp hjJ
      simpa using this
    have hrel : conjRel b j ⟨b⁻¹ * (j : G) * b, hmemL⟩ := rfl
    have h := hBind j ⟨b⁻¹ * (j : G) * b, hmemL⟩ hrel
    refine Subgroup.mem_map.mpr ⟨⟨b⁻¹ * (j : G) * b, hmemL⟩,
      Subgroup.mem_subgroupOf.mpr hmemJ, ?_⟩
    exact h.symm
  have hPJinv : PJ.map φ.toMonoidHom = PJ := by
    refine Subgroup.eq_of_le_of_card_ge hPJle ?_
    rw [show Nat.card ↥(Subgroup.map (MulEquiv.toMonoidHom φ) PJ) = Nat.card ↥PJ from
      Subgroup.card_map_of_injective (f := MulEquiv.toMonoidHom φ) φ.injective]
  have hcomp : (LinearFlag.conjAut N K Mb).toMonoidHom.comp e.symm.toMonoidHom =
      e.symm.toMonoidHom.comp φ.toMonoidHom := by
    ext x
    have hrecipe : MulAut.congr e.symm φ = LinearFlag.conjAut N K Mb :=
      projConj_recipe (K := K) (N := N) Mb hBnorm
    have h := congrArg (fun α : MulAut (projectiveSL N K) => α (e.symm x)) hrecipe
    simpa [MulAut.congr_apply] using h.symm
  have hK0inv : K₀.map (LinearFlag.conjAut N K Mb).toMonoidHom = K₀ := by
    rw [← hJ', Subgroup.map_map, hcomp, ← Subgroup.map_map, hPJinv, hJ']
  intro a ha
  have hmem : (proj N K) a ∈ K₀ := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hmem' : (LinearFlag.conjAut N K Mb) ((proj N K) a) ∈ K₀ := by
    have h := Subgroup.mem_map_of_mem (LinearFlag.conjAut N K Mb).toMonoidHom hmem
    rwa [hK0inv] at h
  rw [LinearFlag.conjAut_proj] at hmem'
  obtain ⟨b', hb', hb'eq⟩ := Subgroup.mem_map.mp hmem'
  exact ⟨b', hb', hb'eq.symm⟩

private lemma final_nonComm_contradiction
    {D Mb : GL (Fin N) K} {f g : K[X]}
    (hfix : ∀ a ∈ specialFactor D f, ∀ {j : K[X]},
      j ∈ primaryFactors (glA D : Module.End K (Fin N → K)) → j ≠ f →
      ∀ v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) j,
        (slGL N K a : Module.End K (Fin N → K)) v = v)
    (hMV : (primaryComponent (glA D : Module.End K (Fin N → K)) f).map
        (glA Mb : Module.End K (Fin N → K)) =
      primaryComponent (glA D : Module.End K (Fin N → K)) g)
    (hgmem : g ∈ primaryFactors (glA D : Module.End K (Fin N → K)))
    (hgf : g ≠ f)
    (hMinj : Function.Injective (glA Mb : Module.End K (Fin N → K)))
    (hproj : ∀ a ∈ specialFactor D f, ∃ b' ∈ specialFactor D f,
      (proj N K) (slConjugation N K Mb a) = (proj N K) b')
    (x : ↥(specialFactor D f))
    (hxscalar : ¬ ∃ μ : K, ∀ v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) f,
      (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) v =
        μ • v) :
    False := by
  classical
  let MblinG : LinearMap.GeneralLinearGroup K (Fin N → K) := glA Mb
  let MbinvG : LinearMap.GeneralLinearGroup K (Fin N → K) := MblinG⁻¹
  let Mblin : Module.End K (Fin N → K) := (MblinG : Module.End K (Fin N → K))
  have hbinvL : ∀ w : Fin N → K, ((MbinvG : Module.End K (Fin N → K)))
      ((MblinG : Module.End K (Fin N → K)) w) = w := by
    intro w
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  obtain ⟨x', hx'mem, hx'proj⟩ := hproj (x : Matrix.SpecialLinearGroup (Fin N) K) x.2
  have hscal : (slConjugation N K Mb
      (x : Matrix.SpecialLinearGroup (Fin N) K))⁻¹ * x' ∈ LinearFlag.scalars N K :=
    (LinearFlag.proj_eq_proj_iff).mp hx'proj
  obtain ⟨c, hcN, hcmat⟩ := LinearFlag.mem_scalars.mp hscal
  have hSL : (slConjugation N K Mb
        (x : Matrix.SpecialLinearGroup (Fin N) K))⁻¹ * x' =
      LinearFlag.scalarElement c hcN := Subtype.ext hcmat
  have heq : x' = slConjugation N K Mb
        (x : Matrix.SpecialLinearGroup (Fin N) K) * LinearFlag.scalarElement c hcN := by
    rw [← hSL]
    group
  have htoGL : Matrix.SpecialLinearGroup.toGL (LinearFlag.scalarElement c hcN) =
      Matrix.GeneralLinearGroup.scalar (Fin N) c := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    simp [LinearFlag.scalarElement]
  have hscalarGL : (slGL N K (LinearFlag.scalarElement c hcN) :
      LinearMap.GeneralLinearGroup K (Fin N → K)) =
      glA (Matrix.GeneralLinearGroup.scalar (Fin N) c) := by
    rw [← htoGL]
    rfl
  have hslconj : (slGL N K (slConjugation N K Mb
        (x : Matrix.SpecialLinearGroup (Fin N) K)) :
      LinearMap.GeneralLinearGroup K (Fin N → K)) =
      MblinG * (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K)) * MbinvG := by
    simp only [slGL, MonoidHom.comp_apply, toGL_slConjugation,
      map_mul, map_inv]
    rfl
  have hact_g : ∀ v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) g,
      (slGL N K (slConjugation N K Mb
        (x : Matrix.SpecialLinearGroup (Fin N) K)) : Module.End K (Fin N → K)) v =
        ((c⁻¹ : Kˣ) : K) • v := by
    intro v hv
    have h := congrArg (fun s : Matrix.SpecialLinearGroup (Fin N) K =>
      (slGL N K s : LinearMap.GeneralLinearGroup K (Fin N → K))) heq
    rw [map_mul, hscalarGL] at h
    have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin N → K) =>
      (u : Module.End K (Fin N → K)) v) h
    rw [Units.val_mul, Module.End.mul_apply, glA_scalar_smul] at h2
    have hxv : (slGL N K x' : Module.End K (Fin N → K)) v = v :=
      hfix x' hx'mem hgmem hgf v hv
    have h2' : v = (slGL N K (slConjugation N K Mb
        (x : Matrix.SpecialLinearGroup (Fin N) K)) : Module.End K (Fin N → K))
        ((c : K) • v) := by
      calc v = (slGL N K x' : Module.End K (Fin N → K)) v := hxv.symm
        _ = (slGL N K (slConjugation
              N K Mb (x : Matrix.SpecialLinearGroup (Fin N) K)) :
              Module.End K (Fin N → K)) ((c : K) • v) := by
            simpa using h2
    rw [map_smul] at h2'
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    have h3 := congrArg (fun w : Fin N → K => ((c : K)⁻¹) • w) h2'.symm
    simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul, Units.val_inv_eq_inv_val] using h3
  refine hxscalar ⟨((c⁻¹ : Kˣ) : K), fun w hw => ?_⟩
  have hMv : Mblin w ∈ primaryComponent (glA D : Module.End K (Fin N → K)) g := by
    rw [← hMV]
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  have h1 : Mblin ((slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) :
      Module.End K (Fin N → K)) w) = ((c⁻¹ : Kˣ) : K) • Mblin w := by
    have h := hact_g (Mblin w) hMv
    rw [hslconj] at h
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hbinvL] at h
    exact h
  exact hMinj (h1.trans (map_smul Mblin ((c⁻¹ : Kˣ) : K) w).symm)

end Private

theorem linTypeOneNonComm_of_wSetup
    {G : Type} [Group G] [Finite G] {p N n : ℕ} {L J A : Subgroup G} {d b : G}
    {K : Type} [Field K] [Finite K] (hcard : Nat.card K = 2 ^ n) (hN : 3 ≤ N)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    (hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ,
      LargeEvenInduces θ (conjRel a) φ)
    (hS : (Set.univ : Set (GL (Fin N) K)) ⊆ Subgroup.normalizer
      (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
    (hw : WSetup p L J A d b)
    (hJ : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)))
    (M : LiftMap (L := L) (A := A) (S := Set.univ) θ hact hS)
    (hc : ∃ c : Kˣ, (M.mat ⟨d, hw.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p))
    (hnc : M.mat ⟨b, hw.b_mem⟩ * M.mat ⟨d, hw.d_mem⟩ ≠
      M.mat ⟨d, hw.d_mem⟩ * M.mat ⟨b, hw.b_mem⟩) : False := by
  classical
  obtain ⟨c, D, Mb, hDnorm, hBnorm, hD_eq, hMb_eq, hDpow, hDind, hBind⟩ :=
    exists_rescaled_lift (M := M) (hw := hw) (θ := θ) (hact := hact) (hS := hS) hc
  obtain ⟨ζ, hconj, hζ1, hζp⟩ :=
    conj_scalar_of_ne (M := M) (hw := hw) hN c hD_eq hMb_eq hDpow hnc
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [← Nat.card_eq_fintype_card]; exact hcard)
  haveI := hchar
  have hpk : (p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    intro hdvd
    have h2p : p = 2 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hw.prime).1 hdvd).symm
    exact hw.odd h2p
  haveI : Fact p.Prime := ⟨hw.prime⟩
  have hζroot : IsPrimitiveRoot (ζ : K) p := by
    have h := IsPrimitiveRoot.orderOf (ζ : K)
    rwa [orderOf_eq_prime hζp (fun h => hζ1 (Units.ext h))] at h
  have hDp' : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : Kˣ) := by
    simpa using hDpow
  have hsq : Squarefree (minpoly K (glA D : Module.End K (Fin N → K))) :=
    squarefree_minpoly_glA (p := p) hpk hDp'
  obtain ⟨⟨⟨f, hf⟩, hgood⟩, hJeq⟩ :=
    specialFactor_of_isComponentOf (K := K) (N := N) (n := n) hw hJ hcard θ D hDnorm hDpow hDind
  obtain ⟨ε, hform, _, hε0⟩ :=
    eq_X_sub_C_of_mem_primaryFactors_of_pow_eq_one (n := N) (p := p) (ω := (ζ : K))
      hw.prime.ne_zero hζroot hDpow hf
  have hVne : primaryComponent (glA D : Module.End K (Fin N → K)) f ≠ ⊥ :=
    primaryComponent_ne_bot hsq hf
  have hMV :=
    map_primaryComponent_X_sub_C_of_conj_eq_scalar_mul (D := D) (Mb := Mb)
      (ζ := ζ) (f := f) (ε := ε) hconj hform
  have hMinj : Function.Injective (glA Mb : Module.End K (Fin N → K)) := by
    simpa using (LinearMap.GeneralLinearGroup.toLinearEquiv (glA Mb)).injective
  obtain ⟨hgmem, hgf⟩ :=
    mem_primaryFactors_X_sub_C_div_and_ne_of_map_primaryComponent (D := D) (Mb := Mb)
      (ζ := ζ) (f := f) (ε := ε) hform hζ1 hε0 hVne hMV
  obtain ⟨x, hxnc⟩ :=
    exists_not_mem_center_specialFactor (D := D) (f := f) hsq hf hgood
  have hfix : ∀ a ∈ specialFactor D f, ∀ {j : K[X]},
      j ∈ primaryFactors (glA D : Module.End K (Fin N → K)) → j ≠ f →
      ∀ v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) j,
        (slGL N K a : Module.End K (Fin N → K)) v = v := by
    intro a ha j hj hjf v hv
    exact (mem_linearSpecialBlock.mp (ha : slGL N K a ∈ linearSpecialBlock (glA D) f)).2.1
      j hj hjf v hv
  have hxscalar : ¬ ∃ μ : K, ∀ v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) f,
      (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) v =
        μ • v :=
    fun h => hxnc (mem_center_specialFactor_of_isScalar_on_primaryComponent
      (D := D) (f := f) hsq x h)
  have hproj := projective_special_factor_preserved (D := D) (Mb := Mb) (f := f)
    (θ := θ) hJeq hBnorm hBind
    (CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hw.idiag hw.b_mem) hw.b_norm
  exact final_nonComm_contradiction (D := D) (Mb := Mb) (f := f) (g := X - C (ε / ζ))
    hfix hMV hgmem hgf hMinj hproj x hxscalar

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
