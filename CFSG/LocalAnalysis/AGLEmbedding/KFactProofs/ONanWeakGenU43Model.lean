module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43Data
public import CFSG.LieType.Multipliers.U43Bridge
public import CFSG.Blueprint.MatrixSeedIdentification
import all CFSG.LieType.Multipliers.U43Bridge

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak.U43Seed

open CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.AGLEmbedding.R3

@[expose] def blk (a : F9) : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![a.re, -a.im; a.im, a.re]

theorem blk_mul (a b : F9) : blk (a * b) = blk a * blk b := by
  revert a b
  decide +kernel

theorem blk_add (a b : F9) : blk (a + b) = blk a + blk b := by
  revert a b
  decide +kernel

theorem blk_one : blk 1 = 1 := by decide +kernel

theorem blk_zero : blk 0 = 0 := by decide +kernel

@[expose] def blkHom : F9 →+* Matrix (Fin 2) (Fin 2) (ZMod 3) where
  toFun := blk
  map_one' := blk_one
  map_mul' := blk_mul
  map_zero' := blk_zero
  map_add' := blk_add

theorem blkHom_injective : Function.Injective blkHom := by
  intro a b h
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 0
  simp only [blkHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, blk] at h0 h1
  exact F9.ext (by simpa using h0) (by simpa using h1)

@[expose] def blockEquiv :
    Matrix (Fin 4) (Fin 4) (Matrix (Fin 2) (Fin 2) (ZMod 3)) ≃+* Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  (Matrix.compRingEquiv (Fin 4) (Fin 2) (ZMod 3)).trans
    (Matrix.reindexAlgEquiv (ZMod 3) (ZMod 3) (finProdFinEquiv : Fin 4 × Fin 2 ≃ Fin 8)).toRingEquiv

@[expose] def resRing : Matrix (Fin 4) (Fin 4) F9 →+* Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  blockEquiv.toRingHom.comp blkHom.mapMatrix

theorem resRing_injective : Function.Injective resRing :=
  blockEquiv.injective.comp (Matrix.map_injective blkHom_injective)

@[expose] def resGL : GL (Fin 4) F9 →* GL (Fin 8) (ZMod 3) := Units.map resRing.toMonoidHom

theorem resGL_injective : Function.Injective resGL := Units.map_injective resRing_injective

theorem decode_seedA : NativeSporadic.decode 3 8 1 U43Three.seedA = resRing matA := by
  decide +kernel

theorem decode_seedB : NativeSporadic.decode 3 8 1 U43Three.seedB = resRing matB := by
  decide +kernel

@[expose] noncomputable def gA : GL (Fin 4) F9 := (suA : GL (Fin 4) F9)

@[expose] noncomputable def gB : GL (Fin 4) F9 := (suB : GL (Fin 4) F9)

theorem seedMonoid_eq :
    NativeSporadic.seedMonoid 3 8 1 U43Three.seedA U43Three.seedB =
      Submonoid.closure {((resGL gA : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)),
        ((resGL gB : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))} := by
  unfold NativeSporadic.seedMonoid
  rw [decode_seedA, decode_seedB]
  rfl

@[expose] def genU : Subgroup (GL (Fin 4) F9) := Subgroup.closure {gA, gB}

theorem closure_resGL : Subgroup.closure {resGL gA, resGL gB} = genU.map resGL := by
  rw [genU, MonoidHom.map_closure, Set.image_pair]

noncomputable def seedEquiv :
    (NativeSporadic.seedMonoid 3 8 1 U43Three.seedA U43Three.seedB)ˣ ≃* ↥genU := by
  rw [seedMonoid_eq]
  exact (NativeSporadic.unitSeedEquiv (resGL gA) (resGL gB)).trans
    ((MulEquiv.subgroupCongr closure_resGL).trans
      (Subgroup.equivMapOfInjective genU resGL resGL_injective).symm)

theorem genU_le : genU ≤ StatedSU 4 3 F9 :=
  (Subgroup.closure_le _).2 (by rintro _ (rfl | rfl); exacts [suA.2, suB.2])

@[expose] noncomputable def toX₀ : genU →* X₀ :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion genU_le)

theorem toX₀_surjective : Function.Surjective toX₀ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_xy]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (rfl | rfl)
  · exact ⟨⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩, rfl⟩
  · exact ⟨⟨gB, Subgroup.subset_closure (by simp)⟩, rfl⟩

theorem det_eq_one_of_mem_statedSU {x : GL (Fin 4) F9} (hx : x ∈ StatedSU 4 3 F9) :
    (x : Matrix (Fin 4) (Fin 4) F9).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hx

theorem scalar_apply_zero (c : F9ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F9) :
      Matrix (Fin 4) (Fin 4) F9) 0 0 = c := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem eq_one_of_toX₀_eq_one (k : genU) (hk : toX₀ k = 1) (hk3 : k ^ 3 = 1) : k = 1 := by
  have hk' : (QuotientGroup.mk (Subgroup.inclusion genU_le k) : X₀) = 1 := hk
  have hs' : Subgroup.inclusion genU_le k ∈
      (StatedScalars (Fin 4) F9).subgroupOf (StatedSU 4 3 F9) :=
    (QuotientGroup.eq_one_iff (Subgroup.inclusion genU_le k)).1 hk'
  have hs : ((k : GL (Fin 4) F9)) ∈ StatedScalars (Fin 4) F9 := Subgroup.mem_subgroupOf.1 hs'
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hs
  have hdet := det_eq_one_of_mem_statedSU (genU_le k.2)
  rw [← hc] at hdet
  have h4 : c ^ 4 = 1 := by
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using
      hdet
  have hk3' : ((k : GL (Fin 4) F9)) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hk3
  rw [← hc, ← map_pow] at hk3'
  have h3 : c ^ 3 = 1 := by
    have h := congrArg (fun g : GL (Fin 4) F9 => (g : Matrix (Fin 4) (Fin 4) F9) 0 0) hk3'
    simp only [scalar_apply_zero, Units.val_one, Matrix.one_apply_eq] at h
    exact Units.ext h
  have hc1 : c = 1 := by
    have := h4
    rwa [pow_succ, h3, one_mul] at this
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak.U43Seed
