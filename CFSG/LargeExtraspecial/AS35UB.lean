module

public import CFSG.LargeExtraspecial.OutSixUnitary
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35U

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification.Unitary CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem timmesfeldPSU_eq_map (m : ℕ) :
    timmesfeldPSU m = (SUid frob m).map ProjGenLinGroup.mk := by
  have hset : {A : GL (Fin m) (GaloisField 2 2) |
      (Matrix.of fun i j => (A : Matrix (Fin m) (Fin m) (GaloisField 2 2)) j i ^ 2) *
          (A : Matrix (Fin m) (Fin m) (GaloisField 2 2)) = 1 ∧
        GeneralLinearGroup.det A = 1} = (SUid frob m : Set (GL (Fin m) K)) := by
    ext A
    have hbar : conjTr frob (A : Matrix (Fin m) (Fin m) K) =
        Matrix.of fun i j => (A : Matrix (Fin m) (Fin m) K) j i ^ 2 := by
      ext i j
      rw [conjTr, transpose_apply, map_apply, frob_apply, of_apply]
    rw [SetLike.mem_coe, mem_SUid, Set.mem_ofPred_eq, hbar, Units.ext_iff,
      GeneralLinearGroup.val_det_apply, Units.val_one, and_comm]
  rw [timmesfeldPSU, hset, Subgroup.closure_eq]

@[expose] noncomputable def pgEquiv (hm : 3 ≤ m) : PG m ≃* timmesfeldPSU m :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [center_SUid hm, CFSG.Assembly.LowTwoRank.StatedScalars,
      ← GeneralLinearGroup.center_eq_range_scalar])).trans
    ((S14.mapMkEquiv (SUid frob m)).symm.trans
      (MulEquiv.subgroupCongr (timmesfeldPSU_eq_map m).symm))

theorem hF : UnitaryFieldData 2 1 K := S14.unitaryFieldData_two_one

theorem bar_eq (c : K) : hF.bar c = frob c := by
  rw [UnitaryFieldData.bar_apply, frob_apply, pow_one]

@[expose] noncomputable def hermB (m : ℕ) : (Fin m → K) →ₛₗ[hF.bar] (Fin m → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ hF.bar (RingHom.id K) (herm frob) (herm_add_left frob)
    (fun c x y => by rw [herm_smul_left, bar_eq, smul_eq_mul]) (herm_add_right frob)
    (fun c x y => by rw [herm_smul_right, RingHom.id_apply, smul_eq_mul])

theorem hermB_apply (x y : Fin m → K) : hermB m x y = herm frob x y := rfl

theorem hermB_isSymm : (hermB m).IsSymm :=
  ⟨fun x y => by rw [hermB_apply, hermB_apply, bar_eq, herm_conj frob frob_frob, frob_frob]⟩

theorem hermB_separatingLeft : (hermB m).SeparatingLeft := fun _ hx =>
  eq_zero_of_herm (σ := frob) fun y => hx y

@[expose] noncomputable def ι (m : ℕ) :
    SUid frob m →* LinearMap.GeneralLinearGroup K (Fin m → K) :=
  GeneralLinearGroup.toLin.toMonoidHom.comp (SUid frob m).subtype

theorem ι_apply (g : SUid frob m) (x : Fin m → K) :
    (ι m g : (Fin m → K) →ₗ[K] (Fin m → K)) x = g • x := by
  rw [smul_def]
  exact GeneralLinearGroup.toLin_apply _ x

theorem ι_injective : Function.Injective (ι m) := fun _ _ h =>
  Subtype.ext (GeneralLinearGroup.toLin.injective h)

theorem ι_mem (g : SUid frob m) : ι m g ∈ sesqSpecialUnitaryGroup (hermB m) := by
  refine mem_sesqSpecialUnitaryGroup.mpr ⟨fun x y => ?_, ?_⟩
  · rw [ι_apply, ι_apply, hermB_apply, hermB_apply, herm_smul_smul]
  · change LinearMap.det (GeneralLinearGroup.toLin (g : GL (Fin m) K) :
      (Fin m → K) →ₗ[K] (Fin m → K)) = 1
    rw [GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply', LinearMap.det_toLin']
    exact ((mem_SUid_iff frob).mp g.2).1

theorem exists_ι_eq {g : LinearMap.GeneralLinearGroup K (Fin m → K)}
    (hg : g ∈ sesqSpecialUnitaryGroup (hermB m)) : ∃ a : SUid frob m, ι m a = g := by
  obtain ⟨hU, hdet⟩ := mem_sesqSpecialUnitaryGroup.mp hg
  set A := GeneralLinearGroup.toLin.symm g with hAdef
  have hA : GeneralLinearGroup.toLin A = g := MulEquiv.apply_symm_apply _ _
  have hAx : ∀ x, (A : Matrix (Fin m) (Fin m) K) *ᵥ x = (g : (Fin m → K) →ₗ[K] _) x := fun x => by
    rw [← hA, GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
  refine ⟨⟨A, (mem_SUid_iff frob).mpr ⟨?_, fun x y => ?_⟩⟩, hA⟩
  · rw [← hdet, ← hA, GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  · rw [hAx, hAx]
    exact hU x y

theorem ι_tvU {e : Fin m → K} (he : hermB m e e = 0) :
    ι m (tvU e) = hermTransvectionGL (hermB m) he 1 := by
  have he' : herm frob e e = 0 := he
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [ι_apply, tvU_smul he', coe_hermTransvectionGL, hermTransvection_apply, one_mul,
    hermB_apply]

end CFSG.LargeExtraspecial.AS35U
