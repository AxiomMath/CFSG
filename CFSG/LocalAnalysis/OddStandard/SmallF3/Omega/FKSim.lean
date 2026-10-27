module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKIso
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4O

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T CFSG.ClassicalInvolution.Q3.TL4
  QuadraticMap
open CFSG.LieType.Universal.Spin (spinAction quadPlus nondegenerate_quadPlus)
open CFSG.Open (StatedProj StatedOmega StatedQuadPlus)

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "Q₀" => quadPlus 4 (ZMod 3)

local notation "Proj₈" => StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))

theorem fk_exists_equiv :
    ∃ e : Proj₈ ≃* omegaProj (nondegenerate_quadPlus 4 (ZMod 3)),
      ∀ x : spinGroup Q₄, ((e (d4Proj (GaloisField 3 1) x) :
        omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) : ProjOrth Q₀) = toProj Q₀ (fkSpin x) := by
  set hQ₀ := nondegenerate_quadPlus 4 (ZMod 3) with hQ₀def
  let E : spinGroup Q₄ →* omegaProj hQ₀ :=
    ((toProj Q₀).comp fkSpin).codRestrict (omegaProj hQ₀) fun x =>
      (mem_omegaProj_iff hQ₀).mpr ⟨fkSpin x, fkSpin_mem_omegaGroup x, rfl⟩
  have hE : Function.Surjective E := by
    intro y
    obtain ⟨g, hg, hgy⟩ := (mem_omegaProj_iff hQ₀).mp y.2
    obtain ⟨x, hx⟩ := fkSpin_exists_of_mem_omegaGroup hg
    refine ⟨x, Subtype.ext ?_⟩
    change toProj Q₀ (fkSpin x) = (y : ProjOrth Q₀)
    rw [hx]
    exact hgy
  have hker : (d4Proj (GaloisField 3 1)).ker = E.ker := by
    ext x
    rw [Q3MFOD.ker_d4Proj, MonoidHom.mem_ker, ← fkSpin_mem_piGroup_iff]
    change _ ↔ E x = 1
    rw [Subtype.ext_iff]
    exact (QuotientGroup.eq_one_iff (fkSpin x)).symm
  obtain ⟨e, he⟩ := Q3T.exists_mulEquiv_apply_eq (d4Proj (GaloisField 3 1))
    Q3MFOD.d4Proj_surjective E hE hker
  exact ⟨e, fun x => by rw [he]; rfl⟩

theorem fk_congr_descAut {e : Proj₈ ≃* omegaProj (nondegenerate_quadPlus 4 (ZMod 3))}
    (he : ∀ x : spinGroup Q₄, ((e (d4Proj (GaloisField 3 1) x) :
        omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) : ProjOrth Q₀) = toProj Q₀ (fkSpin x))
    (α : MulAut (spinGroup Q₄))
    {a : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1] (Fin 4 ⊕ Fin 4 → GaloisField 3 1)}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄)
    (hαa : ∀ x, spinAction Q₄ (α x) = a * spinAction Q₄ x * a⁻¹) :
    MulAut.congr e (Q3MFOD.descAut α) = MulAut.conjNormal (toProj Q₀ (fkOrth ha)) := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨p, rfl⟩ := e.surjective y
  obtain ⟨x, rfl⟩ := Q3MFOD.d4Proj_surjective p
  apply Subtype.ext
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    Q3MFOD.descAut_apply, MulAut.conjNormal_apply, he, he, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change LinearEquiv.autCongr fkCoord (spinAction Q₄ (α x)) =
    LinearEquiv.autCongr fkCoord a * LinearEquiv.autCongr fkCoord (spinAction Q₄ x) *
      (LinearEquiv.autCongr fkCoord a)⁻¹
  rw [hαa, map_mul, map_mul, map_inv]

theorem fk_congr_descAut_conj {e : Proj₈ ≃* omegaProj (nondegenerate_quadPlus 4 (ZMod 3))}
    (α : MulAut (spinGroup Q₄)) (y : spinGroup Q₄)
    (hαy : ∀ x, spinAction Q₄ (α x) = spinAction Q₄ y * spinAction Q₄ x * (spinAction Q₄ y)⁻¹) :
    MulAut.congr e (Q3MFOD.descAut α) = MulAut.conj (e (d4Proj (GaloisField 3 1) y)) := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨p, rfl⟩ := e.surjective z
  obtain ⟨x, rfl⟩ := Q3MFOD.d4Proj_surjective p
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    Q3MFOD.descAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv, ← map_mul, ← map_mul]
  exact d4Proj_eq_of_spinAction_eq (by rw [hαy, map_mul, map_mul, map_inv])

end CFSG.OddStandard.SmallF3.Omega
