module

public import CFSG.GH74.GLS.IVK.L2.Involutions
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.FixedCentralizer
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

section Bridge

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

omit [Finite K] in
theorem centralizer_innDiag_equiv (A : PGL2 F) :
    Nonempty (↥(centralizer ({innDiagHom e A} : Set (MulAut K)) ⊓ innDiagSub e) ≃*
      ↥(centralizer ({A} : Set (PGL2 F)))) := by
  have hmap : centralizer ({innDiagHom e A} : Set (MulAut K)) ⊓ innDiagSub e =
      (centralizer ({A} : Set (PGL2 F))).map (innDiagHom e) := by
    ext x
    constructor
    · rintro ⟨hx, B, rfl⟩
      refine ⟨B, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
      apply innDiagHom_injective e
      rw [map_mul, map_mul]
      exact hx'
    · rintro ⟨B, hB, rfl⟩
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, B, rfl⟩
      have hB' := Subgroup.mem_centralizer_singleton_iff.mp hB
      rw [← map_mul, ← map_mul, hB']
  exact ⟨(MulEquiv.subgroupCongr hmap).trans
    ((centralizer ({A} : Set (PGL2 F))).equivMapOfInjective (innDiagHom e)
      (innDiagHom_injective e)).symm⟩

end Bridge

theorem ivk_1_3a : IVK_1_3a := by
  intro F _ _ hF K _ _ e ε hε1 hε d hd u hu
  have hpp := isOddPrimePower_of_L2Field hF
  have hq3 := hF.2
  obtain ⟨s5, hs5⟩ := hF.1
  have hd4 : 4 ≤ d := by omega
  have hA2 : orderOf (kToPGL e u) = 2 := by
    rw [orderOf_injective (kToPGL e) (kToPGL_injective e) u]
    exact hu
  have hAK : kToPGL e u ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    ⟨toPSL e u, rfl⟩
  obtain ⟨m, hm, ⟨φ⟩⟩ := (pgl2_involution_centralizer_dihedral hpp hq3 hε1 hε hA2).1 hAK
  have hmd : m = d := by omega
  subst hmd
  refine ⟨?_, ?_, ?_⟩
  ·
    have hconj : innDiagHom e (kToPGL e u) = MulAut.conj u := innDiagHom_toPGL e u
    have hψ := centralizer_innDiag_equiv e (kToPGL e u)
    rw [hconj] at hψ
    obtain ⟨ψ⟩ := hψ
    exact ⟨m, rfl, by omega, ⟨ψ.trans φ⟩⟩
  ·
    have ht2 : orderOf (toPSL e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    obtain ⟨m', hm', ⟨φ'⟩⟩ :=
      CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hpp hε hε1 ht2
    obtain ⟨ψ⟩ := DihedralAux.centralizer_equiv_of_mulEquiv (toPSL e) u
    exact ⟨m', by omega, by omega, ⟨ψ.trans φ'⟩⟩
  ·
    intro û hû
    have hker : ∀ y : SL2 F, L2.mk F y = 1 ↔
        y ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) := fun y =>
      QuotientGroup.eq_one_iff y
    exact sl2_centralizer_lift_involution hF ε hε1 hε m hm (L2.mk F) hker e u hu û hû

theorem ivk_1_3b_dihedral {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type} [Group K]
    [Finite K] (e : K ≃* L2 F) (ε : ℤ) (hε1 : ε = 1 ∨ ε = -1)
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (d : ℕ) (hd : (d : ℤ) = Nat.card F + ε)
    (v : MulAut K) (hv : v ∈ innDiagSub e) (hvI : v ∉ innAut K) (hv2 : orderOf v = 2) :
    IsDihedralOrder ↥(centralizer ({v} : Set (MulAut K)) ⊓ innDiagSub e) (2 * d) ∧
      IsDihedralOrder ↥(fixedSubgroup K v) d := by
  have hpp := isOddPrimePower_of_L2Field hF
  have hq3 := hF.2
  obtain ⟨s5, hs5⟩ := hF.1
  obtain ⟨B, rfl⟩ := hv
  have hBout : B ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    fun h => hvI ((innDiagHom_mem_innAut_iff e B).mpr h)
  have hB2 : orderOf B = 2 := by
    rw [← orderOf_injective (innDiagHom e) (innDiagHom_injective e) B]
    exact hv2
  constructor
  · obtain ⟨m, hm, ⟨φ⟩⟩ := (pgl2_involution_centralizer_dihedral hpp hq3 hε1 hε hB2).2 hBout
    obtain ⟨ψ⟩ := centralizer_innDiag_equiv e B
    have hmd : m = d := by omega
    subst hmd
    exact ⟨m, rfl, by omega, ⟨ψ.trans φ⟩⟩
  · obtain ⟨m, hm, ⟨φ⟩⟩ := CFSG.ABGDGroups.pgl2_inf_centralizer_outer_involution_dihedral hpp hε hε1
      hB2 hBout
    have hmap : (fixedSubgroup K (innDiagHom e B)).map (kToPGL e) =
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ⊓
          centralizer ({B} : Set (PGL2 F)) := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨⟨toPSL e k, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hk' : innDiagHom e B k = k := hk
        have h1 := toPGL_toPSL_innDiagHom e B k
        rw [hk'] at h1
        rw [kToPGL_apply]
        calc Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e k) * B
            = (B * Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e k) * B⁻¹) * B := by rw [← h1]
          _ = B * Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e k) := by group
      · rintro ⟨⟨s, rfl⟩, hy⟩
        refine ⟨(toPSL e).symm s, ?_, by rw [kToPGL_apply, MulEquiv.apply_symm_apply]⟩
        have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
        show innDiagHom e B ((toPSL e).symm s) = (toPSL e).symm s
        apply kToPGL_injective e
        rw [kToPGL_apply, kToPGL_apply, toPGL_toPSL_innDiagHom, MulEquiv.apply_symm_apply]
        calc B * Matrix.ProjectiveSpecialLinearGroup.toPGL s * B⁻¹
            = (B * Matrix.ProjectiveSpecialLinearGroup.toPGL s) * B⁻¹ := rfl
          _ = (Matrix.ProjectiveSpecialLinearGroup.toPGL s * B) * B⁻¹ := by rw [← hy']
          _ = Matrix.ProjectiveSpecialLinearGroup.toPGL s := by group
    have ψ : ↥(fixedSubgroup K (innDiagHom e B)) ≃*
        ↥((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ⊓
          centralizer ({B} : Set (PGL2 F))) :=
      ((fixedSubgroup K (innDiagHom e B)).equivMapOfInjective (kToPGL e)
        (kToPGL_injective e)).trans (MulEquiv.subgroupCongr hmap)
    exact ⟨m, by omega, by omega, ⟨ψ.trans φ⟩⟩

theorem ivk_1_3b : IVK_1_3b := by
  intro F _ _ hF K _ _ e ε hε1 hε d hd v hv hvI hv2
  obtain ⟨hi, hii⟩ := ivk_1_3b_dihedral hF e ε hε1 hε d hd v hv hvI hv2
  refine ⟨hi, hii, ?_⟩
  intro g hg
  subst hg
  have hB2 : orderOf (Matrix.ProjGenLinGroup.mk g) = 2 := by
    rw [← orderOf_injective (innDiagHom e) (innDiagHom_injective e)]
    exact hv2
  have hBB : Matrix.ProjGenLinGroup.mk g * Matrix.ProjGenLinGroup.mk g = 1 := by
    have := pow_orderOf_eq_one (Matrix.ProjGenLinGroup.mk g)
    rwa [hB2, pow_two] at this
  have hgg : g * g ∈ Subgroup.center (GL (Fin 2) F) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    rw [map_mul]
    exact hBB
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hgg
  obtain ⟨u, hu⟩ := hgg
  have hsq : (g : Matrix (Fin 2) (Fin 2) F) * g = (u : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hu
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mul] at this
    rw [Matrix.smul_one_eq_diagonal]
    exact this.symm
  have hns : ¬ ∃ s : F, (g : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      have : (g : Matrix (Fin 2) (Fin 2) F).det = 0 := by
        rw [hs]; simp
      exact g.det.ne_zero (by simpa using this)
    have hgs : g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 s hs0) := by
      apply Units.ext
      rw [hs, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
      rfl
    have : Matrix.ProjGenLinGroup.mk g = 1 := by rw [hgs]; exact Matrix.ProjGenLinGroup.mk_scalar _
    rw [this, orderOf_one] at hB2
    omega
  have hBout : Matrix.ProjGenLinGroup.mk g ∉
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    fun h => hvI ((innDiagHom_mem_innAut_iff e _).mpr h)
  have hdet : ¬ IsSquare (g : Matrix (Fin 2) (Fin 2) F).det := by
    intro h
    exact hBout ((pgl2_mk_mem_psl2_range_iff_det_isSquare g).mpr h)
  exact slCentralizer_outer_involution hF ε hε1 hε d hd g ⟨(u : F), hsq⟩ hns hdet

end CFSG.GH74.GLS.IVK
