module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EULift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L3Uni
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Frame
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut (unitaryConjHom coe_unitaryConjHom)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

abbrev scal3 (p f : ℕ) (K : Type) [Field K] : Subgroup (unitarySU p f K 3) :=
  (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K)

theorem val_of_mem_scal3 {z : unitarySU p f K 3} (hz : z ∈ scal3 p f K) :
    ∃ c : Kˣ, ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (c : K) • 1 := by
  have hz' : (z : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := hz
  obtain ⟨c, hc⟩ := hz'
  refine ⟨c, ?_⟩
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
  rfl

theorem mem_center_of_mem_scal3 {z : unitarySU p f K 3} (hz : z ∈ scal3 p f K) :
    z ∈ Subgroup.center (unitarySU p f K 3) := by
  have hz' : (z : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := hz
  obtain ⟨c, hc⟩ := hz'
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
  have hcen : GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.mp hcen _

include h in
theorem eq_smul_of_comm3 {M : Matrix (Fin 3) (Fin 3) K}
    (hM : ∀ g : unitarySU p f K 3, M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M) :
    ∃ c : K, M = c • 1 := by
  have hq : 2 ≤ p ^ f := by
    have := h.prime.two_le
    calc 2 ≤ p := this
      _ ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
  refine RankThree.PartOne.KCUnitary.exists_smul_one_of_commute_gramSU h (by norm_num) hq
    fun A hA => ?_
  rw [← unitarySU_eq_gramSU h] at hA
  exact (hM ⟨A, hA⟩).symm

theorem exists_lift3 (hp2 : p ≠ 2) (α : MulAut (StatedProj (StatedSU 3 (p ^ f) K)))
    (hα : ∀ x, α (α x) = x) :
    ∃ (A : GL (Fin 3) K) (ψ : unitarySU p f K 3 →* unitarySU p f K 3),
      uStar h (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      (∀ g, α (QuotientGroup.mk g) = QuotientGroup.mk (ψ g)) ∧
      (((∀ g, ((ψ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (A : Matrix (Fin 3) (Fin 3) K) * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K)) ∧
        ∃ c : K, (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = c • 1) ∨
      ((∀ g, ((ψ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (A : Matrix (Fin 3) (Fin 3) K) *
            ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar *
            (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K)) ∧
        ∃ c : K, (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K).map h.bar =
          c • 1)) := by
  classical
  have : Finite K := h.finite
  set θ : unitarySU p f K 3 →* StatedProj (StatedSU 3 (p ^ f) K) :=
    QuotientGroup.mk' (scal3 p f K) with hθdef
  have hθ : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hker : θ.ker ≤ Subgroup.center (unitarySU p f K 3) := by
    rw [hθdef, QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal3 hz
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ :=
    GH74.Generic.S45.exists_lift_unitarySU' h hp2 (d := 3) (le_refl 3) θ hθ hker α
  obtain ⟨hφ, hcomp⟩ := hinv hα
  set ψ := unitaryConjHom A φ hA with hψdef
  have hcomp' : ∀ g : unitarySU p f K 3, ψ (ψ g) = g := fun g => by
    have := congrArg (fun F : unitarySU p f K 3 →* unitarySU p f K 3 => F g) hcomp
    exact this
  refine ⟨A, ψ, hAu, fun g => (hlift g).symm, ?_⟩
  rcases hφ with hφ1 | hφb
  · left
    subst hφ1
    have hgl1 : ∀ Y : GL (Fin 3) K, glAut (RingEquiv.refl K) Y = Y := fun Y => by
      change glAut 1 Y = Y
      rw [map_one]
      rfl
    refine ⟨fun g => ?_, ?_⟩
    · rw [hψdef, coe_unitaryConjHom, hgl1, Units.val_mul, Units.val_mul]
    · apply eq_smul_of_comm3 h
      intro g
      have e1 := congrArg (fun Y : unitarySU p f K 3 => (Y : GL (Fin 3) K)) (hcomp' g)
      simp only [hψdef, coe_unitaryConjHom, hgl1] at e1
      have e2 : A * A * (g : GL (Fin 3) K) = (g : GL (Fin 3) K) * (A * A) := by
        calc A * A * (g : GL (Fin 3) K) =
            (A * (A * (g : GL (Fin 3) K) * A⁻¹) * A⁻¹) * (A * A) := by group
          _ = (g : GL (Fin 3) K) * (A * A) := by rw [e1]
      have e3 := congrArg (fun Y : GL (Fin 3) K => (Y : Matrix (Fin 3) (Fin 3) K)) e2
      simpa only [Units.val_mul, Matrix.mul_assoc] using e3
  · right
    have hφb' : (φ : K → K) = h.bar := funext hφb
    have hφφ : φ * φ = 1 := RingEquiv.ext fun c => by
      change φ (φ c) = c
      rw [hφb, hφb, h.bar_bar]
    have hglφ : ∀ Y : GL (Fin 3) K, glAut φ (glAut φ Y) = Y := fun Y => by
      have := congrArg (fun χ : MulAut (GL (Fin 3) K) => χ Y)
        (show glAut φ * glAut φ = 1 by rw [← map_mul, hφφ, map_one])
      exact this
    refine ⟨fun g => ?_, ?_⟩
    · rw [hψdef, coe_unitaryConjHom, Units.val_mul, Units.val_mul, coe_glAut, hφb']
    · apply eq_smul_of_comm3 h
      intro g
      have e1 := congrArg (fun Y : unitarySU p f K 3 => (Y : GL (Fin 3) K)) (hcomp' g)
      simp only [hψdef, coe_unitaryConjHom, map_mul, map_inv, hglφ] at e1
      have e2 : A * glAut φ A * (g : GL (Fin 3) K) = (g : GL (Fin 3) K) * (A * glAut φ A) := by
        calc A * glAut φ A * (g : GL (Fin 3) K) =
            (A * (glAut φ A * (g : GL (Fin 3) K) * (glAut φ A)⁻¹) * A⁻¹) * (A * glAut φ A) := by
              group
          _ = (g : GL (Fin 3) K) * (A * glAut φ A) := by rw [e1]
      have e3 := congrArg (fun Y : GL (Fin 3) K => (Y : Matrix (Fin 3) (Fin 3) K)) e2
      simp only [Units.val_mul, coe_glAut] at e3
      rw [hφb'] at e3
      simpa only [Matrix.mul_assoc] using e3

abbrev ιU3 : StatedProj (StatedSU 3 (p ^ f) K) →* sesqProjUnitary h (stdHermForm h 3) :=
  EscapingNotOddUnitary.projEmbed h 3 (by norm_num)

theorem ιU3_injective : Function.Injective (ιU3 h) :=
  EscapingNotOddUnitary.projEmbed_injective h 3 (by norm_num)

theorem ιU3_range_normal : (ιU3 h).range.Normal := by
  rw [EscapingNotOddUnitary.range_projEmbed]
  exact EscapingNotOddUnitary.toProj_range_normal h 3

theorem ιU3_mk (g : unitarySU p f K 3) :
    ιU3 h (QuotientGroup.mk g) =
      QuotientGroup.mk (EscapingNotOddUnitary.toSesqUnitary h 3 g) :=
  rfl

@[expose] def toSesqU3 (A : GL (Fin 3) K)
    (hA : uStar h (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1) :
    sesqUnitaryGroup (stdHermForm h 3) :=
  ⟨Matrix.GeneralLinearGroup.toLin A, fun x y => by
    have h1 := (gramForm_isometry_iff h (1 : Matrix (Fin 3) (Fin 3) K)
      (A : Matrix (Fin 3) (Fin 3) K)).mpr (by rw [Matrix.mul_one]; exact hA) x y
    rw [← stdHermForm_eq_gramForm] at h1
    exact h1⟩

theorem unitaryOp_toSesqU3 (A : GL (Fin 3) K)
    (hA : uStar h (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1) :
    unitaryOp (toSesqU3 h A hA) = Matrix.toLin' (A : Matrix (Fin 3) (Fin 3) K) :=
  LinearMap.ext fun x => (Matrix.toLin'_apply _ x).symm

theorem unitaryOp_toSesqUnitary3 (g : unitarySU p f K 3) :
    unitaryOp (EscapingNotOddUnitary.toSesqUnitary h 3 g) =
      Matrix.toLin' ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  LinearMap.ext fun x => (EscapingNotOddUnitary.toSesqUnitary_apply h 3 g x).trans
    (Matrix.toLin'_apply _ _).symm

theorem u3_inner_false [Finite K] (hp2 : p ≠ 2)
    {β : MulAut (StatedProj (StatedSU 3 (p ^ f) K))} (hβ1 : β ≠ 1)
    {X' : Subgroup (StatedProj (StatedSU 3 (p ^ f) K))}
    (hX' : CFSG.Assembly.IsComponentOf X' (fixedSubgroup β)) (hs : SmallSource X')
    {A : GL (Fin 3) K}
    (hAu : uStar h (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1)
    {ψ : unitarySU p f K 3 →* unitarySU p f K 3}
    (hψ : ∀ g, β (QuotientGroup.mk g) = QuotientGroup.mk (ψ g))
    (hψA : ∀ g, ((ψ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K))
    {c₀ : K} (hAA : (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = c₀ • 1) :
    False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  set T := toSesqU3 h A hAu with hTdef
  set Zs := sesqNormOneScalars h (stdHermForm h 3)
  have he : ∀ y, ιU3 h (β y) = MulAut.conj (QuotientGroup.mk' Zs T) (ιU3 h y) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hψ, MulAut.conj_apply, ιU3_mk, ιU3_mk]
    change QuotientGroup.mk' Zs (EscapingNotOddUnitary.toSesqUnitary h 3 (ψ g)) =
      QuotientGroup.mk' Zs T * QuotientGroup.mk' Zs (EscapingNotOddUnitary.toSesqUnitary h 3 g) *
        (QuotientGroup.mk' Zs T)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    change ((ψ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      unitaryOp T (unitaryOp (EscapingNotOddUnitary.toSesqUnitary h 3 g)
        (unitaryOp T⁻¹ x))
    have hTi : unitaryOp T⁻¹ = Matrix.toLin' (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) := by
      apply LinearMap.ext
      intro v
      have h1 : unitaryOp T (Matrix.toLin' (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) v) = v := by
        rw [hTdef, unitaryOp_toSesqU3, Matrix.toLin'_apply, Matrix.toLin'_apply,
          Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      have hinvT : unitaryOp T⁻¹ * unitaryOp T = 1 := by
        rw [show unitaryOp T⁻¹ * unitaryOp T = unitaryOp (T⁻¹ * T) from rfl, inv_mul_cancel]
        rfl
      calc unitaryOp T⁻¹ v = unitaryOp T⁻¹ (unitaryOp T
          (Matrix.toLin' (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) v)) := by rw [h1]
        _ = Matrix.toLin' (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) v := by
          rw [← Module.End.mul_apply, hinvT, Module.End.one_apply]
    rw [hTi, hTdef, unitaryOp_toSesqU3, unitaryOp_toSesqUnitary3, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hψA,
      Matrix.mul_assoc]
  have key := Catalog7L4EU.isComponentOf_map_of_intertwine (ιU3 h) (ιU3_injective h)
    (ιU3_range_normal h) he hX'
  have hc₀ : h.norm c₀ = 1 := by
    have e1 := Catalog7U4.unitary_mul h hAu hAu
    rw [hAA, Catalog7U4.uStar_smul, uStar_one, smul_mul_smul_comm, Matrix.one_mul] at e1
    have e2 := congrFun (congrFun e1 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e2
    rw [UnitaryFieldData.norm, mul_comm]
    exact e2
  have hT2 : (QuotientGroup.mk' Zs T) ^ 2 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨c₀, hc₀, ?_⟩
    change unitaryOp (T * T) = c₀ • 1
    rw [show unitaryOp (T * T) = unitaryOp T * unitaryOp T from rfl, hTdef, unitaryOp_toSesqU3,
      Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hAA, map_smul, Matrix.toLin'_one]
    rfl
  have hT1 : QuotientGroup.mk' Zs T ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨d, -, hd⟩ := h1
    change unitaryOp T = d • 1 at hd
    rw [hTdef, unitaryOp_toSesqU3] at hd
    have hAd : (A : Matrix (Fin 3) (Fin 3) K) = d • 1 := by
      apply Matrix.toLin'.injective
      rw [hd, map_smul, Matrix.toLin'_one]
      rfl
    apply hβ1
    apply MulEquiv.ext
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hψ, MulAut.one_apply]
    congr 1
    apply Catalog7U4.SU_ext
    have h1 : (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hAd, Matrix.mul_smul, Matrix.mul_one] at h1
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h1
      exact zero_ne_one h1
    have hAi : (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) = d⁻¹ • 1 := by
      calc (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K) = d⁻¹ • (d • (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K)) :=
            by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
        _ = d⁻¹ • 1 := by rw [h1]
    rw [hψA, hAd, hAi, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h (stdHermForm h 3)) = 2 :=
    orderOf_eq_prime hT2 hT1
  have hZc := sesqNormOneScalars_le_center h (stdHermForm h 3)
  have hφZ := OddClassSelector.map_conj_eq_of_le_center hZc T
  have hX₂ := key
  rw [← OddClassSelector.onQuotient_conj T hφZ] at hX₂
  have hTT : T * T ∈ center (sesqUnitaryGroup (stdHermForm h 3)) := by
    apply hZc
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hT, pow_orderOf_eq_one]
  have hφφ : ∀ g, MulAut.conj T (MulAut.conj T g) = g := by
    intro g
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have h1 := mem_center_iff.mp hTT g
    calc T * (T * g * T⁻¹) * T⁻¹ = (T * T) * g * (T * T)⁻¹ := by group
      _ = g := by rw [← h1, mul_inv_cancel_right]
  obtain ⟨Y, hY, ⟨σY, hσYs, hσYk, hσYv⟩, -⟩ :=
    OddClassSelector.central_lift _ hZc _ hφZ hφφ hX₂
  rw [CatalogueBUnitaryB.fixedSubgroup_conj] at hY
  have eX : X' ≃* X'.map (ιU3 h) := X'.equivMapOfInjective _ (ιU3_injective h)
  have hs₂ : SmallSource (X'.map (ιU3 h)) := OddClassSelector.smallSource_of_mulEquiv eX hs
  exact OddClassSelector.Catalog7L3.su_linear_false3 h hp2 (by rw [Module.finrank_fin_fun])
    (stdHermForm_isSymm h 3) (stdHermForm_separatingLeft h 3) hT hY σY hσYs hσYk
    (fun y hy => by
      have h1 := hσYv y
      rw [hy] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1.symm) hs₂

end CFSG.ComponentClassification.GSThmB.CF23I
