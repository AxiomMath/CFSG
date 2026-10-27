module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUInner
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EULift

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

open CFSG Subgroup Module Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryConj (stdG)
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks (X1)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (scal)
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks (bd)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def centerQuotientCongr {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') :
    X ⧸ center X ≃* X' ⧸ center X' :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

abbrev ιU : StatedProj (StatedSU 4 (p ^ f) K) →* sesqProjUnitary h (stdHermForm h 4) :=
  EscapingNotOddUnitary.projEmbed h 4 (by norm_num)

theorem ιU_injective : Function.Injective (ιU h) :=
  EscapingNotOddUnitary.projEmbed_injective h 4 (by norm_num)

theorem ιU_range_normal : (ιU h).range.Normal := by
  rw [EscapingNotOddUnitary.range_projEmbed]
  exact EscapingNotOddUnitary.toProj_range_normal h 4

theorem ιU_mk (g : unitarySU p f K 4) :
    ιU h (QuotientGroup.mk g) =
      QuotientGroup.mk (EscapingNotOddUnitary.toSesqUnitary h 4 g) :=
  rfl

theorem psu4_inner_case [Finite K] (hp2 : p ≠ 2)
    {β : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hβ1 : β ≠ 1)
    {X' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hX' : CFSG.Assembly.IsComponentOf X' (fixedSubgroup β)) (hs : SmallSource X')
    {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    {ψ : unitarySU p f K 4 →* unitarySU p f K 4}
    (hψ : ∀ g, β (QuotientGroup.mk g) = QuotientGroup.mk (ψ g))
    (hψA : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {c₀ : K} (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = c₀ • 1) :
    Nonempty (X' ⧸ center X' ≃* GorensteinWalter.PSL2 K) ∧
      ∃ (l : K) (Q : GL (Fin 4) K), l ≠ 0 ∧ h.norm l = -1 ∧
        uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = stdG ∧
        (A : Matrix (Fin 4) (Fin 4) K) * Q = Q * X1 l := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  set T := Catalog7U4.toSesqU h A hAu with hTdef
  set Zs := sesqNormOneScalars h (stdHermForm h 4)
  have he : ∀ y, ιU h (β y) = MulAut.conj (QuotientGroup.mk' Zs T) (ιU h y) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hψ, MulAut.conj_apply, ιU_mk, ιU_mk]
    change QuotientGroup.mk' Zs (EscapingNotOddUnitary.toSesqUnitary h 4 (ψ g)) =
      QuotientGroup.mk' Zs T * QuotientGroup.mk' Zs (EscapingNotOddUnitary.toSesqUnitary h 4 g) *
        (QuotientGroup.mk' Zs T)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    change ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x =
      unitaryOp T (unitaryOp (EscapingNotOddUnitary.toSesqUnitary h 4 g)
        (unitaryOp T⁻¹ x))
    have hTi : unitaryOp T⁻¹ = Matrix.toLin' (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
      apply LinearMap.ext
      intro v
      have h1 : unitaryOp T (Matrix.toLin' (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) v) = v := by
        rw [hTdef, Catalog7U4.unitaryOp_toSesqU, Matrix.toLin'_apply, Matrix.toLin'_apply,
          Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      have hinvT : unitaryOp T⁻¹ * unitaryOp T = 1 := by
        rw [show unitaryOp T⁻¹ * unitaryOp T = unitaryOp (T⁻¹ * T) from rfl, inv_mul_cancel]
        rfl
      calc unitaryOp T⁻¹ v = unitaryOp T⁻¹ (unitaryOp T
          (Matrix.toLin' (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) v)) := by rw [h1]
        _ = Matrix.toLin' (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) v := by
          rw [← Module.End.mul_apply, hinvT, Module.End.one_apply]
    rw [hTi, hTdef, Catalog7U4.unitaryOp_toSesqU, Catalog7U4.unitaryOp_toSesqUnitary,
      Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hψA, Matrix.mul_assoc]
  have key := isComponentOf_map_of_intertwine (ιU h) (ιU_injective h) (ιU_range_normal h) he hX'
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
    rw [show unitaryOp (T * T) = unitaryOp T * unitaryOp T from rfl, hTdef,
      Catalog7U4.unitaryOp_toSesqU, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hAA, map_smul,
      Matrix.toLin'_one]
    rfl
  have hT1 : QuotientGroup.mk' Zs T ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨d, -, hd⟩ := h1
    change unitaryOp T = d • 1 at hd
    rw [hTdef, Catalog7U4.unitaryOp_toSesqU] at hd
    have hAd : (A : Matrix (Fin 4) (Fin 4) K) = d • 1 := by
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
    have h1 : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hAd, Matrix.mul_smul, Matrix.mul_one] at h1
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h1
      exact zero_ne_one h1
    have hAi : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = d⁻¹ • 1 := by
      calc (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = d⁻¹ • (d • (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) :=
            by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
        _ = d⁻¹ • 1 := by rw [h1]
    rw [hψA, hAd, hAi, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h (stdHermForm h 4)) = 2 :=
    orderOf_eq_prime hT2 hT1
  have hZc := sesqNormOneScalars_le_center h (stdHermForm h 4)
  have hφZ := OddClassSelector.map_conj_eq_of_le_center hZc T
  have hX₂ := key
  rw [← OddClassSelector.onQuotient_conj T hφZ] at hX₂
  have hTT : T * T ∈ center (sesqUnitaryGroup (stdHermForm h 4)) := by
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
  have eX : X' ≃* X'.map (ιU h) := X'.equivMapOfInjective _ (ιU_injective h)
  have hs₂ : SmallSource (X'.map (ιU h)) := OddClassSelector.smallSource_of_mulEquiv eX hs
  obtain ⟨⟨eP⟩, hbasis⟩ := inner_type h hp2 hAu hT hY σY hσYs hσYk
    (fun y hy => by
      have h1 := hσYv y
      rw [hy] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1.symm) hs₂
  exact ⟨⟨(centerQuotientCongr eX).trans eP⟩, hbasis⟩

theorem psu4_anti_case [Finite K] (hp2 : p ≠ 2)
    {β : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    {X' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hX' : CFSG.Assembly.IsComponentOf X' (fixedSubgroup β)) (hs : SmallSource X')
    {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    {ψ : unitarySU p f K 4 →* unitarySU p f K 4}
    (hψ : ∀ g, β (QuotientGroup.mk g) = QuotientGroup.mk (ψ g))
    (hψA : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {z : K} (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      z • 1) :
    z = 1 ∧
      ((5 ≤ Nat.card h.fixedField ∧
          Nonempty (X' ⧸ center X' ≃* GorensteinWalter.PSL2 h.fixedField) ∧
          (∃ u : K, h.norm u = 1 ∧ (A : Matrix (Fin 4) (Fin 4) K).det = u ^ 2) ∧
          ∃ Y : Subgroup (sesqUnitaryGroup (stdHermForm h 4)), ⁅Y, Y⁆ = Y ∧
            (∃ φq : QuaternionGroup 2 →* Y, Function.Injective φq) ∧
            ∀ y ∈ Y, (QuotientGroup.mk y : sesqProjUnitary h (stdHermForm h 4)) ∈ X'.map (ιU h)) ∨
        ((∃ (E' : Type) (_ : Field E') (_ : Finite E'),
            Nat.card E' = Nat.card h.fixedField ^ 2 ∧
            Nonempty (X' ⧸ center X' ≃* GorensteinWalter.PSL2 E')) ∧
          ∀ Y₁ : Subgroup (sesqUnitaryGroup (stdHermForm h 4)), ⁅Y₁, Y₁⁆ = Y₁ →
            Y₁ ≤ fixedSubgroup (antiConjA h hAu) →
            ∀ φq : QuaternionGroup 2 →* Y₁, ¬ Function.Injective φq)) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hτ := CatFactsL4U4.StabU.antiunitaryMap_bijective h A
  have hτB := CatFactsL4U4.StabU.stdHermForm_antiunitaryMap h hAu
  have he : ∀ y, ιU h (β y) = antiProjConj h (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))
      hτ hτB (ιU h y) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hψ, ιU_mk, ιU_mk, antiProjConj_mk]
    congr 1
    exact (toSesqUnitary_antiConj h hAu g (ψ g) (hψA g)).symm
  have key := isComponentOf_map_of_intertwine (ιU h) (ιU_injective h) (ιU_range_normal h) he hX'
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hAA
    have h1 := congrArg Matrix.det hAA
    rw [det_mul, det_zero, show (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin 4) (Fin 4) K) from rfl, ← RingHom.map_det] at h1
    have hA0 : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact mul_ne_zero hA0 (fun h0 => hA0 ((map_eq_zero h.bar).1 h0)) h1
  have hZc := sesqNormOneScalars_le_center h (stdHermForm h 4)
  obtain ⟨Y, hY, ⟨σY, hσYs, hσYk, hσYv⟩, -⟩ := OddClassSelector.central_lift _ hZc _
    (map_scalars_unitaryConj h _ _ hτB)
    (unitaryConj_unitaryConj h _ _ hτB (Units.mk0 z hz0)
      (CatFactsL4U4.StabU.antiunitaryMap_sq h _ hAA)) key
  have eX : X' ≃* X'.map (ιU h) := X'.equivMapOfInjective _ (ιU_injective h)
  have hs₂ : SmallSource (X'.map (ιU h)) := OddClassSelector.smallSource_of_mulEquiv eX hs
  obtain ⟨hz1, hcase⟩ := anti_type h hp2 hAu hAA hY σY hσYs hσYk hs₂
  refine ⟨hz1, ?_⟩
  rcases hcase with ⟨h5, ⟨eP⟩, hdet, hq⟩ | ⟨⟨E', _, _, hE', ⟨eP⟩⟩, hno⟩
  · left
    have : Group.IsPerfect Y := ⟨hY.2.2.1⟩
    refine ⟨h5, ⟨(centerQuotientCongr eX).trans eP⟩, hdet, Y,
      Subgroup.commutator_eq_self (H := Y), hq, fun y hy => ?_⟩
    have h1 := hσYv ⟨y, hy⟩
    rw [← QuotientGroup.mk'_apply]
    rw [← h1]
    exact (σY ⟨y, hy⟩).2
  · right
    exact ⟨⟨E', inferInstance, inferInstance, hE', ⟨(centerQuotientCongr eX).trans eP⟩⟩, hno⟩

end Catalog7L4EU

end CFSG.ComponentClassification.GSThmB
