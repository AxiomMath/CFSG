module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamSplit
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem b3Lie_intertwine_pow {K Q : Type*} [Group K] [Group Q] (π : K →* Q) (α : MulAut K)
    (β : MulAut Q) (h : ∀ k, π (α k) = β (π k)) (m : ℕ) (k : K) :
    π ((α ^ m) k) = (β ^ m) (π k) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, h]

theorem input14_5Lie_of_bpSimpleLie (hB : BpSimpleLie) : Input14_5Lie := by
  intro Y _ _ p hp hp2 K hq hK ⟨idx, ⟨e⟩⟩ x hx hnc hxp J hJ
  let α₀ : MulAut ↥K := K.normalizerMonoidHom ⟨x, hx⟩
  have hα₀ : ∀ k : ↥K, ((α₀ k : ↥K) : Y) = x * k * x⁻¹ := fun k => rfl
  have hα₀p : α₀ ^ p = 1 := by
    ext k
    have : (α₀ ^ p : MulAut ↥K) = K.normalizerMonoidHom (⟨x, hx⟩ ^ p) := by rw [map_pow]
    rw [this]
    have hk : ((K.normalizerMonoidHom (⟨x, hx⟩ ^ p) k : ↥K) : Y) = x ^ p * k * (x ^ p)⁻¹ := rfl
    rw [MulAut.one_apply, hk]
    have := Subgroup.mem_centralizer_iff.1 (hxp k.2) (x ^ p) rfl
    calc x ^ p * (k : Y) * (x ^ p)⁻¹ = (k : Y) * x ^ p * (x ^ p)⁻¹ := by rw [← this]
      _ = (k : Y) := by group
  let Z := Subgroup.center ↥K
  let π : ↥K →* (↥K ⧸ Z) := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  have hmap : Z.map α₀.toMonoidHom = Z := Subgroup.characteristic_iff_map_eq.1 inferInstance α₀
  let β : MulAut (↥K ⧸ Z) := QuotientGroup.congr Z Z α₀ hmap
  have hαβ : ∀ k, π (α₀ k) = β (π k) := fun k => rfl
  have hβp : β ^ p = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨k, rfl⟩ := hπ q
    rw [← b3Lie_intertwine_pow π α₀ β hαβ, hα₀p]
    rfl
  have hnab : ∃ a b : ↥K ⧸ Z, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hB' := hB (↥K ⧸ Z) hq.2 hnab ⟨idx, ⟨e⟩⟩ p hp hp2 β hβp
  set X : Subgroup ↥K := fixSubgroup α₀ with hX
  have hXmap : X.map K.subtype = K ⊓ Subgroup.centralizer ({x} : Set Y) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      have h1 : x * (k : Y) * x⁻¹ = k := by
        have := congrArg Subtype.val (show α₀ k = k from hk)
        rwa [hα₀] at this
      refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      show (k : Y) * x = x * (k : Y)
      calc (k : Y) * x = (x * (k : Y) * x⁻¹) * x := by rw [h1]
        _ = x * (k : Y) := by group
    · rintro ⟨hyK, hyC⟩
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      show α₀ ⟨y, hyK⟩ = ⟨y, hyK⟩
      apply Subtype.ext
      rw [hα₀]
      have hyC' : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
      show x * y * x⁻¹ = y
      calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [hyC']
        _ = y := by group
  have hc : ∀ y ∈ X ⊓ K.subtype.ker, ∀ z ∈ X, z * y = y * z := by
    intro y hy z _
    have : y = 1 := Subtype.ext (MonoidHom.mem_ker.1 hy.2)
    rw [this, mul_one, one_mul]
  have hJ0 : GLAPComponent p (X.map K.subtype) J := by rw [hXmap]; exact hJ
  obtain ⟨J₁, hJ₁, hJ₁map⟩ := exists_glaPComponent_map_central hp K.subtype hc hJ0
  have hJβ : GLAPComponent p (fixSubgroup β) (J₁.map π) :=
    glaPComponent_map_fixSubgroup π hker α₀ β hαβ hπ hp hJ₁
  have hle : J₁.map π ≤ GLAPLayer p (fixSubgroup β) := le_sSup hJβ
  have hA : CFSG.Open.IsQuasisimple ↥(J₁.map π) :=
    isQuasisimple_of_glaPComponent_of_comm hp hJβ
      (fun g hg o ho =>
        Subgroup.mem_centralizer_iff.1
          (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hB' (hle hg)) o ho)
  have hperf : Group.IsPerfect ↥J₁ := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ₁)
  have hQ1 : CFSG.IsQuasisimple ↥J₁ :=
    isQuasisimple_of_central_cover (π.subgroupMap J₁) (MonoidHom.subgroupMap_surjective π J₁)
      hperf (ker_subgroupMap_le_center π hker J₁)
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hA)
  have hQ1' : CFSG.Open.IsQuasisimple ↥J₁ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hQ1
  have e₂ : ↥J₁ ≃* ↥J :=
    (J₁.equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hJ₁map)
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₂ hQ1'

theorem input14_5Lie_of_unipotentCore (hU : LieUnipotentCore) (hss : LieSemisimpleCent)
    (hout : LieDefCharOuter) : Input14_5Lie :=
  input14_5Lie_of_bpSimpleLie (bpSimpleLie_of_unipotentCore hU hss hout)

end CFSG.HardMathSupport.Solomon.Coordinator
