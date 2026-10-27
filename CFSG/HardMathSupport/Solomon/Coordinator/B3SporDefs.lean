module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamAltQ

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def B3SporPair (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      ∀ β : MulAut S, β ^ p = 1 →
        ⁅GLAPLayer p (fixSubgroup β), GLAPPrimeCoreOf p (fixSubgroup β)⁆ = ⊥

theorem b3SimpleSpor_of_pairs (h : ∀ name, B3SporPair name 3) : B3SimpleSpor := by
  intro S _ _ hs hnc ⟨name, he⟩ β hβ
  exact h name S hs hnc he β hβ

theorem input14_5_of_quotient {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (K : Subgroup Y)
    (hB : ∀ β : MulAut (↥K ⧸ Subgroup.center ↥K), β ^ p = 1 →
      ⁅GLAPLayer p (fixSubgroup β), GLAPPrimeCoreOf p (fixSubgroup β)⁆ = ⊥)
    {x : Y} (hx : x ∈ Subgroup.normalizer (K : Set Y))
    (hxp : K ≤ Subgroup.centralizer ({x ^ p} : Set Y)) {J : Subgroup Y}
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Y)) J) :
    CFSG.Open.IsQuasisimple ↥J := by
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
  let π : ↥K →* ↥K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := (QuotientGroup.ker_mk' _).le
  have hmap : Z.map α₀.toMonoidHom = Z := Subgroup.characteristic_iff_map_eq.1 inferInstance α₀
  let β : MulAut (↥K ⧸ Z) := QuotientGroup.congr Z Z α₀ hmap
  have hαβ : ∀ k, π (α₀ k) = β (π k) := fun k => rfl
  have hβp : β ^ p = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨k, rfl⟩ := hπ q
    rw [← intertwine_pow π α₀ β hαβ, hα₀p]
    rfl
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
  have hA : CFSG.Open.IsQuasisimple ↥(J₁.map π) := by
    refine isQuasisimple_of_glaPComponent_of_comm hp hJβ (fun g hg o ho => ?_)
    have hgL : g ∈ GLAPLayer p (fixSubgroup β) :=
      (le_sSup hJβ : J₁.map π ≤ GLAPLayer p (fixSubgroup β)) hg
    have h1 : ⁅g, o⁆ ∈ (⊥ : Subgroup _) :=
      hB β hβp ▸ Subgroup.commutator_mem_commutator hgL ho
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
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

theorem input14_5Spor_of_pairs (h : ∀ name p, p.Prime → p ≠ 2 → B3SporPair name p) :
    Input14_5Spor := by
  intro Y _ _ p hp hp2 K hq hK ⟨name, ⟨e⟩⟩ x hx hnc hxp J hJ
  obtain ⟨hnab, -⟩ := I1420.catalog_of_quasisimple hq hK
  have hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  refine input14_5_of_quotient hp K ?_ hx hxp hJ
  intro β hβ
  exact h name p hp hp2 _ hsimple hnab ⟨e⟩ β hβ

end CFSG.HardMathSupport.Solomon.Coordinator
