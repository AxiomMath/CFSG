module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Core

public noncomputable section

namespace CFSG.GH74.GLS.IVK

open Subgroup Module Matrix CFSG.ComponentClassification.RestrictedStd
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OddClassSelector
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)



variable {p f : ℕ} {K : Type} [Field K]

@[expose] def hypIota (hud : UnitaryFieldData p f K) (r ε : ℕ) :
    hypPSU hud r ε →* sesqProjUnitary hud (hypForm hud r ε) :=
  (projSpecial hud (hypForm hud r ε)).subtype.comp (hypModelEquiv hud).toMonoidHom

theorem hypIota_injective (hud : UnitaryFieldData p f K) (r ε : ℕ) :
    Function.Injective (hypIota hud r ε) :=
  Subtype.val_injective.comp (hypModelEquiv hud).injective

theorem key_component (hud : UnitaryFieldData p f K) (r ε : ℕ) {X : Subgroup (hypPSU hud r ε)}
    (β : MulAut (hypPSU hud r ε)) (ψ : MulAut (sesqProjUnitary hud (hypForm hud r ε)))
    (he : ∀ y, hypIota hud r ε (β y) = ψ (hypIota hud r ε y))
    (hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup β)) :
    CFSG.Assembly.IsComponentOf (X.map (hypIota hud r ε)) (fixedSubgroup ψ) := by
  have hmap : (fixedSubgroup β).map (hypIota hud r ε) = projSpecial hud (hypForm hud r ε) ⊓
      fixedSubgroup ψ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(hypModelEquiv hud y).2, ?_⟩
      change ψ (hypIota hud r ε y) = hypIota hud r ε y
      rw [← he]
      exact congrArg (hypIota hud r ε) hy
    · rintro ⟨hzN, hzψ⟩
      obtain ⟨y, hy⟩ := (hypModelEquiv hud).surjective ⟨z, hzN⟩
      have hyz : hypIota hud r ε y = z := congrArg Subtype.val hy
      refine ⟨y, ?_, hyz⟩
      change β y = y
      apply hypIota_injective hud r ε
      rw [he, hyz]
      exact hzψ
  have h1 := CFSG.ComponentClassification.SymmetricLocal.isComponentOf_map_of_injective (hypIota hud r ε)
    (hypIota_injective hud r ε) hX
  rw [hmap] at h1
  refine isComponentOf_of_normal_le h1 inf_le_right ?_
  constructor
  intro m hm g
  rw [Subgroup.mem_subgroupOf] at hm ⊢
  exact ⟨(projSpecial_normal hud (hypForm hud r ε)).conj_mem _ hm.1
    (g : sesqProjUnitary hud _), Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hm.2)
      (Subgroup.inv_mem _ g.2)⟩

theorem hypIota_apply (hud : UnitaryFieldData p f K) (r ε : ℕ) (y : hypPSU hud r ε) :
    hypIota hud r ε y = ((hypModelEquiv hud y : projSpecial hud (hypForm hud r ε)) :
      sesqProjUnitary hud (hypForm hud r ε)) := rfl

section Intertwine

variable (hud : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)

theorem linear_intertwine (A : GL (HypIndex r ε) K) (hA : A ∈ hypUnitary hud r ε)
    (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes hud r ε)
    (α : MulAut (hypPSU hud r ε)) (hΦ : semilinearAutHom hud hr hε ⟨_, hx⟩ = α) (y : hypPSU hud r ε) :
    hypIota hud r ε (α y) =
      MulAut.conj (QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε))
        (hypUnitaryEquiv hud ⟨A, hA⟩)) (hypIota hud r ε y) := by
  obtain ⟨g, rfl⟩ := hypProj_surjective hud r ε y
  have happly : α (hypProj hud r ε g) = hypProj hud r ε ⟨_, conj_mem_hypSU hx g⟩ := by
    rw [← hΦ]
    exact semilinearAutHom_apply hud hr hε _ g
  rw [happly, hypIota_apply, hypIota_apply]
  refine hypModelEquiv_conj hud ⟨A, hA⟩ g _ ?_
  have hg : glAut (RingEquiv.refl K) (g : GL (HypIndex r ε) K) = (g : GL (HypIndex r ε) K) :=
    congrArg (fun φ : MulAut (GL (HypIndex r ε) K) => φ (g : GL (HypIndex r ε) K))
      (map_one glAut)
  change A * glAut (RingEquiv.refl K) (g : GL (HypIndex r ε) K) * A⁻¹ = _
  rw [hg]

theorem anti_intertwine (A : GL (HypIndex r ε) K) (σ : K ≃+* K) (hσ : ∀ c, σ c = hud.bar c)
    (hA : A ∈ hypUnitary hud r ε)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes hud r ε)
    (β : MulAut (hypPSU hud r ε)) (hΦ : semilinearAutHom hud hr hε ⟨_, hx⟩ = β) {c : K}
    (hc0 : c ≠ 0)
    (hAc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map hud.bar = c • 1)
    (y : hypPSU hud r ε) :
    hypIota hud r ε (β y) =
      antiProjConj hud (semilinearMatrixMap hud (A : Matrix (HypIndex r ε) (HypIndex r ε) K))
        (semilinearMatrixMap_bijective hud hc0 hAc) (hypForm_semilinearMatrixMap hud hA)
        (hypIota hud r ε y) := by
  obtain ⟨g, rfl⟩ := hypProj_surjective hud r ε y
  have happly : β (hypProj hud r ε g) = hypProj hud r ε ⟨_, conj_mem_hypSU hx g⟩ := by
    rw [← hΦ]
    exact semilinearAutHom_apply hud hr hε _ g
  rw [happly, hypIota_apply, hypIota_apply]
  exact hypModelEquiv_antiConj hud A hc0 hAc (hypForm_semilinearMatrixMap hud hA) σ hσ g _

end Intertwine

section Gamma

variable (hud : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε)

include hn in
theorem gamma_right_eq {x y : semilinearSimilitudes hud r ε}
    (hxy : semilinearAutHom hud hr hε x = semilinearAutHom hud hr hε y) :
    (x : SemiGL (HypIndex r ε) K).right = (y : SemiGL (HypIndex r ε) K).right := by
  have h1 : semilinearAutHom hud hr hε (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have h2 := ((semilinearAutHom_eq_one_iff hud hr hε hn _).mp h1).1
  have h3 : ((x⁻¹ * y : semilinearSimilitudes hud r ε) : SemiGL (HypIndex r ε) K).right =
      (x : SemiGL (HypIndex r ε) K).right⁻¹ * (y : SemiGL (HypIndex r ε) K).right := by
    rw [Subgroup.coe_mul, SemidirectProduct.mul_right, Subgroup.coe_inv,
      SemidirectProduct.inv_right]
  rw [h3] at h2
  exact inv_mul_eq_one.mp h2

include hn in
theorem gamma_comm (x y : semilinearSimilitudes hud r ε)
    (hxy : semilinearAutHom hud hr hε x * semilinearAutHom hud hr hε y =
      semilinearAutHom hud hr hε y * semilinearAutHom hud hr hε x) :
    ∃ c : K, c ≠ 0 ∧
      ((x : SemiGL (HypIndex r ε) K).left : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          ((glAut (x : SemiGL (HypIndex r ε) K).right (y : SemiGL (HypIndex r ε) K).left :
            GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        c • (((y : SemiGL (HypIndex r ε) K).left : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          ((glAut (y : SemiGL (HypIndex r ε) K).right (x : SemiGL (HypIndex r ε) K).left :
            GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) := by
  set z : semilinearSimilitudes hud r ε := (y * x)⁻¹ * (x * y) with hz
  have h1 : semilinearAutHom hud hr hε z = 1 := by
    rw [hz, map_mul, map_inv, map_mul, map_mul, hxy, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := (semilinearAutHom_eq_one_iff hud hr hε hn z).mp h1
  have hxyz : x * y = (y * x) * z := by rw [hz, mul_inv_cancel_left]
  have hleft := congrArg (fun w : semilinearSimilitudes hud r ε =>
    ((w : SemiGL (HypIndex r ε) K).left : GL (HypIndex r ε) K)) hxyz
  simp only [Subgroup.coe_mul, SemidirectProduct.mul_left, SemidirectProduct.mul_right] at hleft
  rw [hc] at hleft
  have hmat := congrArg (fun g : GL (HypIndex r ε) K => (g : Matrix (HypIndex r ε) (HypIndex r ε) K))
    hleft
  simp only [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar] at hmat
  have hsc : ∀ (σ : K ≃+* K) (a : K), (Matrix.scalar (HypIndex r ε) a).map σ =
      Matrix.scalar (HypIndex r ε) (σ a) := by
    intro σ a
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ)]
  rw [hsc] at hmat
  refine ⟨((y : SemiGL (HypIndex r ε) K).right * (x : SemiGL (HypIndex r ε) K).right) (c : K), ?_, ?_⟩
  · exact (map_ne_zero _).mpr c.ne_zero
  · simp only [coe_glAut]
    rw [hmat, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

end Gamma

section PLevel

variable (hud : UnitaryFieldData p f K)

theorem unitaryOp_hypUnitaryEquiv {r ε : ℕ} (A : hypUnitary hud r ε) (v : HypIndex r ε → K) :
    unitaryOp (hypUnitaryEquiv hud A) v = (A : GL (HypIndex r ε) K) *ᵥ v :=
  toLin_hyp_apply _ _

instance finite_sesqUnitaryGroup_hyp [Finite K] (r ε : ℕ) :
    Finite (sesqUnitaryGroup (hypForm hud r ε)) := by
  infer_instance

end PLevel

section LinLin

variable (hud : UnitaryFieldData p f K)

theorem su4_lin_lin (hp : p ≠ 2) {X : Subgroup (hypPSU hud 2 0)} (hs : SmallSource X)
    {α β : MulAut (hypPSU hud 2 0)} (hcomm : α * β = β * α) (hne : α ≠ β)
    (hXα : CFSG.Assembly.IsComponentOf X (fixedSubgroup α))
    (hXβ : CFSG.Assembly.IsComponentOf X (fixedSubgroup β))
    (A : GL (HypIndex 2 0) K) (hA : A ∈ hypUnitary hud 2 0)
    (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes hud 2 0)
    (hΦ : semilinearAutHom hud (r := 2) (ε := 0) (by norm_num) (by norm_num) ⟨_, hx⟩ = α)
    (hid : orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod hud 2 0) = 2)
    (A' : GL (HypIndex 2 0) K) (hA' : A' ∈ hypUnitary hud 2 0)
    (hx' : (⟨A', RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes hud 2 0)
    (hΦ' : semilinearAutHom hud (r := 2) (ε := 0) (by norm_num) (by norm_num) ⟨_, hx'⟩ = β)
    (hid' : orderOf (QuotientGroup.mk ⟨A', hA'⟩ : hypUnitaryMod hud 2 0) = 2) : False := by
  classical
  have : Fact p.Prime := ⟨hud.prime⟩
  have := hud.finite
  set T := hypUnitaryEquiv hud ⟨A, hA⟩ with hTdef
  set S := hypUnitaryEquiv hud ⟨A', hA'⟩ with hSdef
  have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary hud (hypForm hud 2 0)) = 2 := by
    rw [hTdef, ← hypUnitaryModEquiv_mk, MulEquiv.orderOf_eq]
    exact hid
  have hS : orderOf (QuotientGroup.mk S : sesqProjUnitary hud (hypForm hud 2 0)) = 2 := by
    rw [hSdef, ← hypUnitaryModEquiv_mk, MulEquiv.orderOf_eq]
    exact hid'
  have heα := linear_intertwine hud (by norm_num) (by norm_num) A hA hx α hΦ
  have heβ := linear_intertwine hud (by norm_num) (by norm_num) A' hA' hx' β hΦ'
  have hXT := key_component hud 2 0 α _ heα hXα
  have hXS := key_component hud 2 0 β _ heβ hXβ
  have hs₂ : SmallSource (X.map (hypIota hud 2 0)) :=
    smallSource_of_mulEquiv (X.equivMapOfInjective (hypIota hud 2 0)
      (hypIota_injective hud 2 0)) hs
  obtain ⟨c, hc0, hcomm'⟩ := gamma_comm hud (r := 2) (ε := 0) (by norm_num) (by norm_num)
    (by norm_num) ⟨_, hx⟩ ⟨_, hx'⟩ (by rw [hΦ, hΦ', hcomm])
  have hg : ∀ g : GL (HypIndex 2 0) K, glAut (RingEquiv.refl K) g = g := fun g =>
    congrArg (fun φ : MulAut (GL (HypIndex 2 0) K) => φ g) (map_one glAut)
  have hcomm'' : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      c • ((A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by
    have h1 := hcomm'
    simp only [hg] at h1
    exact h1
  have hST : ∀ v, unitaryOp S (unitaryOp T v) = c⁻¹ • unitaryOp T (unitaryOp S v) := by
    intro v
    rw [hTdef, hSdef, unitaryOp_hypUnitaryEquiv, unitaryOp_hypUnitaryEquiv,
      unitaryOp_hypUnitaryEquiv, unitaryOp_hypUnitaryEquiv, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    simp only
    rw [hcomm'', Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hne' : (QuotientGroup.mk S : sesqProjUnitary hud (hypForm hud 2 0)) ≠ QuotientGroup.mk T := by
    intro heq
    apply hne
    ext y
    apply hypIota_injective hud 2 0
    rw [heα y, heβ y]
    exact congrArg (fun z => MulAut.conj z (hypIota hud 2 0 y)) heq.symm
  exact su4_core_linear (V := HypIndex 2 0 → K) hud hp (by rw [UnitaryHigher.finrank_hypIndex_fun])
    (hypForm_isSymm hud) (hypForm_separatingLeft hud) hs₂ hT hS hXT hXS c⁻¹ hST hne'

end LinLin

section LinAnti

variable (hud : UnitaryFieldData p f K)

theorem su4_lin_anti (hp : p ≠ 2) {X : Subgroup (hypPSU hud 2 0)} (hs : SmallSource X)
    {α β : MulAut (hypPSU hud 2 0)} (hcomm : α * β = β * α)
    (hXα : CFSG.Assembly.IsComponentOf X (fixedSubgroup α))
    (hXβ : CFSG.Assembly.IsComponentOf X (fixedSubgroup β))
    (A : GL (HypIndex 2 0) K) (hA : A ∈ hypUnitary hud 2 0)
    (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes hud 2 0)
    (hΦ : semilinearAutHom hud (r := 2) (ε := 0) (by norm_num) (by norm_num) ⟨_, hx⟩ = α)
    (hid : orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod hud 2 0) = 2)
    (A' : GL (HypIndex 2 0) K) (σ : K ≃+* K) (hσ : ∀ c, σ c = hud.bar c)
    (hA' : A' ∈ hypUnitary hud 2 0)
    (hx' : (⟨A', σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes hud 2 0)
    (hΦ' : semilinearAutHom hud (r := 2) (ε := 0) (by norm_num) (by norm_num) ⟨_, hx'⟩ = β)
    {c : K} (hc0 : c ≠ 0)
    (hAc : (A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map hud.bar = c • 1) : False := by
  classical
  have : Fact p.Prime := ⟨hud.prime⟩
  have := hud.finite
  set T := hypUnitaryEquiv hud ⟨A, hA⟩ with hTdef
  have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary hud (hypForm hud 2 0)) = 2 := by
    rw [hTdef, ← hypUnitaryModEquiv_mk, MulEquiv.orderOf_eq]
    exact hid
  have heα := linear_intertwine hud (by norm_num) (by norm_num) A hA hx α hΦ
  have heβ := anti_intertwine hud (by norm_num) (by norm_num) A' σ hσ hA' hx' β hΦ' hc0 hAc
  have hXT := key_component hud 2 0 α _ heα hXα
  have hXτ := key_component hud 2 0 β _ heβ hXβ
  have hs₂ : SmallSource (X.map (hypIota hud 2 0)) :=
    smallSource_of_mulEquiv (X.equivMapOfInjective (hypIota hud 2 0)
      (hypIota_injective hud 2 0)) hs
  obtain ⟨c', hc0', hcomm'⟩ := gamma_comm hud (r := 2) (ε := 0) (by norm_num) (by norm_num)
    (by norm_num) ⟨_, hx⟩ ⟨_, hx'⟩ (by rw [hΦ, hΦ', hcomm])
  have hg : ∀ g : GL (HypIndex 2 0) K, glAut (RingEquiv.refl K) g = g := fun g =>
    congrArg (fun φ : MulAut (GL (HypIndex 2 0) K) => φ g) (map_one glAut)
  have hmap : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map σ =
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map hud.bar :=
    Matrix.ext fun i j => hσ _
  have hcomm'' : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      c' • ((A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map hud.bar) := by
    have h1 := hcomm'
    simp only [hg, coe_glAut, hmap] at h1
    exact h1
  have hTτ : ∀ v, unitaryOp T (semilinearMatrixMap hud (A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) v) =
      c' • semilinearMatrixMap hud (A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (unitaryOp T v) := by
    intro v
    rw [hTdef, unitaryOp_hypUnitaryEquiv, unitaryOp_hypUnitaryEquiv, semilinearMatrixMap_apply,
      semilinearMatrixMap_apply, Matrix.mulVec_mulVec]
    simp only
    rw [hcomm'', Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    congr 2
    funext i
    rw [RingHom.map_mulVec]
    rfl
  exact su4_core_anti (V := HypIndex 2 0 → K) hud hp (by rw [UnitaryHigher.finrank_hypIndex_fun])
    (hypForm_isSymm hud) (hypForm_separatingLeft hud) hs₂ hT _
    (semilinearMatrixMap_bijective hud hc0 hAc) (hypForm_semilinearMatrixMap hud hA')
    (Units.mk0 c hc0) (semilinearMatrixMap_sq hud hAc) hXT hXτ c' hTτ

end LinAnti

section Triple

variable (hud : UnitaryFieldData p f K)

theorem su4_rep (hp : p ≠ 2) (α : MulAut (hypPSU hud 2 0)) (hα : orderOf α = 2) :
    (∃ (A : GL (HypIndex 2 0) K) (hA : A ∈ hypUnitary hud 2 0)
        (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes hud 2 0),
        semilinearAutHom hud (r := 2) (ε := 0) (by norm_num) (by norm_num) ⟨_, hx⟩ = α ∧
        orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod hud 2 0) = 2) ∨
    (∃ (A : GL (HypIndex 2 0) K) (σ : K ≃+* K) (_ : ∀ c, σ c = hud.bar c)
        (_ : A ∈ hypUnitary hud 2 0)
        (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes hud 2 0) (c : K)
        (_ : c ≠ 0),
        semilinearAutHom hud (r := 2) (ε := 0) (by norm_num) (by norm_num) ⟨_, hx⟩ = α ∧
        (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map hud.bar = c • 1) := by
  obtain ⟨A, σ, hx, hA, hΦ, hσ, hid, hbar⟩ :=
    (odd_unitary_automorphism_semilinear_representation hud hp (r := 2) (ε := 0) (by norm_num)
      (by norm_num) (by norm_num)).2.2.2 α hα
  rcases hσ with hσ | hσ
  · subst hσ
    exact Or.inl ⟨A, hA, hx, hΦ, hid rfl⟩
  · obtain ⟨c, hc0, hAc⟩ := hbar hσ
    exact Or.inr ⟨A, σ, hσ, hA, hx, c, hc0, hΦ, hAc⟩

theorem orderOf_mul_of_commute {G : Type*} [Group G] {a b : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hcomm : a * b = b * a) (hne : a ≠ b) : orderOf (a * b) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  refine orderOf_eq_prime ?_ ?_
  · rw [(show Commute a b from hcomm).mul_pow, ha2, hb2, one_mul]
  · intro h1
    apply hne
    have h3 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h3]
    exact eq_inv_iff_mul_eq_one.mpr (by rw [← pow_two]; exact ha2)

end Triple

section Triple2

variable (hud : UnitaryFieldData p f K)

theorem su4_triple_false (hp : p ≠ 2) {X : Subgroup (hypPSU hud 2 0)} (hs : SmallSource X)
    {α β : MulAut (hypPSU hud 2 0)} (hα : orderOf α = 2) (hβ : orderOf β = 2)
    (hcomm : α * β = β * α) (hne : α ≠ β)
    (hXα : CFSG.Assembly.IsComponentOf X (fixedSubgroup α))
    (hXβ : CFSG.Assembly.IsComponentOf X (fixedSubgroup β))
    (hXαβ : CFSG.Assembly.IsComponentOf X (fixedSubgroup (α * β))) : False := by
  have hαβ : orderOf (α * β) = 2 := orderOf_mul_of_commute hα hβ hcomm hne
  rcases su4_rep hud hp α hα with ⟨A, hA, hx, hΦ, hid⟩ |
      ⟨A, σ, hσ, hA, hx, c, hc0, hΦ, hAc⟩
  · rcases su4_rep hud hp β hβ with ⟨A', hA', hx', hΦ', hid'⟩ |
        ⟨A', σ', hσ', hA', hx', c', hc0', hΦ', hAc'⟩
    · exact su4_lin_lin hud hp hs hcomm hne hXα hXβ A hA hx hΦ hid A' hA' hx' hΦ' hid'
    · exact su4_lin_anti hud hp hs hcomm hXα hXβ A hA hx hΦ hid A' σ' hσ' hA' hx' hΦ' hc0' hAc'
  · rcases su4_rep hud hp β hβ with ⟨A', hA', hx', hΦ', hid'⟩ |
        ⟨A', σ', hσ', hA', hx', c', hc0', hΦ', hAc'⟩
    · exact su4_lin_anti hud hp hs hcomm.symm hXβ hXα A' hA' hx' hΦ' hid' A σ hσ hA hx hΦ hc0 hAc
    · rcases su4_rep hud hp (α * β) hαβ with ⟨A'', hA'', hx'', hΦ'', hid''⟩ |
          ⟨A'', σ'', hσ'', hA'', hx'', c'', hc0'', hΦ'', hAc''⟩
      · refine su4_lin_anti hud hp hs ?_ hXαβ hXα A'' hA'' hx'' hΦ'' hid'' A σ hσ hA hx hΦ hc0 hAc
        rw [mul_assoc, ← hcomm]
      · exfalso
        have h1 : semilinearAutHom hud (r := 2) (ε := 0) (by norm_num) (by norm_num)
            (⟨_, hx⟩ * ⟨_, hx'⟩) = α * β := by
          rw [map_mul, hΦ, hΦ']
        have h2 := gamma_right_eq hud (r := 2) (ε := 0) (by norm_num) (by norm_num) (by norm_num)
          (h1.trans hΦ''.symm)
        obtain ⟨c₀, hc₀⟩ := hud.exists_bar_ne
        have h3 := congrArg (fun τ : K ≃+* K => τ c₀) h2
        simp only [Subgroup.coe_mul, SemidirectProduct.mul_right] at h3
        change σ (σ' c₀) = σ'' c₀ at h3
        rw [hσ', hσ, hσ'', hud.bar_bar] at h3
        exact hc₀ h3.symm

end Triple2


end CFSG.GH74.GLS.IVK
