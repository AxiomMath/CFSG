module

public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Converse

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Module Representation CFSG.HardMathSupport.GuralnickMalle CFSG.Quasithin.SmithCurtis
open scoped MonoidAlgebra TensorProduct

section Equiv

variable {k G V V' : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup V']
  [Module k V'] {τ : Representation k G V} {τ' : Representation k G V'} (β : V ≃ₗ[k] V')
  (hβ : ∀ (g : G) (v : V), β (τ g v) = τ' g (β v))
include hβ

def fixSubGenLinearEquiv (A : Subgroup G) : fixSubGen τ A ≃ₗ[k] fixSubGen τ' A where
  toFun v := ⟨β v.1, by
    intro a ha
    rw [← hβ, v.2 a ha]⟩
  invFun w := ⟨β.symm w.1, by
    intro a ha
    apply β.injective
    rw [hβ, β.apply_symm_apply, w.2 a ha]⟩
  left_inv v := by ext; simp
  right_inv w := by ext; simp
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp

theorem finrank_fixSubGen_eq_of_equiv (A : Subgroup G) :
    finrank k (fixSubGen τ A) = finrank k (fixSubGen τ' A) :=
  (fixSubGenLinearEquiv β hβ A).finrank_eq

theorem sub_one_apply_of_equiv (g : G) (v : V') :
    (τ' g - 1) v = β ((τ g - 1) (β.symm v)) := by
  simp [LinearMap.sub_apply, hβ]

theorem finrank_range_sub_one_eq_of_equiv (g : G) :
    finrank k (LinearMap.range (τ g - 1)) = finrank k (LinearMap.range (τ' g - 1)) := by
  have hconj : τ' g - 1 =
      (β : V →ₗ[k] V').comp ((τ g - 1).comp (β.symm : V' →ₗ[k] V)) := by
    ext v
    simp [LinearMap.sub_apply, hβ]
  have hrange : LinearMap.range (τ' g - 1) =
      (LinearMap.range (τ g - 1)).map (β : V →ₗ[k] V') := by
    rw [hconj, LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr β.symm.surjective, Submodule.map_top]
  rw [hrange, LinearEquiv.finrank_map_eq]

theorem eq_one_iff_of_equiv (g : G) : τ g = 1 ↔ τ' g = 1 := by
  constructor
  · intro h
    ext v
    obtain ⟨w, rfl⟩ := β.surjective v
    rw [← hβ, h]
    rfl
  · intro h
    ext v
    apply β.injective
    rw [hβ, h]
    rfl

theorem sub_one_mul_sub_one_of_equiv {a b : G}
    (h : (τ a - 1) * (τ b - 1) = 0) :
    (τ' a - 1) * (τ' b - 1) = 0 := by
  ext v
  change (τ' a - 1) ((τ' b - 1) v) = 0
  rw [sub_one_apply_of_equiv β hβ b v, sub_one_apply_of_equiv β hβ a]
  simp only [LinearEquiv.symm_apply_apply]
  have h' : (τ a - 1) ((τ b - 1) (β.symm v)) = 0 := by
    have := congrArg (fun f : V →ₗ[k] V => f (β.symm v)) h
    simpa using this
  rw [h', map_zero]

end Equiv

theorem finrank_range_sub_one_le {k G V : Type*} [Field k] [Group G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (τ : Representation k G V) (A : Subgroup G) {x : G}
    (hx : x ∈ A) :
    finrank k (LinearMap.range (τ x - 1)) ≤ finrank k V - finrank k (fixSubGen τ A) := by
  have hker : fixSubGen τ A ≤ LinearMap.ker (τ x - 1) := by
    intro w hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact hw x hx
  have hmono : finrank k (fixSubGen τ A) ≤ finrank k (LinearMap.ker (τ x - 1)) :=
    Submodule.finrank_mono hker
  have hrn := LinearMap.finrank_range_add_finrank_ker (τ x - 1)
  omega

theorem isIrreducible_comp_mulEquiv {K G G' V : Type*} [Field K] [Group G] [Group G']
    [AddCommGroup V] [Module K V] (ρ : Representation K G V) [ρ.IsIrreducible]
    (e : G' ≃* G) : Representation.IsIrreducible (ρ.comp e.toMonoidHom) := by
  have : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine { toNontrivial := inferInstance, eq_bot_or_eq_top := fun s => ?_ }
  let s' : Subrepresentation ρ :=
    { toSubmodule := s.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨g', rfl⟩ := e.surjective g
        exact s.apply_mem_toSubmodule g' hv }
  rcases IsSimpleOrder.eq_bot_or_eq_top s' with h | h
  · refine Or.inl (Subrepresentation.ext ?_)
    change s'.toSubmodule = (⊥ : Subrepresentation ρ).toSubmodule
    exact congrArg Subrepresentation.toSubmodule h
  · refine Or.inr (Subrepresentation.ext ?_)
    change s'.toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule
    exact congrArg Subrepresentation.toSubmodule h

theorem weight1Gen_comp_mulEquiv {K G G' V : Type*} [Field K] [Group G] [Group G']
    [AddCommGroup V] [Module K V] (ρ : Representation K G V) (e : G' ≃* G)
    (A : Subgroup G) :
    weight1Gen (ρ.comp e.toMonoidHom) (A.comap e.toMonoidHom) = weight1Gen ρ A := by
  rw [weight1Gen, weight1Gen]
  have hcard : Nat.card (A.comap e.toMonoidHom) = Nat.card A := by
    rw [Subgroup.comap_equiv_eq_map_symm' e A, Subgroup.card_map_of_injective e.symm.injective]
  have hfix : fixSubGen (ρ.comp e.toMonoidHom) (A.comap e.toMonoidHom) =
      fixSubGen ρ A := by
    ext v
    simp only [mem_fixSubGen, Subgroup.mem_comap, MonoidHom.comp_apply]
    constructor
    · intro h a ha
      simpa using h (e.symm a) (by simpa using ha)
    · intro h g hg
      exact h (e g) hg
  rw [hcard, hfix]

section EndField

variable {G : Type*} [Group G] [Finite G] {W : Type*} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible]

omit [Finite G] in
theorem exists_card_endField_eq_two_pow :
    ∃ s : ℕ, 0 < s ∧ Nat.card (End (ZMod 2)[G] ρ.asModule) = 2 ^ s := by
  let K := End (ZMod 2)[G] ρ.asModule
  have : CharP K 2 := endField_charP ρ 2
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

variable (k : Type*) [Field k] [Algebra (End (ZMod 2)[G] ρ.asModule) k]

omit [Finite G] in
theorem card_eq_pow_finrank_extendScalars :
    Nat.card W = Nat.card (End (ZMod 2)[G] ρ.asModule) ^
      finrank k (k ⊗[End (ZMod 2)[G] ρ.asModule] ρ.asModule) := by
  rw [card_eq_pow_finrank_endField ρ, finrank_tensorProduct_asModule ρ k]

theorem card_fixSubGen_eq_pow_finrank_extendScalars (A : Subgroup G) :
    Nat.card (fixSubGen ρ A) = Nat.card (End (ZMod 2)[G] ρ.asModule) ^
      finrank k (fixSubGen (Theory.Representation.extendScalars k (endFieldRep ρ)) A) := by
  rw [card_fixSubGen_endField ρ, finrank_fixSubGen_extendScalars ρ k A]

theorem baseChange_eq_one_iff {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (k : Type*) [Field k] [Algebra K k] (f : Module.End K M) :
    f.baseChange k = 1 ↔ f = 1 := by
  constructor
  · intro h
    ext m
    have h1 := congrArg (fun g : k ⊗[K] M →ₗ[k] k ⊗[K] M => g ((1 : k) ⊗ₜ[K] m)) h
    simp only [LinearMap.baseChange_tmul, Module.End.one_apply] at h1
    have h2 : (1 : k) ⊗ₜ[K] (f m - m) = 0 := by
      rw [TensorProduct.tmul_sub, h1, sub_self]
    exact sub_eq_zero.mp
      ((Module.FaithfullyFlat.one_tmul_eq_zero_iff K M (A := k) (f m - m)).mp h2)
  · rintro rfl
    simp

omit [Finite G] in
theorem extendScalars_endFieldRep_eq_one_iff (g : G) :
    Theory.Representation.extendScalars k (endFieldRep ρ) g = 1 ↔ ρ g = 1 := by
  have hbase : Theory.Representation.extendScalars k (endFieldRep ρ) g =
      (endFieldRep ρ g).baseChange k := rfl
  rw [hbase, baseChange_eq_one_iff]
  constructor
  · intro h
    ext v
    have h1 : endFieldRep ρ g (ρ.asModuleEquiv.symm v) = ρ.asModuleEquiv.symm v := by
      simpa using congrArg (fun f => f (ρ.asModuleEquiv.symm v)) h
    calc (ρ g) v
        = ρ g (ρ.asModuleEquiv (ρ.asModuleEquiv.symm v)) := by simp
      _ = ρ.asModuleEquiv (endFieldRep ρ g (ρ.asModuleEquiv.symm v)) := by
          rw [endFieldRep_apply']
      _ = ρ.asModuleEquiv (ρ.asModuleEquiv.symm v) := by rw [h1]
      _ = v := by simp
  · intro h
    ext m
    simp [endFieldRep_apply, h]

omit [Finite G] in
theorem extendScalars_endFieldRep_sub_one_mul_sub_one {a b : G}
    (h : (ρ a - 1) * (ρ b - 1) = 0) :
    (Theory.Representation.extendScalars k (endFieldRep ρ) a - 1) *
      (Theory.Representation.extendScalars k (endFieldRep ρ) b - 1) = 0 := by
  have h' : (endFieldRep ρ a - 1) * (endFieldRep ρ b - 1) = 0 := by
    ext m
    change (endFieldRep ρ a - 1) ((endFieldRep ρ b - 1) m) = 0
    have hb : (endFieldRep ρ b - 1) m =
        ρ.asModuleEquiv.symm ((ρ b - 1) (ρ.asModuleEquiv m)) := by
      calc (endFieldRep ρ b - 1) m
          = ρ.asModuleEquiv.symm (ρ b (ρ.asModuleEquiv m)) - m := by
            rw [LinearMap.sub_apply, endFieldRep_apply]
            rfl
        _ = ρ.asModuleEquiv.symm (ρ b (ρ.asModuleEquiv m)) -
              ρ.asModuleEquiv.symm (ρ.asModuleEquiv m) := by
            rw [ρ.asModuleEquiv.symm_apply_apply]
        _ = ρ.asModuleEquiv.symm (ρ b (ρ.asModuleEquiv m) - ρ.asModuleEquiv m) := by
            rw [map_sub]
        _ = ρ.asModuleEquiv.symm ((ρ b - 1) (ρ.asModuleEquiv m)) := by
            rfl
    rw [hb]
    have ha : (endFieldRep ρ a - 1)
        (ρ.asModuleEquiv.symm ((ρ b - 1) (ρ.asModuleEquiv m))) =
        ρ.asModuleEquiv.symm ((ρ a - 1) ((ρ b - 1) (ρ.asModuleEquiv m))) := by
      calc ((endFieldRep ρ a - 1)
          (ρ.asModuleEquiv.symm ((ρ b - 1) (ρ.asModuleEquiv m))))
          = ρ.asModuleEquiv.symm
              (ρ a (ρ.asModuleEquiv (ρ.asModuleEquiv.symm ((ρ b - 1) (ρ.asModuleEquiv m))))) -
              ρ.asModuleEquiv.symm ((ρ b - 1) (ρ.asModuleEquiv m)) := by
            rw [LinearMap.sub_apply, endFieldRep_apply]
            rfl
        _ = ρ.asModuleEquiv.symm (ρ a ((ρ b - 1) (ρ.asModuleEquiv m))) -
              ρ.asModuleEquiv.symm ((ρ b - 1) (ρ.asModuleEquiv m)) := by
            rw [ρ.asModuleEquiv.apply_symm_apply]
        _ = ρ.asModuleEquiv.symm
              (ρ a ((ρ b - 1) (ρ.asModuleEquiv m)) - (ρ b - 1) (ρ.asModuleEquiv m)) := by
            rw [map_sub]
        _ = ρ.asModuleEquiv.symm ((ρ a - 1) ((ρ b - 1) (ρ.asModuleEquiv m))) := by
            rfl
    rw [ha]
    have h' : (ρ a - 1) ((ρ b - 1) (ρ.asModuleEquiv m)) = 0 := by
      have := congrArg (fun f : W →ₗ[ZMod 2] W => f (ρ.asModuleEquiv m)) h
      simpa using this
    rw [h', map_zero]
  have hbc (g : G) : Theory.Representation.extendScalars k (endFieldRep ρ) g - 1 =
      (endFieldRep ρ g - 1).baseChange k := by
    rw [Theory.Representation.extendScalars_apply, ← LinearMap.baseChange_one,
      ← LinearMap.baseChange_sub]
  rw [hbc a, hbc b, ← LinearMap.baseChange_mul, h', LinearMap.baseChange_zero]

omit [Finite G] in
theorem isSimpleRep_extendScalars_endFieldRep :
    IsSimpleRep (Theory.Representation.extendScalars k (endFieldRep ρ)) := by
  have : IsIrreducible (Theory.Representation.extendScalars k (endFieldRep ρ)) :=
    extendScalars_isIrreducible ρ k
  exact isSimpleRep_of_isIrreducible _

theorem pow_codim_le_of_card_le (A : Subgroup G) {c : ℕ}
    (h : Nat.card W ≤ c * weight1Gen ρ A) :
    Nat.card (End (ZMod 2)[G] ρ.asModule) ^
        (finrank k (k ⊗[End (ZMod 2)[G] ρ.asModule] ρ.asModule) -
          finrank k (fixSubGen (Theory.Representation.extendScalars k (endFieldRep ρ)) A)) ≤
      c * Nat.card A := by
  let K := End (ZMod 2)[G] ρ.asModule
  let d := finrank k (k ⊗[K] ρ.asModule)
  let e := finrank k (fixSubGen (Theory.Representation.extendScalars k (endFieldRep ρ)) A)
  change Nat.card K ^ (d - e) ≤ c * Nat.card A
  have hW : Nat.card W = Nat.card K ^ d := card_eq_pow_finrank_extendScalars ρ k
  have hC : Nat.card (fixSubGen ρ A) = Nat.card K ^ e :=
    card_fixSubGen_eq_pow_finrank_extendScalars ρ k A
  have hle : Nat.card K ^ d ≤ c * (Nat.card A * Nat.card K ^ e) := by
    calc Nat.card K ^ d = Nat.card W := hW.symm
      _ ≤ c * weight1Gen ρ A := h
      _ = c * (Nat.card A * Nat.card K ^ e) := by rw [weight1Gen, hC]
  have he : e ≤ d := by
    have : Finite ρ.asModule := finite_asModule ρ
    have : Module.Finite K ρ.asModule := Module.finite_iff_finite.mpr inferInstance
    have : Module.Finite k (k ⊗[K] ρ.asModule) := Module.Finite.base_change K k ρ.asModule
    have : Module.Finite k ↥(⊤ : Submodule k (k ⊗[K] ρ.asModule)) := inferInstance
    dsimp only [e, d]
    simpa using Submodule.finrank_mono
      (le_top : fixSubGen (Theory.Representation.extendScalars k (endFieldRep ρ)) A ≤ ⊤)
  have : Finite K := endField_finite ρ
  have : Nonempty K := ⟨0⟩
  have hcalc : Nat.card K ^ (d - e) * Nat.card K ^ e ≤
      (c * Nat.card A) * Nat.card K ^ e := by
    calc Nat.card K ^ (d - e) * Nat.card K ^ e
        = Nat.card K ^ d := by rw [← Nat.pow_add, Nat.sub_add_cancel he]
      _ ≤ c * (Nat.card A * Nat.card K ^ e) := hle
      _ = c * Nat.card A * Nat.card K ^ e := by ring
  exact Nat.le_of_mul_le_mul_right hcalc (pow_pos (Nat.card_pos (α := K)) e)

end EndField

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
