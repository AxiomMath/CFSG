module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Offender

section Binary

variable {W : Type*} [CommGroup W]

@[expose] def dispHom (g : MulAut W) : W →* W where
  toFun w := g w * w⁻¹
  map_one' := by simp
  map_mul' a b := by
    show g (a * b) * (a * b)⁻¹ = (g a * a⁻¹) * (g b * b⁻¹)
    rw [map_mul, mul_inv_rev]
    ac_rfl

@[expose] def dispSub (g : MulAut W) : Subgroup W := (dispHom g).range

theorem mem_dispSub {g : MulAut W} {x : W} : x ∈ dispSub g ↔ ∃ w : W, g w * w⁻¹ = x :=
  Iff.rfl

variable [Finite W]

@[expose] noncomputable def subToSubmodule [Fact (∀ w : W, w * w = 1)] :
    Subgroup W ≃o Submodule (ZMod 2) (Additive W) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

omit [Finite W] in
theorem mem_subToSubmodule [Fact (∀ w : W, w * w = 1)] {S : Subgroup W} {x : Additive W} :
    x ∈ subToSubmodule S ↔ Additive.toMul x ∈ S := Iff.rfl

theorem rank_two_three_elements (hW : ∀ w : W, w * w = 1) {X : Type*} [Group X]
    (ρ : X →* MulAut W) {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → X)
    (hc3 : ∀ i, orderOf (ρ (c i)) = 3) (hrk : ∀ i, Nat.card (dispSub (ρ (c i))) = 4)
    (hinj : Function.Injective fun i => Subgroup.zpowers (ρ (c i)))
    (h3 : IsPGroup 3 ↥(⨆ i, Subgroup.zpowers (ρ (c i)))) :
    (∀ i j, ρ (c i) * ρ (c j) = ρ (c j) * ρ (c i)) ∧
      iSupIndep (fun i => dispSub (ρ (c i))) := by
  classical
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  let ℓ : MulAut W →* (Additive W ≃ₗ[ZMod 2] Additive W) := binaryLin
  have hℓ : Function.Injective ℓ := binaryLin_injective
  let Λ : ι → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W) := fun i =>
    Subgroup.zpowers (ℓ (ρ (c i)))
  have hΛ : ∀ i, Λ i = (Subgroup.zpowers (ρ (c i))).map ℓ := fun i =>
    (MonoidHom.map_zpowers ℓ _).symm
  have hΛord : ∀ i, Nat.card (Λ i) = 3 := fun i => by
    show Nat.card (Subgroup.zpowers (ℓ (ρ (c i)))) = 3
    rw [Nat.card_zpowers, orderOf_injective ℓ hℓ, hc3 i]
  have hΛcyc : ∀ i, IsCyclic (Λ i) := fun i => inferInstanceAs (IsCyclic (Subgroup.zpowers _))
  have hΛinj : Function.Injective Λ := by
    intro i j hij
    apply hinj
    have h1 : (Subgroup.zpowers (ρ (c i))).map ℓ = (Subgroup.zpowers (ρ (c j))).map ℓ := by
      rw [← hΛ, ← hΛ]; exact hij
    exact Subgroup.map_injective hℓ h1
  have hΛD : IsPGroup 3 ↥(⨆ i, Λ i : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)) := by
    have e : (⨆ i, Λ i : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)) =
        (⨆ i, Subgroup.zpowers (ρ (c i))).map ℓ := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hΛ
    rw [e]
    exact h3.of_equiv (Subgroup.equivMapOfInjective _ ℓ hℓ)
  have hplane : ∀ i, commGL (Λ i) ⊤ = subToSubmodule (dispSub (ρ (c i))) := by
    intro i
    show commGL (Subgroup.zpowers (ℓ (ρ (c i)))) ⊤ = _
    rw [commGL_zpowers]
    ext x
    rw [mem_dispOf, mem_subToSubmodule, mem_dispSub]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨Additive.toMul u, ?_⟩
      have := congrArg Additive.toMul hu
      simpa [ℓ, toMul_binaryLin, div_eq_mul_inv] using this
    · rintro ⟨w, hw⟩
      refine ⟨Additive.ofMul w, ?_⟩
      apply Additive.toMul.injective
      simpa [ℓ, toMul_binaryLin, div_eq_mul_inv] using hw
  have hΛrk : ∀ i, Module.finrank (ZMod 2) (commGL (Λ i) ⊤) = 2 := by
    intro i
    rw [hplane i]
    have h1 : Nat.card ↥(subToSubmodule (dispSub (ρ (c i)))) = 4 := by
      rw [← hrk i]
      exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x => Iff.rfl)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h1
    exact Nat.pow_right_injective (le_refl 2) (by simpa using h1)
  have key := binary_three_group_rank_two_generators_disjoint_natural_planes (Nat.card_zmod 2)
    Λ hΛinj hΛcyc hΛord hΛD hΛrk
  refine ⟨fun i j => ?_, ?_⟩
  · by_cases hij : i = j
    · rw [hij]
    · apply hℓ
      rw [map_mul, map_mul]
      exact key.1 i j hij _ (Subgroup.mem_zpowers _) _ (Subgroup.mem_zpowers _)
  · have h2 := key.2.2.1
    simp only [hplane] at h2
    exact (iSupIndep_map_orderIso_iff (subToSubmodule (W := W))).1 h2

end Binary

end CFSG.QuasithinUnique.Setup.Wreath
