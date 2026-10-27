module

public import CFSG.GH74.Generic.BProg.B3.S3KG21dDesc
public import CFSG.GH74.GLS.C3.Layer1.Th2BalLocal

public section

namespace CFSG.GH74.Generic.BProg.B3.S3KG

open Subgroup CFSG.ClassicalInvolution.Balance CFSG.GH74.GLS.Th2.Bal CFSG.Assembly.Dichotomy

@[expose] noncomputable def descendZ (X : Type*) [Group X] :
    MulAut X →* MulAut (X ⧸ center X) where
  toFun v := QuotientGroup.congr (center X) (center X) v (Subgroup.map_center_eq v)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl
  map_mul' v w := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl

theorem descendZ_mk {X : Type*} [Group X] (v : MulAut X) (y : X) :
    descendZ X v (QuotientGroup.mk y : X ⧸ center X) = QuotientGroup.mk (v y) := rfl

theorem descendZ_conj {X : Type*} [Group X] (s : X) :
    descendZ X (MulAut.conj s) = MulAut.conj (QuotientGroup.mk s : X ⧸ center X) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

theorem descendZ_injective {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {X : Type*}
    [Group X] (ι : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Function.Injective (descendZ X) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hw : descend (MulAut.congr ι v) = 1 := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H y =>
      have hx := congrArg (fun φ : MulAut (X ⧸ center X) => φ (QuotientGroup.mk (ι.symm y))) hv
      simp only [descendZ_mk, MulAut.one_apply] at hx
      have hc := QuotientGroup.eq.mp hx
      have hc' : ι ((v (ι.symm y))⁻¹ * ι.symm y) ∈
          center (Matrix.SpecialLinearGroup (Fin 2) F) := by
        rw [← Subgroup.map_center_eq ι]
        exact ⟨_, hc, rfl⟩
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply] at hc'
      rw [descend_mk, MulAut.one_apply]
      exact QuotientGroup.eq.mpr hc'
  have h1 : MulAut.congr ι v = 1 := descend_injective hF (by rw [hw, map_one])
  have h2 := congrArg (MulAut.congr ι).symm h1
  rwa [MulEquiv.symm_apply_apply, map_one] at h2

theorem isLocallyKBalanced_of_injective {K K' : Type*} [Group K] [Group K'] [Finite K] {k : ℕ}
    (ψ : MulAut K →* MulAut K') (hψ : Function.Injective ψ)
    (hinn : ∀ k' : K', ∃ k₀ : K, ψ (MulAut.conj k₀) = MulAut.conj k')
    (h : IsLocallyKBalanced k K') : IsLocallyKBalanced k K := by
  intro H hH F hF hF2
  have : Finite (MulAut K) :=
    Finite.of_injective (fun σ : MulAut K => (σ : K → K)) DFunLike.coe_injective
  let θ : ↥H →* ↥(H.map ψ) := ψ.subgroupMap H
  have hθs : Function.Surjective θ := ψ.subgroupMap_surjective H
  have hθi : Function.Injective θ := fun a b hab =>
    Subtype.ext (hψ (congrArg Subtype.val hab))
  have hH' : (MulAut.conj : K' →* MulAut K').range ≤ H.map ψ := by
    rintro _ ⟨k', rfl⟩
    obtain ⟨k₀, hk₀⟩ := hinn k'
    exact ⟨MulAut.conj k₀, hH ⟨k₀, rfl⟩, hk₀⟩
  have hF' : 2 ^ k ≤ Nat.card (F.map θ) := by
    rw [Subgroup.card_map_of_injective hθi]
    exact hF
  have hF2' : ∀ f ∈ F.map θ, f * f = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, hF2 f hf, map_one]
  have hbot := h (H.map ψ) hH' (F.map θ) hF' hF2'
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply hθi
  rw [map_one, ← Subgroup.mem_bot, ← hbot, mem_deltaCore_iff]
  rintro _ ⟨f, hf, rfl⟩ hf1
  have hf1' : f ≠ 1 := fun h1 => hf1 (by rw [h1, map_one])
  have h2 : IsPGroup 2 (Subgroup.zpowers f) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    have hf2 : f ^ 2 = 1 := by rw [sq]; exact hF2 f hf
    change (f ^ n) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hf2, one_zpow]
  exact map_involutionOddCore_le θ hθs h2
    (Subgroup.mem_map_of_mem θ ((mem_deltaCore_iff.mp hx) f hf hf1'))

end CFSG.GH74.Generic.BProg.B3.S3KG
