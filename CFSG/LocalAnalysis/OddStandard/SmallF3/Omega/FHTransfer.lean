module

public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def FHFixedO3Free (X : Type) [Group X] : Prop :=
  ∀ σ : MulAut X, σ * σ = 1 → ∀ N : Subgroup X, IsPGroup 3 N → (∀ x ∈ N, σ x = x) →
    (∀ y : X, σ y = y → ∀ x ∈ N, y * x * y⁻¹ ∈ N) → N = ⊥

theorem fh_f1_of_fixedO3Free {A : Type} [Group A] (H : Subgroup A) [H.Normal]
    (hX : FHFixedO3Free ↥H) {a : A} (ha : a * a = 1) :
    CFSG.inSubgroup (CFSG.pCore 3) (H ⊓ centralizer ({a} : Set A)) = ⊥ := by
  set K : Subgroup A := H ⊓ centralizer ({a} : Set A) with hK
  set N0 : Subgroup A := CFSG.inSubgroup (CFSG.pCore 3) K with hN0
  have hN0K : N0 ≤ K := Subgroup.map_subtype_le _
  have hN0H : N0 ≤ H := hN0K.trans inf_le_left
  have hN03 : IsPGroup 3 N0 := IsPGroup.map CFSG.pCore_isPGroup K.subtype
  have hKa : ∀ x ∈ K, a * x = x * a := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 hx.2).symm
  have hKmem : ∀ x : H, (a * x * a⁻¹ = x) → (x : A) ∈ K := fun x hx =>
    ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 (by
      have := hx
      calc (x : A) * a = a * x * a⁻¹ * a := by rw [this]
        _ = a * x := by group)⟩
  set σ : MulAut ↥H := MulAut.conjNormal a with hσ
  have hσ2 : σ * σ = 1 := by
    rw [hσ, ← map_mul, ha, map_one]
  set N : Subgroup ↥H := N0.subgroupOf H with hN
  have hN3 : IsPGroup 3 N :=
    hN03.of_injective (Subgroup.subgroupOfEquivOfLe hN0H).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hN0H).injective
  have hfix : ∀ x ∈ N, σ x = x := by
    intro x hx
    have hxK : (x : A) ∈ K := hN0K hx
    apply Subtype.ext
    rw [hσ, MulAut.conjNormal_apply]
    calc a * (x : A) * a⁻¹ = (x : A) * a * a⁻¹ := by rw [hKa _ hxK]
      _ = x := by group
  have hnorm : ∀ y : ↥H, σ y = y → ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
    intro y hy x hx
    have hyA : a * (y : A) * a⁻¹ = y := by
      have := congrArg Subtype.val hy
      rwa [hσ, MulAut.conjNormal_apply] at this
    have hyK : (y : A) ∈ K := hKmem y hyA
    obtain ⟨z, hz, hzx⟩ := hx
    have hzc : (⟨(y : A), hyK⟩ : ↥K) * z * (⟨(y : A), hyK⟩ : ↥K)⁻¹ ∈ CFSG.pCore 3 ↥K :=
      CFSG.pCore_normal.conj_mem z hz _
    refine ⟨_, hzc, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    show (y : A) * (z : A) * (y : A)⁻¹ = (y : A) * (x : A) * (y : A)⁻¹
    rw [show (z : A) = (x : A) from hzx]
  have hNbot : N = ⊥ := hX σ hσ2 N hN3 hfix hnorm
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hxN : (⟨x, hN0H hx⟩ : ↥H) ∈ N := hx
  rw [hNbot, Subgroup.mem_bot] at hxN
  exact congrArg Subtype.val hxN

end CFSG.OddStandard.SmallF3.Omega
