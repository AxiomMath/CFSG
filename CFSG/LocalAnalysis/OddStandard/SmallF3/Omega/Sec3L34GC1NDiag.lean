module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Dec

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A : Type} [Group A] [Finite A] {H : Subgroup A} {𝒮 : Set (Subgroup A)} {x : A}

@[expose] def l34gDiag (x t : A) : A := t * (x * t * x⁻¹)

theorem l34gDiag_mul (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hxS : CFSG.conjugate S x ≠ S) {d e : A} (hd : d ∈ S) (he : e ∈ S) :
    l34gDiag x (d * e) = l34gDiag x d * l34gDiag x e := by
  simpa only [l34gDiag] using L34GFac.diag_mul hF hS hxS hd he

theorem l34gDiag_eq_one (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hxS : CFSG.conjugate S x ≠ S) {d : A} (hd : d ∈ S) (h : l34gDiag x d = 1) : d = 1 := by
  exact L34GFac.diag_eq_one hF hS hxS hd (by simpa only [l34gDiag] using h)

theorem l34gDiag_mem (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hxS : CFSG.conjugate S x ≠ S) {d : A} (hd : d ∈ S) :
    l34gDiag x d ∈ H ⊓ centralizer ({x} : Set A) := by
  simpa only [l34gDiag] using L34GFac.diag_mem hF hS hxS hd

theorem l34gDiag_inv (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hxS : CFSG.conjugate S x ≠ S) {d : A} (hd : d ∈ S) :
    l34gDiag x d⁻¹ = (l34gDiag x d)⁻¹ := by
  have h1 : l34gDiag x d⁻¹ * l34gDiag x d = 1 := by
    rw [← l34gDiag_mul hF hS hxS (S.inv_mem hd) hd]
    simp [l34gDiag]
  exact eq_inv_of_mul_eq_one_left h1

theorem l34gDiag_conj (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hxS : CFSG.conjugate S x ≠ S) {t k : A} (ht : t ∈ S) (hk : k ∈ S) :
    l34gDiag x (k * t * k⁻¹) = l34gDiag x k * l34gDiag x t * (l34gDiag x k)⁻¹ := by
  rw [show k * t * k⁻¹ = k * (t * k⁻¹) by group]
  rw [l34gDiag_mul hF hS hxS hk (S.mul_mem ht (S.inv_mem hk)),
      l34gDiag_mul hF hS hxS ht (S.inv_mem hk), l34gDiag_inv hF hS hxS hk]
  group

theorem l34gDiag_conj_n {n : A} (hnx : n * x = x * n) {d : A} :
    l34gDiag x (n * d * n⁻¹) = n * l34gDiag x d * n⁻¹ := by
  simp only [l34gDiag]
  have hx1 : x * n = n * x := hnx.symm
  have hx2 : n⁻¹ * x⁻¹ = x⁻¹ * n⁻¹ := by
    rw [← mul_inv_rev x n, ← hnx, mul_inv_rev n x]
  calc (n * d * n⁻¹) * (x * (n * d * n⁻¹) * x⁻¹)
      = (n * d * n⁻¹) * ((x * n) * d * (n⁻¹ * x⁻¹)) := by group
    _ = (n * d * n⁻¹) * ((n * x) * d * (x⁻¹ * n⁻¹)) := by rw [hx1, hx2]
    _ = n * (d * (x * d * x⁻¹)) * n⁻¹ := by group

@[expose] def l34gNS (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hxS : CFSG.conjugate S x ≠ S) (N : Subgroup A) : Subgroup A where
  carrier := {t : A | t ∈ S ∧ l34gDiag x t ∈ N}
  mul_mem' := by
    rintro a b ⟨haS, haN⟩ ⟨hbS, hbN⟩
    exact ⟨S.mul_mem haS hbS, by
      rw [l34gDiag_mul hF hS hxS haS hbS]
      exact N.mul_mem haN hbN⟩
  one_mem' := by
    refine ⟨S.one_mem, ?_⟩
    rw [show l34gDiag x (1 : A) = 1 by simp [l34gDiag]]
    exact N.one_mem
  inv_mem' := by
    rintro a ⟨haS, haN⟩
    exact ⟨S.inv_mem haS, by
      rw [l34gDiag_inv hF hS hxS haS]
      exact N.inv_mem haN⟩

theorem l34gNS_le (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hxS : CFSG.conjugate S x ≠ S) (N : Subgroup A) : l34gNS hF hS hxS N ≤ S :=
  fun t ht => (show t ∈ S ∧ l34gDiag x t ∈ N from ht).1

theorem l34gNS_isPGroup (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hxS : CFSG.conjugate S x ≠ S) {N : Subgroup A} (hN : IsPGroup 3 ↥N) :
    IsPGroup 3 ↥(l34gNS hF hS hxS N) := by
  let φ : ↥(l34gNS hF hS hxS N) →* ↥N :=
    { toFun := fun t =>
        ⟨l34gDiag x (t : A), (show (t : A) ∈ S ∧ l34gDiag x (t : A) ∈ N from t.2).2⟩
      map_one' := Subtype.ext (by simp [l34gDiag])
      map_mul' := fun a b => Subtype.ext (l34gDiag_mul hF hS hxS a.2.1 b.2.1) }
  refine hN.of_injective φ ?_
  intro a b hab
  have hδ : l34gDiag x (a : A) = l34gDiag x (b : A) := congrArg Subtype.val hab
  have h1 : l34gDiag x ((a : A) * (b : A)⁻¹) = 1 := by
    rw [l34gDiag_mul hF hS hxS a.2.1 (S.inv_mem b.2.1), l34gDiag_inv hF hS hxS b.2.1, hδ]
    simp
  refine Subtype.ext (mul_inv_eq_one.mp ?_)
  exact l34gDiag_eq_one hF hS hxS (S.mul_mem a.2.1 (S.inv_mem b.2.1)) h1

theorem l34gNS_normal (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hxS : CFSG.conjugate S x ≠ S) {N : Subgroup A}
    (hNn : ∀ f ∈ H ⊓ centralizer ({x} : Set A), ∀ n ∈ N, f * n * f⁻¹ ∈ N) :
    ((l34gNS hF hS hxS N).subgroupOf S).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (l34gNS_le hF hS hxS N)]
  intro p k hp hk
  have hpS : p ∈ S := (show p ∈ S ∧ l34gDiag x p ∈ N from hp).1
  have hpN : l34gDiag x p ∈ N := (show p ∈ S ∧ l34gDiag x p ∈ N from hp).2
  refine ⟨S.mul_mem (S.mul_mem hk hpS) (S.inv_mem hk), ?_⟩
  rw [l34gDiag_conj hF hS hxS hpS hk]
  exact hNn (l34gDiag x k) (l34gDiag_mem hF hS hxS hk) (l34gDiag x p) hpN

theorem l34gNS_eq_bot (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hxS : CFSG.conjugate S x ≠ S) {N : Subgroup A} (hN : IsPGroup 3 ↥N)
    (hNn : ∀ f ∈ H ⊓ centralizer ({x} : Set A), ∀ n ∈ N, f * n * f⁻¹ ∈ N) :
    l34gNS hF hS hxS N = ⊥ := by
  have hsub : (l34gNS hF hS hxS N).subgroupOf S = ⊥ := by
    haveI : ((l34gNS hF hS hxS N).subgroupOf S).Normal := l34gNS_normal hF hS hxS hNn
    exact l34g_pGroup_normal_bot (hF.simple S hS)
      ((l34gNS_isPGroup hF hS hxS hN).of_equiv
        (Subgroup.subgroupOfEquivOfLe (l34gNS_le hF hS hxS N)).symm)
  have hinf : l34gNS hF hS hxS N ⊓ S = ⊥ := by
    rw [← Subgroup.bot_subgroupOf] at hsub
    simpa using Subgroup.subgroupOf_inj.mp hsub
  rwa [inf_eq_left.mpr (l34gNS_le hF hS hxS N)] at hinf

end CFSG.OddStandard.SmallF3.Omega
