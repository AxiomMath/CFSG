module

public import CFSG.LargeExtraspecial.S14Claims
public import CFSG.LargeExtraspecial.S111CMain
public import CFSG.LargeExtraspecial.S111AExists

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.LargeExtraspecial.S4

@[expose] def ShultInput111 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    Hyp S g → ¬ S.IsReducible → 6 ≤ S.width →
    (∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) →
    ∀ (P : Sylow 2 S.Mbar) (t : S.O), t ∈ S.Lbar g → t ≠ 1 →
      (∀ x ∈ (P : Subgroup S.Mbar), (x : S.O) * t = t * x) →
      ¬ IsMulCommutative (closure {y : S.O | ∃ m ∈ S.Mbar, y = m * t * m⁻¹ ∧ y * t = t * y})

@[expose] def NoCommuting111 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (A : Subgroup G),
    Cfg111 S g A → 6 ≤ S.width → ∀ h : G, h ∈ S.M →
      A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z →
      ∀ k j : G, k * S.z * k⁻¹ ∈ A → k * S.z * k⁻¹ ≠ S.z →
      j * S.z * j⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom → j * S.z * j⁻¹ ≠ S.z →
      ∀ σ ∈ S.Lbar k, ∀ τ ∈ S.Lbar j, σ ≠ 1 → τ ≠ 1 → σ * τ ≠ τ * σ

theorem s11_1Stmt_of_noCommuting (hNC : NoCommuting111) (hSh : ShultInput111) :
    S14.S11_1Stmt := by
  intro G _ _ _ S g hy hirr h6 hT
  by_contra hn
  obtain ⟨A, C⟩ := Cfg111.exists hy hirr hT hn
  obtain ⟨P, t, ht, ht1, htP, hab⟩ := C.exists_shult (hNC G S g A C h6)
  exact hSh G S g hy hirr h6 hT P t ht ht1 htP hab

end CFSG.LargeExtraspecial.S11
