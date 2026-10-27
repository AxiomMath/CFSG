module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open

variable {Γ : Type*} [Group Γ]

theorem mul_comm_of_isElemAbelian {p : ℕ} {A : Subgroup Γ} (hA : IsElemAbelian p A) {a b : Γ}
    (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

open scoped IsMulCommutative in
theorem exists_comm_eq_of_card [Finite Γ] {A : Subgroup Γ} {τ : Γ} (hA : IsElemAbelian 2 A)
    (hτ : τ ∈ normalizer (A : Set Γ)) (hτ2 : τ * τ = 1)
    (hcard : Nat.card A =
      Nat.card ↥(A ⊓ centralizer ({τ} : Set Γ)) * Nat.card ↥(A ⊓ centralizer ({τ} : Set Γ)))
    {w : Γ} (hwA : w ∈ A) (hwτ : τ * w = w * τ) : ∃ u ∈ A, w = u * τ * u⁻¹ * τ⁻¹ := by
  haveI : IsMulCommutative ↥A := hA.1
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  set C : Subgroup Γ := A ⊓ centralizer ({τ} : Set Γ) with hC
  have hCA : C ≤ A := inf_le_left
  let ψ : ↥A →* ↥A :=
    { toFun := fun u => ⟨τ * u * τ⁻¹, (mem_normalizer_iff.1 hτ u).1 u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hψ : ∀ u : ↥A, ((ψ u : ↥A) : Γ) = τ * u * τ⁻¹ := fun u => rfl
  have hψψ : ∀ u : ↥A, ψ (ψ u) = u := fun u => Subtype.ext (by
    rw [hψ, hψ, hτi]
    calc τ * (τ * (u : Γ) * τ) * τ = (τ * τ) * (u : Γ) * (τ * τ) := by group
      _ = u := by rw [hτ2]; simp)
  let φ : ↥A →* ↥A := MonoidHom.mk' (fun u => u * (ψ u)⁻¹) (fun a b => by
    rw [map_mul, mul_inv, mul_mul_mul_comm])
  have hφ : ∀ u : ↥A, φ u = u * (ψ u)⁻¹ := fun u => rfl
  have hker : φ.ker = C.subgroupOf A := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf, hφ, mul_inv_eq_one,
      Subtype.ext_iff, hψ, mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨u.2, (eq_mul_inv_iff_mul_eq.1 h)⟩
    · rintro ⟨-, h⟩
      exact eq_mul_inv_iff_mul_eq.2 h
  have hker_card : Nat.card φ.ker = Nat.card C := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hrange_card : Nat.card φ.range = Nat.card C := by
    rw [hker_card] at h1
    exact Nat.eq_of_mul_eq_mul_left hCpos (h1.trans hcard)
  have hexp : ∀ x : ↥A, x⁻¹ = x := fun x =>
    inv_eq_of_mul_eq_one_right (Subtype.ext (by simpa [sq] using hA.2 x x.2))
  have hrange_le : φ.range ≤ C.subgroupOf A := by
    rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf]
    refine ⟨(φ u).2, mem_centralizer_singleton_iff.2 ?_⟩
    have h2 : ψ (φ u) = φ u := by
      rw [hφ, map_mul, map_inv, hψψ, ← hexp (u * (ψ u)⁻¹), mul_inv, inv_inv, mul_comm]
    have h3 := congrArg Subtype.val h2
    rw [hψ] at h3
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hrange_eq : φ.range = C.subgroupOf A := by
    refine Subgroup.eq_of_le_of_card_ge hrange_le ?_
    rw [hrange_card]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv).le
  have hw : (⟨w, hwA⟩ : ↥A) ∈ C.subgroupOf A := by
    rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf]
    exact ⟨hwA, mem_centralizer_singleton_iff.2 hwτ.symm⟩
  rw [← hrange_eq] at hw
  obtain ⟨u, hu⟩ := hw
  refine ⟨u, u.2, ?_⟩
  have h4 := congrArg Subtype.val hu
  rw [hφ] at h4
  have h5 : ((u * (ψ u)⁻¹ : ↥A) : Γ) = u * (τ * u * τ⁻¹)⁻¹ := rfl
  rw [h5] at h4
  have h6 : (u : Γ) * (τ * u * τ⁻¹)⁻¹ = w := h4
  rw [← h6]
  group

theorem mem_of_isPGroup_of_central_sylow {A C : Subgroup Γ} (hA : fusionIsSylowIn 2 A C)
    (hcent : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) {w : Γ} (hwC : w ∈ C)
    (hw : IsPGroup 2 (zpowers w)) : w ∈ A := by
  have hwc : w ∈ centralizer (A : Set Γ) :=
    Subgroup.mem_centralizer_iff.2 fun a ha => (hcent w hwC a ha).symm
  have hnorm : zpowers w ≤ normalizer (A : Set Γ) :=
    zpowers_le.2 (Subgroup.centralizer_le_normalizer _ hwc)
  have hpg : IsPGroup 2 (A ⊔ zpowers w : Subgroup Γ) := hA.2.1.to_sup_of_normal_left' hw hnorm
  have heq : A ⊔ zpowers w = A :=
    hA.2.2 _ (sup_le hA.1 (zpowers_le.2 hwC)) hpg le_sup_left
  rw [← heq]
  exact mem_sup_right (mem_zpowers w)

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
