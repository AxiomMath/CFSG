module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.PairNormal
public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open scoped MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace PairInf

theorem sl23_order3_noncomm : ∃ x₀ : SL(2, ZMod 3), x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧
    ∀ u : SL(2, ZMod 3), u ^ 4 = 1 → u ≠ 1 → u ≠ -1 →
      u * (x₀ * u * x₀⁻¹) ≠ (x₀ * u * x₀⁻¹) * u := by
  decide

theorem pow_four_of_mem_card8 {H : Type*} [Group H] (φ : H ≃* SL(2, ZMod 3)) {P : Subgroup H}
    (hP : Nat.card P = 8) {h : H} (hh : h ∈ P) : φ h ^ 4 = 1 := by
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have h8 : h ^ 8 = 1 := by
    have := congrArg Subtype.val (pow_card_eq_one' (G := P) (x := ⟨h, hh⟩))
    rw [hP] at this
    simpa using this
  apply sl23_pow_eight
  rw [← map_pow, h8, map_one]

theorem sl23_neg_one_central : ∀ u : SL(2, ZMod 3), u * -1 = -1 * u := by decide

theorem pair_inf_core {G : Type*} [Group G] {L Ls K Ks X : Subgroup G} {z : G}
    (ψ : L ≃* SL(2, ZMod 3))
    (hcomm : ∀ x ∈ L, ∀ y ∈ Ls, x * y = y * x)
    (hK : K ≤ L) (hKn : ∀ a ∈ L, ∀ k ∈ K, a * k * a⁻¹ ∈ K)
    (hKs : Ks ≤ Ls)
    (hLX : ∀ a ∈ L, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hKX : ∀ x ∈ K, ∀ y ∈ X, x * y = y * x)
    (hz : IsUniqueInvolution K z) (hP : Nat.card (K.subgroupOf L) = 8) :
    ∀ k ∈ K, ∀ ks ∈ Ks, k * ks ∈ X → k ∈ Subgroup.zpowers z := by
  intro k hk ks hks hkX
  by_contra hkz
  obtain ⟨x₀, -, -, hnc⟩ := sl23_order3_noncomm
  have hzL' : z ∈ L := hK hz.mem
  let zL : L := ⟨z, hzL'⟩
  have hψz : ψ zL = -1 := by
    have hinv : ψ zL * ψ zL = 1 := by
      rw [← map_mul, show zL * zL = 1 from Subtype.ext hz.sq, map_one]
    refine (sl23_involution (ψ zL) hinv).resolve_left ?_
    intro h
    apply hz.ne_one
    have h1 : zL = 1 := ψ.injective (by rw [h, map_one])
    exact congrArg Subtype.val h1
  have hne : ∀ g : L, (g : G) ∉ Subgroup.zpowers z → ψ g ≠ 1 ∧ ψ g ≠ -1 := by
    intro g hg
    constructor
    · intro h
      apply hg
      have h1 : g = 1 := ψ.injective (by rw [h, map_one])
      rw [show (g : G) = 1 by simp [h1]]
      exact Subgroup.one_mem _
    · intro h
      apply hg
      have h1 : g = zL := ψ.injective (by rw [h, hψz])
      rw [show (g : G) = z by simp [h1, zL]]
      exact Subgroup.mem_zpowers z
  obtain ⟨aL, hψa⟩ : ∃ aL : L, ψ aL = x₀ := ⟨ψ.symm x₀, ψ.apply_symm_apply x₀⟩
  have ha : (aL : G) ∈ L := aL.2
  have hkL : k ∈ L := hK hk
  let kL : L := ⟨k, hkL⟩
  have hu4 : ψ kL ^ 4 = 1 := pow_four_of_mem_card8 ψ hP (h := kL) (Subgroup.mem_subgroupOf.mpr hk)
  have hcomm_a : (aL : G) * ks = ks * aL := hcomm _ ha ks (hKs hks)
  have hks' : (aL : G) * ks * (aL : G)⁻¹ = ks := by rw [hcomm_a]; group
  have hc_eq : (aL : G) * (k * ks) * (aL : G)⁻¹ * (k * ks)⁻¹ = (aL : G) * k * (aL : G)⁻¹ * k⁻¹ := by
    calc (aL : G) * (k * ks) * (aL : G)⁻¹ * (k * ks)⁻¹
        = ((aL : G) * k * (aL : G)⁻¹) * ((aL : G) * ks * (aL : G)⁻¹) * ks⁻¹ * k⁻¹ := by group
      _ = ((aL : G) * k * (aL : G)⁻¹) * ks * ks⁻¹ * k⁻¹ := by rw [hks']
      _ = (aL : G) * k * (aL : G)⁻¹ * k⁻¹ := by group
  set c : G := (aL : G) * k * (aL : G)⁻¹ * k⁻¹ with hc
  have hcX : c ∈ X := by
    rw [← hc_eq]
    exact X.mul_mem (hLX _ ha _ hkX) (X.inv_mem hkX)
  have hcK : c ∈ K := by
    rw [hc]
    exact K.mul_mem (hKn _ ha k hk) (K.inv_mem hk)
  have hcL : c ∈ L := by
    rw [hc]
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hkL) (L.inv_mem ha)) (L.inv_mem hkL)
  let cL : L := ⟨c, hcL⟩
  have hcL_eq : cL = aL * kL * aL⁻¹ * kL⁻¹ := Subtype.ext (by simp [cL, kL, hc])
  have hψc : ψ cL = x₀ * ψ kL * x₀⁻¹ * (ψ kL)⁻¹ := by
    rw [hcL_eq]
    simp only [map_mul, map_inv, hψa]
  have hcz : c ∉ Subgroup.zpowers z := by
    intro hcz
    have hcases : ψ cL = 1 ∨ ψ cL = -1 := by
      rcases mem_zpowers_of_sq_eq_one hz.sq hcz with h | h
      · left
        rw [show cL = 1 from Subtype.ext h, map_one]
      · right
        rw [show cL = zL from Subtype.ext h, hψz]
    rw [hψc] at hcases
    rcases hcases with h | h
    · have hd : x₀ * ψ kL * x₀⁻¹ = ψ kL := mul_inv_eq_one.mp h
      exact hnc (ψ kL) hu4 (hne kL hkz).1 (hne kL hkz).2 (by rw [hd])
    · have hd : x₀ * ψ kL * x₀⁻¹ = -1 * ψ kL := mul_inv_eq_iff_eq_mul.mp h
      exact hnc (ψ kL) hu4 (hne kL hkz).1 (hne kL hkz).2
        (by rw [hd, ← mul_assoc, sl23_neg_one_central])
  have hdX : (aL : G) * c * (aL : G)⁻¹ ∈ X := hLX _ ha _ hcX
  have hdL : (aL : G) * c * (aL : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem ha hcL) (L.inv_mem ha)
  let dL : L := ⟨(aL : G) * c * (aL : G)⁻¹, hdL⟩
  have hcd : cL * dL = dL * cL := Subtype.ext (hKX c hcK _ hdX)
  have hfin : ψ cL * (x₀ * ψ cL * x₀⁻¹) = (x₀ * ψ cL * x₀⁻¹) * ψ cL := by
    have hdψ : ψ dL = x₀ * ψ cL * x₀⁻¹ := by
      rw [show dL = aL * cL * aL⁻¹ from Subtype.ext rfl]
      simp only [map_mul, map_inv, hψa]
    have := congrArg ψ hcd
    rw [map_mul, map_mul, hdψ] at this
    exact this
  have hcP : ψ cL ^ 4 = 1 := pow_four_of_mem_card8 ψ hP (h := cL) (Subgroup.mem_subgroupOf.mpr hcK)
  exact hnc (ψ cL) hcP (hne cL hcz).1 (hne cL hcz).2 hfin

end PairInf

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
