module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import Mathlib.Data.Nat.Choose.Dvd
import TauCeti.GroupTheory.Commutator
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Cyclic

public section

open scoped Pointwise commutatorElement

namespace CFSG.GroupTheory

theorem pow_eq_one_iff_mem_sup_of_isElementaryAbelian_isCyclic
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {B P : Subgroup G} [IsElementaryAbelian p B]
    (hPcyc : IsCyclic P) (hPp : IsPGroup p P)
    (hBP : B ≤ Subgroup.normalizer (P : Set G))
    (hOmega : ∀ x ∈ P, x ^ p = 1 → x ∈ B) :
    ∀ s ∈ B ⊔ P, s ^ p = 1 ↔ s ∈ B := by
  have hB_comm : ∀ u ∈ B, ∀ v ∈ B, Commute u v := by
    intro u hu v hv
    change u * v = v * u
    simpa using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := B)).comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hPcomm : IsMulCommutative P := @IsCyclic.isMulCommutative P _ hPcyc
  have hP_comm : ∀ u ∈ P, ∀ v ∈ P, Commute u v := by
    intro u hu v hv
    change u * v = v * u
    simpa using congrArg Subtype.val
      ((@IsMulCommutative.is_comm P _ hPcomm).comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hnorm : ∀ b ∈ B, ∀ y ∈ P, b * y * b⁻¹ ∈ P := by
    intro b hb y hy
    exact (Subgroup.mem_normalizer_iff.mp (hBP hb) y).mp hy
  intro s hs
  constructor
  · intro hspow
    have hsBP : s ∈ (B : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right B P hBP]
      exact hs
    rcases hsBP with ⟨b, hb, x, hx, rfl⟩
    have hbpow : b ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (A := B) b hb
    have hcentral : ∀ y ∈ P, b ^ p * y * (b ^ p)⁻¹ = y := by
      intro y _
      simp [hbpow]
    have hdisp : ∀ y ∈ P, ⁅b, y⁆ ^ p = 1 := by
      intro y hy
      simpa only [commutatorElement_def] using
        CFSG.LocalAnalysis.RankThreeTheoremC.commutator_pow_prime_eq_one_of_cyclic
          hp hp2 hPcyc hPp (hnorm b hb) hcentral y hy
    have hbxp : ⁅b, x⁆ ∈ P := by
      simpa only [commutatorElement_def] using
        mul_mem (hnorm b hb x hx) (P.inv_mem hx)
    have hxb_eq : ⁅x, b⁆ = ⁅b, x⁆⁻¹ :=
      (commutatorElement_inv (g₁ := b) (g₂ := x)).symm
    have hxbp : ⁅x, b⁆ ∈ P := by
      rw [hxb_eq]
      exact P.inv_mem hbxp
    have hdisp_xb : ⁅x, b⁆ ^ p = 1 := by
      rw [hxb_eq, inv_pow, hdisp x hx, inv_one]
    have hxB : ⁅x, b⁆ ∈ B := hOmega ⁅x, b⁆ hxbp hdisp_xb
    have hcomm_b : Commute b ⁅x, b⁆ := hB_comm b hb ⁅x, b⁆ hxB
    have hcomm_x : Commute x ⁅x, b⁆ := hP_comm x hx ⁅x, b⁆ hxbp
    have hchoose : p ∣ p.choose 2 :=
      Nat.Prime.dvd_choose_self hp (by norm_num) (lt_of_le_of_ne hp.two_le hp2.symm)
    have hcommpow : ⁅x, b⁆ ^ p.choose 2 = 1 := by
      obtain ⟨k, hk⟩ := hchoose
      rw [hk, pow_mul, hdisp_xb, one_pow]
    have hpow : (b * x) ^ p = x ^ p := by
      rw [Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two
        (a := b) (b := x) hcomm_b hcomm_x p, hbpow, hcommpow]
      simp
    have hxpow : x ^ p = 1 := by
      rw [hpow] at hspow
      exact hspow
    exact mul_mem hb (hOmega x hx hxpow)
  · intro hsB
    exact elemPow_eq_one_of_isElementaryAbelian (A := B) s hsB

theorem characteristic_subgroupOf_sup_of_isElementaryAbelian_isCyclic
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {B P : Subgroup G} [IsElementaryAbelian p B]
    (hPcyc : IsCyclic P) (hPp : IsPGroup p P)
    (hBP : B ≤ Subgroup.normalizer (P : Set G))
    (hOmega : ∀ x ∈ P, x ^ p = 1 → x ∈ B) :
    (B.subgroupOf (B ⊔ P)).Characteristic := by
  let S : Subgroup G := B ⊔ P
  change (B.subgroupOf S).Characteristic
  have hker : ∀ s ∈ S, s ^ p = 1 ↔ s ∈ B := by
    intro s hs
    exact pow_eq_one_iff_mem_sup_of_isElementaryAbelian_isCyclic
      hp hp2 hPcyc hPp hBP hOmega s (by simpa [S] using hs)
  rw [Subgroup.characteristic_iff_map_le]
  intro φ y hy
  rw [Subgroup.mem_map] at hy
  rcases hy with ⟨z, hz, rfl⟩
  have hzpow : (z : G) ^ p = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (A := B) (z : G)
      (Subgroup.mem_subgroupOf.mp hz)
  have hφpow : ((φ z : G) ^ p) = 1 := by
    have hzS : z ^ p = 1 := by
      apply Subtype.ext
      simpa using hzpow
    calc
      ((φ z : G) ^ p) = ((φ (z ^ p) : G)) := by simp
      _ = 1 := by simp [hzS]
  exact (hker (φ z : G) (φ z).2).mp hφpow

end CFSG.GroupTheory
