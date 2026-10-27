module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup

theorem normalizer_le_centralizer_of_central_involution {G : Type*} [Group G] [Finite G] {x : G}
    (hx : orderOf x = 2) (hxc : ∀ h : G, h * x = x * h) {P : Subgroup G}
    (hPidx : ¬ 2 ∣ P.index) (hcard : Nat.card P = 4) (hxP : x ∈ P) :
    normalizer (P : Set G) ≤ centralizer (P : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ a b : P, a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
      (by rw [hcard]; norm_num)).is_comm.comm a b
  have hPN : P ≤ normalizer (P : Set G) := le_normalizer
  have hstab : ∀ a' : P, MulAction.stabilizer (normalizer (P : Set G)) a' = ⊤ := by
    intro a'
    set N := normalizer (P : Set G) with hN
    let x' : P := ⟨x, hxP⟩
    have hx1 : x' ≠ 1 := by
      intro h
      have : x = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hx
      omega
    have hsmulx : ∀ g : N, g • x' = x' := by
      intro g
      apply Subtype.ext
      show (g : G) * x * (g : G)⁻¹ = x
      rw [hxc, mul_inv_cancel_right]
    by_cases h1 : a' = 1
    · subst h1
      ext g
      simp [MulAction.mem_stabilizer_iff]
    by_cases hxa : a' = x'
    · subst hxa
      ext g
      simp [MulAction.mem_stabilizer_iff, hsmulx]
    have horb : MulAction.orbit N a' ⊆ ({1, x'}ᶜ : Set P) := by
      rintro _ ⟨g, rfl⟩
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro h
        apply h1
        have := congrArg (fun y => g⁻¹ • y) h
        simpa using this
      · intro h
        apply hxa
        have := congrArg (fun y => g⁻¹ • y) h
        simpa [hsmulx] using this
    have hcardS : ({1, x'}ᶜ : Set P).ncard = 2 := by
      rw [Set.ncard_compl, Set.ncard_pair hx1.symm, hcard]
    have hle : (MulAction.stabilizer N a').index ≤ 2 := by
      rw [MulAction.index_stabilizer]
      exact (Set.ncard_le_ncard horb).trans hcardS.le
    have hsub : P.subgroupOf N ≤ MulAction.stabilizer N a' := by
      intro g hg
      rw [MulAction.mem_stabilizer_iff]
      have hgP : (g : G) ∈ P := hg
      have hc := congrArg Subtype.val (hcomm ⟨g, hgP⟩ a')
      apply Subtype.ext
      show (g : G) * a' * (g : G)⁻¹ = a'
      have hc' : (g : G) * a' = a' * g := hc
      rw [hc', mul_inv_cancel_right]
    have hdvd : (MulAction.stabilizer N a').index ∣ P.index :=
      (Subgroup.index_dvd_of_le hsub).trans (Subgroup.relIndex_dvd_index_of_le hPN)
    have hodd : ¬ 2 ∣ (MulAction.stabilizer N a').index := fun h => hPidx (h.trans hdvd)
    have hpos : 0 < (MulAction.stabilizer N a').index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h1' : (MulAction.stabilizer N a').index = 1 := by omega
    exact Subgroup.index_eq_one.mp h1'
  intro g hg
  rw [mem_centralizer_iff]
  intro a ha
  have key := hstab ⟨a, ha⟩
  have hmem : (⟨g, hg⟩ : normalizer (P : Set G)) ∈
      MulAction.stabilizer (normalizer (P : Set G)) (⟨a, ha⟩ : P) := by
    rw [key]; exact mem_top _
  rw [MulAction.mem_stabilizer_iff] at hmem
  have h2 : g * a * g⁻¹ = a := congrArg Subtype.val hmem
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

theorem eq_top_of_central_involution_sylow_four {H : Type} [Group H] [Finite H] {x : H}
    (hx : orderOf x = 2)
    (hxc : ∀ h : H, h * x = x * h) {P : Subgroup H} (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index)
    (hcard : Nat.card P = 4) (hxP : x ∈ P)
    (hO : ∀ W : Subgroup H, W.Normal → Odd (Nat.card W) → W = ⊥) : P = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 H := hP.toSylow hPidx
  have hS : (S : Subgroup H) = P := hP.toSylow_coe hPidx
  have hSset : (S : Set H) = (P : Set H) := congrArg (SetLike.coe : Subgroup H → Set H) hS
  have hnorm : normalizer (S : Set H) ≤ centralizer (S : Set H) := by
    rw [hSset]
    exact normalizer_le_centralizer_of_central_involution hx hxc hPidx hcard hxP
  have hcomp := MonoidHom.ker_transferSylow_isComplement' S hnorm
  have hodd : Odd (Nat.card (MonoidHom.transferSylow S hnorm).ker) :=
    Nat.odd_iff.mpr (by
      have := MonoidHom.not_dvd_card_ker_transferSylow S hnorm
      omega)
  have hbot : (MonoidHom.transferSylow S hnorm).ker = ⊥ := hO _ (MonoidHom.normal_ker _) hodd
  have hidx := hcomp.index_eq_card
  rw [hbot, Subgroup.card_bot, hS] at hidx
  exact Subgroup.index_eq_one.mp hidx

end CFSG.GH74.GLS.C3.Layer1.Back
