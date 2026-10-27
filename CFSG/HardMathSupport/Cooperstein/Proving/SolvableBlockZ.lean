module

public import CFSG.HardMathSupport.Cooperstein.Proving.SolvableBlockDichotomy
public import CFSG.HardMathSupport.Cooperstein.Proving.SolvableShortBlock
public import CFSG.HardMathSupport.Cooperstein.Proving.CharTwoOverPCore
public import CFSG.HardMathSupport.Cooperstein.Proving.SolvableBlockQuotient

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open Subgroup
open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem commutator_pCore_top_solvable [Finite G] {L : Subgroup G}
    (hL : IsShort2 L) (hs : Group.IsSolvable L) :
    ⁅CFSG.pCore 2 L, (⊤ : Subgroup L)⁆ = CFSG.pCore 2 L := by
  have hQ2 : ∀ q ∈ CFSG.pCore 2 L, ∃ k : ℕ, q ^ 2 ^ k = 1 := by
    intro q hq
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (⟨q, hq⟩ : CFSG.pCore 2 L)
    exact ⟨k, congrArg Subtype.val hk⟩
  have hcl1 : ∀ (N : Subgroup L) [N.Normal],
      (∀ g : L, ∃ k : ℕ, (QuotientGroup.mk g : L ⧸ N) ^ 2 ^ k = 1) → N = ⊤ := by
    intro N _ h
    refine hL.1 N (show IsPGroup 2 (L ⧸ N) from fun y => ?_)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact h g
  exact commutator_eq_of_index_three (CFSG.pCore 2 L) hQ2 (index_pCore_eq_three hL hs) hcl1

theorem blockZ_eq_bot_of_solvable [Finite G] {L : Subgroup G}
    (hL : IsShort2 L) (hs : Group.IsSolvable L) : blockZ L = ⊥ := by
  classical
  have hUQ : blockU L = blockQ L := blockU_eq_blockQ_of_solvable hL hs
  have hcore := commutator_pCore_top_solvable hL hs
  have hQ2 : ∀ q ∈ CFSG.pCore 2 L, ∃ k : ℕ, q ^ 2 ^ k = 1 := by
    intro q hq
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (⟨q, hq⟩ : CFSG.pCore 2 L)
    exact ⟨k, congrArg Subtype.val hk⟩
  have hmemQ : ∀ x ∈ CFSG.pCore 2 L, (x : G) ∈ blockQ L := by
    intro x hx
    have h : (x : G) ∈ (CFSG.pCore 2 L).map L.subtype := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [← pCoreOf_eq_map] at h
    exact h
  have hzQ : ∀ z ∈ blockQ L, ∃ x ∈ CFSG.pCore 2 L, (x : G) = z := by
    intro z hz
    have hz' : z ∈ (CFSG.pCore 2 L).map L.subtype := by
      rw [← pCoreOf_eq_map]
      exact hz
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hz'
    exact ⟨x, hx, hxz⟩
  have hcentral : ∀ z ∈ blockQ L, ∀ h ∈ blockQ L, h * z = z * h := by
    intro z hz h hh
    have hzU : z ∈ blockU L := by rw [hUQ]; exact hz
    have hzC : z ∈ Subgroup.centralizer (blockQ L : Set G) := (hL.2.2.1.1 hzU).2
    exact Subgroup.mem_centralizer_iff.mp hzC h hh
  have hab : ∀ a ∈ CFSG.pCore 2 L, ∀ b ∈ CFSG.pCore 2 L, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hcentral (a : G) (hmemQ a ha) (b : G) (hmemQ b hb)).symm
  obtain ⟨t, _, htP⟩ := exists_order_three_sup (CFSG.pCore 2 L) hQ2
    (index_pCore_eq_three hL hs)
  ext z
  rw [Subgroup.mem_bot]
  constructor
  · intro hz
    have hzU : z ∈ blockU L := (Subgroup.mem_inf.mp hz).1
    have hzB : z ∈ blockQ L := by rw [hUQ] at hzU; exact hzU
    have hzC : z ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hz).2
    obtain ⟨x, hx, hxz⟩ := hzQ z hzB
    have hzc : ∀ h : L, h * x = x * h := by
      intro h
      apply Subtype.ext
      have h2 := Subgroup.mem_centralizer_iff.mp hzC (h : G) h.2
      simp only [Subgroup.coe_mul, hxz]
      exact h2
    have h1 : x = 1 := central_eq_one_of_commutator_eq (CFSG.pCore 2 L) hab t htP hcore x hx hzc
    rw [← hxz, h1]
    rfl
  · intro hz
    rw [hz]
    exact Subgroup.one_mem _

theorem dichotomy_of_solvable [Finite G] {L : Subgroup G}
    (hL : IsShort2 L) (hs : Group.IsSolvable L) {K : Subgroup G} (hKL : K ≤ L)
    (hKn : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K)
    (hK2 : ∀ k ∈ K, ∃ n : ℕ, k ^ 2 ^ n = 1) :
    K = ⊥ ∨ K = blockQ L := by
  have hUQ : blockU L = blockQ L := blockU_eq_blockQ_of_solvable hL hs
  have hZ : blockZ L = ⊥ := blockZ_eq_bot_of_solvable hL hs
  have hKQ : K ≤ blockQ L := le_pCoreOf_two_of_normal hKL hK2 hKn
  have hKU : K ≤ blockU L := by rw [hUQ]; exact hKQ
  have hnorm : L ≤ Subgroup.normalizer (K : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hKn l hl h hh
    · intro hh
      have h1 := hKn l⁻¹ (L.inv_mem hl) _ hh
      have e : l⁻¹ * (l * h * l⁻¹) * l⁻¹⁻¹ = h := by group
      rw [e] at h1
      exact h1
  have hW := hL.2.2.2.2.2 K (by rw [hZ]; exact bot_le) hKU hnorm
  rw [hZ, hUQ] at hW
  exact hW

end CFSG.HardMathSupport.Cooperstein.Proving

end
