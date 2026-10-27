module

public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Pairing

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem mem_center_of_sq_mem_center_sylow {n : ℕ} (hn : 8 ≤ n) {X : Type} [Group X] [Finite X]
    (hX : IsDoubleCoverOfAlt X n) (S : Sylow 2 X) {w : X}
    (hwc : ∀ s ∈ (S : Subgroup X), s * w = w * s) (hw2 : w * w ∈ center X) : w ∈ center X := by
  obtain ⟨π, hπs, hπk⟩ :=
    CFSG.Sporadic.Recognition.LyonsSims.exists_centralExtension_of_doubleCover hX
  by_contra hwn
  have hπw : π w ≠ 1 := fun h => hwn (hπk ▸ h)
  have hπw2 : (π w : Perm (Fin n)) * (π w : Perm (Fin n)) = 1 := by
    have : π (w * w) = 1 := by
      rw [← MonoidHom.mem_ker, hπk]
      exact hw2
    rw [map_mul] at this
    exact congrArg Subtype.val this
  have hπw1 : (π w : Perm (Fin n)) ≠ 1 := fun h => hπw (Subtype.ext h)
  obtain ⟨a₁, b₁, a₂, b₂, h12, h1b1, h1b2, h2b1, h2b2, hbb, e1, e2, e3, e4⟩ :=
    exists_swap_pairs (π w).2 hπw2 hπw1
  have hsmem : swap a₁ a₂ * swap b₁ b₂ ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap h12, sign_swap hbb]
    decide
  obtain ⟨y, hy⟩ := hπs ⟨swap a₁ a₂ * swap b₁ b₂, hsmem⟩
  have hy' : (π y : Perm (Fin n)) = swap a₁ a₂ * swap b₁ b₂ := congrArg Subtype.val hy
  have hne : ⁅w, y⁆ ≠ 1 :=
    commutator_ne_one_of_doubleCover hn hX hπs hπk h12 h1b1 h1b2 h2b1 h2b2 hbb e1 e2 e3 e4 hy'
  have hπc : ⁅π w, π y⁆ = 1 := by
    have h1 := comm_swap_pairs h1b1 h1b2 h2b1 h2b2 (π w : Perm (Fin n)) e1 e2 e3 e4
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy', h1, OneMemClass.coe_one]
    group
  have hzc : ⁅w, y⁆ ∈ center X := by
    rw [← hπk, MonoidHom.mem_ker, map_commutatorElement, hπc]
  have hz2 : ⁅w, y⁆ * ⁅w, y⁆ = 1 := by
    have h1 : orderOf (⟨⁅w, y⁆, hzc⟩ : center X) ∣ Nat.card (center X) :=
      orderOf_dvd_natCard _
    rw [hX.2.1] at h1
    have h2 : (⟨⁅w, y⁆, hzc⟩ : center X) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
    have h3 := congrArg Subtype.val h2
    simpa [pow_two] using h3
  have hp : y * w * y⁻¹ = w * ⁅w, y⁆ := by
    have e : ⁅w, y⁆ ⁻¹ = ⁅w, y⁆ := inv_eq_of_mul_eq_one_right hz2
    have hzc' := mem_center_iff.1 hzc
    have h1 : y * w * y⁻¹ = ⁅w, y⁆⁻¹ * w := by
      simp only [commutatorElement_def, mul_inv_rev, inv_inv]
      group
    rw [h1, e]
    exact (hzc' w).symm
  have hev := even_index_centralizer hzc hne hz2 hp
  have hle : (S : Subgroup X) ≤ centralizer ({w} : Set X) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hwc s hs)
  have h1 : (centralizer ({w} : Set X)).index ∣ (S : Subgroup X).index :=
    Subgroup.index_dvd_of_le hle
  have h3 : ¬ 2 ∣ (S : Subgroup X).index := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact S.not_dvd_index
  exact h3 ((even_iff_two_dvd.mp hev).trans h1)

section Center

variable {n : ℕ} {K : Type} [Group K]

theorem center_le_sylow (hK : IsDoubleCoverOfAlt K n) (S : Sylow 2 K) :
    center K ≤ (S : Subgroup K) := by
  have hp : IsPGroup 2 (center K) := IsPGroup.of_card (n := 1) (by rw [hK.2.1]; norm_num)
  exact hp.le_sylow_of_normal S

theorem center_sylow_eq [Finite K] (hn : 8 ≤ n) (hK : IsDoubleCoverOfAlt K n) (S : Sylow 2 K) :
    Subgroup.center ↥(S : Subgroup K) = (center K).subgroupOf (S : Subgroup K) := by
  have key : ∀ k : ℕ, ∀ s : ↥(S : Subgroup K), s ∈ Subgroup.center ↥(S : Subgroup K) →
      s ^ 2 ^ k = 1 → (s : K) ∈ center K := by
    intro k
    induction k with
    | zero =>
      intro s _ hs
      have : s = 1 := by simpa using hs
      rw [this]
      exact one_mem _
    | succ k ih =>
      intro s hs hsk
      have hs2 : s * s ∈ Subgroup.center ↥(S : Subgroup K) := mul_mem hs hs
      have hs2k : (s * s) ^ 2 ^ k = 1 := by
        rw [← pow_two, ← pow_mul, ← pow_succ']
        exact hsk
      have hsq : (s : K) * s ∈ center K := ih (s * s) hs2 hs2k
      refine mem_center_of_sq_mem_center_sylow hn hK S (fun t ht => ?_) hsq
      have := mem_center_iff.1 hs ⟨t, ht⟩
      exact congrArg Subtype.val this
  ext s
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hs
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (S.isPGroup' : IsPGroup 2 (S : Subgroup K))) s
    exact key k s hs (by rw [← hk]; exact pow_orderOf_eq_one s)
  · intro hs
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.1 hs g)

theorem sylow_centralizer_self [Finite K] (hn : 8 ≤ n) (hK : IsDoubleCoverOfAlt K n)
    (S : Sylow 2 K) :
    (centralizer ((S : Subgroup K) : Set K)) ⊓ (S : Subgroup K) = center K := by
  apply le_antisymm
  · rintro x ⟨hxc, hxS⟩
    have h1 : (⟨x, hxS⟩ : ↥(S : Subgroup K)) ∈ Subgroup.center ↥(S : Subgroup K) := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 hxc g g.2)
    have := (center_sylow_eq hn hK S ▸ h1 : _)
    exact (Subgroup.mem_subgroupOf.1 this)
  · intro x hx
    exact ⟨mem_centralizer_iff.2 (fun g _ => mem_center_iff.1 hx g), center_le_sylow hK S hx⟩

end Center

end CFSG.OddStandard.Solomon75
