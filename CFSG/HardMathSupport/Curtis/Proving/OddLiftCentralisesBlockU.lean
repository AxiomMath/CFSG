module

public import CFSG.HardMathSupport.Curtis.Proving.CoprimeCentralizerTwoPart

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique

open scoped commutatorElement

variable {G : Type} [Group G]

theorem blockU_normalized_iff {L : Subgroup G} {g : G} (hg : g ∈ L) (n : G) :
    n ∈ blockU L ↔ g * n * g⁻¹ ∈ blockU L := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := blockU_conj_mem (L.inv_mem hg) h
    simpa using h'
  · have h' := blockU_conj_mem hg h
    simpa [mul_assoc] using h'

theorem centralizes_blockU_of_odd_mod_blockZ {L : Subgroup G} [Finite G] (hL : IsShort2 L)
    {s : G} (hsL : s ∈ L) (hodd : Odd (orderOf s))
    (htriv : ⁅blockU L, Subgroup.zpowers s⁆ ≤ blockZ L) :
    s ∈ Subgroup.centralizer (blockU L : Set G) := by
  have hUQ : blockU L ≤ blockQ L := hL.2.2.1.1.trans inf_le_left
  have hPp : IsPGroup 2 ↥(blockU L) := by
    intro g
    obtain ⟨k, hk⟩ := blockQ_exists_two_pow (hUQ g.2)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow).1 hPp
  set X : Subgroup G := Subgroup.zpowers s with hXdef
  have hXL : X ≤ L := Subgroup.zpowers_le.2 hsL
  have hXN : X ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_normalizer_iff.2 (fun n => blockU_normalized_iff hsL n))
  have hcop2 : Nat.Coprime (orderOf s) (2 ^ n) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have hcop : Nat.Coprime (Nat.card X) (Nat.card (blockU L)) := by
    rw [hXdef, Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right hn hcop2
  have hcomm := CFSG.HardMathSupport.Solomon.Coordinator.coprime_commutator_commutator_eq'
    (G := G) (P := blockU L) (X := X) hXN hcop
  have hZbot : ⁅blockZ L, X⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro z hz x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hzC : z ∈ Subgroup.centralizer (L : Set G) := hz.2
    exact (Subgroup.mem_centralizer_iff.1 hzC x (hXL hx)).symm
  have hbot : ⁅⁅blockU L, X⁆, X⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (Subgroup.commutator_mono htriv le_rfl).trans hZbot.le
  have hUXbot : ⁅blockU L, X⁆ = ⊥ := by
    rw [← hcomm, hbot]
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hmem : ⁅u, s⁆ ∈ ⁅blockU L, X⁆ :=
    Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers s)
  rw [hUXbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem eq_one_of_odd_mod_blockZ {L : Subgroup G} [Finite G] (hL : IsShort2 L) {s : G}
    (hsL : s ∈ L) (hodd : Odd (orderOf s))
    (htriv : ⁅blockU L, Subgroup.zpowers s⁆ ≤ blockZ L) : s = 1 :=
  eq_one_of_odd_centralizes_blockU hL hsL hodd (centralizes_blockU_of_odd_mod_blockZ hL hsL hodd htriv)

end CFSG.HardMathSupport.Curtis.Proving

end
