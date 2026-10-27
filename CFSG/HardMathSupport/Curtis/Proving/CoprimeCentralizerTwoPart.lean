module

public import CFSG.HardMathSupport.Solomon.Coordinator.AlphaFunctor
public import CFSG.HardMathSupport.Curtis.Proving.CentralizerUOverQuasisimple

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique

open scoped commutatorElement

variable {G : Type} [Group G]

theorem blockQ_exists_two_pow {L : Subgroup G} {x : G} (hx : x ∈ blockQ L) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  rw [blockQ_eq_map] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := L) ⟨y, hy⟩
  refine ⟨k, ?_⟩
  have h1 : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem eq_one_of_mem_blockQ_of_odd {L : Subgroup G} {c : G} (hc : c ∈ blockQ L)
    (hodd : Odd (orderOf c)) : c = 1 := by
  obtain ⟨k, hk⟩ := blockQ_exists_two_pow hc
  have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf c) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem eq_one_of_odd_centralizes_blockU {L : Subgroup G} [Finite G] (hL : IsShort2 L) {c : G}
    (hcL : c ∈ L) (hodd : Odd (orderOf c))
    (hc : c ∈ Subgroup.centralizer (blockU L : Set G)) : c = 1 := by
  have hnorm : ∀ g ∈ L, ∀ n : G, n ∈ blockQ L ↔ g * n * g⁻¹ ∈ blockQ L := by
    intro g hg n
    refine ⟨blockQ_conj_mem hg, fun h => ?_⟩
    have h' := blockQ_conj_mem (L := L) (L.inv_mem hg) h
    simpa [mul_assoc] using h'
  set X : Subgroup G := Subgroup.zpowers c with hXdef
  have hXL : X ≤ L := Subgroup.zpowers_le.2 hcL
  have hXN : X ≤ Subgroup.normalizer (blockQ L : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_normalizer_iff.2 (hnorm c hcL))
  have hXC : X ≤ Subgroup.centralizer (blockU L : Set G) := Subgroup.zpowers_le.2 hc
  have hPp : IsPGroup 2 ↥(blockQ L) := by
    intro g
    obtain ⟨k, hk⟩ := blockQ_exists_two_pow g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow).1 hPp
  have hcop2 : Nat.Coprime (orderOf c) (2 ^ n) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have hcop : Nat.Coprime (Nat.card X) (Nat.card (blockQ L)) := by
    rw [hXdef, Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right hn hcop2
  have hcomm := CFSG.HardMathSupport.Solomon.Coordinator.coprime_commutator_commutator_eq'
    (G := G) (P := blockQ L) (X := X) hXN hcop
  have hPX : ⁅blockQ L, X⁆ ≤ blockU L := Subgroup.commutator_mono le_rfl hXL
  have hzero : ⁅⁅blockQ L, X⁆, X⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.1 (hXC hx) u (hPX hu)
  have hPXbot : ⁅blockQ L, X⁆ = ⊥ := by
    rw [← hcomm, hzero]
  have hcP : c ∈ Subgroup.centralizer (blockQ L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hmem : ⁅p, c⁆ ∈ ⁅blockQ L, X⁆ :=
      Subgroup.commutator_mem_commutator hp (Subgroup.mem_zpowers c)
    rw [hPXbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hcQ : c ∈ blockQ L := hL.2.1 (Subgroup.mem_inf.2 ⟨hcL, hcP⟩)
  exact eq_one_of_mem_blockQ_of_odd hcQ hodd

end CFSG.HardMathSupport.Curtis.Proving

end
