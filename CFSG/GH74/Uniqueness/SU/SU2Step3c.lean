module

public import CFSG.GH74.Uniqueness.SU.SU2Step3b
public import CFSG.GH74.Uniqueness.SU.SU2Restrict
public import CFSG.GH74.Uniqueness.SU.SU2Sylow
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

variable {X : Type} [Group X] {V : Type} [Group V] [MulDistribMulAction X V]

namespace GOPair

variable {Y : Subgroup X}

theorem odd_ncard_orbit [Finite X] [Finite V] (hGO : GOPair V Y)
    (htr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ x : X, x • v = w) {v : V} (hv : v ≠ 1) :
    Odd (MulAction.orbit X v).ncard := by
  have horb : MulAction.orbit X v = {u : V | u ≠ 1} := by
    ext u
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩ h
      exact hv ((smul_eq_one_iff' x v).1 h)
    · intro hu
      exact htr v u hv hu
  have h1 : {u : V | u ≠ 1} = (Set.univ : Set V) \ {1} := by ext; simp
  have hn1 : 1 ≤ shapeN V := by
    have : Nontrivial V := ⟨⟨v, 1, hv⟩⟩
    have h2 : 1 < Nat.card V := Finite.one_lt_card
    rw [hGO.card_V] at h2
    by_contra h0
    have : shapeN V = 0 := by omega
    rw [this] at h2
    simp at h2
  rw [horb, h1, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ, hGO.card_V]
  have h2 : 2 ∣ 2 ^ shapeN V := dvd_pow_self 2 (by omega)
  have hpos : 0 < 2 ^ shapeN V := by positivity
  rw [Nat.odd_iff]
  omega

theorem eq_top_of_invariant {K : Subgroup X}
    (hK : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ k ∈ K, k • v = w) {W : Subgroup V}
    (hW : ∀ k ∈ K, k • W = W) (hW1 : W ≠ ⊥) : W = ⊤ := by
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_ne_bot hW1
  rw [eq_top_iff]
  intro w _
  by_cases hw1 : w = 1
  · rw [hw1]; exact W.one_mem
  obtain ⟨k, hk, hkw⟩ := hK u w hu1 hw1
  have h : k • u ∈ k • W := Subgroup.smul_mem_pointwise_smul u k W hu
  rw [hW k hk, hkw] at h
  exact h

theorem step3 [Finite X] [Finite V] (hGO : GOPair V Y) {W₁ W₂ : Subgroup V}
    (hW₁ : W₁ ∈ omegaA V Y) (hW₂ : W₂ ∈ omegaB V Y) :
    shapeK V Y = 1 ∧ shapeN V = 3 ∧ Nat.card X = 21 ∧ ∃ a b : X, a * b ≠ b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ x : X, x • v = w :=
    fun v w hv hw => hGO.transitive_on_V hW₁ hW₂ hv hw
  have hodd₀ : Odd (MulAction.stabilizer X (fixSub V Y)).index := by
    rw [MulAction.index_stabilizer]; exact hGO.odd_ncard_omega hW₁ hW₂
  obtain ⟨S, hSX₀⟩ := exists_sylow_le_of_odd_index hodd₀
  have hS2 : IsPGroup 2 (S : Subgroup X) := S.isPGroup'
  have hfaithS := hGO.faithful_of_isPGroup hW₁ hW₂ hSX₀ hS2
  have hcyc : IsCyclic S := (sem_consequences hGO).2 (S : Subgroup X) hSX₀ hS2 hfaithS
  obtain ⟨-, -, -, ⟨hKn, hKodd, hKindex, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hcyc
  set K : Subgroup X := CFSG.pPrimeCore 2 X with hKdef
  have : K.Normal := hKn
  obtain ⟨a, ha⟩ := hS2.exists_card_eq
  have hKpow : K.index = 2 ^ a := by rw [hKindex]; exact ha
  have hYK : Y ≤ K := le_of_odd_card_of_index_pow hGO.odd_card hKpow
  have hGO' := hGO.restrict hYK
  have hconcl := onan_odd hGO' hKodd
  have hKtr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ k ∈ K, k • v = w := by
    intro v w hv hw
    obtain ⟨x, hx⟩ := htr v w hv hw
    obtain ⟨k, hk, hkx⟩ := exists_mem_of_normal_index_pow hKpow v (hGO.odd_ncard_orbit htr hv) x
    exact ⟨k, hk, hkx.symm.trans hx⟩
  have hV₀top : fixSub V Y = ⊤ → False := by
    intro htop
    apply hGO.commSub_ne_bot
    have h : commSub V Y ⊓ fixSub V Y = ⊥ := hGO.commSub_inf_fixSub'
    rwa [htop, inf_top_eq] at h
  have hV₁top : commSub V Y = ⊤ → False := by
    intro htop
    apply hGO.fixSub_ne_bot
    have h : commSub V Y ⊓ fixSub V Y = ⊥ := hGO.commSub_inf_fixSub'
    rwa [htop, top_inf_eq] at h
  rcases hconcl with h | h | h | h
  · exfalso
    obtain ⟨-, hinv⟩ := h
    rw [fixSub_subgroupOf hYK] at hinv
    exact hV₀top (eq_top_of_invariant hKtr (fun k hk => hinv ⟨k, hk⟩) hGO.fixSub_ne_bot)
  · exfalso
    obtain ⟨hΩ, -⟩ := h
    unfold omega at hΩ
    rw [fixSub_subgroupOf hYK, commSub_subgroupOf hYK] at hΩ
    obtain ⟨v₀, hv₀, hv₀1⟩ := exists_ne_one_of_ne_bot hGO.fixSub_ne_bot
    have hcover : ((⊤ : Subgroup V) : Set V) ⊆ (fixSub V Y : Set V) ∪ (commSub V Y : Set V) := by
      intro v _
      by_cases hv1 : v = 1
      · left; rw [hv1]; exact (fixSub V Y).one_mem
      obtain ⟨k, hk, hkv⟩ := hKtr v₀ v hv₀1 hv1
      have hmem : k • fixSub V Y ∈ ({fixSub V Y, commSub V Y} : Set (Subgroup V)) := by
        rw [← hΩ]
        exact ⟨⟨k, hk⟩, rfl⟩
      have hvk : v ∈ k • fixSub V Y := hkv ▸ Subgroup.smul_mem_pointwise_smul v₀ k _ hv₀
      rcases hmem with h' | h'
      · left; rw [h'] at hvk; exact hvk
      · right; rw [h'] at hvk; exact hvk
    rcases le_or_le_of_subset_union hcover with h' | h'
    · exact hV₀top (top_le_iff.1 h')
    · exact hV₁top (top_le_iff.1 h')
  · exfalso
    obtain ⟨-, -, hinv⟩ := h
    rw [commSub_subgroupOf hYK] at hinv
    exact hV₁top (eq_top_of_invariant hKtr (fun k hk => hinv ⟨k, hk⟩) hGO.commSub_ne_bot)
  · obtain ⟨hk1, hn3, hK21, a, b, hab⟩ := h
    have hk1' : shapeK V Y = 1 := by
      have : shapeK V (Y.subgroupOf K) = shapeK V Y := by
        unfold shapeK; rw [fixSub_subgroupOf hYK]
      rwa [this] at hk1
    refine ⟨hk1', hn3, ?_, ⟨a, b, fun h => hab (Subtype.ext h)⟩⟩
    obtain ⟨E, hEn, hE7⟩ := exists_normal_order_seven hK21
    have hVcard : Nat.card V = 8 := by rw [hGO.card_V, hn3]; norm_num
    have hEtr := transitive_of_normal_order_seven hGO.faithful htr hE7 hVcard
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hEcyc : IsCyclic E := isCyclic_of_prime_card hE7
    have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
      intro a ha b hb
      have := (IsCyclic.commGroup (α := E)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    have hle := sem_card_le (E := E) hGO.mul_comm' hGO.exp_two hGO.faithful hEc hEtr
      (by rw [hE7, hVcard]) (e := 3) (by rw [hVcard]; norm_num) (by norm_num)
    have hdvd : Nat.card K ∣ Nat.card X := Subgroup.card_subgroup_dvd_card K
    rw [hK21] at hdvd
    have hpos : 0 < Nat.card X := Nat.card_pos
    have h21 : (2 ^ 3 - 1) * 3 = 21 := by norm_num
    omega

theorem onan [Finite X] [Finite V] (hGO : GOPair V Y) : OnanConclusion V Y := by
  rcases hGO.step12 with h | ⟨⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩
  · exact h
  · exact Or.inr (Or.inr (Or.inr (hGO.step3 hW₁ hW₂)))

end GOPair

end CFSG.GH74.Uniqueness.SU.SU2
