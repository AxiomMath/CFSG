module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPL
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIASix
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockTypes
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section Perfect

variable {Y : Type*} [Group Y] [Finite Y]

theorem false_of_surjective_perm_of_three {J : Subgroup Y} {n : ℕ} (hn : 5 ≤ n)
    (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V))
    (ψ : ↥J →* Equiv.Perm (Fin n)) (hψ : Function.Surjective ψ) : False := by
  have h5 : 5 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hA := coprime_card_of_surjective_of_perfect hJ ψ hψ (alternatingGroup (Fin n))
    (commutator_alternatingGroup_eq_self h5)
  have hAc := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hAc
  have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  rw [← hAc] at h3
  have h1 := Nat.Coprime.eq_one_of_dvd hA (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)
  omega

theorem not_nine_dvd_card_of_quotient_perm {J : Subgroup Y} {n : ℕ}
    (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V))
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n)) : ¬ 9 ∣ Nat.card J := by
  have hn : n ≤ 4 := by
    by_contra h
    exact false_of_surjective_perm_of_three (by omega) hJ
      (e.toMonoidHom.comp (QuotientGroup.mk' _))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥J),
    Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
  rw [hk]
  intro h9
  have h9' : 9 ∣ n.factorial :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right _ (by norm_num)) h9
  interval_cases n <;> revert h9' <;> decide

theorem false_of_quotient_sp_of_three {J : Subgroup Y} {k : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hk : 3 ≤ k) (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q)
    (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V))
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  have hQ := kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds k d hk hd
  have h := coprime_card_of_surjective_of_perfect hJ (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ⊤ (by rw [← commutator_def, hQ])
  rw [Subgroup.card_top] at h
  obtain ⟨q, hq2, hdq⟩ := hd
  have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
  have hqp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp
    (hpe ▸ dvd_pow_self q.p q.exponent_pos.ne')
  have hqe : q.exponent = 1 := by
    rw [hqp] at hpe
    exact Nat.pow_right_injective le_rfl (by simpa using hpe)
  have hN : Nat.card (CatGroup d) = CFSG.Open.ordBC k (2 ^ q.exponent) :=
    card_catGroup_B_even hk hqp hdq
  have h3 : 3 ∣ CFSG.Open.ordBC k 2 := by
    unfold CFSG.Open.ordBC
    rw [show Nat.gcd 2 (2 - 1) = 1 by norm_num, Nat.div_one]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun i => 2 ^ (2 * i) - 1)
      (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)) _
  change Nat.Coprime 3 (Nat.card (CatGroup d)) at h
  rw [hN, hqe, pow_one] at h
  have h1 := Nat.Coprime.eq_one_of_dvd h h3
  omega

theorem card_le_of_not_pow_dvd {P U : Subgroup Y} (hU : U ≤ P) (hU3 : IsPGroup 3 U) {j : ℕ}
    (h : ¬ 3 ^ (j + 1) ∣ Nat.card P) : Nat.card U ≤ 3 ^ j := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU3
  have hdvd : 3 ^ m ∣ Nat.card P := hm ▸ Subgroup.card_dvd_of_le hU
  rw [hm]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  by_contra hlt
  exact h ((Nat.pow_dvd_pow 3 (by omega)).trans hdvd)

omit [Finite Y] in
theorem pow_three_eq_one_of_not_nine_dvd {P : Subgroup Y} (h : ¬ 9 ∣ Nat.card P) {x : Y}
    (hx : x ∈ P) (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) : x ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := hx3
  obtain ⟨i, -, hix⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
  have hP : orderOf x ∣ Nat.card P := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hi1 : i ≤ 1 := by
    by_contra h2
    exact h ((Nat.pow_dvd_pow 3 (by omega : 2 ≤ i)).trans (hix ▸ hP))
  refine orderOf_dvd_iff_pow_eq_one.mp ?_
  rw [hix]
  simpa using Nat.pow_dvd_pow 3 hi1

end Perfect

theorem pow_three_eq_one_of_mulEquiv_alt_seven {Y : Type*} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 7)) {x : Y} (hx : ∃ k : ℕ, x ^ 3 ^ k = 1) : x ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := hx
  have hσ : orderOf ((e x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = orderOf x := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have hdvd : orderOf ((e x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ∣ 3 ^ k :=
    hσ ▸ orderOf_dvd_of_pow_eq_one hk
  have h3 : orderOf ((e x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ∣ 3 := by
    rw [← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd]
    intro c hc
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      ((Equiv.Perm.dvd_of_mem_cycleType hc).trans hdvd)
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hc
    have h7 : 3 ^ i ≤ 7 := (Equiv.Perm.le_card_support_of_mem_cycleType hc).trans
      ((Finset.card_le_univ _).trans (by simp))
    rcases i with _ | _ | i
    · simp at h2
    · simp
    · have : 9 ≤ 3 ^ (i + 2) := by
        rw [pow_add]
        exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by norm_num))
      omega
  rw [hσ] at h3
  exact orderOf_dvd_iff_pow_eq_one.mp h3

section Bar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_blockPL_dvd_of_nineThreeFour {M S L : Subgroup G} (h4 : NineThreeFour M S L) :
    Nat.card (blockPL M S L) ∣ 72 := by
  obtain ⟨-, hZ, -, -, ⟨e⟩⟩ := h4
  set Lb := barM M L
  set P := blockPL M S L
  have hPL : P ≤ Lb := barM_mono inf_le_right
  set P' : Subgroup ↥Lb := P.subgroupOf Lb
  set φ : ↥P' →* ↥Lb ⧸ Subgroup.center ↥Lb :=
    (QuotientGroup.mk' (Subgroup.center ↥Lb)).comp P'.subtype
  have hrange : φ.range = P'.map (QuotientGroup.mk' (Subgroup.center ↥Lb)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card P' = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : Nat.card φ.ker ∣ 3 := by
    rw [← hZ]
    have hle : φ.ker.map P'.subtype ≤ Subgroup.center ↥Lb := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : QuotientGroup.mk' (Subgroup.center ↥Lb) (x : ↥Lb) = 1 := hx
      exact (QuotientGroup.eq_one_iff _).mp h1
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective P'.subtype_injective] at this
  have hS4 : Nat.card φ.range = 24 := by
    rw [hrange, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, hcard, hS4]
  exact Nat.mul_dvd_mul_right hker 24

theorem not_nine_dvd_card_blockPL_of_rest (hTPL : CitedBlockTransvectionPL) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h : NineThreeThree M S L ∨ NineThreeSix M S L ∨ NineThreeSeven M S L ∨
      NineThreeEight M S L)
    (hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W)) :
    ¬ 9 ∣ Nat.card (blockPL M S L) := by
  rcases h with h3 | ⟨-, n, -, ⟨e⟩⟩ | ⟨-, n, -, ⟨e⟩⟩ | ⟨-, N, r, ⟨m, hm⟩, hr, h0, h2, h4, -, φ, -⟩
  · rcases hTPL G M S L hK hA hL hX hS h3 with ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
    · exact (false_of_quotient_sp_of_three hk hd hperf e).elim
    · exact not_nine_dvd_card_of_quotient_perm hperf e
  · exact not_nine_dvd_card_of_quotient_perm hperf e
  · exact not_nine_dvd_card_of_quotient_perm hperf e
  · exfalso
    refine false_of_surjective_perm_of_three (n := N - 2 * r) (by omega) hperf
      ((MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (QuotientGroup.mk' _))) ?_
    exact Prod.snd_surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _))

theorem pow_three_eq_one_of_blockPL_rest (hTPL : CitedBlockTransvectionPL) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h : NineThreeThree M S L ∨ NineThreeFour M S L ∨ NineThreeFive M L ∨ NineThreeSix M S L ∨
      NineThreeSeven M S L ∨ NineThreeEight M S L)
    (hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W))
    {x : ↥M ⧸ CFSG.pCore 2 ↥M} (hx : x ∈ blockPL M S L) (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) :
    x ^ 3 = 1 := by
  have hPL : blockPL M S L ≤ barM M L := barM_mono inf_le_right
  rcases h with h3 | ⟨-, hZ, he, -⟩ | ⟨-, ⟨e⟩, -⟩ | h6 | h7 | h8
  · exact pow_three_eq_one_of_not_nine_dvd
      (not_nine_dvd_card_blockPL_of_rest hTPL hK hA hL hX hS (Or.inl h3) hperf) hx hx3
  · exact (kFactBlockThreeASix_holds G M L hL.toIsTwoPrimeComponent hZ he).2.1 x (hPL hx) hx3
  · have h1 := pow_three_eq_one_of_mulEquiv_alt_seven e (x := ⟨x, hPL hx⟩)
      (by obtain ⟨k, hk⟩ := hx3; exact ⟨k, Subtype.ext (by simpa using hk)⟩)
    simpa using congrArg Subtype.val h1
  · exact pow_three_eq_one_of_not_nine_dvd
      (not_nine_dvd_card_blockPL_of_rest hTPL hK hA hL hX hS (Or.inr (Or.inl h6)) hperf) hx hx3
  · exact pow_three_eq_one_of_not_nine_dvd (not_nine_dvd_card_blockPL_of_rest hTPL hK hA hL hX hS
      (Or.inr (Or.inr (Or.inl h7))) hperf) hx hx3
  · exact pow_three_eq_one_of_not_nine_dvd (not_nine_dvd_card_blockPL_of_rest hTPL hK hA hL hX hS
      (Or.inr (Or.inr (Or.inr h8))) hperf) hx hx3

theorem card_le_nine_of_blockPL_rest (hTPL : CitedBlockTransvectionPL)
    (hA7PL : CitedBlockAltSevenPL) {M S L : Subgroup G} (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h : NineThreeThree M S L ∨ NineThreeFour M S L ∨ NineThreeFive M L ∨ NineThreeSix M S L ∨
      NineThreeSeven M S L ∨ NineThreeEight M S L)
    (hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W))
    {U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hU : U ≤ blockPL M S L) (hU3 : IsPGroup 3 U) :
    Nat.card U ≤ 3 ^ 2 := by
  have h72 : ¬ 3 ^ (2 + 1) ∣ (72 : ℕ) := by norm_num
  have hrest : NineThreeThree M S L ∨ NineThreeSix M S L ∨ NineThreeSeven M S L ∨
      NineThreeEight M S L → Nat.card U ≤ 3 ^ 2 := fun h' =>
    (card_le_of_not_pow_dvd hU hU3 (j := 1)
      (not_nine_dvd_card_blockPL_of_rest hTPL hK hA hL hX hS h' hperf)).trans (by norm_num)
  rcases h with h3 | h4 | h5 | h6 | h7 | h8
  · exact hrest (Or.inl h3)
  · exact card_le_of_not_pow_dvd hU hU3 fun hd =>
      h72 (hd.trans (card_blockPL_dvd_of_nineThreeFour h4))
  · exact card_le_of_not_pow_dvd hU hU3 fun hd => h72 (hd.trans (hA7PL G M S L hK hA hL hX hS h5))
  · exact hrest (Or.inr (Or.inl h6))
  · exact hrest (Or.inr (Or.inr (Or.inl h7)))
  · exact hrest (Or.inr (Or.inr (Or.inr h8)))

end Bar

end CFSG.AGLEmbedding
