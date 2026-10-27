module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
import CFSG.LocalAnalysis.AGLEmbedding.AltCaseThreeK
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux

public section

namespace CFSG.AGLEmbedding


open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

theorem card_eq_and_not_comm_of_center_ne_bot {K : Type} [Group K] [Finite K] {n p : ℕ}
    (hK : Open.IsQuasisimple K) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) [Fact p.Prime] (hp2 : p ≠ 2)
    (hZp : IsPGroup p (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥) (T : Sylow p K) :
    Nat.card (T : Subgroup K) = p ^ 3 ∧
      ∃ a ∈ (T : Subgroup K), ∃ b ∈ (T : Subgroup K), a * b ≠ b * a := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  have hp : p.Prime := Fact.out
  have hn67 := eq_six_or_seven_of_center hn e hp hp2 hZ hZp
  have hZ6 : Nat.card (Subgroup.center K) ∣ 6 := by
    have h := card_center_dvd_card_hopfMultiplier e
    rwa [(Alternating.Multipliers.schurAlternatingMultiplierInput n hn).2, ite_eq_left hn67] at h
  have hpZ : p ∣ Nat.card (Subgroup.center K) :=
    hZp.card_eq_or_dvd.resolve_left fun h => hZ (Subgroup.card_eq_one.mp h)
  have hp3 : p = 3 := by
    rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 3 from hpZ.trans hZ6) with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  subst hp3
  have hZ3 : Nat.card (Subgroup.center K) = 3 := by
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rw [hk] at hZ6 hpZ ⊢
    have hk1 : k ≤ 1 := by
      by_contra h
      have h9 := (pow_dvd_pow 3 (show 2 ≤ k by omega)).trans hZ6
      norm_num at h9
    have hk0 : k ≠ 0 := by
      rintro rfl
      norm_num at hpZ
    obtain rfl : k = 1 := by omega
    rfl
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hKcard : Nat.card K = n.factorial / 2 * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hZ3,
      Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have hKc : Nat.card K = 1080 ∨ Nat.card K = 7560 := by
    rcases hn67 with rfl | rfl
    · exact Or.inl (by rw [hKcard]; norm_num [Nat.factorial])
    · exact Or.inr (by rw [hKcard]; norm_num [Nat.factorial])
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm⟩ := T.isPGroup'.exists_card_eq
    have hidx := T.not_dvd_index
    have hmul := (T : Subgroup K).card_mul_index
    rw [hm] at hmul
    have hle : 3 ^ m ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos (Dvd.intro _ hmul)
    have hm9 : m < 9 := by
      by_contra h
      have h1 : 19683 ≤ 3 ^ m := calc
        19683 = 3 ^ 9 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      rcases hKc with hK | hK <;> omega
    have hm3 : m = 3 := by
      rcases hKc with hK | hK <;> rw [hK] at hmul <;> interval_cases m <;> norm_num at hmul <;>
        omega
    rw [hm, hm3]
  · obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
    obtain ⟨k, hzk⟩ := hZp ⟨z, hz⟩
    have hzT := center_le_commutator_of_isPerfect T hz ⟨k, congrArg Subtype.val hzk⟩
    by_contra hcon
    push Not at hcon
    have hbot : ⁅(T : Subgroup K), (T : Subgroup K)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcon y hy x hx
    rw [hbot, Subgroup.mem_bot] at hzT
    exact hz1 (Subtype.ext hzT)

theorem kFactP1ThreeAlt : KFactP1ThreeAlt := by
  intro p _ Y _ _ Rb Y₀ h _ K hK huniq hnc hcent m hm ⟨e⟩
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ne_two
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set Y), orderOf c = p → c ∈ K :=
    fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rb hKn
      (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp
  have hCp := isPGroup_centralizer_of_forall_mem hp hp2 h.core_eq_bot hKn hmem
  have hZp := isPGroup_center_of_isComponentOf hp h.core_eq_bot hK
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have : Finite (MulAut K) := MulEquiv.finite_left
  have hOutQ : ¬ p ∣ Nat.card (Outer (K ⧸ Subgroup.center K)) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact not_dvd_card_outer_alternatingGroup m hm p hp hp2
  have hOut := not_dvd_card_outer_of_quotient hOutQ
  have hRK : (Rb : Subgroup Y) ≤ K ⊔ Subgroup.centralizer (K : Set Y) := by
    intro x hx
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp Rb.isPGroup') ⟨x, hx⟩
    refine mem_sup_centralizer_of_pow hp hOut (n := n) ?_
    have h1 := pow_orderOf_eq_one (⟨x, hx⟩ : (Rb : Subgroup Y))
    rw [hn] at h1
    exact congrArg Subtype.val h1
  have hnot := not_le_of_le_sup_centralizer h hnc hCp hRK
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have h3 := h.three_le_pRank
  by_cases hZ : Subgroup.center K = ⊥
  · have e' : K ≃* alternatingGroup (Fin m) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
    rcases lt_trichotomy m (3 * p) with hlt | heq | hgt
    · have hC := centralizer_eq_bot_of_forall_mem hp hp2 h.core_eq_bot hKn hmem hZ
      have h2 := pRank_le_two_of_centralizer_eq_bot T₀ hT₀ hC hRK
        (pRank_le_two_of_lt hp e' hlt _)
      omega
    · exact heq
    · exact (hnot (le_of_weakCore_eq_top h T₀ hT₀
        (weakCore_eq_top_of_three_mul_lt hp hp2 hgt e' T₀))).elim
  ·
    exfalso
    obtain ⟨hTcard, a, ha, b, hb, hab⟩ :=
      card_eq_and_not_comm_of_center_ne_bot hK.2.2 hm e hp2 hZp hZ T₀
    have hCR : Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y) :=
      IsPGroup.le_sylow_of_normal hCp Rb
    have hCcyc := isCyclic_centralizer_of_forall_mem hp hp2 h.core_eq_bot hKn hmem
      (h.isCyclic_map_center hK hKn)
    have hTcard' : Nat.card ((Rb : Subgroup Y) ⊓ K : Subgroup Y) = p ^ 3 := by
      rw [← hT₀, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
    have hna : ∃ a ∈ ((Rb : Subgroup Y) ⊓ K), ∃ b ∈ ((Rb : Subgroup Y) ⊓ K), a * b ≠ b * a :=
      ⟨a, hT₀ ▸ Subgroup.mem_map_of_mem K.subtype ha, b,
        hT₀ ▸ Subgroup.mem_map_of_mem K.subtype hb, fun h' => hab (Subtype.ext h')⟩
    have hCT : Subgroup.centralizer (K : Set Y) ≤
        Subgroup.centralizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) :=
      Subgroup.centralizer_le fun _ hy => hy.2
    have hΩ : ∀ c ∈ Subgroup.centralizer (K : Set Y), c ^ p = 1 →
        c ∈ ((Rb : Subgroup Y) ⊓ K) := by
      intro c hc hcp
      by_cases hc1 : c = 1
      · rw [hc1]
        exact Subgroup.one_mem _
      · exact ⟨hCR hc, hmem c hc (orderOf_eq_prime hcp hc1)⟩
    have h2 := pRank_sup_le_two hTcard' hna hCcyc hCT hΩ
    have h3' := h3.trans
      (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf_sup_centralizer hCR hRK))
    omega

end CFSG.AGLEmbedding
