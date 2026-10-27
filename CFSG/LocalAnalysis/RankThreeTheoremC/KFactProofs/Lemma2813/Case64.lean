module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.PsetStructure
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.OrderThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

section CT

variable {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]

theorem c64_card_add (E L P : AddSubgroup M) (hLE : L ≤ E) (hPE : P ≤ E)
    (hcover : ∀ w ∈ E, w ∈ L ∨ w ∈ P) (hinter : ∀ w ∈ L, w ∈ P → w = 0) :
    Nat.card E + 1 = Nat.card L + Nat.card P := by
  have h1 : (L : Set M) ∪ (P : Set M) = (E : Set M) := by
    ext w
    constructor
    · rintro (hw | hw)
      · exact hLE hw
      · exact hPE hw
    · intro hw
      exact hcover w hw
  have h2 : (L : Set M) ∩ (P : Set M) = {0} := by
    ext w
    constructor
    · rintro ⟨hw1, hw2⟩
      exact hinter w hw1 hw2
    · intro hw
      have hw0 : w = 0 := hw
      subst hw0
      exact ⟨L.zero_mem, P.zero_mem⟩
  have h3 := Set.ncard_union_add_ncard_inter (L : Set M) (P : Set M)
  rw [h1, h2, Set.ncard_singleton] at h3
  exact h3

theorem c64_Pset_act {w : M} {d : GL32} (hw : d • w = w) (z : V3) :
    act d z ∈ Pset M w ↔ z ∈ Pset M w := by
  have h := Pset_smul d w (act d z)
  rw [hw, act_inv_act] at h
  exact h

theorem ct_case_64 {p₀ : V3} {d : GL32} (h : CTHyp M p₀ d) (hn : Nat.card M = 64)
    (ha : Nat.card (fixSub M (Spt p₀)) = 16)
    (hb : ∀ p q : V3, p ≠ 0 → q ≠ 0 → p ≠ q → Nat.card (fixSub M (Spt p ⊔ Spt q)) = 4)
    (hN : Ncnt M 0 = 0) : CTConcl M p₀ d := by
  obtain ⟨p, q, hp, hq, hpq, hdpq, hdp, hdq, hfix⟩ := order3_exists_invariant_pair h.hd
  obtain ⟨hp₀p, hp₀q, hp₀pq⟩ := hfix p₀ h.hp₀ h.hdp
  have hLE : fixSub M (Spt p ⊔ Spt q) ≤ fixSub M (zpowers d) := by
    intro m hm
    rw [mem_fixSub_zpowers]
    exact hm d hdpq
  have hPE : fixSub M (Spt p₀ ⊔ zpowers d) ≤ fixSub M (zpowers d) :=
    fixSub_mono le_sup_right
  have hinter : ∀ m ∈ fixSub M (Spt p ⊔ Spt q), m ∈ fixSub M (Spt p₀ ⊔ zpowers d) → m = 0 := by
    intro m hmL hmP
    rw [fixSub_sup] at hmL hmP
    apply h.fixed
    intro g
    have htop : m ∈ fixSub M (Spt p ⊔ Spt q ⊔ Spt p₀) := by
      rw [fixSub_sup, fixSub_sup]
      exact ⟨hmL, hmP.1⟩
    rw [Spt_sup_three hp hq h.hp₀ hpq (Ne.symm hp₀p) (Ne.symm hp₀q) hp₀pq] at htop
    exact htop g (Subgroup.mem_top g)
  have hcover : ∀ w ∈ fixSub M (zpowers d),
      w ∈ fixSub M (Spt p ⊔ Spt q) ∨ w ∈ fixSub M (Spt p₀ ⊔ zpowers d) := by
    intro w hwE
    by_cases hw : w = 0
    · left
      rw [hw]
      exact zero_mem _
    · have hdw : d • w = w := mem_fixSub_zpowers.1 hwE
      have hne : (Pset M w).card ≠ 0 := by
        intro h0
        have hpos : 0 < Ncnt M 0 := by
          unfold Ncnt
          haveI : Nonempty {w : M // w ≠ 0 ∧ (Pset M w).card = 0} := ⟨⟨w, hw, h0⟩⟩
          exact Nat.card_pos
        omega
      rcases Pset_card_cases h.fixed hw with h0 | h1 | ⟨x, y, hx, hy, hxy, hxyP⟩
      · exact absurd h0 hne
      · right
        obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
        have hxP : x ∈ Pset M w := by
          rw [hx]
          exact Finset.mem_singleton_self x
        have hdxP : act d x ∈ Pset M w := (c64_Pset_act hdw x).2 hxP
        rw [hx, Finset.mem_singleton] at hdxP
        have hx0 : x ≠ 0 := ((mem_Pset).1 hxP).1
        have hxp₀ : x = p₀ := order3_fixed_unique h.hd hx0 h.hp₀ hdxP h.hdp
        rw [hxp₀] at hxP
        rw [fixSub_sup]
        exact ⟨((mem_Pset).1 hxP).2, hwE⟩
      · left
        have hxP : x ∈ Pset M w := by
          rw [hxyP]
          simp
        have hyP : y ∈ Pset M w := by
          rw [hxyP]
          simp
        have h1 : act d x ∈ ({x, y, x + y} : Finset V3) := by
          rw [← hxyP]
          exact (c64_Pset_act hdw x).2 hxP
        have h2 : act d y ∈ ({x, y, x + y} : Finset V3) := by
          rw [← hxyP]
          exact (c64_Pset_act hdw y).2 hyP
        have heq := order3_invariant_triple_unique h.hd hx hy hxy hp hq hpq h1 h2 hdp hdq
        have hpP : p ∈ Pset M w := by
          rw [hxyP, heq]
          simp
        have hqP : q ∈ Pset M w := by
          rw [hxyP, heq]
          simp
        rw [fixSub_sup]
        exact ⟨((mem_Pset).1 hpP).2, ((mem_Pset).1 hqP).2⟩
  have hsum := c64_card_add _ _ _ hLE hPE hcover hinter
  obtain ⟨i, hi⟩ := card_addSubgroup_pow_two h.two (fixSub M (zpowers d))
  obtain ⟨j, hj⟩ := card_addSubgroup_pow_two h.two (fixSub M (Spt p₀ ⊔ zpowers d))
  have hΛ := hb p q hp hq hpq
  have hj0 : j = 0 := by
    rw [hi, hj, hΛ] at hsum
    rcases i with _ | i
    · rw [pow_zero] at hsum
      omega
    · rcases j with _ | j
      · rfl
      · rw [pow_succ, pow_succ] at hsum
        omega
  have hPD1 : Nat.card (fixSub M (Spt p₀ ⊔ zpowers d)) = 1 := by
    rw [hj, hj0]
    rfl
  have hE4 : Nat.card (fixSub M (zpowers d)) = 4 := by omega
  have hPD0 : fixSub M (Spt p₀ ⊔ zpowers d) = ⊥ := AddSubgroup.eq_bot_of_card_eq _ hPD1
  have hcomm := commSub_card_mul h.two h.hd
  rw [hE4, hn] at hcomm
  exact ⟨by omega, by omega, fun _ => hPD0⟩

end CT

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
