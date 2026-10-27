module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeModelDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeClassical
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeArith
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeAbelian
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.AbelianTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

section Transfer

theorem I294Cross.transfer_rankThree {L M : Type} [Group L] [Finite L] [Group M] [Finite M]
    (e : L ≃* M)
    (h : ∀ y : M, orderOf y = 3 → 3 ≤ CFSG.Open.pRank 3 (centralizer ({y} : Set M))) :
    ∀ x : L, orderOf x = 3 → 3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set L)) := by
  intro x hx
  have h1 := h (e x) (by rw [MulEquiv.orderOf_eq]; exact hx)
  have h2 : CFSG.Open.pRank 3 (centralizer ({e x} : Set M)) ≤
      CFSG.Open.pRank 3 ((centralizer ({e x} : Set M)).map e.symm.toMonoidHom) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) e.symm.toMonoidHom e.symm.injective _
  have h3 : (centralizer ({e x} : Set M)).map e.symm.toMonoidHom ≤ centralizer ({x} : Set L) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y * e x = e x * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (by simpa using congrArg e.symm hy')
  exact h1.trans (h2.trans (CFSG.SectionRank.pRank_mono (by norm_num) h3))

end Transfer

section Arith5

open CrossArith

theorem I294Cross.three_pow_five_dvd_ordA {m q : ℕ} (hq : ¬ 3 ∣ q)
    (hLU : ¬ (3 ∣ m + 1 ∧ 3 ∣ q - 1)) (hm : 1 ≤ m)
    (h : (q % 3 = 1 ∧ 5 ≤ m + 1) ∨ (q % 3 = 2 ∧ 8 ≤ m + 1)) : 3 ^ 5 ∣ ordA m q := by
  have hg : ¬ 3 ∣ Nat.gcd (m + 1) (q - 1) := fun h' =>
    hLU ⟨h'.trans (Nat.gcd_dvd_left _ _), h'.trans (Nat.gcd_dvd_right _ _)⟩
  refine (dvd_ordA_iff hm (coprime_three_pow hq) (coprime_three_pow hg)).2 ?_
  rcases h with ⟨h1, h5⟩ | ⟨-, h8⟩
  · exact three_pow_five_dvd_prod_one h1 h5
  · exact three_pow_five_dvd_prod_two hq h8

theorem I294Cross.three_pow_five_dvd_ordTwistedA {m q : ℕ} (hq : ¬ 3 ∣ q)
    (hLU : ¬ (3 ∣ m + 1 ∧ 3 ∣ q + 1)) (hm : 1 ≤ m)
    (h : (q % 3 = 2 ∧ 5 ≤ m + 1) ∨ (q % 3 = 1 ∧ 8 ≤ m + 1)) : 3 ^ 5 ∣ ordTwistedA m q := by
  have hg : ¬ 3 ∣ Nat.gcd (m + 1) (q + 1) := fun h' =>
    hLU ⟨h'.trans (Nat.gcd_dvd_left _ _), h'.trans (Nat.gcd_dvd_right _ _)⟩
  refine (dvd_ordTwistedA_iff hm (by omega) (coprime_three_pow hq) (coprime_three_pow hg)).2 ?_
  rcases h with ⟨h2, h5⟩ | ⟨h1, h8⟩
  · exact three_pow_five_dvd_prodU_two h2 h5
  · exact three_pow_five_dvd_prodU_one h1 h8

theorem I294Cross.three_pow_five_dvd_ordBC {n q : ℕ} (hq : ¬ 3 ∣ q) (hn : 4 ≤ n) :
    3 ^ 5 ∣ ordBC n q := by
  have hdg : ¬ 3 ∣ Nat.gcd 2 (q - 1) := fun h' => by
    have := h'.trans (Nat.gcd_dvd_left _ _); omega
  exact (dvd_ordBC_iff (by omega) (coprime_three_pow hq) (coprime_three_pow hdg)).2
    (three_pow_five_dvd_prod_even hq hn)

theorem I294Cross.three_pow_five_dvd_ordTwistedD {n q : ℕ} (hq : ¬ 3 ∣ q) (hn : 5 ≤ n) :
    3 ^ 5 ∣ ordTwistedD n q := by
  have hdg : ¬ 3 ∣ Nat.gcd 4 (q ^ n + 1) := fun h' => by
    have := h'.trans (Nat.gcd_dvd_left _ _); omega
  exact (dvd_ordTwistedD_iff (coprime_three_pow hq) (coprime_three_pow hdg)).2
    (Dvd.dvd.mul_left (three_pow_five_dvd_prod_even hq (k := n - 1) (by omega)) _)

end Arith5

theorem I294Cross.rankThree_of_classical_model
    (hL4 : I294CrossModelPSL4) (hL67 : I294CrossModelPSL67) (hU4 : I294CrossModelPSU4)
    (hU67 : I294CrossModelPSU67) (hSp : I294CrossModelPSp6) (hO7 : I294CrossModelPOmega7)
    (hOm : I294CrossModelPOmegaMinus4)
    {L : Type} [Group L] [Finite L] {t : StatedLieTag} {n p f : ℕ}
    (hm : StatedClassicalModel L t n p f) (hp3 : p ≠ 3) (hLU : ¬ IsLinearOrUnitaryAt 3 L)
    (hS : ∃ S : Sylow 3 L, ¬ IsMulCommutative (S : Subgroup L))
    (h243 : ¬ 3 ^ 5 ∣ Nat.card L) :
    ∀ x : L, orderOf x = 3 → 3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set L)) := by
  obtain ⟨hdiv27, E, hE, hEc⟩ := I294Cross.nonabelian_sylow_three hS
  have hcard := I294Cross.card_of_scm hm
  have hab : ¬ (∀ S : Sylow 3 L, IsMulCommutative (S : Subgroup L)) := by
    intro h
    obtain ⟨S, hS'⟩ := hS
    exact hS' (h S)
  obtain ⟨hadm, hrest⟩ := id hm
  obtain ⟨hp, hf, hadm⟩ := hadm
  have hq3 : ¬ 3 ∣ p ^ f := I294Cross.not_three_dvd_pow hp hp3
  cases t with
  | PSL =>
    have hn : 2 ≤ n := hadm.1
    have hc := hcard.1 rfl
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have hK3 : ¬ 3 ∣ Nat.card K := by rw [hK]; exact hq3
    have hLU' : ¬ (3 ∣ n - 1 + 1 ∧ 3 ∣ p ^ f - 1) := fun h => hLU (Or.inl
      ⟨n, K, inferInstance, inferInstance, by rw [Nat.sub_add_cancel (by omega)] at h; exact h.1,
        by rw [hK]; exact h.2, ⟨e⟩⟩)
    by_cases hn2 : n = 2
    · subst hn2
      exact (I294Cross.false_elemAbelian_psl_two hm hp3 hdiv27 hE hEc).elim
    by_cases hn3 : n = 3
    · subst hn3
      exact (I294Cross.false_elemAbelian_psl_three hm hp3 hLU hE hEc).elim
    rcases (by omega : p ^ f % 3 = 1 ∨ p ^ f % 3 = 2) with h1 | h2
    · by_cases hn4 : n = 4
      · subst hn4
        exact I294Cross.transfer_rankThree e (hL4 K (by rw [hK]; omega))
      · exfalso
        have h5 := I294Cross.three_pow_five_dvd_ordA hq3 hLU' (by omega) (Or.inl ⟨h1, by omega⟩)
        exact h243 (hc ▸ h5)
    · have hK2 : Nat.card K % 3 = 2 := by rw [hK]; exact h2
      have hK1 : ¬ 3 ∣ Nat.card K - 1 := by omega
      by_cases hn5 : n ≤ 5
      · exfalso
        exact hab (WeakClosureHeis.sylow_comm_of_surjective e.symm.toMonoidHom e.symm.surjective
          (I294Cross.sylow_comm_psl hn5 hK3 hK2))
      · by_cases hn7 : n ≤ 7
        · exact I294Cross.transfer_rankThree e fun y hy => hL67 K hK3 hK1 n (by omega) y hy
        · exfalso
          have h5 := I294Cross.three_pow_five_dvd_ordA hq3 hLU' (by omega)
            (Or.inr ⟨h2, by omega⟩)
          exact h243 (hc ▸ h5)
  | PSU =>
    have hn : 3 ≤ n := hadm.1
    have hc := hcard.2.1 rfl
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have hLU' : ¬ (3 ∣ n - 1 + 1 ∧ 3 ∣ p ^ f + 1) := fun h => hLU (Or.inr
      ⟨n, p ^ f, K, inferInstance, inferInstance, hK,
        by rw [Nat.sub_add_cancel (by omega)] at h; exact h.1, h.2, ⟨e⟩⟩)
    rcases (by omega : p ^ f % 3 = 1 ∨ p ^ f % 3 = 2) with h1 | h2
    · by_cases hn3 : n = 3
      · subst hn3
        exact (I294Cross.false_elemAbelian_psu_three hm hp3 hLU hE hEc).elim
      by_cases hn5 : n ≤ 5
      · exfalso
        exact hab (WeakClosureHeis.sylow_comm_of_surjective e.symm.toMonoidHom e.symm.surjective
          (I294Cross.sylow_comm_psu hK hq3 h1 (by omega) hn5))
      · by_cases hn7 : n ≤ 7
        · exact I294Cross.transfer_rankThree e fun y hy =>
            hU67 (p ^ f) K hK hq3 (by omega) n (by omega) y hy
        · exfalso
          have h5 := I294Cross.three_pow_five_dvd_ordTwistedA hq3 hLU' (by omega)
            (Or.inr ⟨h1, by omega⟩)
          exact h243 (hc ▸ h5)
    · by_cases hn3 : n = 3
      · subst hn3
        exact (hLU' ⟨by norm_num, by omega⟩).elim
      by_cases hn4 : n = 4
      · subst hn4
        exact I294Cross.transfer_rankThree e (hU4 (p ^ f) K hK (by omega))
      · exfalso
        have h5 := I294Cross.three_pow_five_dvd_ordTwistedA hq3 hLU' (by omega)
          (Or.inl ⟨h2, by omega⟩)
        exact h243 (hc ▸ h5)
  | PSp =>
    have hn : 2 ≤ n := hadm.1
    have hc := hcard.2.2.1 rfl
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have hK3 : ¬ 3 ∣ Nat.card K := by rw [hK]; exact hq3
    by_cases hn2 : n = 2
    · subst hn2
      exfalso
      exact hab (WeakClosureHeis.sylow_comm_of_surjective e.symm.toMonoidHom e.symm.surjective
        (I294Cross.sylow_comm_psp_two hK3))
    by_cases hn3 : n = 3
    · subst hn3
      exact I294Cross.transfer_rankThree e (hSp K hK3)
    · exfalso
      exact h243 (by rw [hc]; exact I294Cross.three_pow_five_dvd_ordBC hq3 (by omega))
  | POmegaOdd =>
    have hn : 3 ≤ n := hadm.1
    have hp2 : p ≠ 2 := hadm.2
    have hc := hcard.2.2.2.1 rfl
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have hK3 : ¬ 3 ∣ Nat.card K := by rw [hK]; exact hq3
    by_cases hn3 : n = 3
    · subst hn3
      refine I294Cross.transfer_rankThree e (hO7 K hK3 ?_)
      rw [hK]
      exact (hp.odd_of_ne_two hp2).pow
    · exfalso
      exact h243 (by rw [hc]; exact I294Cross.three_pow_five_dvd_ordBC hq3 (by omega))
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm
    have hc := hcard.2.2.2.2.1 rfl
    exfalso
    exact h243 (by rw [hc]; exact I294Cross.three_pow_five_dvd_ordD hq3 hn)
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm
    have hc := hcard.2.2.2.2.2 rfl
    obtain ⟨K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hrest
    have hK3 : ¬ 3 ∣ Nat.card K := by rw [hK]; exact hq3
    by_cases hn4 : n = 4
    · subst hn4
      exact I294Cross.transfer_rankThree e (hOm K hK3 b c hbc)
    · exfalso
      exact h243 (by rw [hc]; exact I294Cross.three_pow_five_dvd_ordTwistedD hq3 (by omega))
  | G2 => exact hrest.elim
  | F4 => exact hrest.elim
  | E6 => exact hrest.elim
  | E7 => exact hrest.elim
  | E8 => exact hrest.elim
  | twistedE6 => exact hrest.elim
  | trialityD4 => exact hrest.elim
  | twistedB2 => exact hrest.elim
  | twistedG2 => exact hrest.elim
  | twistedF4 => exact hrest.elim
  | Tits => exact hrest.elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
