module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossRankTwoRest
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeArith
import CFSG.Goldschmidt.Steps.G63Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueGroup
import CFSG.ClassicalInvolution.Orders.Classical
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResLinOuter
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResUniWeir
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TwistedA
import CFSG.Adapters.LinearCatalogStated
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
import CFSG.Monster.B.Fischer.Fi22Order
import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedProj StatedSL StatedSU)

theorem I294Cross.nonabelian_sylow_three {L : Type} [Group L] [Finite L]
    (hS : ∃ S : Sylow 3 L, ¬ IsMulCommutative (S : Subgroup L)) :
    3 ^ 3 ∣ Nat.card L ∧ ∃ E : Subgroup L, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  obtain ⟨S, hS⟩ := hS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSp : IsPGroup 3 (S : Subgroup L) := S.isPGroup'
  have hSp' : IsPGroup 3 ↥(S : Subgroup L) := hSp
  refine ⟨?_, ?_⟩
  · have h27 : 3 ^ 3 ≤ Nat.card (S : Subgroup L) :=
      WeakClosureHeis.pow_three_le_card_of_nonabelian hSp' hS
    obtain ⟨k, hk⟩ := hSp'.exists_card_eq
    have hdvd : Nat.card (S : Subgroup L) ∣ Nat.card L := Subgroup.card_subgroup_dvd_card _
    rw [hk] at h27 hdvd
    exact (pow_dvd_pow 3 ((Nat.pow_le_pow_iff_right (by norm_num)).1 h27)).trans hdvd
  · have hnc : ¬ IsCyclic (S : Subgroup L) := fun h => hS (IsCyclic.isMulCommutative)
    exact CFSG.Goldschmidt.G63.exists_isElemAbelian_card_sq Nat.prime_three (by norm_num) hSp hnc
      |>.imp fun E hE => ⟨hE.2.1, hE.2.2⟩

theorem I294Cross.card_of_scm {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) :
    (t = .PSL → Nat.card G = ordA (n - 1) (p ^ f)) ∧
    (t = .PSU → Nat.card G = ordTwistedA (n - 1) (p ^ f)) ∧
    (t = .PSp → Nat.card G = ordBC n (p ^ f)) ∧
    (t = .POmegaOdd → Nat.card G = ordBC n (p ^ f)) ∧
    (t = .POmegaPlus → Nat.card G = ordD n (p ^ f)) ∧
    (t = .POmegaMinus → Nat.card G = ordTwistedD n (p ^ f)) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨h1, h2, h3, h5, h6⟩ := CFSG.Timmesfeld.card_statedClassicalModel_two h
    refine ⟨h1, h2, h3, ?_, h5, h6⟩
    intro ht
    subst ht
    exact absurd rfl h.1.2.2.2
  · exact CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 h

theorem I294Cross.not_three_dvd_pow {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ¬ 3 ∣ p ^ f := fun h =>
  hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm

section Arithmetic

open CrossArith

private theorem not_three_dvd_gcd_of_dvd {a b : ℕ} (ha : a ∣ 4) : ¬ 3 ∣ Nat.gcd a b := by
  intro h
  have : 3 ∣ 4 := h.trans ((Nat.gcd_dvd_left a b).trans ha)
  omega

theorem I294Cross.eighty_one_dvd_ordBC {n q : ℕ} (hq : ¬ 3 ∣ q) (hn : 2 ≤ n)
    (h27 : 3 ^ 3 ∣ ordBC n q) : 3 ^ 4 ∣ ordBC n q := by
  have hdq : ∀ k, Nat.Coprime (3 ^ k) q := fun k => coprime_three_pow hq
  have hdg : ∀ k, Nat.Coprime (3 ^ k) (Nat.gcd 2 (q - 1)) := fun k =>
    coprime_three_pow (not_three_dvd_gcd_of_dvd (by norm_num))
  refine (dvd_ordBC_iff (by omega) (hdq 4) (hdg 4)).2 ?_
  rcases Nat.lt_or_ge n 3 with h2 | h3
  · obtain rfl : n = 2 := by omega
    have h27' := (dvd_ordBC_iff (by omega) (hdq 3) (hdg 3)).1 h27
    rw [show Finset.Icc 1 2 = {1, 2} by decide] at h27' ⊢
    rw [show ∏ i ∈ ({1, 2} : Finset ℕ), (q ^ (2 * i) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) * 1 by
      simp [Finset.prod_insert]] at h27' ⊢
    exact eighty_one_dvd_of_twentySeven_dvd hq (by omega) h27'
  · exact three_pow_four_dvd_prod_even hq h3

theorem I294Cross.three_pow_five_dvd_ordD {n q : ℕ} (hq : ¬ 3 ∣ q) (hn : 4 ≤ n) :
    3 ^ 5 ∣ ordD n q := by
  have hdq : Nat.Coprime (3 ^ 5) q := coprime_three_pow hq
  have hdg : Nat.Coprime (3 ^ 5) (Nat.gcd 4 (q ^ n - 1)) :=
    coprime_three_pow (not_three_dvd_gcd_of_dvd (by norm_num))
  refine (dvd_ordD_iff hdq hdg).2 ?_
  rcases Nat.lt_or_ge n 5 with h4 | h5
  · obtain rfl : n = 4 := by omega
    have h4 := three_dvd_pow_two_mul_sub_one hq 2
    have := mul_dvd_mul h4 (three_pow_four_dvd_prod_even hq (k := 3) (by norm_num))
    simpa [pow_succ, mul_comm] using this
  · exact Dvd.dvd.mul_left (three_pow_five_dvd_prod_even hq (k := n - 1) (by omega)) _

theorem I294Cross.eighty_one_dvd_ordTwistedD {n q : ℕ} (hq : ¬ 3 ∣ q) (hn : 4 ≤ n) :
    3 ^ 4 ∣ ordTwistedD n q := by
  have hdq : Nat.Coprime (3 ^ 4) q := coprime_three_pow hq
  have hdg : Nat.Coprime (3 ^ 4) (Nat.gcd 4 (q ^ n + 1)) :=
    coprime_three_pow (not_three_dvd_gcd_of_dvd (by norm_num))
  exact (dvd_ordTwistedD_iff hdq hdg).2
    (Dvd.dvd.mul_left (three_pow_four_dvd_prod_even hq (k := n - 1) (by omega)) _)

theorem I294Cross.eighty_one_dvd_ordA {m q : ℕ} (hq : ¬ 3 ∣ q)
    (hLU : ¬ (3 ∣ m + 1 ∧ 3 ∣ q - 1)) (hm : 3 ≤ m) (h27 : 3 ^ 3 ∣ ordA m q) :
    3 ^ 4 ∣ ordA m q := by
  have hdq : ∀ k, Nat.Coprime (3 ^ k) q := fun k => coprime_three_pow hq
  have hg : ¬ 3 ∣ Nat.gcd (m + 1) (q - 1) := fun h =>
    hLU ⟨h.trans (Nat.gcd_dvd_left _ _), h.trans (Nat.gcd_dvd_right _ _)⟩
  have hdg : ∀ k, Nat.Coprime (3 ^ k) (Nat.gcd (m + 1) (q - 1)) := fun k => coprime_three_pow hg
  refine (dvd_ordA_iff (by omega) (hdq 4) (hdg 4)).2 ?_
  rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with h1 | h2
  · exact three_pow_four_dvd_prod_one h1 (by omega)
  · rcases Nat.lt_or_ge (m + 1) 6 with hlt | hge
    · exact eighty_one_dvd_prod_two_small h2 (by omega) (by omega)
        ((dvd_ordA_iff (by omega) (hdq 3) (hdg 3)).1 h27)
    · exact three_pow_four_dvd_prod_two hq hge

theorem I294Cross.eighty_one_dvd_ordTwistedA {m q : ℕ} (hq : ¬ 3 ∣ q)
    (hLU : ¬ (3 ∣ m + 1 ∧ 3 ∣ q + 1)) (hm : 3 ≤ m) (h27 : 3 ^ 3 ∣ ordTwistedA m q) :
    3 ^ 4 ∣ ordTwistedA m q := by
  have hq1 : 1 ≤ q := by omega
  have hdq : ∀ k, Nat.Coprime (3 ^ k) q := fun k => coprime_three_pow hq
  have hg : ¬ 3 ∣ Nat.gcd (m + 1) (q + 1) := fun h =>
    hLU ⟨h.trans (Nat.gcd_dvd_left _ _), h.trans (Nat.gcd_dvd_right _ _)⟩
  have hdg : ∀ k, Nat.Coprime (3 ^ k) (Nat.gcd (m + 1) (q + 1)) := fun k => coprime_three_pow hg
  refine (dvd_ordTwistedA_iff (by omega) hq1 (hdq 4) (hdg 4)).2 ?_
  rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with h1 | h2
  · rcases Nat.lt_or_ge (m + 1) 6 with hlt | hge
    · exact eighty_one_dvd_prodU_one_small h1 (by omega) (by omega)
        ((dvd_ordTwistedA_iff (by omega) hq1 (hdq 3) (hdg 3)).1 h27)
    · exact three_pow_four_dvd_prodU_one h1 hge
  · exact three_pow_four_dvd_prodU_two h2 (by omega)

end Arithmetic

section ElemAbelian

theorem I294Cross.not_isCyclic_of_elemAbelian {X : Type} [Group X] {E : Subgroup X}
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) : ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h3 : g ^ 3 = 1 := Subtype.ext (by simpa using hE.2 g.1 g.2)
  have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [hg, hEc] at h1
  omega

theorem I294Cross.zmod3_two_sq : (2 : ZMod 3) ^ 2 = 1 := by decide

theorem I294Cross.zmod3_two_ne_one : (2 : ZMod 3) ≠ 1 := by decide

theorem I294Cross.zmod3_neg_one : -(1 : ZMod 3) = 2 := by decide

theorem I294Cross.orderOf_natCast_two {q : ℕ} (h : q % 3 = 2) : orderOf (q : ZMod 3) = 2 := by
  have hq : (q : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, h]; rfl
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [hq]
  exact orderOf_eq_prime I294Cross.zmod3_two_sq I294Cross.zmod3_two_ne_one

theorem I294Cross.orderOf_neg_natCast_one {q : ℕ} (h : q % 3 = 1) :
    orderOf (-(q : ZMod 3)) = 2 := by
  have hq : -(q : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, h]
    exact I294Cross.zmod3_neg_one
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [hq]
  exact orderOf_eq_prime I294Cross.zmod3_two_sq I294Cross.zmod3_two_ne_one

theorem I294Cross.false_elemAbelian_psl_two {L : Type} [Group L] [Finite L] {p f : ℕ}
    (hm : StatedClassicalModel L .PSL 2 p f) (hp3 : p ≠ 3) (h27 : 3 ^ 3 ∣ Nat.card L)
    {E : Subgroup L} (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) : False := by
  have hcard := ((I294Cross.card_of_scm hm).1 rfl)
  obtain ⟨⟨hp, hf, hn2, hne1, hne2⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  haveI : Fact p.Prime := ⟨hp⟩
  have hq3 : ¬ 3 ∣ p ^ f := I294Cross.not_three_dvd_pow hp hp3
  by_cases h7 : 7 ≤ p ^ f
  · let e' : L ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K :=
      e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hK
      (by rw [hK]; exact h7) 3 (by norm_num)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by rw [hK]; exact hq3))
    have hEp : IsPGroup 3 (E.map e'.toMonoidHom) := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Subgroup.card_map_of_injective e'.injective]; exact hEc
    obtain ⟨R, hR⟩ := hEp.exists_le_sylow
    have hEcyc : IsCyclic ↥(E.map e'.toMonoidHom) :=
      isCyclic_of_injective (Subgroup.inclusion hR) (Subgroup.inclusion_injective hR)
    have hEc' : Nat.card (E.map e'.toMonoidHom) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective e'.injective]; exact hEc
    have hE' : IsElemAbelian 3 (E.map e'.toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _
    exact I294Cross.not_isCyclic_of_elemAbelian hE' hEc' hEcyc
  · push Not at h7
    have hq2 : 2 ≤ p ^ f := by
      have := hp.two_le
      calc 2 ≤ p := this
        _ ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hq4 : 4 ≤ p ^ f := by
      by_contra h
      have : p ^ f = 2 ∨ p ^ f = 3 := by omega
      rcases this with h | h
      · exact hne1 (by rw [h])
      · exact hne2 (by rw [h])
    rw [hcard] at h27
    generalize p ^ f = q at *
    interval_cases q
    · exact absurd (by decide : ordA (2 - 1) 4 = 60) (fun h => by rw [h] at h27; omega)
    · exact absurd (by decide : ordA (2 - 1) 5 = 60) (fun h => by rw [h] at h27; omega)
    · exact absurd (dvd_refl 3) (by simpa using hq3)

theorem I294Cross.false_elemAbelian_psl_three {L : Type} [Group L] [Finite L] {p f : ℕ}
    (hm : StatedClassicalModel L .PSL 3 p f) (hp3 : p ≠ 3)
    (hLU : ¬ IsLinearOrUnitaryAt 3 L) {E : Subgroup L} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) : False := by
  obtain ⟨⟨hp, hf, hn2, hne1, hne2⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have hq3 : ¬ 3 ∣ Nat.card K := by rw [hK]; exact I294Cross.not_three_dvd_pow hp hp3
  by_cases h1 : 3 ∣ Nat.card K - 1
  · exact hLU (Or.inl ⟨3, K, inferInstance, inferInstance, dvd_rfl, h1, ⟨e⟩⟩)
  · have hmod : Nat.card K % 3 = 2 := by omega
    let e' : L ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
      e.trans (CFSG.LocalAnalysis.RankFourTheoremC.l212in_projectiveSLEquivStated 3 K).symm
    have h := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.two_mul_orderOf_le_of_elemAbelian
      (K := K) (n := 3) le_rfl Nat.prime_three (by norm_num) h1 hq3
      (E := E.map e'.toMonoidHom) (CFSG.Open.IsElemAbelian.map hE _)
      (by rw [Subgroup.card_map_of_injective e'.injective]; exact hEc)
    rw [I294Cross.orderOf_natCast_two hmod] at h
    omega

theorem I294Cross.false_elemAbelian_psu_three {L : Type} [Group L] [Finite L] {p f : ℕ}
    (hm : StatedClassicalModel L .PSU 3 p f) (hp3 : p ≠ 3)
    (hLU : ¬ IsLinearOrUnitaryAt 3 L) {E : Subgroup L} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) : False := by
  obtain ⟨K, _, hU, ⟨e₀⟩, ⟨eP⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.exists_primeFormP_mulEquiv_of_statedModel hm
  obtain ⟨⟨hp, hf, hn3, hne⟩, K', _, _, hK', ⟨e⟩⟩ := hm
  have hq3 : ¬ 3 ∣ p ^ f := I294Cross.not_three_dvd_pow hp hp3
  by_cases h1 : 3 ∣ p ^ f + 1
  · exact hLU (Or.inr ⟨3, p ^ f, K', inferInstance, inferInstance, hK', dvd_rfl, h1, ⟨e⟩⟩)
  · have hmod : p ^ f % 3 = 1 := by omega
    have hq2 : ¬ (3 = 3 ∧ p ^ f = 2) := fun h => by omega
    have h := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.two_mul_orderOf_le_of_elemAbelian_unitary
      hU le_rfl hq2 Nat.prime_three (by norm_num) hp3.symm h1
      (E := E.map eP.toMonoidHom) (CFSG.Open.IsElemAbelian.map hE _)
      (by rw [Subgroup.card_map_of_injective eP.injective]; exact hEc)
    rw [I294Cross.orderOf_neg_natCast_one hmod] at h
    omega

end ElemAbelian


theorem I294Cross.false_of_classical_model {L : Type} [Group L] [Finite L] {t : StatedLieTag}
    {n p f : ℕ} (hm : StatedClassicalModel L t n p f) (hp3 : p ≠ 3)
    (hLU : ¬ IsLinearOrUnitaryAt 3 L) (h27 : 3 ^ 3 ∣ Nat.card L)
    (hE : ∃ E : Subgroup L, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2)
    (h81 : ¬ 3 ^ 4 ∣ Nat.card L) : False := by
  obtain ⟨E, hE, hEc⟩ := hE
  have hcard := I294Cross.card_of_scm hm
  obtain ⟨hadm, hrest⟩ := id hm
  obtain ⟨hp, hf, hadm⟩ := hadm
  have hq3 : ¬ 3 ∣ p ^ f := I294Cross.not_three_dvd_pow hp hp3
  cases t with
  | PSL =>
    have hn : 2 ≤ n := hadm.1
    have hc := hcard.1 rfl
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · rcases (by omega : n = 2 ∨ n = 3) with rfl | rfl
      · exact I294Cross.false_elemAbelian_psl_two hm hp3 h27 hE hEc
      · exact I294Cross.false_elemAbelian_psl_three hm hp3 hLU hE hEc
    · have hLU' : ¬ (3 ∣ n - 1 + 1 ∧ 3 ∣ p ^ f - 1) := fun h => hLU (Or.inl
        ⟨n, K, inferInstance, inferInstance, by rw [Nat.sub_add_cancel (by omega)] at h; exact h.1,
          by rw [hK]; exact h.2, ⟨e⟩⟩)
      have h27' : 3 ^ 3 ∣ ordA (n - 1) (p ^ f) := by rwa [hc] at h27
      exact h81 (by rw [hc]; exact I294Cross.eighty_one_dvd_ordA hq3 hLU' (by omega) h27')
  | PSU =>
    have hn : 3 ≤ n := hadm.1
    have hc := hcard.2.1 rfl
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · obtain rfl : n = 3 := by omega
      exact I294Cross.false_elemAbelian_psu_three hm hp3 hLU hE hEc
    · have hLU' : ¬ (3 ∣ n - 1 + 1 ∧ 3 ∣ p ^ f + 1) := fun h => hLU (Or.inr
        ⟨n, p ^ f, K, inferInstance, inferInstance, hK,
          by rw [Nat.sub_add_cancel (by omega)] at h; exact h.1, h.2, ⟨e⟩⟩)
      have h27' : 3 ^ 3 ∣ ordTwistedA (n - 1) (p ^ f) := by rwa [hc] at h27
      exact h81 (by rw [hc]; exact I294Cross.eighty_one_dvd_ordTwistedA hq3 hLU' (by omega) h27')
  | PSp =>
    have hn : 2 ≤ n := hadm.1
    have hc := hcard.2.2.1 rfl
    have h27' : 3 ^ 3 ∣ ordBC n (p ^ f) := by rwa [hc] at h27
    exact h81 (by rw [hc]; exact I294Cross.eighty_one_dvd_ordBC hq3 hn h27')
  | POmegaOdd =>
    have hn : 3 ≤ n := hadm.1
    have hc := hcard.2.2.2.1 rfl
    have h27' : 3 ^ 3 ∣ ordBC n (p ^ f) := by rwa [hc] at h27
    exact h81 (by rw [hc]; exact I294Cross.eighty_one_dvd_ordBC hq3 (by omega) h27')
  | POmegaPlus =>
    have hc := hcard.2.2.2.2.1 rfl
    exact h81 (by
      rw [hc]
      exact (pow_dvd_pow 3 (by norm_num : 4 ≤ 5)).trans
        (I294Cross.three_pow_five_dvd_ordD hq3 (by omega)))
  | POmegaMinus =>
    have hc := hcard.2.2.2.2.2 rfl
    exact h81 (by rw [hc]; exact I294Cross.eighty_one_dvd_ordTwistedD hq3 (by omega))
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

theorem i294CrossThreeRankTwoClassical_holds : I294CrossThreeRankTwoClassical := by
  intro L _ _ _ _ d hd hc3 hLe hLU hS _ h81 _ _
  exfalso
  obtain ⟨hdiv27, hE⟩ := I294Cross.nonabelian_sylow_three hS
  obtain ⟨idx, hv⟩ := d
  obtain ⟨e⟩ := hLe
  cases idx with
  | A r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_A] using hc3
    exact I294Cross.false_of_classical_model
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e) hp3 hLU hdiv27 hE h81
  | twistedA r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_twistedA] using hc3
    exact I294Cross.false_of_classical_model
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e) hp3 hLU hdiv27 hE h81
  | B r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_B] using hc3
    have hr2 : 2 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    rcases Nat.lt_or_ge r 3 with hr | hr
    · obtain rfl : r = 2 := by omega
      exact I294Cross.false_of_classical_model
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) hp3 hLU hdiv27 hE h81
    · by_cases hq2 : q.p = 2
      · exact I294Cross.false_of_classical_model
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 hr e)
          hp3 hLU hdiv27 hE h81
      · exact I294Cross.false_of_classical_model
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hq2 hr e)
          hp3 hLU hdiv27 hE h81
  | C r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_C] using hc3
    exact I294Cross.false_of_classical_model
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e) hp3 hLU hdiv27 hE h81
  | D r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_D] using hc3
    exact I294Cross.false_of_classical_model
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e) hp3 hLU hdiv27 hE h81
  | twistedD r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_twistedD] using hc3
    exact I294Cross.false_of_classical_model
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)
      hp3 hLU hdiv27 hE h81
  | _ => exact (hd : False).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
