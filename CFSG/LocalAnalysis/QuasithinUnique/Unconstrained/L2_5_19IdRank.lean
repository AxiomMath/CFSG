module

public import CFSG.Quasithin.Vol2.Ch1Rank
public import CFSG.CharacterTheory.Wreathed.ProjectiveTwoParameterUniqueness
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.Sporadic.J1

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

theorem card_of_l2p {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p 1) :
    p * (p * p - 1) = 2 * Nat.card X := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hc := CFSG.Wreathed.ProjectiveTwoParameterUniqueness.card_stated_psl_two_of_odd X p 1 h hodd
  have hev : 2 ∣ p * (p * p - 1) := by
    have : Even (p * p - 1) := (hodd.mul hodd).tsub_odd odd_one
    exact Dvd.dvd.mul_left this.two_dvd p
  rw [pow_one] at hc
  have : p * (p ^ 2 - 1) = p * (p * p - 1) := by rw [sq]
  rw [this] at hc
  rw [hc]
  exact (Nat.mul_div_cancel' hev).symm

section PRank

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem pRank_le_one_of_sylow_cyclic (hp : p.Prime)
    (h : ∀ P : Sylow p X, IsCyclic ↥(P : Subgroup X)) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E _ hE
  have hpE : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hEP⟩ := hpE.exists_le_sylow
  have hcycP : IsCyclic ↥(P : Subgroup X) := h P
  have hcyc : IsCyclic ↥E := by
    have : IsCyclic ↥(E.subgroupOf (P : Subgroup X)) := Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEP).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEP).surjective
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hE.2 g g.2)
  have hdvd : Nat.card E ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hgp
  rw [pow_one]
  exact Nat.le_of_dvd hp.pos hdvd

theorem pRank_le_one_of_not_sq_dvd (hp : p.Prime) (h : ¬ p ^ 2 ∣ Nat.card X) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E _ hE
  have hpE : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpE
  rw [hm, pow_one]
  by_contra hlt
  push Not at hlt
  have hm2 : 2 ≤ m := by
    by_contra h1
    have : m ≤ 1 := by omega
    have h2 : p ^ m ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
    rw [pow_one] at h2
    omega
  apply h
  exact (pow_dvd_pow p hm2).trans (hm ▸ Subgroup.card_subgroup_dvd_card E)

end PRank

theorem no_sq_dvd_21945 : ∀ p < 149, 2 ≤ p → ¬ p ^ 2 ∣ 21945 := by decide

theorem not_sq_dvd_J1 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 175560 := by
  intro h
  have h1 : p ^ 2 ∣ 2 ^ 3 * 21945 := by simpa using h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 3) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h2 : p ^ 2 ∣ 21945 := hcop.dvd_of_dvd_mul_left h1
  have hle : p ^ 2 ≤ 21945 := Nat.le_of_dvd (by norm_num) h2
  have hp148 : p < 149 := by nlinarith
  exact no_sq_dvd_21945 p hp148 hp.two_le h2

theorem not_sq_dvd_60 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 60 := by
  intro h
  have hle : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) h
  have hp8 : p < 8 := by nlinarith
  interval_cases p <;> first | omega | exact absurd hp (by decide)

section Families

variable {X : Type} [Group X] [Finite X]

theorem pRank_le_one_psl_two_even {n : ℕ}
    (hn : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 2 n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  have hn' := hn
  obtain ⟨⟨-, hf, -, h22, -⟩, K, _, _, hK, ⟨e⟩⟩ := hn
  have hn2 : 2 ≤ n := by
    by_contra h
    have h1 : n = 1 := by omega
    subst h1
    exact h22 (by norm_num)
  by_cases h2 : n = 2
  · subst h2
    refine pRank_le_one_of_not_sq_dvd hp ?_
    rw [CFSG.Wreathed.ProjectiveTwoParameterUniqueness.card_stated_psl_two X 2 2 hn']
    norm_num
    exact not_sq_dvd_60 hp hp2
  · have h3 : 3 ≤ n := by omega
    let e' : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
      e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := Finite.of_equiv X e'.toEquiv
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e']
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact p.Prime := ⟨hp⟩
    have h8 : 7 ≤ Nat.card K := by
      rw [hK]
      calc 7 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    refine pRank_le_one_of_sylow_cyclic hp fun R => ?_
    exact CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hK h8 p hp2
      (by rw [hK]; exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)) R

theorem pRank_le_one_psl_two_prime {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 q 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  have hq2 : q ≠ 2 := by omega
  have hcard := card_of_l2p hq hq2 hm
  by_cases hpq : p = q
  ·
    subst hpq
    refine pRank_le_one_of_not_sq_dvd hp ?_
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    have h1 : p * (p * p - 1) = 2 * (p ^ 2 * c) := by rw [← hc, hcard]
    have h2 : p * p - 1 = 2 * (p * c) := by
      have hp0 : 0 < p := hp.pos
      have : p * (p * p - 1) = p * (2 * (p * c)) := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hp0 this
    have h3 : p ∣ p * p - 1 := ⟨2 * c, by rw [h2]; ring⟩
    have h4 : p ∣ p * p := dvd_mul_right p p
    have h5 : p ∣ p * p - (p * p - 1) := Nat.dvd_sub h4 h3
    have h6 : p * p - (p * p - 1) = 1 := by
      have : 1 ≤ p * p := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hp.ne_zero)
      omega
    rw [h6] at h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp h5)
  · by_cases h7 : 7 ≤ q
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
      let e' : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
        e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
      have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
        Finite.of_equiv X e'.toEquiv
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e']
      have : Fact q.Prime := ⟨hq⟩
      have : Fact p.Prime := ⟨hp⟩
      have hK' : Nat.card K = q ^ 1 := hK
      have h8 : 7 ≤ Nat.card K := by rw [hK']; simpa using h7
      refine pRank_le_one_of_sylow_cyclic hp fun R => ?_
      exact CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hK' h8 p hp2
        (by rw [hK']; exact Nat.Coprime.pow_right 1 ((Nat.coprime_primes hp hq).2 hpq)) R
    ·
      have hq5 : q = 5 := by
        have : q < 7 := by omega
        interval_cases q <;> first | rfl | exact absurd hq (by decide)
      subst hq5
      refine pRank_le_one_of_not_sq_dvd hp ?_
      have h60 : Nat.card X = 60 := by omega
      rw [h60]
      exact not_sq_dvd_60 hp hp2

theorem pRank_le_one_suzuki {f : ℕ} (hm : SuzukiModel X 2 f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  obtain ⟨a, ha, ⟨e⟩⟩ := CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hm
  have : Finite (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) := Finite.of_equiv X e.toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  have : Fact p.Prime := ⟨hp⟩
  exact pRank_le_one_of_sylow_cyclic hp fun R => CFSG.SectionRank.suzuki_sylow_isCyclic a ha hp2 R

theorem pRank_le_one_J1
    (hm : Nonempty (X ≃* NativeSporadic.Carrier .J1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  obtain ⟨e⟩ := hm
  refine pRank_le_one_of_not_sq_dvd hp ?_
  rw [Nat.card_congr e.toEquiv]
  change ¬ p ^ 2 ∣ Nat.card NativeSporadic.J1
  rw [CFSG.Sporadic.J1.card_J1]
  exact not_sq_dvd_J1 hp hp2

end Families

theorem lemma122Rank : Lemma122Rank := by
  intro X _ _ hX p hp hp2
  rcases hX with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨q, hq, hq3, hm⟩
  · exact pRank_le_one_psl_two_even hn hp hp2
  · exact pRank_le_one_suzuki hn hp hp2
  · exact pRank_le_one_J1 hJ hp hp2
  · exact pRank_le_one_psl_two_prime hq hq3 hm hp hp2

end CFSG.QuasithinUnique.Id2519
