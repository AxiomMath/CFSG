module

public import CFSG.GH74.Generic.S45.LQData
public import CFSG.GH74.Uniqueness.Bender.FixedLinear
public import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint Subgroup
open CFSG.GH74.Uniqueness.Bender CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem not_sixteen_dvd {q : ℕ} (hq8 : q % 8 = 3 ∨ q % 8 = 5) : ¬ 16 ∣ q * (q ^ 2 - 1) := by
  have hq1 : 1 ≤ q := by omega
  have hQ : q * (q ^ 2 - 1) + q = q ^ 3 := by
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    zify [h2]
    ring
  intro h
  have h16 : q % 16 = 3 ∨ q % 16 = 5 ∨ q % 16 = 11 ∨ q % 16 = 13 := by omega
  have hmod : q ^ 3 % 16 = (q % 16) ^ 3 % 16 := Nat.pow_mod q 3 16
  rcases h16 with h' | h' | h' | h' <;> rw [h'] at hmod <;> norm_num at hmod <;> omega

theorem three_dvd_of_card {N q : ℕ} (h : N * 2 = q * (q ^ 2 - 1)) : 3 ∣ N := by
  have hq1 : 1 ≤ q ∨ q = 0 := by omega
  rcases hq1 with hq1 | rfl
  · have hQ : q * (q ^ 2 - 1) + q = q ^ 3 := by
      have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
      zify [h2]
      ring
    have hmod : q ^ 3 % 3 = (q % 3) ^ 3 % 3 := Nat.pow_mod q 3 3
    have h3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases h3 with h' | h' | h' <;> rw [h'] at hmod <;> norm_num at hmod <;> omega
  · simp at h
    omega

theorem two_pow_card_eq {N m q : ℕ} (hdvd : N ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1)) (hm : 1 ≤ m)
    (hq5 : 5 ≤ q) (hq8 : q % 8 = 3 ∨ q % 8 = 5) (h : N * 2 = q * (q ^ 2 - 1))
    (hall : 2 ≤ m → N = 2 ^ m * ((2 ^ m) ^ 2 - 1)) : m = 2 ∧ q = 5 := by
  have hq120 : 120 ≤ q * (q ^ 2 - 1) := by
    have h1 : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
    have h2 : 5 * (5 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq5 (Nat.sub_le_sub_right h1 1)
    simpa using h2
  by_cases hm1 : m = 1
  · subst hm1
    exfalso
    have hN6 : N ≤ 6 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      simpa using this
    omega
  · have hm2 : 2 ≤ m := by omega
    have hN := hall hm2
    by_cases hm2' : m = 2
    · subst hm2'
      refine ⟨rfl, ?_⟩
      have h60 : N = 60 := by rw [hN]; norm_num
      rw [h60] at h
      by_contra hne
      have hq6 : 6 ≤ q := by omega
      have h1 : 6 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq6 2
      have h2 : 6 * (6 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul hq6 (Nat.sub_le_sub_right h1 1)
      omega
    · exfalso
      have hm3 : 3 ≤ m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      have h8 : 8 ∣ N := by
        rw [hN, pow_add]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (by norm_num) _) _
      obtain ⟨c, hc⟩ := h8
      apply not_sixteen_dvd hq8
      rw [← h, hc]
      exact ⟨c, by ring⟩

variable {S : Type} [Group S]

theorem not_exists_conj_of_not_mem_inner {ya : MulAut S} (hout : ya ∉ inner S) :
    ¬ ∃ g : S, ∀ x : S, ya x = g * x * g⁻¹ := by
  rintro ⟨g, hg⟩
  exact hout ⟨g, MulEquiv.ext fun x => by rw [hg x]; rfl⟩

theorem exists_involution_of_mem_inner (hZ : Subgroup.center S = ⊥) {ya : MulAut S}
    (hya2 : ya * ya = 1) (hya1 : ya ≠ 1) (hin : ya ∈ inner S) :
    ∃ x : S, orderOf x = 2 ∧ ya = MulAut.conj x := by
  obtain ⟨x, hx⟩ := hin
  have hxx : x * x = 1 := by
    have h1 : MulAut.conj (x * x) = 1 := by rw [map_mul, hx, hya2]
    have hc : x * x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun a : MulAut S => a z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc z * (x * x) = (x * x * z * (x * x)⁻¹) * (x * x) := by rw [this]
        _ = x * x * z := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hya1 (by rw [← hx, map_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨x, orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1, hx.symm⟩

theorem autFixed_conj_eq_centralizer (x : S) :
    autFixed (MulAut.conj x : MulAut S) = Subgroup.centralizer ({x} : Set S) := by
  ext s
  rw [mem_autFixed_iff, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc s * x = (x * s * x⁻¹) * x := by rw [h]
      _ = x * s := by group
  · intro h
    calc x * s * x⁻¹ = (s * x) * x⁻¹ := by rw [h]
      _ = s := by group


theorem false_of_inner_component [Finite S] (hZ : Subgroup.center S = ⊥)
    (hfree : ∀ u : S, orderOf u = 2 →
      ∀ B : Subgroup ↥(Subgroup.centralizer ({u} : Set S)), ¬ CFSG.IsComponent B)
    {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) (hin : ya ∈ inner S) :
    False := by
  obtain ⟨x, hx2, rfl⟩ := exists_involution_of_mem_inner hZ hQ.sq hQ.ne hin
  have hF := autFixed_conj_eq_centralizer x
  have hLC : Lb ≤ Subgroup.centralizer ({x} : Set S) := hF ▸ hQ.le
  have hsub : (Lb.subgroupOf (Subgroup.centralizer ({x} : Set S))).IsSubnormal := by
    have := hQ.sub
    rw [hF] at this
    exact this
  refine hfree x hx2 (Lb.subgroupOf (Subgroup.centralizer ({x} : Set S))) ⟨?_, hsub⟩
  let e : ↥(Lb.subgroupOf (Subgroup.centralizer ({x} : Set S))) ≃* ↥Lb :=
    Subgroup.subgroupOfEquivOfLe hLC
  have hs : IsSimpleGroup ↥(Lb.subgroupOf (Subgroup.centralizer ({x} : Set S))) := by
    have : IsSimpleGroup ↥Lb := hQ.simple
    exact e.isSimpleGroup
  have hnab : ∃ a b : ↥(Lb.subgroupOf (Subgroup.centralizer ({x} : Set S))), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hQ.nonab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  exact isQuasisimple_of_simple_nonab hs hnab

theorem false_of_inner_pgroup [Finite S] (hZ : Subgroup.center S = ⊥)
    (hP : ∀ u : S, orderOf u = 2 → IsPGroup 2 ↥(Subgroup.centralizer ({u} : Set S)))
    {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) (hin : ya ∈ inner S) :
    False := by
  obtain ⟨x, hx2, rfl⟩ := exists_involution_of_mem_inner hZ hQ.sq hQ.ne hin
  have hLC : Lb ≤ Subgroup.centralizer ({x} : Set S) := (autFixed_conj_eq_centralizer x) ▸ hQ.le
  have hLP : IsPGroup 2 ↥Lb := (hP x hx2).to_le hLC
  obtain ⟨k, hk⟩ := hLP.exists_card_eq
  have h3 := three_dvd_of_card hQ.card
  rw [hk] at h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3)
  omega

theorem sl2_fixed_outcome [Finite S] {m : ℕ} (hm1 : 1 ≤ m) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (eC : ↥(autFixed ya) ≃* CFSG.Theory.Comparator.PSL2Model m) (hQ : QData S ya Lb q) :
    m = 2 ∧ q = 5 := by
  have hcardC : Nat.card ↥(autFixed ya) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr eC.toEquiv]
    exact CFSG.Walter.psl2_even_card (by omega)
  have hdvd : Nat.card ↥Lb ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := hcardC ▸ Subgroup.card_dvd_of_le hQ.le
  have hall : 2 ≤ m → Nat.card ↥Lb = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    intro hm2
    have hCs : IsSimpleGroup ↥(autFixed ya) := by
      have : IsSimpleGroup (CFSG.Theory.Comparator.PSL2Model m) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
          rw [GaloisField.card 2 m (by omega)]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2)
      exact eC.isSimpleGroup
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hCs hQ.sub with hbot | htop
    · exfalso
      have : Nontrivial ↥Lb := hQ.simple.toNontrivial
      obtain ⟨l, hl⟩ := exists_ne (1 : ↥Lb)
      have hmem : (⟨l, hQ.le l.2⟩ : ↥(autFixed ya)) ∈ Lb.subgroupOf (autFixed ya) := l.2
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 : (l : S) = 1 := congrArg (fun z : ↥(autFixed ya) => (z : S)) hmem
      exact hl (Subtype.ext h1)
    · have hle : autFixed ya ≤ Lb := Subgroup.subgroupOf_eq_top.1 htop
      rw [le_antisymm hQ.le hle, hcardC]
  exact two_pow_card_eq hdvd hm1 hQ.q5 hQ.mod8 hQ.card hall

theorem l2even_outer [Finite S] {f : ℕ} (hf : 2 ≤ f) (e : S ≃* CFSG.Theory.Comparator.PSL2Model f)
    {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) (hout : ya ∉ inner S) :
    f = 4 ∧ q = 5 := by
  have hbt : BenderType S f 1 1 := BenderType.linear f hf e
  obtain ⟨m, hm, ⟨eC⟩, -⟩ :=
    BenderType.fixed_linear hbt ya hQ.sq (not_exists_conj_of_not_mem_inner hout)
  obtain ⟨hm2, hq5⟩ := sl2_fixed_outcome (by omega) eC hQ
  exact ⟨by omega, hq5⟩

theorem u3even_outer [Finite S] {f : ℕ} (hf : 2 ≤ f) (e : S ≃* CFSG.Theory.Comparator.PSU3Model f)
    {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) (hout : ya ∉ inner S) :
    f = 2 ∧ q = 5 := by
  have hbt := BenderType.unitary f hf e
  obtain ⟨eC⟩ := BenderType.fixed_unitary hbt ya hQ.sq (not_exists_conj_of_not_mem_inner hout)
  exact sl2_fixed_outcome (by omega) eC hQ


open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem suzuki_false [Finite S] {f : ℕ}
    (hS : CFSG.Blueprint.SuzukiModel S 2 f) (hZ : Subgroup.center S = ⊥) {ya : MulAut S}
    {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) : False := by
  obtain ⟨-, a, ha, K, hKf, hKfin, hfa, hK, ⟨e⟩⟩ := hS
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hK
  have hOdd := (CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K
    hK').2.2.2.2.2.2
  have hOddS : Odd (Nat.card (Outer S)) := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact hOdd
  have hin : ya ∈ inner S := by
    have h2 : (QuotientGroup.mk ya : Outer S) ^ 2 = 1 := by
      rw [pow_two, ← QuotientGroup.mk_mul, hQ.sq, QuotientGroup.mk_one]
    have h1 : orderOf (QuotientGroup.mk ya : Outer S) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h3 : orderOf (QuotientGroup.mk ya : Outer S) ∣ Nat.card (Outer S) :=
      orderOf_dvd_natCard _
    have hodd' : Odd (orderOf (QuotientGroup.mk ya : Outer S)) := Odd.of_dvd_nat hOddS h3
    have h4 : orderOf (QuotientGroup.mk ya : Outer S) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact h
      · rw [h] at hodd'
        exact absurd hodd' (by decide)
    exact (QuotientGroup.eq_one_iff ya).1 (orderOf_eq_one_iff.1 h4)
  refine false_of_inner_pgroup hZ ?_ hQ hin
  intro u hu
  have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  obtain ⟨P, -, hPc, -⟩ :=
    (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK').1 (e u) hu'
  have hPp : IsPGroup 2 ↥(Subgroup.centralizer ({e u} : Set (CFSG.Blueprint.suzukiGroup a K))) := by
    rw [hPc]
    exact P.isPGroup'
  have hcomap : (Subgroup.centralizer ({e u} : Set (CFSG.Blueprint.suzukiGroup a K))).comap
      e.toMonoidHom = Subgroup.centralizer ({u} : Set S) := by
    ext s
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply e.injective
      rw [map_mul, map_mul]
      exact h
    · intro h
      show e s * e u = e u * e s
      rw [← map_mul, ← map_mul, h]
  rw [← hcomap]
  exact hPp.comap_of_injective e.toMonoidHom e.injective

end CFSG.GH74.Generic.S45
