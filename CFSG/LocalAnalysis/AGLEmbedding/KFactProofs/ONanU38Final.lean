module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Dich
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Models9
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Link
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Models

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts

theorem orderOf_pow_three_pow {X : Type*} [Group X] {c : X} {n m : ℕ} (hn : orderOf c = 3 ^ n)
    (hm : m ≤ n) : orderOf (c ^ 3 ^ (n - m)) = 3 ^ m := by
  rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (hn ▸ pow_dvd_pow 3 (Nat.sub_le n m)), hn,
    Nat.pow_div (Nat.sub_le n m) (by norm_num)]
  congr 1
  omega

theorem exists_order_three {X : Type*} [Group X] {C : Subgroup X} (hC : IsPGroup 3 C) {c : X}
    (hc : c ∈ C) (hc1 : c ≠ 1) : ∃ z ∈ C, orderOf z = 3 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf (p := 3)).1 hC ⟨c, hc⟩
  rw [Subgroup.orderOf_mk] at hn
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hn
    exact hc1 hn
  refine ⟨c ^ 3 ^ (n - 1), C.pow_mem hc _, ?_⟩
  have := orderOf_pow_three_pow hn hn1
  simpa using this

theorem exists_order_nine {X : Type*} [Group X] {C : Subgroup X} (hC : IsPGroup 3 C) {c : X}
    (hc : c ∈ C) (hc3 : c ^ 3 ≠ 1) : ∃ z ∈ C, orderOf z = 9 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf (p := 3)).1 hC ⟨c, hc⟩
  rw [Subgroup.orderOf_mk] at hn
  have hn2 : 2 ≤ n := by
    by_contra h
    apply hc3
    have hdvd : orderOf c ∣ 3 := by
      rw [hn]
      interval_cases n <;> norm_num
    exact orderOf_dvd_iff_pow_eq_one.1 hdvd
  refine ⟨c ^ 3 ^ (n - 2), C.pow_mem hc _, ?_⟩
  have := orderOf_pow_three_pow hn hn2
  simpa using this

theorem omegaSU_pow_three : omegaSU ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_omegaSU_pow]
  show zeta ^ 9 • (1 : Matrix (Fin 3) (Fin 3) GF64) = 1
  rw [zeta_pow_nine, one_smul]

theorem scalar_cases {g : SU} (hg : g ∈ unitaryScalars hU 3) : ∃ m < 3, g = omegaSU ^ m := by
  obtain ⟨c, hc, hgc⟩ := exists_scalar_of_mem hg
  have hc3 : c ^ 3 = 1 := by
    rcases hc with rfl | rfl | rfl <;> decide +kernel
  obtain ⟨k, hk, hck⟩ := det_cases c hc3
  refine ⟨k, hk, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [coe_omegaSU_pow, ← hck]
  exact hgc

theorem pow_three_of_mem_unitaryScalars {g : SU} (hg : g ∈ unitaryScalars hU 3) : g ^ 3 = 1 := by
  obtain ⟨m, -, rfl⟩ := scalar_cases hg
  rw [← pow_mul, mul_comm, pow_mul, omegaSU_pow_three, one_pow]

section Nine

variable {X : Type} [Group X] (K : Subgroup X) (e : K ≃* SU)

theorem exists_good_nine
    (hZc : ∀ c ∈ Subgroup.center K, e c ∈ unitaryScalars hU 3)
    (hCZ : ∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype)
    {z : X} (hzC : z ∈ Subgroup.centralizer (K : Set X)) (hz9 : orderOf z = 9) :
    ∃ z' ∈ Subgroup.centralizer (K : Set X), orderOf z' = 9 ∧
      z' ^ 3 = ((e.symm omegaSU : K) : X) := by
  have hz3 : orderOf (z ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hz9]; norm_num), hz9]
  obtain ⟨k₀, hk₀, hk₀z⟩ := Subgroup.mem_map.1 (hCZ _ ((Subgroup.centralizer _).pow_mem hzC 3) hz3)
  obtain ⟨m, hm, hm'⟩ := scalar_cases (hZc k₀ hk₀)
  have hk₀e : k₀ = e.symm (omegaSU ^ m) := by rw [← hm']; simp
  interval_cases m
  · exfalso
    have : k₀ = 1 := by rw [hk₀e, pow_zero, map_one]
    rw [this] at hk₀z
    have h1 : z ^ 3 = 1 := by rw [← hk₀z]; rfl
    rw [h1, orderOf_one] at hz3
    omega
  · refine ⟨z, hzC, hz9, ?_⟩
    rw [← hk₀z, hk₀e, pow_one]
    rfl
  · refine ⟨z⁻¹, (Subgroup.centralizer _).inv_mem hzC, by rw [orderOf_inv, hz9], ?_⟩
    rw [inv_pow, ← hk₀z, hk₀e]
    have h2 : (omegaSU ^ 2)⁻¹ = omegaSU := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ, omegaSU_pow_three]
    have : (e.symm (omegaSU ^ 2) : K)⁻¹ = e.symm omegaSU := by
      rw [← map_inv, h2]
    rw [← this]
    rfl

theorem three_dvd_of_pow_mem
    (hZc : ∀ c ∈ Subgroup.center K, e c ∈ unitaryScalars hU 3)
    {z : X} (hzC : z ∈ Subgroup.centralizer (K : Set X)) (hz9 : orderOf z = 9) {k : ℕ}
    (hk : z ^ k ∈ K) : 3 ∣ k := by
  by_contra h3
  have hcop : Nat.Coprime k 9 := by
    have : Nat.Coprime k (3 ^ 2) :=
      Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
    simpa using this
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
  have hzK : z ∈ K := by
    have : z = (z ^ k) ^ j := by
      rw [← pow_mul, ← pow_mod_orderOf, hz9, hj, pow_one]
    rw [this]
    exact K.pow_mem hk j
  set κ : K := ⟨z, hzK⟩ with hκ
  have hκc : κ ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using (Subgroup.mem_centralizer_iff.1 hzC (g : X) g.2))
  have h1 : (e κ) ^ 3 = 1 := pow_three_of_mem_unitaryScalars (hZc κ hκc)
  have h2 : κ ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, h1, map_one]
  have h3' : z ^ 3 = 1 := congrArg Subtype.val h2
  have := orderOf_dvd_of_pow_eq_one h3'
  rw [hz9] at this
  omega

end Nine

theorem conj_mem_range_suConj (g : SU) : MulAut.conj g ∈ (suConj hU).range :=
  ⟨_, (mulAut_conj_eq_suConj' g).symm⟩

theorem conj_mem_range_psuConj (p : unitaryPSU hU 3) : MulAut.conj p ∈ (psuConj hU).range := by
  obtain ⟨g, rfl⟩ := unitaryProj_surjective hU 3 p
  exact ⟨_, (conj_mk_eq_psuConj g).symm⟩

theorem not_mem_of_not_mem_range {X G : Type*} [Group X] [Group G] (K : Subgroup X) [K.Normal]
    (e : K ≃* G) {S : Subgroup (MulAut G)} (hS : ∀ g : G, MulAut.conj g ∈ S) {x : X}
    (hx : actOn K e x ∉ S) : x ∉ K := fun hxK => hx (by
  have := actOn_coe K e ⟨x, hxK⟩
  rw [show ((⟨x, hxK⟩ : K) : X) = x from rfl] at this
  rw [this]
  exact hS _)

theorem le_weakCore_of_su
    {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal] (e : K ≃* SU)
    (hZc : ∀ c ∈ Subgroup.center K, e c ∈ unitaryScalars hU 3)
    (hC3 : IsPGroup 3 (Subgroup.centralizer (K : Set X)))
    (hCZ : ∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype)
    (E : Subgroup X) (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : 27 ≤ Nat.card E)
    (R : Sylow 3 X) : K ≤ CFSG.Open.GLBWeakCore 3 (R : Subgroup X) := by
  by_cases hI : ∃ x ∈ E, actOn K e x ∉ (suConj hU).range
  · obtain ⟨x, hxE, hD⟩ := hI
    have hx3 : x ^ 3 = 1 := hE.2 x hxE
    obtain ⟨e', y, hy, hact⟩ := exists_sigma_model_su K e hx3 hD
    have hxK : x ∉ K := not_mem_of_not_mem_range K e conj_mem_range_suConj hD
    have hyK : y ∉ K := by
      rcases hy with rfl | rfl
      · exact hxK
      · exact fun h => hxK (by simpa using K.inv_mem h)
    have hy3 : y ^ 3 = 1 := by
      rcases hy with rfl | rfl
      · exact hx3
      · rw [inv_pow, hx3, inv_one]
    exact le_weakCore_of_sigma_su K e' y hy3 hyK hact R
  · push Not at hI
    by_cases hA : ∃ z ∈ Subgroup.centralizer (K : Set X), orderOf z = 9
    · obtain ⟨z, hzC, hz9⟩ := hA
      obtain ⟨z', hz'C, hz'9, hz'3⟩ := exists_good_nine K e hZc hCZ hzC hz9
      exact le_weakCore_of_order_nine K e z'
        (fun k hk => (Subgroup.mem_centralizer_iff.1 hz'C k hk).symm)
        (hz'9 ▸ pow_orderOf_eq_one z') hz'3
        (fun k hk => three_dvd_of_pow_mem K e hZc hz'C hz'9 hk) R
    · push Not at hA
      have hCK : ∀ c ∈ Subgroup.centralizer (K : Set X), c ∈ K := by
        intro c hc
        by_cases hc3 : c ^ 3 = 1
        · by_cases hc1 : c = 1
          · rw [hc1]
            exact K.one_mem
          · obtain ⟨k, -, hk⟩ := Subgroup.mem_map.1 (hCZ c hc (orderOf_eq_prime hc3 hc1))
            rw [← hk]
            exact k.2
        · obtain ⟨z, hzC, hz9⟩ := exists_order_nine hC3 hc hc3
          exact absurd hz9 (hA z hzC)
      exact (false_of_inner_su K e hCK E hE hcard hI).elim

theorem le_weakCore_of_psu {X : Type} [Group X] [Finite X]
    (K : Subgroup X) [K.Normal] (e : K ≃* unitaryPSU hU 3)
    (hC1 : ∀ c ∈ Subgroup.centralizer (K : Set X), c = 1)
    (E : Subgroup X) (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : 27 ≤ Nat.card E)
    (R : Sylow 3 X) : K ≤ CFSG.Open.GLBWeakCore 3 (R : Subgroup X) := by
  by_cases hI : ∃ x ∈ E, actOn K e x ∉ (psuConj hU).range
  · obtain ⟨x, hxE, hD⟩ := hI
    have hx3 : x ^ 3 = 1 := hE.2 x hxE
    obtain ⟨e', y, hy, hact⟩ := exists_sigma_model_psu K e hx3 hD
    have hxK : x ∉ K := not_mem_of_not_mem_range K e conj_mem_range_psuConj hD
    have hyK : y ∉ K := by
      rcases hy with rfl | rfl
      · exact hxK
      · exact fun h => hxK (by simpa using K.inv_mem h)
    have hy3 : y ^ 3 = 1 := by
      rcases hy with rfl | rfl
      · exact hx3
      · rw [inv_pow, hx3, inv_one]
    exact le_weakCore_of_sigma_psu K e' y hy3 hyK hact R
  · push Not at hI
    exact (false_of_inner_psu K e hC1 E hE hcard hI).elim

theorem chevOuterGenAt_u38
    (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.LocalAnalysis.RankThreeTheoremC.IsChevTwoOuterU38Index d) :
    CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterGenAt d := by
  intro X _ _ K hKn hKq hiso hC3 hCZ R hR
  have := hKn
  obtain ⟨eK⟩ := hiso
  obtain ⟨eL⟩ := exists_equiv_unitaryPSU d hd
  have e1 : K ⧸ Subgroup.center K ≃* unitaryPSU hU 3 := eK.trans eL
  have hperf : Group.IsPerfect K := Group.isPerfect_def.2 hKq.1
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (R : Subgroup X)
  have hE27 : 27 ≤ Nat.card E := by
    rw [hEcard]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (R : Subgroup X) := Nat.pow_le_pow_right (by norm_num) hR
  rcases (Nat.dvd_prime Nat.prime_three).1 (card_center_dvd_three hperf e1) with h1 | h3
  · have hZ : Subgroup.center K = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    obtain ⟨e⟩ := exists_equiv_psu e1 hZ
    refine le_weakCore_of_psu K e ?_ E hE hE27 R
    intro c hc
    by_contra hc1
    obtain ⟨z, hzC, hz3⟩ := exists_order_three hC3 hc hc1
    have := hCZ z hzC hz3
    rw [hZ, Subgroup.map_bot, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hz3
    omega
  · obtain ⟨f, hf⟩ := exists_equiv_su hperf e1 h3
    refine le_weakCore_of_su K f.symm ?_ hC3 hCZ E hE hE27 R
    intro c hc
    obtain ⟨z, hz, rfl⟩ := hf c hc
    simpa using hz

end CFSG.AGLEmbedding.ChevOuter.U38

namespace CFSG.AGLEmbedding.ChevOuter

theorem kFactChevTwoOuterGenU38 :
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactChevTwoOuterGenU38 :=
  fun d hd => U38.chevOuterGenAt_u38 d hd

end CFSG.AGLEmbedding.ChevOuter
