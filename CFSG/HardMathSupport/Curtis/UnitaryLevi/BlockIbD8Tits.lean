module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSpin
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviBorel

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem mem_of_mul_two_power_three_power {J K : Subgroup G} (hKJ : K ≤ J)
    (hKn : J ≤ Subgroup.normalizer (K : Set G)) {z g b : G} (hz : z ∈ J) (hg : g ∈ K)
    (hzgb : z = g * b) (hb : ∃ m : ℕ, b ^ 2 ^ m = 1) (hz3 : ∃ k : ℕ, z ^ 3 ^ k = 1) : z ∈ K := by
  obtain ⟨m, hm⟩ := hb
  obtain ⟨k, hk⟩ := hz3
  have hbJ : b ∈ J := by
    have : b = g⁻¹ * z := by rw [hzgb]; group
    rw [this]
    exact J.mul_mem (J.inv_mem (hKJ hg)) hz
  have hN : (K.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).mpr hKn
  let q : J →* J ⧸ K.subgroupOf J := QuotientGroup.mk' (K.subgroupOf J)
  have hqg : q ⟨g, hKJ hg⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.2 hg)
  have hqz : q ⟨z, hz⟩ = q ⟨b, hbJ⟩ := by
    have : (⟨z, hz⟩ : J) = ⟨g, hKJ hg⟩ * ⟨b, hbJ⟩ := Subtype.ext hzgb
    rw [this, map_mul, hqg, one_mul]
  have h2 : (q ⟨z, hz⟩) ^ 2 ^ m = 1 := by
    rw [hqz, ← map_pow]
    have : (⟨b, hbJ⟩ : J) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
    rw [this, map_one]
  have h3 : (q ⟨z, hz⟩) ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨z, hz⟩ : J) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ m) (3 ^ k) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have h1 : orderOf (q ⟨z, hz⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  have h4 : q ⟨z, hz⟩ = 1 := orderOf_eq_one_iff.1 h1
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h4)

end Generic

section Main

variable {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.three_mem_perfectJoin
    (h : BorelQuotient D n H π M) (hM : M = 1)
    (hnode : ∀ i, Nat.card (rankOne D.rootGroup i) ∣ 6)
    (hcomm : ∀ i j, i ≠ j → D.cartan i j = 0 →
      Commutes (rankOne D.rootGroup i) (rankOne D.rootGroup j))
    (hpair : ∀ i j, i ≠ j → D.cartan i j ≠ 0 →
      ⁅rankOne D.rootGroup i ⊔ rankOne D.rootGroup j,
          rankOne D.rootGroup i ⊔ rankOne D.rootGroup j⁆ =
        rankOne D.rootGroup i ⊔ rankOne D.rootGroup j)
    (hhub : ∀ i j k : Fin D.rank, i ≠ j → D.cartan i j ≠ 0 →
      k = i ∨ k = j ∨ (k ≠ i ∧ D.cartan i k ≠ 0) ∨ (k ≠ j ∧ D.cartan j k ≠ 0))
    (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hK : perfectJoin J ≠ ⊥) :
    ∀ y ∈ J, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ∈ perfectJoin J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel D H).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  have hBA : borel D H ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hBU : borel D H ≤ posUnipotent D := by
    refine sup_le (fun t ht => ?_) le_rfl
    have := hQ.pow_eq_one_of_mem_iSup ht
    rw [hM, pow_one] at this
    rw [this]
    exact one_mem _
  have hU2 : IsPGroup 2 ((posUnipotent D).map π') := (isPGroup_iSup_pos h.extras h.pGroup).map π'
  have hB2 : ∀ b ∈ (borel D H).map π', ∃ m : ℕ, b ^ 2 ^ m = 1 := by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    obtain ⟨m, hm⟩ := hU2 ⟨π' b₀, ⟨b₀, hBU hb₀, rfl⟩⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  set I : Set (Fin D.rank) := negIndices D (J.comap π') with hI
  have hLJ : ∀ i ∈ I, (rankOne D.rootGroup i).map π' ≤ J := fun i hi =>
    Subgroup.map_le_iff_le_comap.2 (rankOne_le_of_mem_negIndices hBA hi)
  set Λ : Subgroup Y := ⨆ i ∈ I, (rankOne D.rootGroup i).map π' with hΛ
  have hΛJ : Λ ≤ J := iSup₂_le hLJ
  have hprod : ∀ z ∈ J, ∃ g ∈ Λ, ∃ b ∈ (borel D H).map π', z = g * b := fun z hz =>
    exists_mul_of_mem_of_borel_le hQ.ct hQ.extras hπ' hBJ hz
  set K' : Subgroup Y := perfectJoin J with hK'
  by_cases hadj : ∃ i ∈ I, ∃ j ∈ I, i ≠ j ∧ D.cartan i j ≠ 0
  ·
    obtain ⟨i, hi, j, hj, hij, hA⟩ := hadj
    have hpairK : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → D.cartan a b ≠ 0 →
        (rankOne D.rootGroup a).map π' ≤ K' ∧ (rankOne D.rootGroup b).map π' ≤ K' := by
      intro a ha b hb hab hAab
      have hle : ((rankOne D.rootGroup a ⊔ rankOne D.rootGroup b).map π') ≤ K' := by
        refine le_perfectJoin ?_ (map_commutator_self_eq π' (hpair a b hab hAab))
        rw [Subgroup.map_sup]
        exact sup_le (hLJ a ha) (hLJ b hb)
      rw [Subgroup.map_sup] at hle
      exact ⟨le_sup_left.trans hle, le_sup_right.trans hle⟩
    have hΛK : Λ ≤ K' := by
      refine iSup₂_le fun k hk => ?_
      rcases hhub i j k hij hA with hki | hkj | ⟨hki, hAik⟩ | ⟨hkj, hAjk⟩
      · rw [hki]; exact (hpairK i hi j hj hij hA).1
      · rw [hkj]; exact (hpairK i hi j hj hij hA).2
      · exact (hpairK i hi k hk (Ne.symm hki) hAik).2
      · exact (hpairK j hj k hk (Ne.symm hkj) hAjk).2
    intro y hy hy3
    obtain ⟨g, hg, b, hb, hyg⟩ := hprod y hy
    exact mem_of_mul_two_power_three_power (perfectJoin_le J) (le_normalizer_perfectJoin J) hy
      (hΛK hg) hyg (hB2 b hb) hy3
  ·
    exfalso
    push Not at hadj
    have hcomm' : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        Commutes ((rankOne D.rootGroup i).map π') ((rankOne D.rootGroup j).map π') :=
      fun i hi j hj hij => (hcomm i j hij (hadj i hi j hj hij)).map π'
    set A : Fin D.rank → Subgroup Y := fun i => (rankOne D.rootGroup i).map π' with hA
    set s : Finset (Fin D.rank) := Finset.univ.filter (fun i => i ∈ I) with hs
    have hsI : ∀ i ∈ s, i ∈ I := fun i hi => (Finset.mem_filter.1 hi).2
    have hAcard : ∀ i, Nat.card (A i) ∣ 6 := fun i =>
      (Subgroup.card_map_dvd (rankOne D.rootGroup i) π').trans (hnode i)
    have hsup : ∀ t : Finset (Fin D.rank), (∀ i ∈ t, i ∈ I) →
        ∃ N : ℕ, Nat.card ↥(t.sup A) ∣ 6 ^ N := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        intro _
        refine ⟨0, ?_⟩
        simp
      | insert j t hjt ih =>
        intro ht
        obtain ⟨N, hN⟩ := ih (fun i hi => ht i (Finset.mem_insert_of_mem hi))
        refine ⟨N + 1, ?_⟩
        rw [Finset.sup_insert]
        have hjI : j ∈ I := ht j (Finset.mem_insert_self _ _)
        have hle : t.sup A ≤ Subgroup.centralizer ((A j : Subgroup Y) : Set Y) := by
          refine Finset.sup_le fun i hi => ?_
          have hij : j ≠ i := fun e => hjt (e ▸ hi)
          exact commutes_iff_le_centralizer.1
            (hcomm' i (ht i (Finset.mem_insert_of_mem hi)) j hjI (Ne.symm hij))
        have hcm : Commutes (A j) (t.sup A) := (commutes_iff_le_centralizer.2 hle).symm
        have hnorm : A j ≤ Subgroup.normalizer ((t.sup A : Subgroup Y) : Set Y) :=
          (commutes_iff_le_centralizer.1 hcm).trans (Subgroup.centralizer_le_normalizer _)
        refine (card_sup_dvd_mul (A j) (t.sup A) hnorm).trans ?_
        rw [pow_succ']
        exact mul_dvd_mul (hAcard j) hN
    obtain ⟨N, hN⟩ := hsup s hsI
    have hΛs : Λ ≤ s.sup A := iSup₂_le fun i hi =>
      Finset.le_sup (f := A) (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
    have hΛcard : Nat.card Λ ∣ 6 ^ N := (Subgroup.card_dvd_of_le hΛs).trans hN
    have hBU' : (borel D H).map π' ≤ (posUnipotent D).map π' := Subgroup.map_mono hBU
    obtain ⟨c, hc⟩ := (hU2.to_le hBU').exists_card_eq
    have hJdvd : Nat.card J ∣ Nat.card Λ * Nat.card ((borel D H).map π') :=
      card_dvd_mul_of_forall_mem_mul hΛJ hBJ hprod
    have hJdvd' : Nat.card J ∣ 2 ^ (N + c) * 3 ^ N := by
      refine hJdvd.trans ?_
      rw [hc]
      have : 6 ^ N = 2 ^ N * 3 ^ N := by rw [← mul_pow]; norm_num
      rw [this] at hΛcard
      calc Nat.card Λ * 2 ^ c ∣ (2 ^ N * 3 ^ N) * 2 ^ c := mul_dvd_mul_right hΛcard _
        _ = 2 ^ (N + c) * 3 ^ N := by ring
    obtain ⟨d1, d2, hd1, hd2, hd⟩ := Nat.dvd_mul.1 hJdvd'
    obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd2
    have : Fintype J := Fintype.ofFinite J
    have hsolv : Group.IsSolvable J :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) (a := a) (b := b)
        (by rw [← Nat.card_eq_fintype_card, ← hd])
    have hKperf : ⁅K', K'⁆ = K' := perfectJoin_perfect J
    have : Group.IsSolvable K' :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (perfectJoin_le J))
        (Subgroup.inclusion_injective _)
    have hnt : Nontrivial K' := (Subgroup.nontrivial_iff_ne_bot K').2 hK
    have : Group.IsPerfect K' := Subgroup.isPerfect_iff.2 hKperf
    exact Group.IsPerfect.not_isSolvable K' inferInstance

end Main

section D8

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame

theorem three_mem_perfectJoin_of_model_d8 {X : Type} [Group X] [Finite X]
    (h : StatedClassicalModel X .POmegaPlus 4 2 1) (T : Sylow 2 X) (J : Subgroup X)
    (hNJ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ J) (hK : perfectJoin J ≠ ⊥) :
    ∀ y ∈ J, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ∈ perfectJoin J := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have hn3 : 3 ≤ 4 := by norm_num
  have : NeZero 4 := ⟨by norm_num⟩
  have : Finite (spinGroup (quadPlus 4 F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := 4) (K := F))
  have hB := borelQuotient_spinPlus (n := 4) (F := F) hn3 e
  refine hB.three_mem_perfectJoin (by rw [hF2]) ?_ ?_ ?_ ?_ T J hNJ hK
  · intro i
    obtain ⟨ρ, -, hU, hL⟩ := SpinPlus.rankOne (K := F) hn3 i
    have hpar := SpinPlus.isParametrization (K := F) hn3
    rw [rankOne_eq_range_of_sl2 hpar hU hL]
    exact (Subgroup.card_range_dvd ρ).trans (by rw [card_sl2, hF2]; norm_num)
  · intro i j hij hA
    exact commutes_rankOne_of_cartan_eq_zero hB.extras hij hA
  · intro i j hij hA
    obtain ⟨h1, h2⟩ := cartanD_eq_neg_one hij hA
    exact commutator_rankOne_sup_eq_of_param hB.ct hB.extras (SpinPlus.isParametrization hn3) hF2
      hij h1 h2 ⟨1, 1, spinPlus_commutator_ne_one hn3 hij h2⟩
  · have key : ∀ i j k : Fin 4, i ≠ j → cartanD 4 i j ≠ 0 →
        k = i ∨ k = j ∨ (k ≠ i ∧ cartanD 4 i k ≠ 0) ∨ (k ≠ j ∧ cartanD 4 j k ≠ 0) := by
      intro i j k
      fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [cartanD]
    intro i j k hij hA
    exact key i j k hij hA

end D8

end CFSG.HardMathSupport.Curtis.UnitaryLevi
