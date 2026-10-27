module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1G2Par
public import CFSG.Quasithin.Vol2.F134LieG2Borel
public import CFSG.LieType.Chevalley.OrdinaryExceptionalOuterTwoPart

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.Blueprint
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)



theorem threeNineOut_G2 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hG : ChevalleyExceptionalModel G .G2 p 1) :
    Subgroup.center G = ⊥ ∧ ¬ p ∣ Nat.card (Outer G) ∧
      (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (Outer G) → q = 3) ∧ 3 ∣ Nat.card G := by
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (G := G) .G2 hG.2
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hKp : Nat.card K = p := by simpa using hKcard
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hZ : Subgroup.center G = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmap
  have hOutC : Nat.card (Outer (adjointGroup .G2 K)) = 1 := by
    obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
      CFSG.LieType.Chevalley.odd_F4_and_nonexceptional_G2_automorphism_normal_form
        hp hp2 (le_refl 1) K (by simpa using hKp) .G2 (Or.inr ⟨rfl, hp3⟩)
    rw [CFSG.LieType.Chevalley.card_outer_eq_of_ker_eq_inner Θ hsurj hker]
    rw [(CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (n := 1) hp K
      (by simpa using hKp)).1]
  have hOutG : Nat.card (Outer G) = 1 := by
    rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e, hOutC]
  have hcardG : Nat.card G = ordG2 (p ^ 1) :=
    CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hG.2
  refine ⟨hZ, ?_, ?_, ?_⟩
  · rw [hOutG]
    exact Nat.Prime.not_dvd_one hp
  · intro q hq hq2 hdvd
    rw [hOutG] at hdvd
    exact absurd hdvd (Nat.Prime.not_dvd_one hq)
  · rw [hcardG, CFSG.Open.ordG2]
    exact dvd_trans (by norm_num : 3 ∣ 27)
      (CFSG.HardMathSupport.Lang.E27Lie.twentySeven_dvd_ordG2 (p ^ 1))

private theorem fin_two_eq_of_ne :
    ∀ a b c : Fin Tag.G2.rank, a ≠ c → b ≠ c → b = a := by decide

private theorem geomSum_six_one (p : ℕ) :
    CFSG.Timmesfeld.ExceptionalOrders.geomSum 6 1 p = (p + 1) * (p ^ 4 + p ^ 2 + 1) := by
  unfold CFSG.Timmesfeld.ExceptionalOrders.geomSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one]
  ring

private theorem not_dvd_card_borelGroup_G2 {K : Type} [Field K] [Finite K] {p d : ℕ}
    (hp : p.Prime) (hd : d.Prime) (hdp : d ≠ p) (hKp : Nat.card K = p)
    (hnd : ¬ d ∣ p - 1) :
    ¬ d ∣ Nat.card (borelGroup .G2 K) := by
  have hcard := card_borelGroup (τ := .G2) (K := K)
  have htor := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2 (K := K)
  have hUB := card_posUnipotent (τ := .G2) (K := K)
  rw [CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2] at hUB
  rw [hcard, htor, hUB, hKp]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hd).1 hdvd with h | h
  · exact hnd (hd.dvd_of_dvd_pow h)
  · exact hdp ((Nat.prime_dvd_prime_iff_eq hd hp).1 (hd.dvd_of_dvd_pow h))

private theorem card_parabolicSubgroup_singleton_G2 {K : Type} [Field K] [Finite K]
    {p : ℕ} (hKp : Nat.card K = p) (i : Fin Tag.G2.rank) :
    Nat.card ↥(parabolicSubgroup .G2 K ({i} : Set (Fin Tag.G2.rank))) =
      Nat.card (borelGroup .G2 K) * (p + 1) := by
  rw [CFSG.Quasithin.F134.LieG2.card_parabolicSubgroup_singleton, hKp]

private theorem relIndex_parabolicSubgroup_singleton_G2 {K : Type} [Field K] [Finite K]
    {p : ℕ} (hKp : Nat.card K = p) (i : Fin Tag.G2.rank) :
    (parabolicSubgroup .G2 K ({i} : Set (Fin Tag.G2.rank))).relIndex
        (adjointGroup .G2 K) =
      CFSG.Timmesfeld.ExceptionalOrders.geomSum 6 1 p := by
  classical
  have : Fintype (WeylGroup .G2) := Fintype.ofFinite _
  have h := CFSG.LieType.SeitzGeneration.parabolicSum_univ_eq_mul_index (τ := .G2)
    (K := K) ({i} : Set (Fin Tag.G2.rank))
  have hsum_univ : CFSG.Timmesfeld.ExceptionalOrders.parabolicSum .G2 Set.univ
      (Nat.card K) = (Nat.card K + 1) *
        CFSG.Timmesfeld.ExceptionalOrders.geomSum 6 1 (Nat.card K) := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.parabolicSum_univ,
      CFSG.Timmesfeld.ExceptionalOrders.sum_length_G2]
    congr 1
    unfold CFSG.Timmesfeld.ExceptionalOrders.geomSum
    simp
  have hsum_i : CFSG.Timmesfeld.ExceptionalOrders.parabolicSum .G2
      ({i} : Set (Fin Tag.G2.rank)) (Nat.card K) = Nat.card K + 1 := by
    unfold CFSG.Timmesfeld.ExceptionalOrders.parabolicSum
    rw [CFSG.Timmesfeld.ExceptionalOrders.parabolic_eq_parabolicWeylGroup]
    have hset : Finset.univ.filter (fun w : WeylGroup .G2 =>
        w ∈ parabolicWeylGroup .G2 ({i} : Set (Fin Tag.G2.rank))) =
          {1, simple .G2 i} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hw
        exact mem_parabolicWeylGroup_singleton hw
      · rintro (rfl | rfl)
        · exact one_mem _
        · exact Subgroup.subset_closure ⟨i, rfl, rfl⟩
    rw [hset]
    have hne : (1 : WeylGroup .G2) ≠ simple .G2 i := by
      intro h
      have := congrArg (coxeterSystem .G2).length h
      rw [(coxeterSystem .G2).length_one, (coxeterSystem .G2).length_simple] at this
      omega
    rw [Finset.sum_pair hne, (coxeterSystem .G2).length_one,
      (coxeterSystem .G2).length_simple]
    ring
  rw [hsum_univ, hsum_i] at h
  have hpos : 0 < Nat.card K + 1 := Nat.succ_pos _
  have heq := Nat.eq_of_mul_eq_mul_left hpos h
  have heq' : (parabolicSubgroup .G2 K ({i} : Set (Fin Tag.G2.rank))).relIndex
      (adjointGroup .G2 K) =
        CFSG.Timmesfeld.ExceptionalOrders.geomSum 6 1 (Nat.card K) := heq.symm
  rwa [hKp] at heq'

private theorem exists_conj_borel_le {G : Type} [Group G] [Finite G] {p d : ℕ}
    {Y : Subgroup G} (hp : p.Prime) (hG : ChevalleyExceptionalModel G .G2 p 1)
    (h : IsBorelDLocal p d Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : G ≃* adjointGroup .G2 K)
      (Y' : Subgroup ↥(adjointGroup .G2 K)),
      Nat.card K = p ∧ IsBorelDLocal p d Y' ∧
      (borelGroup .G2 K).subgroupOf (adjointGroup .G2 K) ≤ Y' := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (G := G) .G2 hG.2
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hKp : Nat.card K = p := by simpa using hKcard
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (le_refl 1)
      (by simpa using hKp)
  haveI : Finite (adjointGroup .G2 K) := Subtype.finite
  have hY : IsBorelDLocal p d (Y.map e.toMonoidHom) := h.map_equiv e
  have hUC : posUnipotent .G2 K ≤ adjointGroup .G2 K := posUnipotent_le_adjointGroup
  have hU := card_posUnipotent (τ := .G2) (K := K)
  have hUp : IsPGroup p ↥((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)) :=
    (isPGroup_and_not_dvd_index p hUC hU).1
  have hUi : ¬ p ∣ ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)).index :=
    (isPGroup_and_not_dvd_index p hUC hU).2
  let P0 : Sylow p ↥(adjointGroup .G2 K) := hUp.toSylow hUi
  obtain ⟨g, hYg, hNle⟩ := IsBorelDLocal.exists_conj hp hY P0
  set Y' : Subgroup ↥(adjointGroup .G2 K) :=
    (Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom with hY'def
  have hBsN : adjointGroup .G2 K ⊓
      Subgroup.normalizer (posUnipotent .G2 K : Set (ModGL .G2 K)) = borelGroup .G2 K :=
    (borel_self_normalizers .G2 K).1
  have hNUC : Subgroup.normalizer
      (((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) : Subgroup ↥(adjointGroup .G2 K)) :
        Set ↥(adjointGroup .G2 K)) = (borelGroup .G2 K).subgroupOf (adjointGroup .G2 K) := by
    rw [← Subgroup.subgroupOf_normalizer_eq (H := posUnipotent .G2 K)
      (N := adjointGroup .G2 K) hUC]
    rw [← Subgroup.inf_subgroupOf_left (Subgroup.normalizer
      (posUnipotent .G2 K : Set (ModGL .G2 K))) (adjointGroup .G2 K), hBsN]
  have hP0coe : ((P0 : Subgroup ↥(adjointGroup .G2 K))) =
      (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) := IsPGroup.toSylow_coe hUp hUi
  have hBle : (borelGroup .G2 K).subgroupOf (adjointGroup .G2 K) ≤ Y' := by
    have h := hNle
    rw [hP0coe, hNUC] at h
    exact h
  exact ⟨K, hKfield, hKfin, e, Y', hKp, hYg, hBle⟩

private theorem exists_parabolic_eq_of_borel_le {K : Type} [Field K]
    {Y' : Subgroup ↥(adjointGroup .G2 K)}
    (hBle : (borelGroup .G2 K).subgroupOf (adjointGroup .G2 K) ≤ Y') :
    ∃ J : Set (Fin Tag.G2.rank),
      Y' = (parabolicSubgroup .G2 K J).subgroupOf (adjointGroup .G2 K) := by
  obtain ⟨J, hJ⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.exists_PG_eq K hBle
  exact ⟨J, hJ⟩

private theorem eq_empty_or_exists_singleton_of_ne_univ {J : Set (Fin Tag.G2.rank)}
    (hJ : J ≠ Set.univ) : J = ∅ ∨ ∃ i, J = {i} := by
  by_cases hJ0 : J = ∅
  · exact Or.inl hJ0
  · right
    obtain ⟨i, hiJ⟩ := Set.nonempty_iff_ne_empty.mpr hJ0
    obtain ⟨k, hkJ⟩ : ∃ k : Fin Tag.G2.rank, k ∉ J := by
      by_contra hcon
      push Not at hcon
      exact hJ (Set.eq_univ_of_forall hcon)
    refine ⟨i, ?_⟩
    ext j
    constructor
    · intro hj
      by_contra hji
      have hik : i ≠ k := fun h => hkJ (h ▸ hiJ)
      have hjk_ne : j ≠ k := fun h => hkJ (h ▸ hj)
      exact hji (fin_two_eq_of_ne i j k hik hjk_ne)
    · intro hj
      rw [Set.mem_singleton_iff] at hj
      exact hj ▸ hiJ

private theorem normalizer_torus_le_of_dvd_sub_one {K : Type} [Field K] [Finite K]
    {p d : ℕ} {Y' : Subgroup ↥(adjointGroup .G2 K)}
    (hp : p.Prime) (hKp : Nat.card K = p) (hd : d.Prime)
    (hYg : IsBorelDLocal p d Y')
    (hBle : (borelGroup .G2 K).subgroupOf (adjointGroup .G2 K) ≤ Y')
    (hdp1 : d ∣ p - 1) :
    Subgroup.normalizer ((torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) : Set
      ↥(adjointGroup .G2 K)) ≤ Y' := by
  let H : Subgroup ↥(adjointGroup .G2 K) :=
    (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)
  have hHC : H ≤ Y' := by
    have hHB : H ≤ (borelGroup .G2 K).subgroupOf (adjointGroup .G2 K) :=
      Subgroup.subgroupOf_mono _ torusGroup_le_borelGroup
    exact hHB.trans hBle
  have hHab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    have hx' : (x : ModGL .G2 K) ∈ torusGroup .G2 K := by
      simpa [H, Subgroup.mem_subgroupOf] using hx
    have hy' : (y : ModGL .G2 K) ∈ torusGroup .G2 K := by
      simpa [H, Subgroup.mem_subgroupOf] using hy
    exact mul_comm_of_mem_diagonalGroup
      (torusGroup_le_diagonalGroup hx') (torusGroup_le_diagonalGroup hy')
  have hHdvd : d ∣ Nat.card H := by
    have hHcard : Nat.card H = (p - 1) ^ 2 := by
      rw [show Nat.card H = Nat.card (torusGroup .G2 K) from
        card_subgroupOf_of_le (torusGroup_le_borelGroup.trans borelGroup_le_adjointGroup')]
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2, hKp]
    rw [hHcard, pow_two]
    exact dvd_mul_of_dvd_left hdp1 (p - 1)
  exact IsBorelDLocal.normalizer_le_of_dvd hd hYg hHC hHab hHdvd

private theorem exists_weyl_mem_normalizer_torus_not_mem {K : Type} [Field K]
    {Y' : Subgroup ↥(adjointGroup .G2 K)} {J : Set (Fin Tag.G2.rank)}
    (hYeq : Y' = (parabolicSubgroup .G2 K J).subgroupOf (adjointGroup .G2 K))
    (hJ : J ≠ Set.univ) :
    ∃ n : ↥(adjointGroup .G2 K),
      n ∈ Subgroup.normalizer ((torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) : Set
        ↥(adjointGroup .G2 K)) ∧ n ∉ Y' := by
  obtain ⟨i, hiJ⟩ : ∃ i : Fin Tag.G2.rank, i ∉ J := by
    by_contra hcon
    push Not at hcon
    exact hJ (Set.eq_univ_of_forall hcon)
  have hweylC : weylElt .G2 K i 1 ∈ adjointGroup .G2 K := weylElt_mem_adjointGroup i 1
  let n : ↥(adjointGroup .G2 K) := ⟨weylElt .G2 K i 1, hweylC⟩
  have hnN : n ∈ Subgroup.normalizer
      ((torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) : Set
        ↥(adjointGroup .G2 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have hnNorm := weylElt_mem_normalizer_torus .G2 K i 1
      have hmem := (Subgroup.mem_normalizer_iff.1 hnNorm (y : ModGL .G2 K)).1 hy
      simpa [n, torusGroup, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have hnNorm := weylElt_mem_normalizer_torus .G2 K i 1
      refine (Subgroup.mem_normalizer_iff.1 hnNorm (y : ModGL .G2 K)).2 ?_
      simpa [n, torusGroup, Subgroup.coe_mul, Subgroup.coe_inv] using hy
  have hnNot : n ∉ Y' := by
    rw [hYeq, Subgroup.mem_subgroupOf]
    intro hn
    exact hiJ ((weylElt_mem_parabolicSubgroup_iff (τ := .G2) (K := K) (J := J)
      (i := i)).1 (by simpa [n] using hn))
  exact ⟨n, hnN, hnNot⟩

private theorem false_of_dvd_sub_one {K : Type} [Field K] [Finite K] {p d : ℕ}
    {Y' : Subgroup ↥(adjointGroup .G2 K)} {J : Set (Fin Tag.G2.rank)}
    (hp : p.Prime) (hKp : Nat.card K = p) (hd : d.Prime)
    (hYg : IsBorelDLocal p d Y')
    (hYeq : Y' = (parabolicSubgroup .G2 K J).subgroupOf (adjointGroup .G2 K))
    (hJ : J ≠ Set.univ) (hdp1 : d ∣ p - 1) : False := by
  have hBle : (borelGroup .G2 K).subgroupOf (adjointGroup .G2 K) ≤ Y' := by
    rw [hYeq]
    exact Subgroup.subgroupOf_mono _ (borelGroup_le_parabolicSubgroup J)
  have hNle := normalizer_torus_le_of_dvd_sub_one hp hKp hd hYg hBle hdp1
  obtain ⟨n, hnN, hnNot⟩ := exists_weyl_mem_normalizer_torus_not_mem hYeq hJ
  exact hnNot (hNle hnN)

private theorem false_of_not_dvd_sub_one {K : Type} [Field K] [Finite K] {p d : ℕ}
    {Y' : Subgroup ↥(adjointGroup .G2 K)} {J : Set (Fin Tag.G2.rank)}
    (hp : p.Prime) (hKp : Nat.card K = p) (hd : d.Prime) (hdp : d ≠ p)
    (hYg : IsBorelDLocal p d Y')
    (hYeq : Y' = (parabolicSubgroup .G2 K J).subgroupOf (adjointGroup .G2 K))
    (hJ : J ≠ Set.univ) (hdY : d ∣ Nat.card Y') (hndY : ¬ d ∣ Y'.index)
    (hdp1 : ¬ d ∣ p - 1) : False := by
  have hBnot := not_dvd_card_borelGroup_G2 hp hd hdp hKp hdp1
  rcases eq_empty_or_exists_singleton_of_ne_univ hJ with hJ0 | ⟨i, hJi⟩
  · have hcardY : Nat.card ↥Y' = Nat.card (borelGroup .G2 K) := by
      rw [hYeq, hJ0, parabolicSubgroup_empty]
      exact card_subgroupOf_of_le borelGroup_le_adjointGroup'
    exact hBnot (hcardY ▸ hdY)
  · have hcardY : Nat.card ↥Y' = Nat.card (borelGroup .G2 K) * (p + 1) := by
      rw [hYeq, hJi]
      rw [show Nat.card ↥((parabolicSubgroup .G2 K
          ({i} : Set (Fin Tag.G2.rank))).subgroupOf (adjointGroup .G2 K)) =
          Nat.card ↥(parabolicSubgroup .G2 K ({i} : Set (Fin Tag.G2.rank))) from
        card_subgroupOf_of_le (parabolicSubgroup_le_adjointGroup .G2 K _)]
      exact card_parabolicSubgroup_singleton_G2 hKp i
    have hdvd_p1 : d ∣ p + 1 := by
      have h := hdY
      rw [hcardY] at h
      rcases (Nat.Prime.dvd_mul hd).1 h with hB | hp1
      · exact absurd hB hBnot
      · exact hp1
    have hYindex : Y'.index = CFSG.Timmesfeld.ExceptionalOrders.geomSum 6 1 p := by
      rw [hYeq, hJi]
      change (parabolicSubgroup .G2 K ({i} : Set (Fin Tag.G2.rank))).relIndex
        (adjointGroup .G2 K) = _
      exact relIndex_parabolicSubgroup_singleton_G2 hKp i
    have hdvd_index : d ∣ Y'.index := by
      rw [hYindex, geomSum_six_one]
      exact dvd_mul_of_dvd_left hdvd_p1 _
    exact hndY hdvd_index

theorem not_isBorelDLocal_G2 {G : Type} [Group G] [Finite G] {p d : ℕ} {Y : Subgroup G}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ≠ p)
    (hdG : d ∣ Nat.card G) (hG : ChevalleyExceptionalModel G .G2 p 1) :
    ¬ IsBorelDLocal p d Y := by
  intro h
  obtain ⟨K, hKfield, hKfin, e, Y', hKp, hYg, hBle⟩ := exists_conj_borel_le hp hG h
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨J, hYeq⟩ := exists_parabolic_eq_of_borel_le hBle
  have hJ : J ≠ Set.univ := by
    intro hJtop
    have htop : Y' = ⊤ := by
      rw [hYeq, hJtop, (standard_parabolic_cells .G2 K).2.2.2.2.2.1]
      exact Subgroup.subgroupOf_self (H := adjointGroup .G2 K)
    exact hYg.lt_top.ne htop
  have hdC : d ∣ Nat.card ↥(adjointGroup .G2 K) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hdG
  have hndY : ¬ d ∣ Y'.index := IsBorelDLocal.not_dvd_index hd hYg
  have hdY : d ∣ Nat.card ↥Y' := by
    have hmul := Subgroup.card_mul_index Y'
    rw [← hmul] at hdC
    rcases (Nat.Prime.dvd_mul hd).1 hdC with hc | hc
    · exact hc
    · exact absurd hc hndY
  by_cases hdp1 : d ∣ p - 1
  · exact false_of_dvd_sub_one hp hKp hd hYg hYeq hJ hdp1
  · exact false_of_not_dvd_sub_one hp hKp hd hdp hYg hYeq hJ hdY hndY hdp1

end CFSG.LocalAnalysis.AGL81I.Section3
