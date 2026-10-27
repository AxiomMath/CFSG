module

public import CFSG.LieType.OutStructureTwistedAN
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCLin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCUni
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubLinRank

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.GorensteinLyons.LinearUnitaryOuter
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Assembly.LowTwoRank

theorem not_dvd_totient_of_lt_two_mul {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : m < 2 * p) (hpm : ¬ p ∣ m) : ¬ p ∣ Nat.totient m := by
  intro h
  rw [Nat.totient_eq_div_primeFactors_mul] at h
  have hmpos : 0 < m := by
    by_contra h0
    have : m = 0 := by omega
    exact hpm (by rw [this]; exact dvd_zero p)
  have h1 : ¬ p ∣ m / ∏ q ∈ m.primeFactors, q := by
    intro hd
    exact hpm (hd.trans (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_dvd m)))
  rcases hp.dvd_mul.mp h with h2 | h2
  · exact h1 h2
  · obtain ⟨q, hq, hpq⟩ :=
      (hp.prime.dvd_finsetProd_iff (fun q => q - 1)).mp h2
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
    have hqle : q ≤ m := Nat.le_of_dvd hmpos hqm
    have hqlt : q < 2 * p := lt_of_le_of_lt hqle hm
    have hqne : q ≠ p := fun hqp => hpm (hqp ▸ hqm)
    have hq2 : 2 ≤ q := hqprime.two_le
    have hpqle : p ≤ q - 1 := Nat.le_of_dvd (by omega) hpq
    obtain ⟨k, hk⟩ := hpq
    have hkq : q = p * k + 1 := by omega
    have hkpos : 0 < k := by
      by_contra hk0
      have hk' : k = 0 := by omega
      rw [hk', mul_zero] at hk
      have : q = 1 := by omega
      exact hqprime.ne_one this
    have hklt : k < 2 := by
      nlinarith [hkq, hqlt, hp.pos]
    have hk1 : k = 1 := by omega
    have hqeq : q = p + 1 := by
      rw [hk1, mul_one] at hk
      omega
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    obtain ⟨t, ht⟩ := hpodd
    have hqeven : Even q := ⟨t + 1, by rw [hqeq, ht]; ring⟩
    have hqodd : Odd q := hqprime.odd_of_ne_two (by omega)
    exact (Nat.not_even_iff_odd.mpr hqodd) hqeven

theorem sylow_normal_of_normal_cyclic_of_card_lt_two_mul {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (D C : Subgroup G) (hDn : D.Normal)
    (hDcyc : IsCyclic ↥D) (hDlt : Nat.card D < 2 * p) (hpD : ¬ p ∣ Nat.card D)
    (hab : ∀ x y : G ⧸ D, x * y = y * x)
    (hCp : IsPGroup p C) (hidx : ¬ p ∣ C.index) :
    ∀ S : Sylow p G, (S : Subgroup G).Normal := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : D.Normal := hDn
  haveI : IsCyclic ↥D := hDcyc
  have hAutD : ¬ p ∣ Nat.card (MulAut ↥D) := by
    rw [IsCyclic.card_mulAut]
    exact not_dvd_totient_of_lt_two_mul hp hp2 hDlt hpD
  let ψ : C →* MulAut D := (MulAut.conjNormal).comp C.subtype
  have hψp : IsPGroup p ψ.range := by
    rw [isPGroup_iff_pow_pow_eq_one]
    rintro ⟨y, c, rfl⟩
    obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hCp) c
    refine ⟨k, Subtype.ext ?_⟩
    change (ψ c) ^ (p ^ k) = 1
    rw [← map_pow, hk, map_one]
  have hψdvd : Nat.card ψ.range ∣ Nat.card (MulAut D) := Subgroup.card_subgroup_dvd_card _
  have hψnot : ¬ p ∣ Nat.card ψ.range := fun h => hAutD (h.trans hψdvd)
  have hψbot : ψ.range = ⊥ := by
    obtain ⟨k, hk⟩ := hψp.exists_card_eq
    have hk0 : k = 0 := by
      by_contra hkne
      exact hψnot (hk ▸ dvd_pow_self p hkne)
    have hcard : Nat.card ψ.range = 1 := by rw [hk, hk0, pow_zero]
    exact Subgroup.eq_bot_of_card_eq _ hcard
  have hcentCD : C ≤ Subgroup.centralizer (D : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : ψ ⟨c, hc⟩ = 1 := by
      have hmem : ψ ⟨c, hc⟩ ∈ ψ.range := ⟨_, rfl⟩
      rw [hψbot] at hmem
      exact hmem
    have h2 := congrArg (fun f : MulAut D => f ⟨d, hd⟩) h1
    have h2' := congrArg (fun x : D => (x : G)) h2
    have h3 : c * d * c⁻¹ = d := by
      simpa [ψ, MulAut.conjNormal_apply] using h2'
    calc d * c = (c * d * c⁻¹) * c := by rw [h3]
      _ = c * d := by group
  have hCDnorm : (C ⊔ D).Normal := by
    let mk : G →* G ⧸ D := QuotientGroup.mk' D
    have hmap' : (C ⊔ D).map mk = C.map mk := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    have hpre : (C.map mk).comap mk = C ⊔ D := by
      rw [← hmap']
      exact Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact le_sup_right)
    rw [← hpre]
    haveI : IsMulCommutative (G ⧸ D) := IsMulCommutative.of_comm hab
    exact (inferInstance : (C.map mk).Normal).comap mk
  have hp_sub_C : ∀ {Q : Subgroup G}, Q ≤ C ⊔ D → IsPGroup p Q → Q ≤ C := by
    intro Q hQH hQ x hx
    obtain ⟨c, hc, d, hd, hcd⟩ := Subgroup.mem_sup_of_normal_right.mp (hQH hx)
    have hcomm_cd : Commute c d := by
      have hcent := hcentCD hc
      exact (Subgroup.mem_centralizer_iff.mp hcent d hd).symm
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨x, hx⟩
    obtain ⟨k, hck⟩ := (IsPGroup.iff_orderOf.mp hCp) ⟨c, hc⟩
    have hxord : orderOf x = p ^ n := by
      have h := hn
      rwa [Subgroup.orderOf_mk x hx] at h
    have hck' : orderOf c = p ^ k := by
      have h := hck
      rwa [Subgroup.orderOf_mk c hc] at h
    have hDp : ¬ p ∣ orderOf d := by
      have hdvd : orderOf d ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hd
      exact fun h => hpD (h.trans hdvd)
    have hcop : Nat.Coprime (orderOf c) (orderOf d) := by
      rw [hck']
      exact (hp.coprime_pow_of_not_dvd hDp).symm
    have hordmul : orderOf (c * d) = orderOf c * orderOf d :=
      hcomm_cd.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    have hprod : orderOf c * orderOf d = p ^ n := by
      rw [← hordmul, hcd, hxord]
    have hddiv : orderOf d ∣ p ^ n := by
      rw [← hprod]
      exact dvd_mul_left _ _
    obtain ⟨m', -, hdm⟩ := (Nat.dvd_prime_pow hp).mp hddiv
    have hm'0 : m' = 0 := by
      by_contra hm'ne
      exact hDp (by rw [hdm]; exact dvd_pow_self p hm'ne)
    have hd1 : d = 1 := orderOf_eq_one_iff.mp (by rw [hdm, hm'0, pow_zero])
    rw [hd1, mul_one] at hcd
    exact hcd.symm ▸ hc
  have hCpH : IsPGroup p (C.subgroupOf (C ⊔ D)) :=
    hCp.comap_of_injective (C ⊔ D).subtype (C ⊔ D).subtype_injective
  have hCcharH : (C.subgroupOf (C ⊔ D)).Characteristic := by
    refine Subgroup.characteristic_iff_map_eq.mpr ?_
    intro φH
    have himg_p : IsPGroup p ((C.subgroupOf (C ⊔ D)).map φH.toMonoidHom) :=
      hCpH.map φH.toMonoidHom
    have hle : ((C.subgroupOf (C ⊔ D)).map φH.toMonoidHom) ≤ C.subgroupOf (C ⊔ D) := by
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      have hQH : ((C.subgroupOf (C ⊔ D)).map φH.toMonoidHom).map (C ⊔ D).subtype ≤ C ⊔ D := by
        intro z hz
        obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp hz
        exact w.2
      have hQp : IsPGroup p (((C.subgroupOf (C ⊔ D)).map φH.toMonoidHom).map
          (C ⊔ D).subtype) := himg_p.map (C ⊔ D).subtype
      have hsub := hp_sub_C hQH hQp (Subgroup.mem_map_of_mem (C ⊔ D).subtype hy)
      exact hsub
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective φH.injective]
  have hCnorm : C.Normal := by
    haveI hCDnormal : (C ⊔ D).Normal := hCDnorm
    haveI : (C.subgroupOf (C ⊔ D)).Characteristic := hCcharH
    haveI : ((C.subgroupOf (C ⊔ D)).map (C ⊔ D).subtype).Normal := inferInstance
    rwa [Subgroup.map_subgroupOf_eq_of_le (le_sup_left : C ≤ C ⊔ D)] at this
  intro S'
  let PC : Sylow p G := hCp.toSylow hidx
  haveI : Unique (Sylow p G) := Sylow.unique_of_normal PC hCnorm
  have hS' : S' = PC := Subsingleton.elim S' PC
  rw [hS']
  exact hCnorm

theorem pRank_projectiveSL_formula {N : ℕ} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hN : 1 ≤ N)
    (hpK : ¬ p ∣ Nat.card K) (hdiv : ¬ p ∣ Nat.gcd N (Nat.card K - 1)) :
    CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL N K)) =
      if p ∣ Nat.card K - 1 then N - 1 else N / orderOf (Nat.card K : ZMod p) := by
  let e : projectiveSL N K ≃* StatedProj (StatedSL N K) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL N K).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj N K)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_SL_formula
    hp hp2 hN hpK hdiv

theorem two_le_pRank_projectiveSL_of_charP {N : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hN : 3 ≤ N) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL N K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let e : projectiveSL N K ≃* StatedProj (StatedSL N K) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL N K).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj N K)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  rcases (show N = 3 ∨ 4 ≤ N by omega) with rfl | h4
  · have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := 3) (a := 1) (b := 2)
      (p := p) (f := f) (by norm_num) (by norm_num) hK
    omega
  · have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := N) (a := 2) (b := 2)
      (p := p) (f := f) (by norm_num) h4 hK
    omega

theorem pRank_primeFormP_formula {p₀ f N : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p₀ f K) (hN : 1 ≤ N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ p₀ ^ f) (hdiv : ¬ p ∣ Nat.gcd N (p₀ ^ f + 1)) :
    CFSG.Open.pRank p (⊤ : Subgroup (primeFormP h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))) =
      if p ∣ p₀ ^ f + 1 then N - 1 else N / orderOf (-((p₀ ^ f : ℕ) : ZMod p)) := by
  let ePU : primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) ≃*
      unitaryPSU h N := Classical.choice (nonempty_primeFormP_mulEquiv h isPrimeFormGram_one)
  let ePS : unitaryPSU h N ≃*
      StatedProj (StatedSU N (p₀ ^ f) K) := unitaryPSUEquiv h hN
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (ePU.trans ePS)]
  have hcard : Nat.card K = (p₀ ^ f) ^ 2 := by
    rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_SU_formula
    hp hp2 h.prime ⟨f, rfl⟩ hN hcard hpq hdiv

theorem two_le_pRank_primeFormP_of_charP {p₀ f N : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p₀ f K) (hp2 : p₀ ≠ 2) (hN : 3 ≤ N) :
    2 ≤ CFSG.Open.pRank p₀ (⊤ : Subgroup (primeFormP h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))) := by
  haveI : Fact p₀.Prime := ⟨h.prime⟩
  let ePU : primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) ≃*
      unitaryPSU h N := Classical.choice (nonempty_primeFormP_mulEquiv h isPrimeFormGram_one)
  let ePS : unitaryPSU h N ≃*
      StatedProj (StatedSU N (p₀ ^ f) K) := unitaryPSUEquiv h (by omega)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv h.prime.one_lt (ePU.trans ePS)]
  have hcard : Nat.card K = (p₀ ^ f) ^ 2 := by
    rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
  have hf : 1 ≤ f := h.one_le
  rcases (show N = 3 ∨ 4 ≤ N by omega) with rfl | h4
  · have hh := CFSG.SectionRank.ClassicalOdd.two_mul_le_pRank_SU_three
      (p := p₀) (f := f) (K := K) hp2 hcard
    omega
  · have hh := CFSG.SectionRank.ClassicalOdd.four_mul_le_pRank_SU
      (n := N) (p := p₀) (f := f) (K := K) hp2 h4 hcard
    omega

theorem linear_outer_sylow_normal (N : ℕ) (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hN : 3 ≤ N)
    (hpRank : CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL N K)) ≤ 1) :
    ∀ S : Sylow p (Outer (projectiveSL N K)),
      (S : Subgroup (Outer (projectiveSL N K))).Normal := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hgcd : ¬ p ∣ Nat.gcd N (Nat.card K - 1) := by
    intro hdvd
    have h2 := GL83.I713.two_le_pRank_projectiveSL_of_dvd (K := K) (n := N) hN hp hp2 hdvd
    omega
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, hp0, hKcard⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp0⟩
  have hKcard' : Nat.card K = ringChar K ^ (e : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hKcard
  have hepos : 1 ≤ e := e.pos
  have hpchar : ringChar K ≠ p := by
    intro hchar
    haveI : CharP K p := by
      rw [← hchar]
      exact ringChar.charP K
    have hKcardp : Nat.card K = p ^ (e : ℕ) := by rw [hKcard', hchar]
    have h2 := two_le_pRank_projectiveSL_of_charP (N := N) (K := K) (f := e) hp hp2 hN
      hepos hKcardp
    omega
  have hpK : ¬ p ∣ Nat.card K := by
    intro h
    rw [hKcard'] at h
    exact hpchar (Nat.prime_eq_prime_of_dvd_pow hp hp0 h).symm
  have hq1 : ¬ p ∣ Nat.card K - 1 := by
    intro h
    have h2 := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.two_le_pRank_psl_of_dvd_sub_one
      (K := K) (n := N) hN hp hp2 h
    omega
  have hformula := pRank_projectiveSL_formula (N := N) (K := K) hp hp2 (by omega) hpK hgcd
  rw [if_neg hq1] at hformula
  set d := orderOf (Nat.card K : ZMod p) with hd
  have hqne : (Nat.card K : ZMod p) ≠ 0 := by
    intro h
    exact hpK ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hdvd : d ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hqne
  have hpge : 2 ≤ p := hp.two_le
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hdle : d ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
  have hdivle : N / d ≤ 1 := by rwa [hformula] at hpRank
  have hNlt : N < 2 * d := by
    have := (Nat.div_lt_iff_lt_mul hdpos).mp (show N / d < 2 by omega)
    simpa [two_mul, mul_comm] using this
  have hNltp : N < 2 * p := by omega
  obtain ⟨D, hDn, hDcyc, hDcard, hDcomm⟩ :=
    linear_outer_filtration (K := K) (n := N) hN
  haveI : D.Normal := hDn
  have hDle : Nat.card D ≤ N := by
    refine Nat.le_of_dvd (by omega : 0 < N) ?_
    exact hDcard.trans (Nat.gcd_dvd_left N (Nat.card K - 1))
  have hDlt : Nat.card D < 2 * p := lt_of_le_of_lt hDle hNltp
  have hpD : ¬ p ∣ Nat.card D := fun h => hgcd (h.trans hDcard)
  have hfcard : Nat.card (K ≃+* K) = (e : ℕ) := fieldAut_card K hp0 hKcard'
  haveI : Finite (K ≃+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hfcard]; exact e.pos.ne')
  haveI : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  let S : Sylow p (K ≃+* K) := default
  let F : Subgroup (MulAut (projectiveSL N K)) :=
    (S : Subgroup (K ≃+* K)).map (fieldAut N K)
  have hfinj : Function.Injective (fieldAut N K) := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (n := N) hN 1 σ
      (by rw [map_one, one_mul]; exact hσ)).1
  have hinner_le : CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) ≤
      linearAutGroup N K :=
    (standard_outer_quotients (n := N) (K := K)).1
  have hFbot : F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := hx
    obtain ⟨σ, -, rfl⟩ := hxF
    have hxI' : fieldAut N K σ ∈ linearAutGroup N K := hinner_le hxI
    rw [linearAutGroup_eq_range] at hxI'
    obtain ⟨A, hA⟩ := hxI'
    have h1 : conjAut N K A * fieldAut N K σ⁻¹ = 1 := by
      rw [map_inv, ← hA, mul_inv_cancel]
    have h2 : σ⁻¹ = 1 :=
      (eq_one_of_conjAut_mul_fieldAut_eq_one (n := N) hN A σ⁻¹ h1).1
    have h3 : σ = 1 := inv_eq_one.mp h2
    rw [h3, map_one]
    exact one_mem ⊥
  have hFcyc : IsCyclic ↥F := by
    have hScyc : IsCyclic ↥(S : Subgroup (K ≃+* K)) := Subgroup.isCyclic _
    exact (Subgroup.equivMapOfInjective (S : Subgroup (K ≃+* K)) (fieldAut N K)
      hfinj).isCyclic.mp hScyc
  let φ : (K ≃+* K) →* Outer (projectiveSL N K) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL N K))).comp (fieldAut N K)
  let C : Subgroup (Outer (projectiveSL N K)) := (S : Subgroup (K ≃+* K)).map φ
  have hCp : IsPGroup p C := (S.isPGroup').map φ
  have hFC : F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL N K))) = C := by
    dsimp [F, C, φ]
    rw [Subgroup.map_map]
  have hmap : (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) ⊔ F).map
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (projectiveSL N K))) =
        F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (projectiveSL N K))) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hCindex : C.index =
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) ⊔ F).index := by
    rw [← hFC, ← hmap]
    exact Subgroup.index_map_eq (H := CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL N K) ⊔ F) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
  have hinj : Function.Injective (φ.comp (S : Subgroup (K ≃+* K)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxI : fieldAut N K (x : K ≃+* K) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) := by
      have hx' : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (projectiveSL N K))) (fieldAut N K (x : K ≃+* K)) = 1 := hx
      exact (QuotientGroup.eq_one_iff
        (N := CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K)) _).mp hx'
    have hxbot : fieldAut N K (x : K ≃+* K) ∈
        F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) :=
      ⟨Subgroup.mem_map_of_mem (fieldAut N K) x.2, hxI⟩
    rw [hFbot] at hxbot
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (hfinj (by simpa using Subgroup.mem_bot.mp hxbot)))
  have hCcard : Nat.card ↥C = Nat.card ↥(S : Subgroup (K ≃+* K)) := by
    have hrange : C = (φ.comp (S : Subgroup (K ≃+* K)).subtype).range := by
      dsimp [C, φ]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hScard : Nat.card ↥(S : Subgroup (K ≃+* K)) =
      p ^ Nat.factorization (e : ℕ) p := by
    rw [Sylow.card_eq_multiplicity, hfcard]
  have hOutdvd : Nat.card (Outer (projectiveSL N K)) ∣
      2 * (e : ℕ) * Nat.gcd N (Nat.card K - 1) := by
    have h := higher_linear_outer_order_divides_field_gcd_bound
      (k := K) (p := ringChar K) (f := (e : ℕ)) (n := N) hp0 e.pos hN hKcard'
    rw [hKcard']
    exact h
  have hOutEq : Nat.card (Outer (projectiveSL N K)) =
      C.index * p ^ Nat.factorization (e : ℕ) p := by
    have h1 := Subgroup.index_mul_card C
    rw [hCcard, hScard] at h1
    exact h1.symm
  set v := Nat.factorization (e : ℕ) p with hv
  set m := ordCompl[p] (e : ℕ) with hm
  have hpm : ¬ p ∣ m := by
    have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp (by positivity)
    exact (hp.coprime_iff_not_dvd).mp hcop
  have heq : (e : ℕ) = p ^ v * m := by
    rw [hv, hm, Nat.ordProj_mul_ordCompl_eq_self (e : ℕ) p]
  have hout' : C.index * p ^ v ∣ p ^ v * (2 * m * Nat.gcd N (Nat.card K - 1)) := by
    have h := hOutdvd
    rw [hOutEq] at h
    rw [show 2 * (e : ℕ) * Nat.gcd N (Nat.card K - 1) =
      p ^ v * (2 * m * Nat.gcd N (Nat.card K - 1)) by rw [heq]; ring] at h
    exact h
  have hidxC : C.index ∣ 2 * m * Nat.gcd N (Nat.card K - 1) := by
    have hpv0 : 0 < p ^ v := pow_pos hp.pos v
    rw [mul_comm C.index (p ^ v)] at hout'
    exact (Nat.mul_dvd_mul_iff_left hpv0).mp hout'
  have h2not : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hidxC' : ¬ p ∣ C.index := by
    intro h
    rcases hp.dvd_mul.mp (h.trans hidxC) with h1 | h1
    · rcases hp.dvd_mul.mp h1 with h2 | h2
      · exact h2not h2
      · exact hpm h2
    · exact hgcd h1
  exact sylow_normal_of_normal_cyclic_of_card_lt_two_mul hp hp2 D C hDn hDcyc hDlt hpD
    hDcomm.1 hCp hidxC'

theorem exists_fieldPart_projectiveSL (N : ℕ) (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hN : 3 ≤ N)
    (hpRank : CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL N K)) ≤ 1)
    (hSylow : ∀ S : Sylow p (Outer (projectiveSL N K)),
      (S : Subgroup (Outer (projectiveSL N K))).Normal) :
    ∃ F : Subgroup (MulAut (projectiveSL N K)),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) ⊔ F).Normal ∧
      IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) ⊔ F).index ∧
      ∀ x : MulAut (projectiveSL N K), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) ⊔ F := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, hp0, hKcard⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp0⟩
  have hKcard' : Nat.card K = ringChar K ^ (e : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hKcard
  have hfcard : Nat.card (K ≃+* K) = (e : ℕ) := fieldAut_card K hp0 hKcard'
  haveI : Finite (K ≃+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hfcard]; exact e.pos.ne')
  haveI : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  let S : Sylow p (K ≃+* K) := default
  let F : Subgroup (MulAut (projectiveSL N K)) :=
    (S : Subgroup (K ≃+* K)).map (fieldAut N K)
  have hfinj : Function.Injective (fieldAut N K) := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (n := N) hN 1 σ
      (by rw [map_one, one_mul]; exact hσ)).1
  have hinner_le : CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) ≤
      linearAutGroup N K :=
    (standard_outer_quotients (n := N) (K := K)).1
  have hFbot : F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := hx
    obtain ⟨σ, -, rfl⟩ := hxF
    have hxI' : fieldAut N K σ ∈ linearAutGroup N K := hinner_le hxI
    rw [linearAutGroup_eq_range] at hxI'
    obtain ⟨A, hA⟩ := hxI'
    have h1 : conjAut N K A * fieldAut N K σ⁻¹ = 1 := by
      rw [map_inv, ← hA, mul_inv_cancel]
    have h2 : σ⁻¹ = 1 :=
      (eq_one_of_conjAut_mul_fieldAut_eq_one (n := N) hN A σ⁻¹ h1).1
    have h3 : σ = 1 := inv_eq_one.mp h2
    rw [h3, map_one]
    exact one_mem ⊥
  have hFcyc : IsCyclic ↥F := by
    have hScyc : IsCyclic ↥(S : Subgroup (K ≃+* K)) := Subgroup.isCyclic _
    exact (Subgroup.equivMapOfInjective (S : Subgroup (K ≃+* K)) (fieldAut N K)
      hfinj).isCyclic.mp hScyc
  have hFp : IsPGroup p F := (S.isPGroup').map (fieldAut N K)
  have hgcd : ¬ p ∣ Nat.gcd N (Nat.card K - 1) := by
    intro hdvd
    have h2 := GL83.I713.two_le_pRank_projectiveSL_of_dvd (K := K) (n := N) hN hp hp2 hdvd
    omega
  let φ : (K ≃+* K) →* Outer (projectiveSL N K) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL N K))).comp (fieldAut N K)
  let C : Subgroup (Outer (projectiveSL N K)) := (S : Subgroup (K ≃+* K)).map φ
  have hFC : F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL N K))) = C := by
    dsimp [F, C, φ]
    rw [Subgroup.map_map]
  have hmap : (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) ⊔ F).map
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (projectiveSL N K))) =
        F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (projectiveSL N K))) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hCindex : C.index =
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) ⊔ F).index := by
    rw [← hFC, ← hmap]
    exact Subgroup.index_map_eq (H := CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL N K) ⊔ F) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
  have hinj : Function.Injective (φ.comp (S : Subgroup (K ≃+* K)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxI : fieldAut N K (x : K ≃+* K) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) := by
      have hx' : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (projectiveSL N K))) (fieldAut N K (x : K ≃+* K)) = 1 := hx
      exact (QuotientGroup.eq_one_iff
        (N := CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K)) _).mp hx'
    have hxbot : fieldAut N K (x : K ≃+* K) ∈
        F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL N K) :=
      ⟨Subgroup.mem_map_of_mem (fieldAut N K) x.2, hxI⟩
    rw [hFbot] at hxbot
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (hfinj (by simpa using Subgroup.mem_bot.mp hxbot)))
  have hCcard : Nat.card ↥C = Nat.card ↥(S : Subgroup (K ≃+* K)) := by
    have hrange : C = (φ.comp (S : Subgroup (K ≃+* K)).subtype).range := by
      dsimp [C, φ]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hScard : Nat.card ↥(S : Subgroup (K ≃+* K)) =
      p ^ Nat.factorization (e : ℕ) p := by
    rw [Sylow.card_eq_multiplicity, hfcard]
  have hOutEq : Nat.card (Outer (projectiveSL N K)) =
      C.index * p ^ Nat.factorization (e : ℕ) p := by
    have h1 := Subgroup.index_mul_card C
    rw [hCcard, hScard] at h1
    exact h1.symm
  have hOutdvd : Nat.card (Outer (projectiveSL N K)) ∣
      2 * (e : ℕ) * Nat.gcd N (Nat.card K - 1) := by
    have h := higher_linear_outer_order_divides_field_gcd_bound
      (k := K) (p := ringChar K) (f := (e : ℕ)) (n := N) hp0 e.pos hN hKcard'
    rw [hKcard']
    exact h
  set v := Nat.factorization (e : ℕ) p with hv
  set m := ordCompl[p] (e : ℕ) with hm
  have hpm : ¬ p ∣ m := by
    have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp (by positivity)
    exact (hp.coprime_iff_not_dvd).mp hcop
  have heq : (e : ℕ) = p ^ v * m := by
    rw [hv, hm, Nat.ordProj_mul_ordCompl_eq_self (e : ℕ) p]
  have hout' : C.index * p ^ v ∣ p ^ v * (2 * m * Nat.gcd N (Nat.card K - 1)) := by
    have h := hOutdvd
    rw [hOutEq] at h
    rw [show 2 * (e : ℕ) * Nat.gcd N (Nat.card K - 1) =
      p ^ v * (2 * m * Nat.gcd N (Nat.card K - 1)) by rw [heq]; ring] at h
    exact h
  have hidxC : C.index ∣ 2 * m * Nat.gcd N (Nat.card K - 1) := by
    have hpv0 : 0 < p ^ v := pow_pos hp.pos v
    rw [mul_comm C.index (p ^ v)] at hout'
    exact (Nat.mul_dvd_mul_iff_left hpv0).mp hout'
  have h2not : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hidxC' : ¬ p ∣ C.index := by
    intro h
    rcases hp.dvd_mul.mp (h.trans hidxC) with h1 | h1
    · rcases hp.dvd_mul.mp h1 with h2 | h2
      · exact h2not h2
      · exact hpm h2
    · exact hgcd h1
  have hidx : ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL N K) ⊔ F).index := by
    rw [← hCindex]
    exact hidxC'
  exact exists_fieldPart_of_isPGroup hp F hFp hFcyc hFbot hSylow hidx

theorem unitary_outer_sylow_normal {p₀ f N : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p₀ f K) (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ p₀ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hpRank : CFSG.Open.pRank p (⊤ : Subgroup (primeFormP h
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))) ≤ 1) :
    ∀ S : Sylow p (Outer (primeFormP h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))),
      (S : Subgroup (Outer (primeFormP h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))).Normal := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := h.finite
  let T := primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
  have hC : IsPrimeFormGram (1 : GL (Fin N) K) := isPrimeFormGram_one
  have hgcd : ¬ p ∣ Nat.gcd N (p₀ ^ f + 1) := by
    intro hdvd
    obtain ⟨hpN, hpq⟩ := Nat.dvd_gcd_iff.1 hdvd
    have hKsq : Nat.card K = (p₀ ^ f) ^ 2 := by
      rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
    have h2 := GL83.I713.two_le_pRank_statedPSU_of_dvd (K := K) (q := p₀ ^ f)
      (n := N) (ℓ := p) hKsq hp hp2 hN hpN hpq
    let ePU : T ≃* unitaryPSU h N := Classical.choice (nonempty_primeFormP_mulEquiv h hC)
    let ePS : unitaryPSU h N ≃* StatedProj (StatedSU N (p₀ ^ f) K) :=
      unitaryPSUEquiv h (by omega)
    have hEq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (ePU.trans ePS)
    have hpRank' : CFSG.Open.pRank p
        (⊤ : Subgroup (StatedProj (StatedSU N (p₀ ^ f) K))) ≤ 1 := by
      rwa [hEq] at hpRank
    exact Nat.not_le_of_lt (Nat.lt_of_le_of_lt hpRank' (by norm_num)) h2
  have hpq : ¬ p ∣ p₀ ^ f := by
    intro hpq
    have hpp0 : p = p₀ := (Nat.prime_dvd_prime_iff_eq hp h.prime).mp (hp.dvd_of_dvd_pow hpq)
    subst hpp0
    have h2 := two_le_pRank_primeFormP_of_charP (K := K) (f := f) (N := N) h hp2 hN
    omega
  have hformula := pRank_primeFormP_formula (h := h) (N := N) (by omega) (p := p) hp hp2 hpq hgcd
  rw [hformula] at hpRank
  set d := orderOf (-((p₀ ^ f : ℕ) : ZMod p)) with hd
  have hqne : ((p₀ ^ f : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hpq ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  have hneg : (-((p₀ ^ f : ℕ) : ZMod p)) ≠ 0 := by
    intro hzero
    exact hqne (neg_eq_zero.mp hzero)
  have hdvd : d ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hneg
  have hpge : 2 ≤ p := hp.two_le
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hdle : d ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
  have hdivle : N / d ≤ 1 := by
    split_ifs at hpRank
    · omega
    · exact hpRank
  have hNlt : N < 2 * d := by
    have := (Nat.div_lt_iff_lt_mul hdpos).mp (show N / d < 2 by omega)
    simpa [two_mul, mul_comm] using this
  have hNltp : N < 2 * p := by omega
  obtain ⟨D, hDn, hDcyc, hDcard, hDcycquot⟩ := unitary_outer_filtration h hN hq
  haveI : D.Normal := hDn
  have hDle : Nat.card D ≤ N := by
    refine Nat.le_of_dvd (by omega : 0 < N) ?_
    exact hDcard.trans (Nat.gcd_dvd_left N (p₀ ^ f + 1))
  have hDlt : Nat.card D < 2 * p := lt_of_le_of_lt hDle hNltp
  have hpD : ¬ p ∣ Nat.card D := fun hh => hgcd (hh.trans hDcard)
  have hcardAut : Nat.card (K ≃+* K) = 2 * f := fieldAut_card K h.prime h.card
  have h2f : 0 < 2 * f := Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le zero_lt_one h.one_le)
  haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; exact h2f.ne')
  haveI : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  let S : Sylow p (K ≃+* K) := default
  let F : Subgroup (MulAut T) := (S : Subgroup (K ≃+* K)).map (primeFormFieldHom h hC)
  obtain ⟨-, -, -, -, -, hfac, -, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hN hq
  have hfacφ : ∀ φ : K ≃+* K,
      primeFormFieldFactor h hC hN hq (primeFormFieldHom h hC φ) = φ := by
    intro φ
    have := hfac (1 : primeFormUnitary h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) φ
    simpa using this
  have hfinj : Function.Injective (primeFormFieldHom h hC) := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    have h1 := hfacφ φ
    rw [hφ, map_one] at h1
    exact h1.symm
  have hinner_le_D : CFSG.ComponentClassification.OuterAutomorphisms.inner T ≤
      primeFormD h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
    intro α hα
    obtain ⟨s, hs⟩ := (hinn α).1 hα
    exact ⟨⟨s, s.2.1⟩, hs.symm⟩
  have hFbot : F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner T = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := hx
    obtain ⟨φ, -, rfl⟩ := hxF
    have hmem : primeFormFieldHom h hC φ ∈
        (primeFormFieldFactor h hC hN hq).ker := by
      rw [hFker]
      exact hinner_le_D hxI
    have hφ1 : φ = 1 := by
      have h1 := (MonoidHom.mem_ker).mp hmem
      rw [hfacφ φ] at h1
      exact h1
    rw [hφ1, map_one]
    exact one_mem ⊥
  have hFcyc : IsCyclic ↥F := by
    have hScyc : IsCyclic ↥(S : Subgroup (K ≃+* K)) := Subgroup.isCyclic _
    exact (Subgroup.equivMapOfInjective (S : Subgroup (K ≃+* K))
      (primeFormFieldHom h hC) hfinj).isCyclic.mp hScyc
  have hFp : IsPGroup p F := (S.isPGroup').map (primeFormFieldHom h hC)
  let φ : (K ≃+* K) →* Outer T :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)).comp
      (primeFormFieldHom h hC)
  let C : Subgroup (Outer T) := (S : Subgroup (K ≃+* K)).map φ
  have hFC : F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)) =
      C := by
    dsimp [F, C, φ]
    rw [Subgroup.map_map]
  have hmap : (CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F).map
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)) =
      F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hCindex : C.index =
      (CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F).index := by
    rw [← hFC, ← hmap]
    exact Subgroup.index_map_eq (H := CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F)
      (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
  have hinj : Function.Injective (φ.comp (S : Subgroup (K ≃+* K)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxI : primeFormFieldHom h hC (x : K ≃+* K) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner T := by
      have hx' : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T))
          (primeFormFieldHom h hC (x : K ≃+* K)) = 1 := hx
      exact (QuotientGroup.eq_one_iff
        (N := CFSG.ComponentClassification.OuterAutomorphisms.inner T) _).mp hx'
    have hxbot : primeFormFieldHom h hC (x : K ≃+* K) ∈
        F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner T :=
      ⟨Subgroup.mem_map_of_mem (primeFormFieldHom h hC) x.2, hxI⟩
    rw [hFbot] at hxbot
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (hfinj (by simpa using Subgroup.mem_bot.mp hxbot)))
  have hCcard : Nat.card ↥C = Nat.card ↥(S : Subgroup (K ≃+* K)) := by
    have hrange : C = (φ.comp (S : Subgroup (K ≃+* K)).subtype).range := by
      dsimp [C, φ]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hScard : Nat.card ↥(S : Subgroup (K ≃+* K)) =
      p ^ Nat.factorization (2 * f) p := by
    rw [Sylow.card_eq_multiplicity, hcardAut]
  have hCp : IsPGroup p C := (S.isPGroup').map φ
  obtain ⟨-, -, -, hOut, -, -⟩ := unitary_full_diagonal_outer_order h hN hq
  have hTout : Nat.card (Outer T) = 2 * f * Nat.gcd N (p₀ ^ f + 1) := by
    simpa [T] using hOut
  have hOutEq : Nat.card (Outer T) = C.index * p ^ Nat.factorization (2 * f) p := by
    have h1 := Subgroup.index_mul_card C
    rw [hCcard, hScard] at h1
    exact h1.symm
  set v := Nat.factorization (2 * f) p with hv
  set m := ordCompl[p] (2 * f) with hm
  have hpm : ¬ p ∣ m := by
    have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp (by positivity)
    exact (hp.coprime_iff_not_dvd).mp hcop
  have heq : 2 * f = p ^ v * m := by
    rw [hv, hm, Nat.ordProj_mul_ordCompl_eq_self (2 * f) p]
  have hCindex_eq : C.index = m * Nat.gcd N (p₀ ^ f + 1) := by
    have h1 : C.index * p ^ v = p ^ v * (m * Nat.gcd N (p₀ ^ f + 1)) := by
      rw [← hOutEq, hTout, heq]
      ring
    have h2 : C.index * p ^ v = (m * Nat.gcd N (p₀ ^ f + 1)) * p ^ v := by
      rw [h1]; ring
    exact mul_right_cancel₀ (pow_ne_zero v hp.ne_zero) h2
  have hidxC' : ¬ p ∣ C.index := by
    rw [hCindex_eq]
    intro hh
    rcases hp.dvd_mul.mp hh with h1 | h1
    · exact hpm h1
    · exact hgcd h1
  have hcommD : ∀ x y : Outer T ⧸ D, x * y = y * x := by
    haveI : IsCyclic (Outer T ⧸ D) := hDcycquot
    exact fun x y => mul_comm' x y
  exact sylow_normal_of_normal_cyclic_of_card_lt_two_mul hp hp2 D C hDn hDcyc hDlt hpD
    hcommD hCp hidxC'

theorem i713ClauseFor_lie_A (n : ℕ) (hn : 2 ≤ n) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A n q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let Fq := GaloisField q.p q.exponent
  have hqcard : Nat.card Fq = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  let ePSL : (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group ≃*
      projectiveSL (n + 1) Fq :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) Fq)
  have hEq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (eK.trans ePSL)
  have hpRank' : CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL (n + 1) Fq)) ≤ 1 :=
    hEq ▸ hpRank
  refine Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans ePSL)
    (exists_fieldPart_projectiveSL (n + 1) Fq hp hp2 (by omega) hpRank'
      (linear_outer_sylow_normal (n + 1) Fq hp hp2 (by omega) hpRank'))))

theorem i713ClauseFor_lie_twistedA (n : ℕ) (hn : 3 ≤ n) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA n q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨⟨hpq, hf, hN, h32⟩, L, _, _, hL, ⟨eL⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv
      (G := (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group) (MulEquiv.refl _)
  let hU : UnitaryFieldData q.p q.exponent L :=
    ⟨hpq, hf, by rw [hL, ← pow_mul, mul_comm]⟩
  haveI : Finite L := hU.finite
  have hq : ¬(n + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
    rintro ⟨h1, h2⟩
    exact h32 (by rw [h1, h2])
  have hC : IsPrimeFormGram (1 : GL (Fin (n + 1)) L) := isPrimeFormGram_one
  let ePU : primeFormP hU ((1 : GL (Fin (n + 1)) L) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) L) ≃* unitaryPSU hU (n + 1) :=
    Classical.choice (nonempty_primeFormP_mulEquiv hU hC)
  let ePS : unitaryPSU hU (n + 1) ≃*
      StatedProj (StatedSU (n + 1) (q.p ^ q.exponent) L) :=
    unitaryPSUEquiv hU (by omega)
  let eC : (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group ≃*
      primeFormP hU ((1 : GL (Fin (n + 1)) L) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) L) :=
    eL.trans (ePU.trans ePS).symm
  have hEq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (eK.trans eC)
  have hpRank' : CFSG.Open.pRank p (⊤ : Subgroup (primeFormP hU
      ((1 : GL (Fin (n + 1)) L) : Matrix (Fin (n + 1)) (Fin (n + 1)) L))) ≤ 1 :=
    hEq ▸ hpRank
  refine Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eC)
    (exists_fieldPart_primeFormP hU (by omega) hq hp hp2
      (unitary_outer_sylow_normal hU (by omega) hq hp hp2 hpRank') hpRank')))
