module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem pRank_quotient_pPrimeCore (Y : Type*) [Group Y] [Finite Y] :
    CFSG.pRank 2 (Y ⧸ pPrimeCore 2 Y) = CFSG.pRank 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (pPrimeCore_coprime_card (p := 2)))

theorem not_mem_pPrimeCore_two_of_orderOf {Y : Type*} [Group Y] [Finite Y] {y : Y}
    (hy : orderOf y = 2) : y ∉ pPrimeCore 2 Y := fun h => by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf y ∣ Nat.card (pPrimeCore 2 Y) := by
    rw [← Subgroup.orderOf_mk y h]
    exact orderOf_dvd_natCard _
  have h2 := Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1
  rw [hy] at h2
  exact absurd h2 (by decide)

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_of_isTwoComponentAt {z : G} {A : Subgroup G}
    (hA : IsTwoComponentAt z A) : ∃ a ∈ A, orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hAz, hApc⟩ := hA
  have h2 : 2 ∣ Nat.card A := by
    by_contra h
    exact not_le_of_isPComponent_of_coprime hAz hApc
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h) le_rfl
  obtain ⟨⟨a, haA⟩, ha⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨a, haA, by rwa [Subgroup.orderOf_mk] at ha⟩

theorem mem_coreActionKernel_of_pRank_le_one {z : G} {A : Subgroup G}
    (hA : IsTwoComponentAt z A) (hrank : CFSG.pRank 2 ↥A ≤ 1) {a : G} (haA : a ∈ A)
    (ha : orderOf a = 2) : a ∈ coreActionKernel A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hAz, hApc⟩ := hA
  have hq := isQuasisimple_quotient_of_isPComponent hAz hApc
  have hq' : IsQuasisimple (A ⧸ CFSG.oddCore A) := LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore_two A)).symm hq
  obtain ⟨-, z₀, -, huniq, hcen, -⟩ :=
    UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrank hq'
  have ha'2 : orderOf (⟨a, haA⟩ : A) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hmk2 : orderOf (QuotientGroup.mk ⟨a, haA⟩ : A ⧸ CFSG.oddCore A) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, ← ha'2, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h
      have hO : (⟨a, haA⟩ : A) ∈ CFSG.oddCore A := (QuotientGroup.eq_one_iff _).mp h
      rw [oddCore_eq_pPrimeCore_two] at hO
      exact not_mem_pPrimeCore_two_of_orderOf ha'2 hO
  have hcentral : (QuotientGroup.mk ⟨a, haA⟩ : A ⧸ CFSG.oddCore A) ∈
      center (A ⧸ CFSG.oddCore A) := by
    rw [huniq _ hmk2, hcen]
    exact mem_zpowers _
  refine ⟨le_normalizer haA, fun j hj => ?_⟩
  rw [mk_mem_center_iff] at hcentral
  have h1 := hcentral (⟨j, hj⟩ : A)⁻¹
  rw [oddCore_eq_pPrimeCore_two, mem_pPrimeCore_iff_mem_oddCoreIn] at h1
  have e : (((((⟨j, hj⟩ : A)⁻¹ * ⟨a, haA⟩)⁻¹ * (⟨a, haA⟩ * (⟨j, hj⟩ : A)⁻¹) : A)) : G) =
      a⁻¹ * j * a * j⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e] at h1
  have h3 := (mem_normalizer_iff.mp (mem_normalizer_oddCoreIn (le_normalizer (inv_mem hj))) _).mp
    h1
  rw [inv_inv] at h3
  rw [show j⁻¹ * a⁻¹ * j * a = j⁻¹ * (a⁻¹ * j * a * j⁻¹) * j by group]
  exact h3

theorem center_ne_bot_of_mem_coreActionKernel {A : Subgroup G} {a : G} (haA : a ∈ A)
    (ha : orderOf a = 2) (haK : a ∈ coreActionKernel A) :
    center (A ⧸ pPrimeCore 2 A) ≠ ⊥ := by
  have ha'2 : orderOf (⟨a, haA⟩ : A) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨QuotientGroup.mk ⟨a, haA⟩, ?_⟩, fun h => ?_⟩
  · rw [mk_mem_center_iff]
    intro j
    rw [mem_pPrimeCore_iff_mem_oddCoreIn]
    have h1 := haK.2 ((j : G)⁻¹) (inv_mem j.2)
    have h2 := (mem_normalizer_iff.mp
      (mem_normalizer_oddCoreIn (le_normalizer (inv_mem j.2))) _).mp h1
    have e : (((j * ⟨a, haA⟩)⁻¹ * (⟨a, haA⟩ * j) : A) : G) =
        (j : G)⁻¹ * (((j : G)⁻¹)⁻¹ * a⁻¹ * (j : G)⁻¹ * a) * ((j : G)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h2
  · have h1 := congrArg Subtype.val h
    have h2 : (QuotientGroup.mk ⟨a, haA⟩ : A ⧸ pPrimeCore 2 A) = 1 := h1
    exact not_mem_pPrimeCore_two_of_orderOf ha'2 ((QuotientGroup.eq_one_iff _).mp h2)

omit [Finite G] in
theorem mem_footeFixed_self {L : Subgroup G} {b : G} (hbL : b ∈ L) (hb : orderOf b = 2) :
    b ∈ footeFixed L b :=
  Subgroup.subset_closure ⟨mem_sup_left (mem_inf.mpr ⟨hbL, mem_centralizer_singleton_iff.mpr
    rfl⟩), 1, by rw [hb, pow_one]⟩

theorem pRank_footeFixed_eq {a b : G} {L : Subgroup G} (hL : IsTwoComponentAt a L)
    (hb : orderOf b = 2) (hbL : b ∈ coreActionKernel L)
    (hLb : IsTwoComponentAt b (footeFixed L b)) :
    CFSG.pRank 2 ↥(footeFixed L b) = CFSG.pRank 2 ↥L := by
  obtain ⟨φ, -, -⟩ := exists_quotient_mulEquiv_footeFixed hL hb hbL hLb
  rw [← pRank_quotient_pPrimeCore, ← pRank_quotient_pPrimeCore ↥L]
  exact (pRank_eq_of_mulEquiv one_lt_two φ).symm

omit [Finite G] in
theorem le_of_commutator_eq_self_of_sup_zpowers {N X : Subgroup G} {t : G}
    (hgen : N ⊔ zpowers t = ⊤) (htN : t ∈ normalizer (N : Set G)) (hX : ⁅X, X⁆ = X) :
    X ≤ N := by
  have hnorm : normalizer (N : Set G) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le le_normalizer ((zpowers_le).mpr htN)
  have : N.Normal := normalizer_eq_top_iff.mp hnorm
  set π := QuotientGroup.mk' N with hπ
  have hcyc : ∀ g : G, π g ∈ zpowers (π t) := by
    intro g
    have h1 : π g ∈ (N ⊔ zpowers t).map π := mem_map_of_mem π (hgen ▸ mem_top g)
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
  rw [← hX, commutator_le]
  intro x _ y _
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_commutatorElement]
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hcyc x)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hcyc y)
  rw [← hπ, ← hi, ← hj, commutatorElement_eq_one_iff_mul_comm]
  exact zpow_mul_comm _ _ _

theorem oddLieType_of_classical_in_subgroup (hCI : GSLit.ClassicalInvolutionInput)
    {G₀ : Subgroup G} [IsSimpleGroup G₀] (hnonab : ∃ u v : G₀, u * v ≠ v * u) {x : G}
    (hxG₀ : x ∈ G₀) (hx : orderOf x = 2) {X : Subgroup G} (hXG₀ : X ≤ G₀)
    (hX : IsTwoComponentAt x X) (hxX : x ∈ X) (hrank : CFSG.pRank 2 ↥X ≤ 1) :
    Blueprint.OddLieType G₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hXC, hXpc⟩ := hX
  set x' : G₀ := ⟨x, hxG₀⟩
  have hx' : orderOf x' = 2 := by rw [Subgroup.orderOf_mk]; exact hx
  have hcen : centralizer ({x'} : Set G₀) = (centralizer ({x} : Set G) ⊓ G₀).subgroupOf G₀ := by
    ext y
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨congrArg Subtype.val h, y.2⟩, fun h => Subtype.ext h.1⟩
  have hXCG : X ≤ centralizer ({x} : Set G) ⊓ G₀ := le_inf hXC hXG₀
  have hJC : X.subgroupOf G₀ ≤ centralizer ({x'} : Set G₀) := by
    rw [hcen]
    intro y hy
    exact mem_subgroupOf.mpr (hXCG (mem_subgroupOf.mp hy))
  have hJ : IsPComponent 2 ((X.subgroupOf G₀).subgroupOf (centralizer ({x'} : Set G₀))) := by
    rw [hcen, isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two]
    exact isPComponent_subgroupOf_of_le hXCG inf_le_left hXpc
  have hxJ : x' ∈ X.subgroupOf G₀ := mem_subgroupOf.mpr hxX
  have hrank' : CFSG.pRank 2 ↥(X.subgroupOf G₀) ≤ 1 := by
    rw [pRank_eq_of_mulEquiv one_lt_two (subgroupOfEquivOfLe hXG₀)]
    exact hrank
  exact oddLieType_of_classical_twoComponent hCI hnonab hx' hJC hJ hxJ hrank'

theorem footeConclusion_of_oddLieType {t : G} {L A : Subgroup G} [IsSimpleGroup A]
    (hnonab : ∃ u v : A, u * v ≠ v * u) (hodd : Blueprint.OddLieType A) :
    FooteConclusion t L A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, v, huv⟩ := hnonab
  obtain ⟨y, hy⟩ : ∃ y : A, orderOf y = 2 := by
    by_contra hno
    have hodd' : Odd (Nat.card A) := by
      by_contra hev
      exact hno (exists_prime_orderOf_dvd_card' 2
        (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)))
    have hsolv : Group.IsSolvable A := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
    have hcomm : commutator A = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator A) with h | h
      · exfalso
        apply huv
        have hmem : u * v * u⁻¹ * v⁻¹ ∈ commutator A := by
          have := Subgroup.commutator_mem_commutator (mem_top u) (mem_top v)
          rwa [commutatorElement_def] at this
        rw [h, mem_bot] at hmem
        calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
          _ = v * u := by rw [hmem, one_mul]
      · exact h
    have hnt : Nontrivial A := ⟨⟨u, v, fun h => huv (by rw [h])⟩⟩
    exact (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial A)) hcomm
  have hOA : pPrimeCore 2 A = ⊥ := pPrimeCore_two_eq_bot_of_isSimpleGroup hy
  let e : A ⧸ pPrimeCore 2 A ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hOA).trans QuotientGroup.quotientBot
  right; right; right; right
  exact ⟨e.isSimpleGroup, (ClassicalInvolution.oddLieType_congr e).2 hodd⟩

end CFSG.ComponentClassification.FooteLit
