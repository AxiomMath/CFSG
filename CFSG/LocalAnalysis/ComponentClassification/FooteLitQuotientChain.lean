module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitComponentReduction
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneLayer
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem map_oddResidualIn_hom {X Y' : Type*} [Group X] [Group Y'] [Finite X] (f : X →* Y')
    (Y : Subgroup X) : (oddResidualIn Y).map f = oddResidualIn (Y.map f) := by
  unfold oddResidualIn
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · refine (closure_le _).mpr ?_
    rintro _ ⟨y, ⟨hyY, k, hk⟩, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨mem_map_of_mem f hyY, ?_⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (hk ▸ orderOf_map_dvd f y)
    exact ⟨j, hj⟩
  · refine (closure_le _).mpr ?_
    rintro _ ⟨⟨y, hyY, rfl⟩, k, hk⟩
    obtain ⟨i, m, hm, hym⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    have hm0 : m ≠ 0 := fun h => by simp [h] at hm
    have hu : f (y ^ m) ∈ closure (f '' {g : X | g ∈ Y ∧ ∃ k : ℕ, orderOf g = 2 ^ k}) := by
      apply Subgroup.subset_closure
      refine ⟨y ^ m, ⟨pow_mem hyY m, i, ?_⟩, rfl⟩
      rw [orderOf_pow' y hm0, hym, Nat.gcd_mul_left_left,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
    have hg := Nat.gcd_eq_gcd_ab m (2 ^ k)
    rw [hcop.gcd_eq_one, Nat.cast_one] at hg
    have e : f y = (f (y ^ m)) ^ (Nat.gcdA m (2 ^ k)) := by
      have h2k : (f y) ^ (2 ^ k) = 1 := by rw [← hk, pow_orderOf_eq_one]
      calc f y = (f y) ^ ((m : ℤ) * Nat.gcdA m (2 ^ k) + (2 ^ k : ℕ) * Nat.gcdB m (2 ^ k)) := by
            rw [← hg, zpow_one]
        _ = (f (y ^ m)) ^ (Nat.gcdA m (2 ^ k)) := by
            rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, h2k, one_zpow,
              mul_one, map_pow]
    rw [e]
    exact zpow_mem hu _

variable {G : Type} [Group G] [Finite G]

theorem eq_or_eq_of_isPComponent_le_sup {C M K₁ K₂ : Subgroup G} (hMC : M ≤ C) (hK₁C : K₁ ≤ C)
    (hK₂C : K₂ ≤ C) (hM : IsPComponent 2 (M.subgroupOf C))
    (hK₁ : IsPComponent 2 (K₁.subgroupOf C)) (hK₂ : IsPComponent 2 (K₂.subgroupOf C))
    (hle : M ≤ K₁ ⊔ K₂) : M = K₁ ∨ M = K₂ := by
  by_cases hn1 : M = K₁
  · exact Or.inl hn1
  by_cases hn2 : M = K₂
  · exact Or.inr hn2
  exfalso
  have h1 : K₁ ≤ coreActionKernel M := GSThmB.B5a.le_coreActionKernel_of_ne hMC hK₁C hM hK₁ hn1
  have h2 : K₂ ≤ coreActionKernel M := GSThmB.B5a.le_coreActionKernel_of_ne hMC hK₂C hM hK₂ hn2
  have hMK : M ≤ coreActionKernel M := hle.trans (sup_le h1 h2)
  obtain ⟨u, v, huv⟩ := exists_mul_ne_mul_of_isQuasisimple
    (isQuasisimple_quotient_of_isPComponent hMC hM)
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  apply huv
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    mem_pPrimeCore_iff_mem_oddCoreIn]
  have h3 := (hMK v'.2).2 (u' : G) u'.2
  have e : (((u' * v')⁻¹ * (v' * u') : M) : G) =
      ((u' : G)⁻¹ * (v' : G)⁻¹ * (u' : G) * (v' : G))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact inv_mem h3

section Quotient

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 G)

theorem orderOf_mk_eq_two {x : G} (hx : orderOf x = 2) : orderOf (π x) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact not_mem_pPrimeCore_two_of_orderOf hx h

theorem map_centralizer_mk {x : G} (hx : orderOf x = 2) :
    (centralizer ({x} : Set G)).map π = centralizer ({π x} : Set (G ⧸ pPrimeCore 2 G)) := by
  have hxx : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  exact (GSThmB.OddQuot.centralizer_singleton_map_eq hxx).symm

theorem exists_involution_lift_commute {a : G} (ha : orderOf a = 2) {cq : G ⧸ pPrimeCore 2 G}
    (hc : orderOf cq = 2) (hac : π a * cq = cq * π a) :
    ∃ c : G, orderOf c = 2 ∧ π c = cq ∧ a * c = c * a := by
  have hmem : cq ∈ (centralizer ({a} : Set G)).map π := by
    rw [map_centralizer_mk ha, mem_centralizer_singleton_iff]
    exact hac.symm
  obtain ⟨d, hdC, hd⟩ := mem_map.mp hmem
  obtain ⟨i, m, hm, hdm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  have hc2 : cq ^ 2 = 1 := by
    have h := pow_orderOf_eq_one cq
    rwa [hc] at h
  have hπc : π (d ^ m) = cq := by
    rw [map_pow, hd]
    obtain ⟨r, rfl⟩ := hm
    rw [pow_succ, pow_mul, hc2, one_pow, one_mul]
  have hord : orderOf (d ^ m) = 2 ^ i := by
    rw [orderOf_pow' d hm0, hdm, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hsq : (d ^ m) ^ 2 = 1 := by
    have h1 : (d ^ m) ^ 2 ∈ pPrimeCore 2 G := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hπc, hc2]
    have h2 : ∃ k : ℕ, orderOf ((d ^ m) ^ 2) = 2 ^ k := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (hord ▸ orderOf_pow_dvd (x := d ^ m) 2)
      exact ⟨j, hj⟩
    exact eq_one_of_two_element_of_odd
      (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))) h1 h2
  have hne : d ^ m ≠ 1 := by
    intro h
    rw [h, map_one] at hπc
    rw [← hπc, orderOf_one] at hc
    exact absurd hc (by decide)
  refine ⟨d ^ m, orderOf_eq_prime hsq hne, hπc, ?_⟩
  exact (mem_centralizer_singleton_iff.mp (pow_mem hdC m)).symm

theorem isTwoComponentAt_map {x : G} {K : Subgroup G} (hK : IsTwoComponentAt x K) :
    IsTwoComponentAt (π x) (K.map π) := by
  obtain ⟨hx, hKC, hpc⟩ := hK
  refine ⟨orderOf_mk_eq_two hx, ?_, ?_⟩
  · rw [← map_centralizer_mk hx]
    exact map_mono hKC
  · have h := GSThmB.OddQuot.isPComponent_map π (GSThmB.OddQuot.not_two_dvd_card_ker (H := G))
      hKC hpc
    rwa [map_centralizer_mk hx] at h

theorem exists_isTwoComponentAt_lift {x : G} (hx : orderOf x = 2)
    {Kq : Subgroup (G ⧸ pPrimeCore 2 G)} (hK : IsTwoComponentAt (π x) Kq) :
    ∃ K : Subgroup G, IsTwoComponentAt x K ∧ K.map π = Kq := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hKC, hpc⟩ := hK
  set C := centralizer ({x} : Set G) with hC
  have hCmap := map_centralizer_mk hx
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (MonoidHom.subgroupMap π C) (MonoidHom.subgroupMap_surjective π C)
    (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap π
      (GSThmB.OddQuot.not_two_dvd_card_ker (H := G)) C)
  have hKC' : Kq ≤ C.map π := hCmap ▸ hKC
  have hpc' : IsPComponent 2 (Kq.subgroupOf (C.map π)) := by rw [hCmap]; exact hpc
  obtain ⟨K', hK', hK'map⟩ := hbij.surjOn hpc'
  have hK'map' : K'.map (MonoidHom.subgroupMap π C) = Kq.subgroupOf (C.map π) := hK'map
  refine ⟨K'.map C.subtype, ⟨hx, map_subtype_le _, ?_⟩, ?_⟩
  · have h1 : (K'.map C.subtype).subgroupOf C = K' :=
      comap_map_eq_self_of_injective C.subtype_injective K'
    rw [show centralizer ({x} : Set G) = C from rfl, h1]
    exact hK'
  · have h1 : (K'.map (MonoidHom.subgroupMap π C)).map (C.map π).subtype = Kq := by
      rw [hK'map']
      exact map_subgroupOf_eq_of_le hKC'
    rw [← h1, Subgroup.map_map, Subgroup.map_map]
    rfl

theorem eq_of_isTwoComponentAt_of_map_eq {x : G} {K M : Subgroup G} (hK : IsTwoComponentAt x K)
    (hM : IsTwoComponentAt x M) (h : K.map π = M.map π) : K = M :=
  GSThmB.OddQuot.eq_of_map_eq π (GSThmB.OddQuot.not_two_dvd_card_ker (H := G)) hK.2.1 hM.2.1
    hK.2.2 hM.2.2 h

theorem isPGroup_zpowers_of_orderOf {X : Type*} [Group X] {b : X} (hb : orderOf b = 2) :
    IsPGroup 2 (zpowers b) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])

theorem mem_coreActionKernel_of_map {x b : G} {K : Subgroup G} (hK : IsTwoComponentAt x K)
    (hb : orderOf b = 2) (hxb : x * b = b * x) (hbK : π b ∈ coreActionKernel (K.map π)) :
    b ∈ coreActionKernel K := by
  have hbC : b ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hxb.symm
  have hKb : IsTwoComponentAt x (conjugate K b) :=
    ⟨hK.1, conjugate_le_of_mem hK.2.1 hbC, isPComponent_conjugate_subgroupOf hbC hK.2.2⟩
  have hNb : b ∈ normalizer (K : Set G) := by
    apply mem_normalizer_of_conjugate_eq
    apply eq_of_isTwoComponentAt_of_map_eq hKb hK
    rw [UnbalancedLayer.map_conjugate, conjugate_eq_of_mem_normalizer hbK.1]
  have hz := isPGroup_zpowers_of_orderOf hb
  have h1 := GSThmB.OddQuot.map_inf_coreActionKernel (H := G) (X := K) (Y := zpowers b)
    ((zpowers_le).mpr hNb)
  have h2 : π b ∈ (zpowers b ⊓ coreActionKernel K).map π := by
    rw [h1]
    exact mem_inf.mpr ⟨mem_map_of_mem π (mem_zpowers b), hbK⟩
  obtain ⟨y, hy, hyb⟩ := mem_map.mp h2
  have hyeq : y = b :=
    GSThmB.OddQuot.injOn_of_isPGroup hz (mem_inf.mp hy).1 (mem_zpowers b) hyb
  rw [← hyeq]
  exact (mem_inf.mp hy).2

theorem map_footeFixed {b : G} {K : Subgroup G} (hb : orderOf b = 2)
    (hbK : b ∈ coreActionKernel K) : (footeFixed K b).map π = footeFixed (K.map π) (π b) := by
  have hz := isPGroup_zpowers_of_orderOf hb
  have hA : (K ⊓ centralizer ({b} : Set G)).map π =
      K.map π ⊓ centralizer ({π b} : Set (G ⧸ pPrimeCore 2 G)) := by
    have h := GSThmB.OddQuot.map_inf_centralizer π hz ((zpowers_le).mpr hbK.1)
      (GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict π
        (GSThmB.OddQuot.not_two_dvd_card_ker (H := G)) K)
    rw [centralizer_zpowers_eq, MonoidHom.map_zpowers, centralizer_zpowers_eq] at h
    exact h
  have hB : (oddCoreOfCentralizer b).map π = oddCoreOfCentralizer (π b) := by
    have h := GSThmB.OddQuot.map_oddCoreIn π (GSThmB.OddQuot.not_two_dvd_card_ker (H := G))
      (centralizer ({b} : Set G))
    rw [map_centralizer_mk hb] at h
    exact h
  rw [footeFixed_eq_oddResidualIn, footeFixed_eq_oddResidualIn, map_oddResidualIn_hom,
    Subgroup.map_sup, hA, hB]

theorem map_twoLayerOf {b : G} (hb : orderOf b = 2) :
    (twoLayerOf b).map π = twoLayerOf (π b) := by
  have h := GSThmB.OddQuot.map_layerIn π (GSThmB.OddQuot.not_two_dvd_card_ker (H := G))
    (centralizer ({b} : Set G))
  rw [map_centralizer_mk hb] at h
  exact h

theorem exists_footePointedStep_lift (hLB : FooteLBalanceInput) {a : G} {K : Subgroup G}
    (hK : IsTwoComponentAt a K) {cq : G ⧸ pPrimeCore 2 G} {Mq : Subgroup (G ⧸ pPrimeCore 2 G)}
    (h : FootePointedStep (π a) (K.map π) cq Mq) :
    ∃ (c : G) (M : Subgroup G), π c = cq ∧ M.map π = Mq ∧ FootePointedStep a K c M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hMq, hacq, hneq, hcKq, hclq⟩ := h
  have haa : a * a = 1 := by rw [← sq, ← hK.1, pow_orderOf_eq_one]
  obtain ⟨c, hc, hπc, hac⟩ := exists_involution_lift_commute hK.1 hMq.1 hacq
  subst hπc
  have hne : a ≠ c := fun h => hneq (by rw [h])
  have hcK : c ∈ coreActionKernel K := mem_coreActionKernel_of_map hK hc hac hcKq
  obtain ⟨B, hBc, -, -, hclB, -⟩ := exists_footeStep hLB hK hc hac hne hcK
  have hmap : B.map π ⊔ conjugate (B.map π) (π a) = Mq ⊔ conjugate Mq (π a) := by
    rw [← hclq, ← UnbalancedLayer.map_conjugate, ← Subgroup.map_sup, ← hclB, map_conjClosure,
      map_footeFixed hc hcK, map_twoLayerOf hc]
  have hπB := isTwoComponentAt_map hBc
  have hπaC : π a ∈ centralizer ({π c} : Set (G ⧸ pPrimeCore 2 G)) :=
    mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hac])
  have hMqa : IsTwoComponentAt (π c) (conjugate Mq (π a)) :=
    ⟨hMq.1, conjugate_le_of_mem hMq.2.1 hπaC, isPComponent_conjugate_subgroupOf hπaC hMq.2.2⟩
  have hle : B.map π ≤ Mq ⊔ conjugate Mq (π a) := hmap ▸ le_sup_left
  rcases eq_or_eq_of_isPComponent_le_sup hπB.2.1 hMq.2.1 hMqa.2.1 hπB.2.2 hMq.2.2 hMqa.2.2 hle
    with h1 | h1
  · exact ⟨c, B, rfl, h1, hK, hBc, hac, hne, hcK, hclB⟩
  · have haC : a ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.mpr hac
    have hπaa : π a * π a = 1 := by rw [← map_mul, haa, map_one]
    refine ⟨c, conjugate B a, rfl, ?_, hK,
      ⟨hc, conjugate_le_of_mem hBc.2.1 haC, isPComponent_conjugate_subgroupOf haC hBc.2.2⟩,
      hac, hne, hcK, ?_⟩
    · rw [UnbalancedLayer.map_conjugate, h1, conjugate_conjugate_self_of_mul_self hπaa]
    · rw [hclB, conjugate_conjugate_self_of_mul_self haa, sup_comm]

theorem exists_footePointedReach_lift (hLB : FooteLBalanceInput) {t : G} {L : Subgroup G}
    (hL : IsTwoComponentAt t L) {bq : G ⧸ pPrimeCore 2 G} {Kq : Subgroup (G ⧸ pPrimeCore 2 G)}
    (h : FootePointedReach (π t) (L.map π) bq Kq) :
    ∃ (b : G) (K : Subgroup G), π b = bq ∧ K.map π = Kq ∧ FootePointedReach t L b K := by
  unfold FootePointedReach at h
  generalize hp : ((π t, L.map π) : (G ⧸ pPrimeCore 2 G) × Subgroup (G ⧸ pPrimeCore 2 G)) = p
    at h
  generalize hq : ((bq, Kq) : (G ⧸ pPrimeCore 2 G) × Subgroup (G ⧸ pPrimeCore 2 G)) = q at h
  induction h generalizing bq Kq with
  | refl =>
    rw [← hq] at hp
    obtain ⟨h1, h2⟩ := Prod.mk.inj hp
    exact ⟨t, L, h1, h2, Relation.ReflTransGen.refl⟩
  | @tail r q' _ hstep ih =>
    obtain ⟨b, K, hb, hK, hreach⟩ := ih (bq := r.1) (Kq := r.2) rfl
    rw [← hq] at hstep
    change FootePointedStep r.1 r.2 bq Kq at hstep
    rw [← hb, ← hK] at hstep
    obtain ⟨c, M, hc, hM, hstep'⟩ := exists_footePointedStep_lift hLB (hreach.target hL) hstep
    exact ⟨c, M, hc, hM, Relation.ReflTransGen.tail hreach hstep'⟩

theorem footePointedMaximal_map (hLB : FooteLBalanceInput) {t : G} {L : Subgroup G}
    (hmax : FootePointedMaximal t L) : FootePointedMaximal (π t) (L.map π) := by
  refine ⟨isTwoComponentAt_map hmax.1, fun bq Kq h => ?_⟩
  obtain ⟨b, K, -, rfl, hreach⟩ := exists_footePointedReach_lift hLB hmax.1 h
  obtain ⟨e⟩ := hmax.2 b K hreach
  obtain ⟨eL⟩ := GSThmB.OddQuot.nonempty_quotient_fusionZStar_equiv π
    (GSThmB.OddQuot.not_two_dvd_card_ker (H := G)) L
  obtain ⟨eK⟩ := GSThmB.OddQuot.nonempty_quotient_fusionZStar_equiv π
    (GSThmB.OddQuot.not_two_dvd_card_ker (H := G)) K
  exact ⟨eL.symm.trans (e.trans eK)⟩

end Quotient

end CFSG.ComponentClassification.FooteLit
