module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceTypes
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Triple

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem eq_bot_of_odd_le_centralizer_generalizedFitting {X : Type} [Group X] [Finite X]
    (hX : pPrimeCore 2 X = ⊥) {D : Subgroup X}
    (hD : D ≤ centralizer (generalizedFitting X : Set X)) (hodd : Odd (Nat.card D)) :
    D = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (generalizedFitting X).Normal := generalizedFitting_normal
  have hAF : centralizer (generalizedFitting X : Set X) ≤ generalizedFitting X :=
    centralizer_generalizedFitting_le X
  have hAcomm : ∀ a ∈ centralizer (generalizedFitting X : Set X),
      ∀ b ∈ centralizer (generalizedFitting X : Set X), a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp ha b (hAF hb)).symm
  have hA2 : IsPGroup 2 (centralizer (generalizedFitting X : Set X)) :=
    isPGroup_two_of_normal_comm hX hAcomm
  have hD2 : IsPGroup 2 D := hA2.to_le hD
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥D)).mp hD2
  rw [hk] at hodd
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact card_eq_one.mp (by rw [hk, pow_zero])
  · exfalso
    rw [Nat.odd_iff] at hodd
    have : 2 ^ k % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hk0.ne')
    omega

theorem le_pPrimeCore_of_commutators {H : Type} [Group H] [Finite H] {D : Subgroup H}
    (hodd : Odd (Nat.card D))
    (hO22 : ∀ y ∈ (pCore 2 (H ⧸ pPrimeCore 2 H)).comap (QuotientGroup.mk' (pPrimeCore 2 H)),
      ∀ d ∈ D, y⁻¹ * d⁻¹ * y * d ∈ pPrimeCore 2 H)
    (hcomp : ∀ M : Subgroup H, IsPComponent 2 M → ∀ y ∈ M, ∀ d ∈ D,
      y⁻¹ * d⁻¹ * y * d ∈ pPrimeCore 2 H) :
    D ≤ pPrimeCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  have hcore : pPrimeCore 2 (H ⧸ pPrimeCore 2 H) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have key : ∀ y : H, (∀ d ∈ D, y⁻¹ * d⁻¹ * y * d ∈ pPrimeCore 2 H) →
      π y ∈ centralizer ((D.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) := by
    intro y hy
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have h := (QuotientGroup.eq_one_iff _).mpr (hy d hd)
    have h3 : (π y)⁻¹ * (π d)⁻¹ * π y * π d = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h
    calc π d * π y = π d * π y * ((π y)⁻¹ * (π d)⁻¹ * π y * π d) := by rw [h3, mul_one]
      _ = π y * π d := by group
  have hF : generalizedFitting (H ⧸ pPrimeCore 2 H) ≤
      centralizer ((D.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) := by
    refine sup_le ?_ ?_
    · refine (GorensteinWalter.fittingSubgroup_le_sup_pCore_pPrimeCore).trans ?_
      rw [hcore, sup_bot_eq]
      intro z hz
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 H) z
      exact key y (hO22 y hz)
    · rw [← LBalance.Quot.map_pLayer_eq_layer_quotient, map_le_iff_le_comap]
      refine sSup_le fun M hM y hy => ?_
      exact key y (hcomp M hM y hy)
  have hDbar : D.map π ≤ centralizer (generalizedFitting (H ⧸ pPrimeCore 2 H) :
      Set (H ⧸ pPrimeCore 2 H)) := (le_centralizer_iff).mp hF
  have hodd' : Odd (Nat.card (D.map π)) := hodd.of_dvd_nat (Subgroup.card_map_dvd D π)
  have hbot := eq_bot_of_odd_le_centralizer_generalizedFitting hcore hDbar hodd'
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem centralizer_zpowers_eq {G : Type*} [Group G] (g : G) :
    centralizer (zpowers g : Set G) = centralizer ({g} : Set G) := by
  ext y
  rw [mem_centralizer_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h g (mem_zpowers g)).symm
  · intro h z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute g y from h.symm) k).eq

theorem eq_of_mem_zpowers_of_ne_one {G : Type*} [Group G] {e s : G} (he : orderOf e = 2)
    (hs : s ∈ zpowers e) (hs1 : s ≠ 1) : s = e := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exfalso
    apply hs1
    rw [← zpow_mod_orderOf, he, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · rw [← zpow_mod_orderOf, he, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

theorem solomon_at (hSol : SolomonCommutingCoreInput) {G : Type} [Group G] [Finite G] {e x : G}
    (he : orderOf e = 2) (hx : orderOf x = 2) (hex : e * x = x * e) :
    ⁅((pCore 2 (centralizer ({x} : Set G) ⧸ pPrimeCore 2 (centralizer ({x} : Set G)))).comap
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({x} : Set G))))).map
          (centralizer ({x} : Set G)).subtype,
      (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype ⊓
        centralizer ({x} : Set G)⁆ ≤
      (pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ∧
    ∀ L : Subgroup G, L ≤ centralizer ({x} : Set G) →
      IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set G))) →
      ¬ ⁅L, (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype ⊓
        centralizer ({x} : Set G)⁆ ≤ (pPrimeCore 2 L).map L.subtype →
      e ∈ normalizer (L : Set G) := by
  have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he; exact absurd he (by norm_num)
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; exact absurd hx (by norm_num)
  have he2 : e * e = 1 := by rw [← pow_two, ← he, pow_orderOf_eq_one]
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hS := isElemTwo_zpowers he2
  have hT := isElemTwo_zpowers hx2
  have hST : ∀ y ∈ zpowers e, ∀ z ∈ zpowers x, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
    exact ((Commute.zpow_zpow (show Commute e x from hex) i j)).eq
  have h := hSol G (zpowers e) (zpowers x)
    (fun hb => he1 (by rw [← mem_bot, ← hb]; exact mem_zpowers e))
    (fun hb => hx1 (by rw [← mem_bot, ← hb]; exact mem_zpowers x))
    hS.1 hS.2 hT.1 hT.2 hST
  obtain ⟨⟨h1, -⟩, h2, -⟩ := h
  let P : Subgroup G → Subgroup G → Prop := fun A K =>
    ⁅((pCore 2 (K ⧸ pPrimeCore 2 K)).comap (QuotientGroup.mk' (pPrimeCore 2 K))).map K.subtype,
      (pPrimeCore 2 A).map A.subtype ⊓ K⁆ ≤ (pPrimeCore 2 K).map K.subtype
  let Q : Subgroup G → Subgroup G → Prop := fun A K =>
    ∀ L : Subgroup G, L ≤ K → IsPComponent 2 (L.subgroupOf K) →
      ¬ ⁅L, (pPrimeCore 2 A).map A.subtype ⊓ K⁆ ≤ (pPrimeCore 2 L).map L.subtype →
      zpowers e ⊓ normalizer (L : Set G) ≠ ⊥
  have h1' : P (centralizer (zpowers e : Set G)) (centralizer (zpowers x : Set G)) := h1
  have h2' : Q (centralizer (zpowers e : Set G)) (centralizer (zpowers x : Set G)) :=
    fun L hLC hL hLD => ((h2 L hLC hL).2 hLD).1
  rw [centralizer_zpowers_eq, centralizer_zpowers_eq] at h1' h2'
  refine ⟨h1', fun L hLC hL hLD => ?_⟩
  have hne := h2' L hLC hL hLD
  obtain ⟨⟨s, hs⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  rw [mem_inf] at hs
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  rw [← eq_of_mem_zpowers_of_ne_one he hs.1 hs1']
  exact hs.2

@[expose] def LocallyTwoBalancedAt (G : Type*) [Group G] : Prop :=
  ∀ J : Subgroup G, IsUnbalancingComponent J → ∀ a : G, orderOf a = 2 →
    J ≤ centralizer ({a} : Set G) → IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) →
    ∀ E : Subgroup G, E ≤ normalizer (J : Set G) ⊓ centralizer ({a} : Set G) →
      Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      ⁅J, wGroup E ⊓ centralizer ({a} : Set G)⁆ ≤
        (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype

theorem locallyTwoBalancedAt_of_locallyTwoBalanced {G : Type*} [Group G]
    (h : LocallyTwoBalanced G) : LocallyTwoBalancedAt G :=
  fun J hJ a ha hJa _ E hE hE4 => h J hJ a ha hJa E hE hE4

theorem gwTwoBalanced_of_locallyTwoBalancedAt (hSol : SolomonCommutingCoreInput) {G : Type}
    [Group G] [Finite G] (hLB : LocallyTwoBalancedAt G) : GWTwoBalanced G := by
  intro E hE4 x hx hxE
  obtain ⟨φ⟩ := hE4
  have hm : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * y = 1 := by decide
  have h4 : Nat.card E = 4 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
    rfl
  have h2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have : (⟨e, he⟩ : E) * ⟨e, he⟩ = 1 := φ.injective (by rw [map_mul, map_one, hm])
    exact congrArg Subtype.val this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  set Δ : Subgroup G := ⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
    (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype with hΔ
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hxC : ∀ g, x * g = g * x → g ∈ C := fun g hg => mem_centralizer_singleton_iff.mpr hg.symm
  obtain ⟨e, heE, he1, hex⟩ : ∃ e ∈ E, e ≠ 1 ∧ e ≠ x := by
    by_contra h
    push Not at h
    have hle : E ≤ zpowers x := fun g hg => by
      by_cases hg1 : g = 1
      · rw [hg1]; exact one_mem _
      · rw [h g hg hg1]; exact mem_zpowers x
    have h1 := Subgroup.card_le_of_le hle
    rw [h4, Nat.card_zpowers, hx] at h1
    omega
  have hord : ∀ g ∈ E, g ≠ 1 → orderOf g = 2 := fun g hg hg1 =>
    orderOf_eq_prime (by rw [pow_two]; exact h2 g hg) hg1
  have he : orderOf e = 2 := hord e heE he1
  have hexc : e * x = x * e := hxE e heE
  have hΔe : ∀ g ∈ E, g ≠ 1 → Δ ≤ (pPrimeCore 2 (centralizer ({g} : Set G))).map
      (centralizer ({g} : Set G)).subtype := fun g hg hg1 =>
    (iInf_le _ g).trans ((iInf_le _ hg).trans (iInf_le _ hg1))
  set D'' : Subgroup ↥C := (Δ ⊓ C).subgroupOf C with hD''
  have hmemH : ∀ z : ↥C, (z : G) ∈ (pPrimeCore 2 ↥C).map C.subtype →
      z ∈ pPrimeCore 2 ↥C := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hz
    rwa [← Subtype.ext hwz]
  have hodd : Odd (Nat.card D'') := by
    have hle : Δ ⊓ C ≤ (pPrimeCore 2 (centralizer ({e} : Set G))).map
        (centralizer ({e} : Set G)).subtype := inf_le_left.trans (hΔe e heE he1)
    have h1 : Nat.card D'' = Nat.card ↥(Δ ⊓ C) := by
      rw [hD'', ← card_map_of_injective C.subtype_injective, subgroupOf_map_subtype,
        inf_eq_left.mpr (inf_le_right : Δ ⊓ C ≤ C)]
    have h2 := card_dvd_of_le hle
    rw [card_map_of_injective (centralizer ({e} : Set G)).subtype_injective] at h2
    rw [h1]
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h2
  obtain ⟨hO22, hnorm⟩ := solomon_at hSol he hx hexc
  have hDΔ : Δ ⊓ C ≤ (pPrimeCore 2 (centralizer ({e} : Set G))).map
      (centralizer ({e} : Set G)).subtype ⊓ C := inf_le_inf_right _ (hΔe e heE he1)
  have hle := le_pPrimeCore_of_commutators (H := ↥C) (D := D'') hodd ?_ ?_
  · intro g hg
    have hgC : g ∈ C := (mem_inf.mp hg).2
    have hmem : (⟨g, hgC⟩ : ↥C) ∈ D'' := hg
    exact ⟨⟨g, hgC⟩, hle hmem, rfl⟩
  ·
    intro y hy d hd
    apply hmemH
    have hy' : (y : G)⁻¹ ∈ ((pCore 2 (↥C ⧸ pPrimeCore 2 ↥C)).comap
        (QuotientGroup.mk' (pPrimeCore 2 ↥C))).map C.subtype := ⟨y⁻¹, inv_mem hy, rfl⟩
    have hd' : (d : G)⁻¹ ∈ (pPrimeCore 2 (centralizer ({e} : Set G))).map
        (centralizer ({e} : Set G)).subtype ⊓ C := hDΔ (inv_mem (show (d : G) ∈ Δ ⊓ C from hd))
    have := hO22 (commutator_mem_commutator hy' hd')
    rw [commutatorElement_def, inv_inv, inv_inv] at this
    exact this
  ·
    intro M hM y hy d hd
    apply hmemH
    set M' : Subgroup G := M.map C.subtype with hM'
    have hM'C : M' ≤ C := map_subtype_le M
    have hM'sub : M'.subgroupOf C = M := comap_map_eq_self_of_injective C.subtype_injective M
    have hM'p : IsPComponent 2 (M'.subgroupOf C) := hM'sub ▸ hM
    have hyM' : (y : G) ∈ M' := ⟨y, hy, rfl⟩
    have hdΔ : (d : G) ∈ Δ ⊓ C := hd
    by_cases hA : ∀ y' ∈ M', ∀ d' ∈ Δ ⊓ C, y'⁻¹ * d'⁻¹ * y' * d' ∈ (pPrimeCore 2 M').map M'.subtype
    · exact GSLit.map_pPrimeCore_le_of_isPComponent hM'C hM'p (hA _ hyM' _ hdΔ)
    · push Not at hA
      obtain ⟨y', hy', d', hd', hnot⟩ := hA
      have hEN : E ≤ normalizer (M' : Set G) := by
        intro g hg
        by_cases hg1 : g = 1
        · rw [hg1]; exact one_mem _
        by_cases hgx : g = x
        · rw [hgx, mem_normalizer_iff]
          intro z
          constructor
          · intro hz
            rwa [(mem_centralizer_singleton_iff.mp (hM'C hz)).symm, mul_inv_cancel_right]
          · intro hz
            have hzC := hM'C hz
            have hc := mem_centralizer_singleton_iff.mp hzC
            have : z = x * z * x⁻¹ := by
              have e1 : x * z * x⁻¹ * x = x * z := by group
              have e2 : (x * z * x⁻¹) * x = x * (x * z * x⁻¹) := hc
              calc z = x⁻¹ * (x * z * x⁻¹ * x) := by group
                _ = x⁻¹ * (x * (x * z * x⁻¹)) := by rw [e2]
                _ = x * z * x⁻¹ := by group
            rw [this]
            exact hz
        · have hgo := hord g hg hg1
          have hgx' : g * x = x * g := hxE g hg
          have hDg := hΔe g hg hg1
          refine (solomon_at hSol hgo hx hgx').2 M' hM'C hM'p fun hle => hnot ?_
          have hmem : y'⁻¹ * d'⁻¹ * y' * d' ∈ ⁅M', (pPrimeCore 2 (centralizer ({g} : Set G))).map
              (centralizer ({g} : Set G)).subtype ⊓ C⁆ := by
            have := commutator_mem_commutator (inv_mem hy')
              (inv_mem (inf_le_inf_right C hDg hd'))
            rwa [commutatorElement_def, inv_inv, inv_inv] at this
          exact hle hmem
      have hU : IsUnbalancingComponent M' :=
        ⟨x, e, GSThmB.Eight.gsUnbalancingTriple_of_active (G := G) (w := x) (a := e) hx he
          hexc.symm hM'C hM'p (d := d') (inf_le_inf_right C (hΔe e heE he1) hd') hy' hnot⟩
      have hEle : E ≤ normalizer (M' : Set G) ⊓ centralizer ({x} : Set G) :=
        le_inf hEN fun g hg => hxC g (hxE g hg).symm
      have hloc := hLB M' hU x hx hM'C hM'p E hEle ⟨φ⟩
      rw [wGroup_eq_iInf_of_four h4 h2] at hloc
      have := hloc (commutator_mem_commutator (inv_mem hyM') (inv_mem hdΔ))
      rw [commutatorElement_def, inv_inv, inv_inv] at this
      exact this

theorem gwTwoBalanced_of_locallyTwoBalanced (hSol : SolomonCommutingCoreInput) {G : Type}
    [Group G] [Finite G] (hLB : LocallyTwoBalanced G) : GWTwoBalanced G :=
  gwTwoBalanced_of_locallyTwoBalancedAt hSol (locallyTwoBalancedAt_of_locallyTwoBalanced hLB)

theorem locallyTwoBalanced_of_gwTwoBalanced {G : Type} [Group G] [Finite G] (h : GWTwoBalanced G) :
    LocallyTwoBalanced G := by
  intro J _ a ha hJa E hE hE4
  obtain ⟨φ⟩ := id hE4
  have h4 : Nat.card E = 4 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
    rfl
  have h2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have hm : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * y = 1 := by decide
    have : (⟨e, he⟩ : E) * ⟨e, he⟩ = 1 := φ.injective (by rw [map_mul, map_one, hm])
    exact congrArg Subtype.val this
  rw [wGroup_eq_iInf_of_four h4 h2]
  have hle := h E hE4 a ha fun e he => (mem_centralizer_singleton_iff.mp (mem_inf.mp (hE he)).2)
  rw [commutator_le]
  intro j hj d hd
  have hdO := hle hd
  have hdC : d ∈ centralizer ({a} : Set G) := (mem_inf.mp hd).2
  have hjC : j ∈ centralizer ({a} : Set G) := hJa hj
  have hO : centralizer ({a} : Set G) ≤ normalizer
      (((pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype :
        Subgroup G) : Set G) := by
    have h := Subgroup.le_normalizer_map (H := pPrimeCore 2 (centralizer ({a} : Set G)))
      (centralizer ({a} : Set G)).subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.mp (hO hjC) d).mp hdO) (inv_mem hdO)

end CFSG.ComponentClassification.GrSLit
