module

public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentInitial.StandardCriterion
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup
public import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorConfiguration
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBLocalB
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

namespace RankDominance

variable {X : Type*} [Group X] [Finite X]

theorem isTwoPComponent_of_isComponent {K : Subgroup X} (hK : CFSG.IsComponent K) :
    CFSG.Assembly.ComponentType.IsTwoPComponent K :=
  (isTwoPComponent_iff_isPComponent K).2
    ((solvable_prime_core_ordinary_components 2 Nat.prime_two (CFSG.FeitThompson.isSolvable_of_odd_natCard _
      (Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card))).1 K hK)

theorem closure_pair_four {x y : X} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : x * y = y * x) (hne : x ≠ y) :
    CFSG.IsElementaryAbelian 2 (closure ({x, y} : Set X)) ∧
      Nat.card (closure ({x, y} : Set X)) = 4 := by
  obtain ⟨V, hV, hVe, hV4⟩ := AlternatingFourGroup.exists_elementary_four_of_commute hx hy hxy hne
  have hcl : closure ({x, y} : Set X) = zpowers x ⊔ zpowers y := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hcomm : ∀ a ∈ zpowers x, ∀ b ∈ zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    exact ((Commute.zpow_zpow (show Commute x y from hxy) i j))
  have hle : Nat.card (closure ({x, y} : Set X)) ≤ 4 := by
    have h := card_sup_mul_card_inf_of_commute hcomm
    rw [Nat.card_zpowers, Nat.card_zpowers, hx, hy] at h
    rw [hcl]
    have hpos : 0 < Nat.card ↥(zpowers x ⊓ zpowers y) := Nat.card_pos
    nlinarith
  have heq : V = closure ({x, y} : Set X) := Subgroup.eq_of_le_of_card_ge hV (by omega)
  subst heq
  exact ⟨hVe, hV4⟩


omit [Finite X] in
theorem card_eq_two_pow_pRank [Finite X] {A : Subgroup X} (hA : CFSG.IsElementaryAbelian 2 A) :
    Nat.card A = 2 ^ CFSG.pRank 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA' := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).1 hA
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one]; exact hA'.2 _ x.2)⟩
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank 2 A := CFSG.SectionRank.le_pRank one_lt_two le_rfl hA' hk
  have h2 : CFSG.Open.pRank 2 A ≤ k := CFSG.SectionRank.pRank_le one_lt_two fun F hFA _ => by
    rw [← hk]
    exact Subgroup.card_le_of_le hFA
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, hk,
    le_antisymm h1 h2]

section Propagation

variable {C : CFSG.Assembly.GroupProp} {G : Type} [Group G] [Finite G]

theorem propagation (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) (hK : CFSG.Assembly.KProper C G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) {J A : Subgroup G}
    (hAe : CFSG.IsElementaryAbelian 2 A)
    (hM1 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
        (center Q).index ≤ (center J).index)
    (hM2 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
      CFSG.Assembly.ComponentType.IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
      (center Q).index = (center J).index →
        (CFSG.pPrimeCore 2 Q).index ≤ (CFSG.pPrimeCore 2 J).index)
    (hM3 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
      CFSG.Assembly.ComponentType.IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
      (center Q).index = (center J).index →
      (CFSG.pPrimeCore 2 Q).index = (CFSG.pPrimeCore 2 J).index →
      ∀ B : Subgroup G, B ≤ centralizer (Q : Set G) → CFSG.IsElementaryAbelian 2 B → t ∈ B →
        Nat.card B ≤ Nat.card A)
    (hrs : CFSG.pRank 2 A ≤ CFSG.pRank 2 J) {t b : G} (ht : orderOf t = 2) (hb : orderOf b = 2)
    (htC : t ∈ centralizer (J : Set G)) (hbC : b ∈ centralizer (J : Set G)) (htb : t * b = b * t)
    (hJt : CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G))) :
    CFSG.Assembly.IsComponentOf J (centralizer ({b} : Set G)) := by
  by_cases htb' : t = b
  · subst htb'
    exact hJt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({b} : Set G) with hHdef
  have hJH : J ≤ H := fun x hx => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hbC x hx)
  have htH : t ∈ H := mem_centralizer_singleton_iff.2 htb
  have hbH : b ∈ H := mem_centralizer_singleton_iff.2 rfl
  have hKH : CFSG.Assembly.KProper C H := kProper_subgroup hC hK H
  have hlocB : ∀ Q : Subgroup H, CFSG.Assembly.ComponentType.IsTwoPComponent Q →
      CFSG.Assembly.IsComponentOf Q ⊤ := fun Q hQ =>
    AssemblyBLocalB.ordinary_at_involution hB b hb Q hQ
  set t' : H := ⟨t, htH⟩ with ht'def
  set b' : H := ⟨b, hbH⟩ with hb'def
  have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hb' : orderOf b' = 2 := by rw [Subgroup.orderOf_mk]; exact hb
  have hJ' : CFSG.Assembly.IsComponentOf (J.subgroupOf H) (centralizer ({t'} : Set H)) := by
    rw [← isComponentOf_map_iff H.subtype_injective, map_centralizer_singleton_of_injective
      H.subtype_injective, Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le hJH]
    exact isComponentOf_of_le hJt (le_inf hJH hJt.1) inf_le_right
  obtain ⟨-, M, hM, hcase⟩ := hpump H hKH hlocB t' ht' _ hJ'
  have hMG : CFSG.Assembly.IsComponentOf (M.map H.subtype) H := by
    have h := (isComponentOf_map_iff H.subtype_injective (Q := M) (K := ⊤)).2
      ((AssemblyBPredicates.isComponentOf_top_iff_native M).2 hM)
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rcases hcase with ⟨-, hJM⟩ | ⟨hMt, hJset, ⟨δ, hδ, hδs, hδker⟩, ⟨eJM⟩⟩
  ·
    have hJle : J.subgroupOf H ≤ M := hJM.1.trans inf_le_left
    rcases hJle.lt_or_eq with hlt | heq
    · exfalso
      have : Group.IsPerfect M := hM.1.1
      have h1 := index_center_lt_of_lt hlt
      have h2 := hM1 b hb _ hMG
      rw [index_center_eq_of_mulEquiv (M.equivMapOfInjective H.subtype H.subtype_injective),
        index_center_eq_of_mulEquiv (subgroupOfEquivOfLe hJH)] at h1
      omega
    · have h := (isComponentOf_map_iff H.subtype_injective (Q := J.subgroupOf H) (K := ⊤)).2
        ((AssemblyBPredicates.isComponentOf_top_iff_native _).2 (heq ▸ hM))
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype,
        Subgroup.map_subgroupOf_eq_of_le hJH] at h
  ·
    exfalso
    set MG := M.map H.subtype with hMGdef
    let eM : M ≃* MG := M.equivMapOfInjective H.subtype H.subtype_injective
    let eJ : J.subgroupOf H ≃* J := subgroupOfEquivOfLe hJH
    have hdJ' : (center (J.subgroupOf H)).index = (center M).index := Nat.card_congr eJM.toEquiv
    have hdMG : (center MG).index = (center J).index := by
      rw [← index_center_eq_of_mulEquiv eM, ← hdJ', index_center_eq_of_mulEquiv eJ]
    have hMG2 : CFSG.Assembly.ComponentType.IsTwoPComponent (MG.subgroupOf H) := by
      have h : MG.subgroupOf H = M := Subgroup.comap_map_eq_self_of_injective H.subtype_injective M
      rw [h]
      exact isTwoPComponent_of_isComponent hM
    have hcore : ∀ {X Y : Type} [Group X] [Group Y] (e : X ≃* Y),
        (CFSG.pPrimeCore 2 X).index = (CFSG.pPrimeCore 2 Y).index := fun e => by
      rw [← CFSG.pPrimeCore_map_iso 2 e]
      exact (Subgroup.index_map_equiv _ e).symm
    have heM := hM2 b hb MG hMG hMG2 hdMG
    rw [← hcore eM] at heM
    have himg : (CFSG.pPrimeCore 2 M).map δ ≤ CFSG.pPrimeCore 2 (J.subgroupOf H) := by
      apply le_sSup
      refine ⟨Subgroup.Normal.map inferInstance δ hδs, ?_⟩
      exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ δ)
        (CFSG.pPrimeCore_coprime_card (p := 2) (G := M))
    have hle : (CFSG.pPrimeCore 2 (J.subgroupOf H)).index ≤ (CFSG.pPrimeCore 2 M).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        ((Subgroup.index_dvd_of_le himg).trans (Subgroup.index_map_dvd _ hδs))
    have heq : (CFSG.pPrimeCore 2 M).index = (CFSG.pPrimeCore 2 (J.subgroupOf H)).index := by
      rw [hcore eJ] at hle ⊢
      omega
    have hcardM : Nat.card M = Nat.card (J.subgroupOf H) * Nat.card δ.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective δ hδs).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
    have hoddker : Odd (Nat.card δ.ker) := by
      have h1 := (CFSG.pPrimeCore 2 M).index_mul_card
      have h2 := (CFSG.pPrimeCore 2 (J.subgroupOf H)).index_mul_card
      have hO : Nat.card (CFSG.pPrimeCore 2 M) =
          Nat.card (CFSG.pPrimeCore 2 (J.subgroupOf H)) * Nat.card δ.ker := by
        have he0 : (CFSG.pPrimeCore 2 M).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he0)
        rw [h1, hcardM, ← h2, heq, mul_assoc]
      have hc := CFSG.pPrimeCore_coprime_card (p := 2) (G := M)
      rw [hO] at hc
      exact Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hc)
    have hrk : ∀ {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y),
        CFSG.pRank 2 X = CFSG.pRank 2 Y := fun e => by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e
    have hrankM : CFSG.pRank 2 J ≤ CFSG.pRank 2 M := by
      let S : Sylow 2 M := default
      have hinj : Function.Injective (δ.comp (S : Subgroup M).subtype) := by
        rw [injective_iff_map_eq_one]
        intro x hx
        obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.1 S.isPGroup' x
        have hxk : (x : M) ∈ δ.ker := hx
        have hdvd : orderOf (⟨(x : M), hxk⟩ : δ.ker) ∣ Nat.card δ.ker := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hn] at hdvd
        have hn0 : n = 0 := by
          by_contra hn0
          exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hoddker hdvd))
            ((Nat.even_pow' hn0).2 even_two)
        rw [hn0, pow_zero, orderOf_eq_one_iff] at hn
        exact hn
      let T := (δ.comp (S : Subgroup M).subtype).range
      have hTcard : Nat.card T = Nat.card S :=
        (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hv : (Nat.card M).factorization 2 = (Nat.card (J.subgroupOf H)).factorization 2 := by
        rw [hcardM, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd
            (fun h => (Nat.not_even_iff_odd.2 hoddker) (even_iff_two_dvd.2 h)), add_zero]
      have hTsyl : Nat.card T = 2 ^ (Nat.card (J.subgroupOf H)).factorization 2 := by
        rw [hTcard, Sylow.card_eq_multiplicity, hv]
      let T' : Sylow 2 (J.subgroupOf H) := Sylow.ofCard T hTsyl
      have h1 := (CFSG.SectionRank.pRank_sylow S).2
      have h2 := (CFSG.SectionRank.pRank_sylow T').2
      have h3 : CFSG.pRank 2 (T' : Subgroup (J.subgroupOf H)) = CFSG.pRank 2 (S : Subgroup M) := by
        rw [Sylow.coe_ofCard]
        exact (hrk (MonoidHom.ofInjective hinj)).symm
      have h4 := hrk eJ
      omega
    have htb'' : t' ≠ b' := fun h => htb' (congrArg Subtype.val h)
    have htbc : t' * b' = b' * t' := Subtype.ext htb
    obtain ⟨hUe, hU4⟩ := closure_pair_four ht' hb' htbc htb''
    obtain ⟨hJdiag, -, -, -, -, -, -, -, -, -, -, hprod⟩ :=
      diagonal_component_centralizer_index_two hM hMt ht'
    have hJeq : (swapDiag (commutator_conjSub_eq_bot hM hMt)).range = J.subgroupOf H :=
      SetLike.ext' (hJdiag.trans hJset.symm)
    have hUCJ : closure ({t', b'} : Set H) ≤
        centralizer (((swapDiag (commutator_conjSub_eq_bot hM hMt)).range : Subgroup H) :
          Set H) := by
      rw [hJeq, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · rw [SetLike.mem_coe, mem_centralizer_iff]
        intro x hx
        exact Subtype.ext (mem_centralizer_iff.1 htC x hx)
      · rw [SetLike.mem_coe, mem_centralizer_iff]
        intro x hx
        exact Subtype.ext (mem_centralizer_iff.1 hbC x hx)
    have ht'U : t' ∈ closure ({t', b'} : Set H) := subset_closure (Set.mem_insert _ _)
    have hb'U : b' ∈ closure ({t', b'} : Set H) := subset_closure (by simp)
    obtain ⟨-, hBprod⟩ := hprod _ hUCJ hUe ht'U
    have hUt : closure ({t', b'} : Set H) ≤ centralizer ({t'} : Set H) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact mem_centralizer_singleton_iff.2 rfl
      · exact mem_centralizer_singleton_iff.2 htbc.symm
    have hbot : closure ({t', b'} : Set H) ⊓
        centralizer ((M ⊔ conjSub t'⁻¹ M : Subgroup H) : Set H) ⊓ conjSub t'⁻¹ M = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨hxU, -⟩, y, hyM, hyx⟩
      have hxt : x * t' = t' * x := mem_centralizer_singleton_iff.1 (hUt hxU)
      have hx2 : x ^ 2 = 1 := by
        have := hUe
        exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hxU
      have hyx' : t'⁻¹ * y * t' = x := by simpa using hyx
      have hyxe : y = x := by
        calc y = t' * (t'⁻¹ * y * t') * t'⁻¹ := by group
          _ = t' * x * t'⁻¹ := by rw [hyx']
          _ = x := by rw [← hxt]; group
      subst hyxe
      have hconj : t'⁻¹ * y * t' = y := hyx'
      have hδy : δ ⟨y, hyM⟩ = 1 := by
        apply Subtype.ext
        rw [hδ, hconj, ← sq, hx2]
        rfl
      have hk : (⟨y, hyM⟩ : M) ∈ δ.ker := hδy
      have hdvd : orderOf (⟨⟨y, hyM⟩, hk⟩ : δ.ker) ∣ Nat.card δ.ker := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at hdvd
      exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
        (Nat.coprime_two_left.2 hoddker) (orderOf_dvd_of_pow_eq_one hx2) hdvd))
    obtain ⟨B, hBM, hBe, hBcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two
      (conjSub t'⁻¹ M)
    have hBrank : CFSG.pRank 2 J ≤ CFSG.Open.pRank 2 (conjSub t'⁻¹ M) := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← hrk (M.equivMapOfInjective _ (MulAut.conj t'⁻¹).injective)]
      exact hrankM
    obtain ⟨hWM, hWe, hWcard⟩ := hBprod B hBM
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 B).2 hBe)
      (by rw [hbot]; exact bot_le)
    rw [hbot, Subgroup.card_bot, hU4, hBcard] at hWcard
    set W := closure ({t', b'} : Set H) ⊓
      centralizer ((M ⊔ conjSub t'⁻¹ M : Subgroup H) : Set H) ⊔ B with hWdef
    have hb'C : ∀ X : Set H, b' ∈ centralizer X := fun X => mem_centralizer_iff.2 fun h _ =>
      Subtype.ext (mem_centralizer_singleton_iff.1 h.2)
    have hb'W : b' ∈ W := le_sup_left (a := closure ({t', b'} : Set H) ⊓
      centralizer ((M ⊔ conjSub t'⁻¹ M : Subgroup H) : Set H)) ⟨hb'U, hb'C _⟩
    have hWG : W.map H.subtype ≤ centralizer (MG : Set G) := by
      rintro _ ⟨w, hw, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨m, hm, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.1 (hWM hw) m hm)
    have hWGe : CFSG.IsElementaryAbelian 2 (W.map H.subtype) := by
      have := hWe
      exact CFSG.IsElementaryAbelian.map_subtype
    have heMG : (CFSG.pPrimeCore 2 MG).index = (CFSG.pPrimeCore 2 J).index := by
      rw [← hcore eM, heq, hcore eJ]
    have hcardW := hM3 b hb MG hMG hMG2 hdMG heMG _ hWG hWGe ⟨b', hb'W, rfl⟩
    rw [Subgroup.card_map_of_injective H.subtype_injective, hWcard] at hcardW
    have hA : Nat.card A = 2 ^ CFSG.pRank 2 A := card_eq_two_pow_pRank hAe
    rw [hA] at hcardW
    have hpow : 2 ^ CFSG.pRank 2 A ≤ 2 ^ CFSG.Open.pRank 2 (conjSub t'⁻¹ M) :=
      Nat.pow_le_pow_right (by norm_num) (hrs.trans hBrank)
    have hpos : 0 < 2 ^ CFSG.Open.pRank 2 (conjSub t'⁻¹ M) := by positivity
    omega

end Propagation

end RankDominance

open RankDominance

theorem rank_dominance_propagates_selected_component {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G) (hB : CFSG.Assembly.ComponentType.LocalBProperty G)
    {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set G)))
    (_hJ2 : CFSG.Assembly.ComponentType.IsTwoPComponent (J.subgroupOf (centralizer ({a} : Set G))))
    {A : Subgroup G} (hAC : A ≤ centralizer (J : Set G)) (hAe : CFSG.IsElementaryAbelian 2 A)
    (haA : a ∈ A)
    (hM1 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
        (center Q).index ≤ (center J).index)
    (hM2 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
      CFSG.Assembly.ComponentType.IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
      (center Q).index = (center J).index →
        (CFSG.pPrimeCore 2 Q).index ≤ (CFSG.pPrimeCore 2 J).index)
    (hM3 : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
      CFSG.Assembly.ComponentType.IsTwoPComponent (Q.subgroupOf (centralizer ({t} : Set G))) →
      (center Q).index = (center J).index →
      (CFSG.pPrimeCore 2 Q).index = (CFSG.pPrimeCore 2 J).index →
      ∀ B : Subgroup G, B ≤ centralizer (Q : Set G) → CFSG.IsElementaryAbelian 2 B → t ∈ B →
        Nat.card B ≤ Nat.card A) :
    (CFSG.pRank 2 A ≤ CFSG.pRank 2 J →
      (∀ t ∈ centralizer (J : Set G), orderOf t = 2 →
        CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G))) ∧
      CFSG.pRank 2 (centralizer (J : Set G)) = CFSG.pRank 2 A) ∧
    (CFSG.pRank 2 A < CFSG.pRank 2 J → CFSG.Assembly.ComponentType.IsStandardSubgroup J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CJ := centralizer (J : Set G) with hCJ
  have haC : a ∈ CJ := hAC haA
  have hUM : CFSG.pRank 2 A ≤ CFSG.pRank 2 J → ∀ t ∈ CJ, orderOf t = 2 →
      CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G)) := by
    intro hrs
    have hprop := fun {t b : G} (ht : orderOf t = 2) (hb : orderOf b = 2) (htC : t ∈ CJ)
        (hbC : b ∈ CJ) (htb : t * b = b * t)
        (hJt : CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G))) =>
      propagation hC hpump hK hB hAe hM1 hM2 hM3 hrs ht hb htC hbC htb hJt
    let a' : CJ := ⟨a, haC⟩
    have ha' : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha
    obtain ⟨P, haP⟩ := (IsPGroup.of_card (n := 1)
      (show Nat.card (zpowers a') = 2 ^ 1 by rw [Nat.card_zpowers, ha', pow_one])).exists_le_sylow
    have ha'P : a' ∈ (P : Subgroup CJ) := haP (mem_zpowers a')
    have hPnt : Nontrivial (P : Subgroup CJ) := ⟨⟨⟨a', ha'P⟩, 1, fun h => by
      have h1 : a' = 1 := congrArg Subtype.val h
      rw [h1, orderOf_one] at ha'
      exact absurd ha' (by norm_num)⟩⟩
    have hZnt : Nontrivial (center (P : Subgroup CJ)) := P.isPGroup'.center_nontrivial
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (P.isPGroup'.to_subgroup (center (P : Subgroup CJ)))
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' hk
    obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' (G := center (P : Subgroup CJ)) 2
      (by rw [hk]; exact dvd_pow_self 2 hk0)
    set zG : G := (((z : P) : CJ) : G) with hzGdef
    have hzG2 : orderOf zG = 2 := by
      rw [hzGdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz2]
    have hzC : zG ∈ CJ := ((z : P) : CJ).2
    have hzcomm : ∀ y ∈ (P : Subgroup CJ), (y : G) * zG = zG * y := fun y hy => by
      have := mem_center_iff.1 z.2 ⟨y, hy⟩
      exact congrArg (fun w : (P : Subgroup CJ) => ((w : CJ) : G)) this
    have hJz : CFSG.Assembly.IsComponentOf J (centralizer ({zG} : Set G)) :=
      hprop ha hzG2 haC hzC (hzcomm a' ha'P) hJ
    intro t htC ht
    let t' : CJ := ⟨t, htC⟩
    have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht
    obtain ⟨P', htP'⟩ := (IsPGroup.of_card (n := 1)
      (show Nat.card (zpowers t') = 2 ^ 1 by rw [Nat.card_zpowers, ht', pow_one])).exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq CJ P P'
    have htgP : t' ∈ ((g • P : Sylow 2 CJ) : Subgroup CJ) := hg ▸ htP' (mem_zpowers t')
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htgP
    obtain ⟨y, hyP, hyt⟩ := htgP
    have hyt' : (g : G) * y * (g : G)⁻¹ = t := congrArg Subtype.val hyt
    have hy2 : orderOf (y : G) = 2 := by
      have h := orderOf_injective (MulAut.conj (g : G)).toMonoidHom (MulAut.conj (g : G)).injective
        (y : G)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hyt', ht] at h
      exact h.symm
    have hJy := hprop hzG2 hy2 hzC y.2 (hzcomm y hyP).symm hJz
    have hconj := isComponentOf_map_conj hJy (g : G)
    rw [map_conj_centralizer_singleton, hyt'] at hconj
    have hJg : J.map (MulAut.conj (g : G)).toMonoidHom = J :=
      conjSub_eq_of_mem_normalizer (centralizer_le_normalizer _ g.2)
    rwa [hJg] at hconj
  have hmono : ∀ {K₁ K₂ : Subgroup G}, K₁ ≤ K₂ → CFSG.pRank 2 K₁ ≤ CFSG.pRank 2 K₂ := fun h => by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_top_le_of_injective one_lt_two (Subgroup.inclusion h)
      (Subgroup.inclusion_injective h)
  have hrankC : CFSG.pRank 2 A ≤ CFSG.pRank 2 J → CFSG.pRank 2 CJ = CFSG.pRank 2 A := by
    intro hrs
    refine le_antisymm ?_ (hmono hAC)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    refine CFSG.SectionRank.pRank_le one_lt_two fun E hEC hEe => ?_
    rw [← card_eq_two_pow_pRank hAe]
    by_cases hE : E = ⊥
    · rw [hE, Subgroup.card_bot]
      exact Nat.card_pos
    · obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE
      have ht2 : orderOf (t : G) = 2 :=
        orderOf_eq_prime (hEe.2 _ t.2) fun h => ht1 (Subtype.ext h)
      have hJt := hUM hrs t (hEC t.2) ht2
      exact hM3 t ht2 J hJt (isTwoPComponent_of_isComponent
        ((isComponentOf_iff_isComponent_subgroupOf hJt.1).1 hJt)) rfl rfl E hEC
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).2 hEe) t.2
  refine ⟨fun hrs => ⟨hUM hrs, hrankC hrs⟩, fun hlt => ?_⟩
  have hrs := hlt.le
  have heven : Even (Nat.card CJ) := by
    have h := Subgroup.orderOf_dvd_natCard CJ haC
    rw [ha] at h
    exact even_iff_two_dvd.2 h
  have hLg : ∀ g : G, ⁅J, J.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro g h
    have hle : J.map (MulAut.conj g).toMonoidHom ≤ CJ := by
      rw [commutator_comm] at h
      exact commutator_eq_bot_iff_le_centralizer.1 h
    have h1 := hmono hle
    rw [hrankC hrs] at h1
    have h2 : CFSG.pRank 2 (J.map (MulAut.conj g).toMonoidHom) = CFSG.pRank 2 J := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv one_lt_two
        (J.equivMapOfInjective _ (MulAut.conj g).injective)).symm
    omega
  exact (involution_component_standard_criterion hJ.2.2 heven hLg).2 (hUM hrs)

end CFSG.LocalAnalysis.ComponentInitial
