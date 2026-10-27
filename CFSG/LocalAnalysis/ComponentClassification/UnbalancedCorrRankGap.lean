module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSwapRank
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrReach
public import CFSG.Assembly.OddCoreElimination.IsolatedFour

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem closure_pair_comm_sq {b e : G} (hbb : b * b = 1) (hee : e * e = 1) (hbe : b * e = e * b) :
    (∀ x ∈ closure ({b, e} : Set G), ∀ y ∈ closure ({b, e} : Set G), x * y = y * x) ∧
      ∀ x ∈ closure ({b, e} : Set G), x * x = 1 := by
  have hcomm : closure ({b, e} : Set G) ≤
      centralizer ((closure ({b, e} : Set G) : Subgroup G) : Set G) := by
    rw [centralizer_closure, closure_le]
    rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_iff] <;>
      rintro y (rfl | rfl)
    all_goals first | rfl | exact hbe | exact hbe.symm
  refine ⟨fun x hx y hy => (mem_centralizer_iff.mp (hcomm hy) x hx), fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hbb
    · exact hee
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := mem_centralizer_iff.mp (hcomm hy) x hx
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ih => rw [← mul_inv_rev, ih, inv_one]

omit [Finite G] in
theorem closure_pair_elementary {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b) :
    IsElementaryAbelian 2 ↥(closure ({a, b} : Set G)) ∧
      Nat.card ↥(closure ({a, b} : Set G)) = 4 := by
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  obtain ⟨hc, hsq⟩ := closure_pair_comm_sq haa hbb hab
  refine ⟨(SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mpr
    ⟨⟨⟨fun x y => Subtype.ext (hc _ x.2 _ y.2)⟩⟩, fun x hx => by rw [pow_two]; exact hsq x hx⟩, ?_⟩
  have hzp : ∀ {g : G}, g * g = 1 → ∀ x ∈ zpowers g, x = 1 ∨ x = g := by
    intro g hgg x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hgg, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hgg, one_zpow, one_mul, zpow_one]
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; exact absurd ha (by norm_num)
  have hcomm : ∀ (x : zpowers a) (y : zpowers b),
      Commute ((zpowers a).subtype x) ((zpowers b).subtype y) := by
    intro x y
    have hx : (x : G) ∈ closure ({a, b} : Set G) := by
      rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure]
      exact mem_sup_left x.2
    have hy : (y : G) ∈ closure ({a, b} : Set G) := by
      rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
      exact mem_sup_right y.2
    exact hc _ hx _ hy
  let f : zpowers a × zpowers b →* G :=
    MonoidHom.noncommCoprod (zpowers a).subtype (zpowers b).subtype hcomm
  have hf : ∀ x : zpowers a × zpowers b, f x = (x.1 : G) * x.2 := fun x => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hf] at hx
    have h1 : (x.1 : G) = (x.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have h2 : (x.1 : G) ∈ zpowers b := h1 ▸ inv_mem x.2.2
    have h3 : (x.1 : G) = 1 := by
      rcases hzp haa _ x.1.2 with h4 | h4
      · exact h4
      · exfalso
        rw [h4] at h2
        rcases hzp hbb _ h2 with h5 | h5
        · exact ha1 h5
        · exact hne h5
    have h4 : (x.2 : G) = 1 := by
      rw [h3] at h1
      exact inv_eq_one.mp h1.symm
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  have hrange : f.range = closure ({a, b} : Set G) := by
    rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hf]
      exact mul_mem (mem_sup_left x.1.2) (mem_sup_right x.2.2)
    · refine sup_le (fun x hx => ⟨(⟨x, hx⟩, 1), by rw [hf]; simp⟩)
        (fun y hy => ⟨(1, ⟨y, hy⟩), by rw [hf]; simp⟩)
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_prod,
    Nat.card_zpowers, Nat.card_zpowers, ha, hb]

omit [Finite G] in
theorem mem_of_sylow_of_central {X S : Subgroup G} {a : G} (ha : orderOf a = 2) (haX : a ∈ X)
    (hcen : X ≤ centralizer ({a} : Set G))
    (hS : ∃ P₀ : Sylow 2 ↥X, (P₀ : Subgroup X) = S.subgroupOf X) : a ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hS
  have hn : ((zpowers a).subgroupOf X).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
    have hga : (g : G) * a = a * g := mem_centralizer_singleton_iff.mp (hcen g.2)
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ = n := by
      rw [← hk, (Commute.zpow_right hga k).eq, mul_inv_cancel_right]
    simpa [h1] using hn⟩
  have h2 : IsPGroup 2 ((zpowers a).subgroupOf X) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])).comap_subtype
  have h4 : (⟨a, haX⟩ : X) ∈ (P₀ : Subgroup X) :=
    h2.le_sylow_of_normal P₀ (show (⟨a, haX⟩ : X) ∈ (zpowers a).subgroupOf X from mem_zpowers a)
  rw [hP₀] at h4
  exact h4

theorem sylow_inf_coreActionKernel {a : G} {J S : Subgroup G}
    (hSH : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :
    (∃ PQ : Sylow 2
        ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J),
      (PQ : Subgroup _) =
        (S ⊓ (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J)).subgroupOf
          (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J)) ∧
    pRank 2 ↥(S ⊓ (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J)) =
      pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set HJ := centralizer ({a} : Set G) ⊓ normalizer (J : Set G) with hHJdef
  set QJ := HJ ⊓ coreActionKernel J with hQJdef
  have hQJN : HJ ≤ normalizer (QJ : Set G) := fun g hg =>
    normalizer_inf_mem (le_normalizer hg)
      (normalizer_le_normalizer_coreActionKernel J (mem_inf.mp hg).2)
  obtain ⟨PQ, hPQ⟩ := UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer hSH
    hSsyl inf_le_left hQJN
  refine ⟨⟨PQ, hPQ⟩, ?_⟩
  have e₁ : ↥(S ⊓ QJ) ≃* ↥(PQ : Subgroup ↥QJ) :=
    (subgroupOfEquivOfLe (inf_le_right : S ⊓ QJ ≤ QJ)).symm.trans
      (MulEquiv.subgroupCongr hPQ.symm)
  rw [pRank_eq_of_mulEquiv one_lt_two e₁, (SectionRank.pRank_sylow PQ).2]

omit [Finite G] in
theorem mem_inf_coreActionKernel_of_sylow {a : G} {J S : Subgroup G} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :
    a ∈ S ⊓ (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J) := by
  have haJ : a ∈ normalizer (J : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_le_centralizer hJa)
  have haHJ : a ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, haJ⟩
  have haQJ : a ∈ coreActionKernel J := by
    refine mem_coreActionKernel.mpr ⟨haJ, fun j hj => ?_⟩
    have hja : j * a = a * j := mem_centralizer_singleton_iff.mp (hJa hj)
    rw [show j⁻¹ * a⁻¹ * j * a = j⁻¹ * (a⁻¹ * (j * a)) by group, hja, inv_mul_cancel_left,
      inv_mul_cancel]
    exact one_mem _
  exact mem_inf.mpr ⟨mem_of_sylow_of_central ha haHJ inf_le_left hSsyl,
    mem_inf.mpr ⟨haHJ, haQJ⟩⟩

theorem nonisomorphic_unbalancing_correspondence_rank_gap {a : G} (ha : orderOf a = 2)
    {J : Subgroup G} (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hmax : ∀ (c v : G) (K : Subgroup G), GSUnbalancingTriple c v K → GSReach J K →
      (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index ∧
        ((pPrimeCore 2 K).index = (pPrimeCore 2 J).index →
          pRank 2 ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G) ⊓ coreActionKernel K) ≤
            pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J)))
    {b y : G} {L : Subgroup G} (hC : UnbalancedGS.GSCorr a J b L)
    (hUL : GSUnbalancingTriple b y L) (hnotiso : ¬ UnbalancedGS.GSIsoCorr a J b L)
    {S P Q T : Subgroup G} (hSH : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)))
    (hbS : b ∈ S)
    (hP : P = S ⊓ (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J))
    (hQ : Q = S ⊓ centralizer ({b} : Set G)) (hT : T = P ⊓ centralizer ({b} : Set G)) :
    conjugate L a ≠ L ∧ (pPrimeCore 2 L).index = (pPrimeCore 2 J).index ∧
    IsElementaryAbelian 2 ↥(closure ({a, b} : Set G)) ∧
    Nat.card ↥(closure ({a, b} : Set G)) = 4 ∧ closure ({a, b} : Set G) ≤ T ∧
    pRank 2 ↥J + pRank 2 ↥T - 1 ≤
      pRank 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (L : Set G) ⊓ coreActionKernel L) ∧
    pRank 2 ↥J + 1 ≤
      pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J) ∧
    pRank 2 ↥P =
      pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J) ∧
    (2 ≤ pRank 2 ↥J → pRank 2 ↥T < pRank 2 ↥P ∧ T < P ∧ ¬ P ≤ Q ∧ 8 ≤ Nat.card T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hP hQ hT
  have hcmp := UnbalancingLocal.correspondence_quotient_order_comparison hC
  have hcorr := hC
  obtain ⟨-, hbo, hab, -, -, hLb, hL, hbN, hcomm, -⟩ := hcorr
  set HJ := centralizer ({a} : Set G) ⊓ normalizer (J : Set G) with hHJdef
  set QJ := HJ ⊓ coreActionKernel J with hQJdef
  set Cb := centralizer ({b} : Set G) with hCbdef
  set P := S ⊓ QJ with hPdef
  set T := P ⊓ Cb with hTdef
  have hbr : ∀ X : Subgroup G, pRank 2 ↥X = Open.pRank 2 X := fun X =>
    (SectionRank.pRank_eq_open_pRank_top 2 X).trans (SectionRank.pRank_eq_pRank_top_subgroup X).symm
  obtain ⟨hdle, hrank⟩ := hmax b y L hUL (GSReach.of_gsCorr hC)
  have hdge : (pPrimeCore 2 J).index ≤ (pPrimeCore 2 L).index := by
    rw [index_eq_card, index_eq_card]
    exact hcmp.1
  have hdeq : (pPrimeCore 2 L).index = (pPrimeCore 2 J).index := le_antisymm hdle hdge
  have hne : conjugate L a ≠ L := by
    intro hLa
    apply hnotiso
    exact (hcmp.2.1 hLa).mp (by rw [← index_eq_card, ← index_eq_card]; exact hdeq.symm)
  have hQLQJ := hrank hdeq
  obtain ⟨P₀, hP₀⟩ := hSsyl
  have hS2 : IsPGroup 2 S := by
    have h1 : IsPGroup 2 ((P₀ : Subgroup HJ).map HJ.subtype) := P₀.isPGroup'.map HJ.subtype
    rwa [hP₀, map_subgroupOf_eq_of_le hSH] at h1
  have haP : a ∈ P := mem_inf_coreActionKernel_of_sylow ha hJa ⟨P₀, hP₀⟩
  have haT : a ∈ T := mem_inf.mpr ⟨haP, mem_centralizer_singleton_iff.mpr hab⟩
  have hbHJ : b ∈ HJ := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hab.symm, hbN⟩
  have hbT : b ∈ T := mem_inf.mpr ⟨mem_inf.mpr ⟨hbS, mem_inf.mpr ⟨hbHJ,
    mem_coreActionKernel.mpr ⟨hbN, hcomm⟩⟩⟩, mem_centralizer_singleton_iff.mpr rfl⟩
  have hab' : a ≠ b := by
    intro heq
    apply hne
    rw [heq]
    exact conjugate_eq_self_of_le_centralizer hLb
  obtain ⟨hEA, hE4⟩ := closure_pair_elementary ha hbo hab hab'
  have hET : closure ({a, b} : Set G) ≤ T := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact haT
    · exact hbT
  have hPS : P ≤ S := inf_le_left
  have hT2 : IsPGroup 2 T := hS2.to_le (inf_le_left.trans hPS)
  have hTle : T ≤ centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) ⊓ normalizer (J : Set G) :=
    fun u hu => by
      obtain ⟨hP', hCb'⟩ := mem_inf.mp hu
      have hHJ' := (mem_inf.mp (mem_inf.mp hP').2).1
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hHJ').1, hCb'⟩, (mem_inf.mp hHJ').2⟩
  have hJT : ∀ u ∈ T, ∀ j ∈ J, j⁻¹ * u⁻¹ * j * u ∈ (pPrimeCore 2 J).map J.subtype := fun u hu =>
    (mem_coreActionKernel.mp (mem_inf.mp (mem_inf.mp (mem_inf.mp hu).1).2).2).2
  obtain ⟨R, -, -, -, -, -, -, hrk, hLJ⟩ :=
    swapped_correspondence_centralizer_rank_bound hC hne hdeq.symm hT2 hTle haT hJT
  rw [hLJ] at hrk
  have hT2r : 2 ≤ pRank 2 ↥T := by
    rw [hbr]
    exact SectionRank.le_pRank one_lt_two hET
      ((SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mp hEA) (by rw [hE4]; norm_num)
  have hPQJ : pRank 2 ↥P = pRank 2 ↥QJ := (sylow_inf_coreActionKernel hSH ⟨P₀, hP₀⟩).2
  refine ⟨hne, hdeq, hEA, hE4, hET, hrk, by omega, hPQJ, fun hJ2 => ?_⟩
  have hlt : pRank 2 ↥T < pRank 2 ↥P := by omega
  have hTP : T < P := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hlt, hTP, fun hPQ' => ?_, ?_⟩
  · apply (lt_iff_le_not_ge.mp hTP).2
    intro x hx
    exact mem_inf.mpr ⟨hx, (mem_inf.mp (hPQ' hx)).2⟩
  · obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have h4 : 4 ≤ Nat.card T := hE4 ▸ card_le_of_le hET
    rw [hk] at h4 ⊢
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      interval_cases k <;> simp at h4
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · exfalso
      have hk2' : k = 2 := by omega
      subst hk2'
      have hTE : closure ({a, b} : Set G) = T := eq_of_le_of_card_ge hET (by rw [hk, hE4]; norm_num)
      have hP2 : IsPGroup 2 P := hS2.to_le hPS
      have hTEA : Assembly.IsElemAbelian 2 T := by
        rw [← hTE]
        exact (SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mp hEA
      have hT4 : Nat.card ↥T = 4 := by
        rw [← hTE, hE4]
      have h5 := Assembly.Dichotomy.four_involution_centralizer_rank_bound hP2
        (mem_inf.mp hbT).1 hTEA hT4
      have h6 : pRank 2 ↥P ≤ 2 := by
        rw [hbr]
        exact h5
      omega
    · calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3

end CFSG.ComponentClassification.UnbalancedCorr
