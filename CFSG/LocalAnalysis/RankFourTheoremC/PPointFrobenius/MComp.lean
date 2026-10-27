module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.CaseIIComp
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.HypDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MComp
import CFSG.RankThree.PartOne.D4RC.Burnside

public section

open Subgroup
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

structure FrobMCompHyp (p n : ℕ) [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] (x : Y)
    (U : Subgroup Y) (σ : Y) : Prop where
  five_le : 5 ≤ p
  core_eq_bot : primeComplementCore (G := Y) p = ⊥
  catalog : CatalogSimpleSections Y
  abelian : ∀ Q : Sylow p Y, IsMulCommutative (Q : Subgroup Y)
  ne_one : x ≠ 1
  pow_eq_one : x ^ p = 1
  weakClosed : ∀ Q : Sylow p Y, x ∈ (Q : Subgroup Y) → ∀ g : Y,
    (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup Y) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x
  perfect_eq_bot : ∀ J : Subgroup Y, J ≤ centralizer ({x} : Set Y) → ⁅J, J⁆ = J → J = ⊥
  isElemAbelian : IsElemAbelian p U
  card_eq : Nat.card U = p ^ n
  le_centralizer : U ≤ centralizer ({x} : Set Y)
  moves : MovesHyperplanes p U σ

namespace FrobMCompHyp

open GL83Generic5MComp

variable {p n : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {x : Y} {U : Subgroup Y} {σ : Y}
  {K : Subgroup Y}

theorem ne_two (h : FrobMCompHyp p n x U σ) : p ≠ 2 := by
  have := h.five_le
  omega

theorem center_eq_bot (h : FrobMCompHyp p n x U σ) (hK : IsComponentOf K ⊤) :
    center K = ⊥ :=
  center_eq_bot_of_isComponentOf_of_abelian h.core_eq_bot h.abelian hK

theorem not_mem_centralizer (h : FrobMCompHyp p n x U σ) (hK : IsComponentOf K ⊤) :
    x ∉ centralizer (K : Set Y) := by
  intro hx
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow p Y))
  obtain ⟨t, htRK, hto, -⟩ :=
    exists_mem_sylow_inf_component Fact.out h.ne_two h.core_eq_bot R hK
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hK1 := h.perfect_eq_bot K (fun k hk => mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hx k hk)) commutator_eq_self
  have ht : t ∈ (⊥ : Subgroup Y) := hK1 ▸ (mem_inf.mp htRK).2
  rw [mem_bot.mp ht, orderOf_one] at hto
  exact (Fact.out : p.Prime).one_lt.ne hto

theorem sup_le_normalizer (h : FrobMCompHyp p n x U σ) (hK : IsComponentOf K ⊤) :
    U ⊔ zpowers x ≤ normalizer (K : Set Y) :=
  sup_le (fun _ hu => mem_normalizer_of_isComponentOf_of_pow_eq_one_abelian Fact.out h.ne_two
      h.core_eq_bot h.abelian hK (h.isElemAbelian.2 _ hu))
    (zpowers_le.mpr (mem_normalizer_of_isComponentOf_of_pow_eq_one_abelian Fact.out h.ne_two
      h.core_eq_bot h.abelian hK h.pow_eq_one))

theorem isPGroup_sup (h : FrobMCompHyp p n x U σ) :
    IsPGroup p (U ⊔ zpowers x : Subgroup Y) :=
  CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p _
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p h.isElemAbelian
      (isElemAbelian_zpowers h.pow_eq_one) (le_centralizer_iff.mpr (zpowers_le.mpr
        (mem_centralizer_iff.mpr fun _ hu => mem_centralizer_singleton_iff.mp
          (h.le_centralizer hu)))))

theorem exists_decomp (h : FrobMCompHyp p n x U σ) (hInn : KFactInnerAction)
    (hK : IsComponentOf K ⊤) :
    ∃ Q : Sylow p Y, U ≤ (Q : Subgroup Y) ∧ x ∈ (Q : Subgroup Y) ∧
      ∃ P : Sylow p K, (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K ∧
        (P : Subgroup K) ≠ ⊥ ∧
        ∃ r ∈ (Q : Subgroup Y) ⊓ K, r⁻¹ * x ∈ centralizer (K : Set Y) ∧ orderOf r = p := by
  have hZ := h.center_eq_bot hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  obtain ⟨Q, hQ, P, hP⟩ := exists_sylow_le_subgroupOf h.isPGroup_sup (h.sup_le_normalizer hK)
  have hxQ : x ∈ (Q : Subgroup Y) := hQ (mem_sup_right (mem_zpowers x))
  have hP1 : (P : Subgroup K) ≠ ⊥ := by
    obtain ⟨t, htQK, hto, -⟩ :=
      exists_mem_sylow_inf_component Fact.out h.ne_two h.core_eq_bot Q hK
    intro hbot
    have ht : (⟨t, (mem_inf.mp htQK).2⟩ : K) ∈ (P : Subgroup K) := by
      rw [hP, mem_subgroupOf]
      exact (mem_inf.mp htQK).1
    rw [hbot, mem_bot] at ht
    rw [show t = 1 from congrArg Subtype.val ht, orderOf_one] at hto
    exact (Fact.out : p.Prime).one_lt.ne hto
  obtain ⟨r, hrQK, hc⟩ := exists_inv_mul_mem_centralizer hInn h.ne_two hsimple hnonab
    (h.catalog.simple_subgroup K hsimple hnonab) (h.abelian Q) hP hP1 hxQ
    (h.sup_le_normalizer hK (mem_sup_right (mem_zpowers x))) h.pow_eq_one
  refine ⟨Q, le_sup_left.trans hQ, hxQ, P, hP, hP1, r, hrQK, hc, ?_⟩
  have hrc : Commute r (r⁻¹ * x) := mem_centralizer_iff.mp hc r hrQK.2
  have hrp : r ^ p = 1 := by
    have h1 : r ^ p * (r⁻¹ * x) ^ p = 1 := by
      rw [← hrc.mul_pow, mul_inv_cancel_left, h.pow_eq_one]
    exact eq_one_of_mem_of_mem_centralizer hZ (pow_mem hrQK.2 p)
      ((eq_inv_of_mul_eq_one_left h1) ▸ inv_mem (pow_mem hc p))
  refine orderOf_eq_prime hrp fun hr1 => h.not_mem_centralizer hK ?_
  rwa [hr1, inv_one, one_mul] at hc

theorem isCyclic_of_decomp (h : FrobMCompHyp p n x U σ) (hWC : KFactWeakClosure)
    (hK : IsComponentOf K ⊤) {Q : Sylow p Y} (hxQ : x ∈ (Q : Subgroup Y)) {P : Sylow p K}
    (hP : (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K) {r : Y}
    (hrQK : r ∈ (Q : Subgroup Y) ⊓ K) (hc : r⁻¹ * x ∈ centralizer (K : Set Y))
    (hro : orderOf r = p) : IsCyclic (P : Subgroup K) := by
  by_contra hnc
  have hZ := h.center_eq_bot hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hmem := mem_sylow_iff hP
  have := h.abelian Q
  have : IsSimpleGroup K := hsimple
  set r' : K := ⟨r, hrQK.2⟩ with hr'
  obtain ⟨g, hg1, hg2⟩ := hWC p Fact.out h.ne_two K ⊤ inferInstance
    Subgroup.topEquiv.isSimpleGroup
    (by
      obtain ⟨a, b, hab⟩ := hnonab
      exact ⟨⟨a, mem_top a⟩, ⟨b, mem_top b⟩, fun hba => hab (congrArg Subtype.val hba)⟩)
    (IsCatalogGroup.of_mulEquiv Subgroup.topEquiv (h.catalog.simple_subgroup K hsimple hnonab))
    (by rw [coe_top, centralizer_univ, hZ])
    (by
      rw [card_top, ← hro, ← Subgroup.orderOf_mk r hrQK.2]
      exact orderOf_dvd_natCard r')
    P (top_sup_eq _)
    (IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
      (setLike_mul_comm ((hmem a).mp a.2) ((hmem b).mp b.2))))
    (by
      rw [inf_top_eq]
      exact two_le_pRank_of_not_isCyclic Fact.out h.ne_two P.isPGroup' hnc)
    (zpowers r') (zpowers_le.mpr ((hmem r').mpr hrQK.1))
    (by rw [Nat.card_zpowers, hr', Subgroup.orderOf_mk, hro])
  have hgr : (g : Y) * r * (g : Y)⁻¹ ∈ (Q : Subgroup Y) :=
    (hmem _).mp (hg1 (mem_map_of_mem _ (mem_zpowers r')))
  obtain ⟨m, hm, -⟩ := exists_conj_eq_zpow hZ (h.weakClosed Q hxQ) hxQ hrQK.1 hrQK.2 hc g.2 hgr
  refine hg2 (eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj g).injective]))
  rw [MonoidHom.map_zpowers, zpowers_le]
  have hgm : (MulAut.conj g).toMonoidHom r' = r' ^ m := Subtype.ext (by simpa using hm)
  rw [hgm]
  exact zpow_mem (mem_zpowers _) m

theorem mem_of_decomp (h : FrobMCompHyp p n x U σ) (hK : IsComponentOf K ⊤)
    {Q : Sylow p Y} (hxQ : x ∈ (Q : Subgroup Y)) {P : Sylow p K}
    (hP : (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K) (hP1 : (P : Subgroup K) ≠ ⊥)
    (hPc : IsCyclic (P : Subgroup K)) {r : Y} (hrQK : r ∈ (Q : Subgroup Y) ⊓ K)
    (hc : r⁻¹ * x ∈ centralizer (K : Set Y)) (hro : orderOf r = p) : x ∈ K := by
  have hZ := h.center_eq_bot hK
  have hmem := mem_sylow_iff hP
  set r' : K := ⟨r, hrQK.2⟩ with hr'
  have hr'P : r' ∈ (P : Subgroup K) := (hmem r').mpr hrQK.1
  obtain ⟨g, hgN, a, haP, hap, hga⟩ := CFSG.RankThree.PartOne.D4RC.rcb_exists_normalizer_elt_perfect
    hK.2.2.1 P.isPGroup' P.not_dvd_index hPc hP1
  have ha1 : a ≠ 1 := fun ha => hga (by rw [ha, mul_one, mul_inv_cancel])
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, r' ^ j = a := by
    have hr'p : (⟨r', hr'P⟩ : (P : Subgroup K)) ^ p = 1 :=
      Subtype.ext (Subtype.ext (by simp [hr', ← hro, pow_orderOf_eq_one]))
    have hr'1 : (⟨r', hr'P⟩ : (P : Subgroup K)) ≠ 1 := fun h1 => by
      have h2 : r = 1 := congrArg Subtype.val (congrArg Subtype.val h1)
      rw [h2, orderOf_one] at hro
      exact (Fact.out : p.Prime).one_lt.ne hro
    have heq : zpowers (⟨a, haP⟩ : (P : Subgroup K)) = zpowers ⟨r', hr'P⟩ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
        orderOf_eq_prime (Subtype.ext hap) (fun h1 => ha1 (congrArg Subtype.val h1)),
        orderOf_eq_prime hr'p hr'1]
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (heq ▸ mem_zpowers (⟨a, haP⟩ : (P : Subgroup K)))
    exact ⟨j, congrArg Subtype.val hj⟩
  have hgr : (g : Y) * r * (g : Y)⁻¹ ∈ (Q : Subgroup Y) :=
    (hmem _).mp ((mem_normalizer_iff.mp hgN r').mp hr'P)
  obtain ⟨m, hm, hcm⟩ := exists_conj_eq_zpow hZ (h.weakClosed Q hxQ) hxQ hrQK.1 hrQK.2 hc g.2 hgr
  have hrm : r ^ (m - 1) ≠ 1 := by
    intro hr1
    apply hga
    have hfix : g * r' * g⁻¹ = r' := Subtype.ext (by
      rw [zpow_sub_one, mul_inv_eq_one] at hr1
      simpa [hr1] using hm)
    rw [← conj_zpow, hfix]
  set c := r⁻¹ * x with hcdef
  have hcp : c ^ p = 1 := by
    have := h.abelian Q
    have hrx : Commute r⁻¹ x := setLike_mul_comm (inv_mem (mem_inf.mp hrQK).1) hxQ
    have hrp : r ^ p = 1 := hro ▸ pow_orderOf_eq_one r
    rw [hcdef, hrx.mul_pow, inv_pow, hrp, inv_one, one_mul, h.pow_eq_one]
  have hc1 : c = 1 := by
    have hcm1 : c ^ (m - 1) = 1 := by rw [zpow_sub_one, hcm, mul_inv_cancel]
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hcp) with
      h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      refine hrm (orderOf_dvd_iff_zpow_eq_one.mp ?_)
      rw [hro, ← h1]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hcm1
  have hxr : x = r := by
    rw [hcdef, inv_mul_eq_one] at hc1
    exact hc1.symm
  exact hxr ▸ hrQK.2

theorem mem_of_isComponentOf (h : FrobMCompHyp p n x U σ) (hWC : KFactWeakClosure)
    (hInn : KFactInnerAction) (hK : IsComponentOf K ⊤) : x ∈ K := by
  obtain ⟨Q, -, hxQ, P, hP, hP1, r, hrQK, hc, hro⟩ := h.exists_decomp hInn hK
  exact h.mem_of_decomp hK hxQ hP hP1 (h.isCyclic_of_decomp hWC hK hxQ hP hrQK hc hro) hrQK hc
    hro

theorem eq_of_isComponentOf (h : FrobMCompHyp p n x U σ) (hWC : KFactWeakClosure)
    (hInn : KFactInnerAction) (hK : IsComponentOf K ⊤) {K' : Subgroup Y}
    (hK' : IsComponentOf K' ⊤) : K' = K := by
  by_contra hne
  have hC : K' ≤ centralizer (K : Set Y) := commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK' hK hne)
  exact h.ne_one (eq_one_of_mem_of_mem_centralizer (h.center_eq_bot hK)
    (h.mem_of_isComponentOf hWC hInn hK) (hC (h.mem_of_isComponentOf hWC hInn hK')))

theorem le_centralizer_of_normal (h : FrobMCompHyp p n x U σ) (hInn : KFactInnerAction)
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) {Q : Sylow p Y} (hUQ : U ≤ (Q : Subgroup Y))
    {P : Sylow p K} (hP : (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K)
    (hP1 : (P : Subgroup K) ≠ ⊥) (hPc : IsCyclic (P : Subgroup K)) :
    U ≤ centralizer (K : Set Y) := by
  haveI := hKn
  obtain ⟨hσN, hσmove⟩ := h.moves
  have hZ := h.center_eq_bot hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hcat := h.catalog.simple_subgroup K hsimple hnonab
  have hUN : U ≤ normalizer (K : Set Y) := by
    rw [normalizer_eq_top]
    exact le_top
  set D : Subgroup Y := U ⊓ centralizer (K : Set Y) with hD
  let α : U →* MulAut K := K.normalizerMonoidHom.comp (inclusion hUN)
  have hα : α.range ≤ (P : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨r, hrQK, hc⟩ := GL83Generic5MComp.exists_inv_mul_mem_centralizer hInn h.ne_two hsimple
      hnonab hcat (h.abelian Q) hP hP1 (hUQ u.2) (hUN u.2) (h.isElemAbelian.2 _ u.2)
    refine ⟨⟨r, hrQK.2⟩, (GL83Generic5MComp.mem_sylow_iff hP _).mpr hrQK.1, ?_⟩
    ext k
    have hk := mem_centralizer_iff.mp hc k k.2
    change r * k * r⁻¹ = u * k * (u : Y)⁻¹
    calc r * k * r⁻¹ = r * (k * (r⁻¹ * u)) * (u : Y)⁻¹ := by group
      _ = r * (r⁻¹ * u * k) * (u : Y)⁻¹ := by rw [hk]
      _ = u * k * (u : Y)⁻¹ := by group
  have hker : ∀ u : U, u ∈ α.ker ↔ (u : Y) ∈ centralizer (K : Set Y) := by
    intro u
    constructor
    · intro hu
      refine mem_centralizer_iff.mpr fun k hk => ?_
      have h1 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : Y)) (MonoidHom.mem_ker.mp hu)
      change u * k * (u : Y)⁻¹ = k at h1
      calc k * u = u * k * (u : Y)⁻¹ * u := by rw [h1]
        _ = u * k := by group
    · intro hu
      rw [MonoidHom.mem_ker]
      ext k
      have hk := mem_centralizer_iff.mp hu k k.2
      change (u : Y) * (k : Y) * (u : Y)⁻¹ = (k : Y)
      rw [← hk]
      group
  have : IsCyclic ((P : Subgroup K).map (MulAut.conj : K →* MulAut K)) :=
    isCyclic_of_surjective _ ((MulAut.conj : K →* MulAut K).subgroupMap_surjective _)
  have hcyc : IsCyclic α.range := (subgroupOfEquivOfLe hα).isCyclic.mp inferInstance
  have hexp : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    obtain ⟨u, hu⟩ := g.2
    refine Subtype.ext ?_
    have hup : u ^ p = 1 :=
      Subtype.ext (by rw [coe_pow, coe_one]; exact h.isElemAbelian.2 _ u.2)
    change (g : MulAut K) ^ p = 1
    rw [← hu, ← map_pow, hup, map_one]
  have hrange : Nat.card α.range ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact hexp
  have hidx : α.ker.index = Nat.card α.range := Subgroup.index_ker α
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (hidx ▸ hrange) with h1 | hpidx
  ·
    have htop : α.ker = ⊤ := Subgroup.index_eq_one.mp h1
    intro u hu
    refine (hker ⟨u, hu⟩).mp ?_
    rw [htop]
    exact mem_top _
  ·
    exfalso
    have hmapD : α.ker.map U.subtype = D := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u.2, (hker u).mp hu⟩
      · rintro ⟨hyU, hyC⟩
        exact ⟨⟨y, hyU⟩, (hker ⟨y, hyU⟩).mpr hyC, rfl⟩
    have h3 : Nat.card α.ker = Nat.card D := by
      rw [← hmapD, Subgroup.card_map_of_injective U.subtype_injective]
    have hDcard : Nat.card U = p * Nat.card D := by
      have h2 := Subgroup.card_mul_index α.ker
      rw [hpidx, h3] at h2
      linarith
    obtain ⟨d, hdD, hd⟩ := hσmove 1 le_rfl (by norm_num) D inf_le_left hDcard
    refine hd ?_
    rw [pow_one]
    exact ⟨(mem_normalizer_iff.mp hσN d).mp hdD.1,
      (normal_centralizer (H := K)).conj_mem d hdD.2 σ⟩

end FrobMCompHyp

theorem frobMComp_holds :
    KFactWeakClosure → KFactInnerAction →
    ∀ {p n : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {x : Y} {U : Subgroup Y} {σ : Y},
      FrobMCompHyp p n x U σ → ∀ {K : Subgroup Y}, IsComponentOf K ⊤ →
        K.Normal ∧ center K = ⊥ ∧ x ∈ K ∧ (∀ R : Sylow p K, IsCyclic (R : Subgroup K)) ∧
          U ≤ centralizer (K : Set Y) ∧ ∀ K' : Subgroup Y, IsComponentOf K' ⊤ → K' = K := by
  intro hWC hInn p n _ Y _ _ x U σ h K hK
  have huniq : ∀ K' : Subgroup Y, IsComponentOf K' ⊤ → K' = K :=
    fun _ hK' => h.eq_of_isComponentOf hWC hInn hK hK'
  have hKn : K.Normal := ⟨fun n hn g => by
    rw [← huniq _ ((CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr
      hK)]
    exact ⟨n, hn, rfl⟩⟩
  obtain ⟨Q, hUQ, hxQ, P, hP, hP1, r, hrQK, hc, hro⟩ := h.exists_decomp hInn hK
  have hPc := h.isCyclic_of_decomp hWC hK hxQ hP hrQK hc hro
  exact ⟨hKn, h.center_eq_bot hK, h.mem_of_decomp hK hxQ hP hP1 hPc hrQK hc hro,
    fun R => (Sylow.equiv P R).isCyclic.mp hPc,
    h.le_centralizer_of_normal hInn hK hKn hUQ hP hP1 hPc, huniq⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
