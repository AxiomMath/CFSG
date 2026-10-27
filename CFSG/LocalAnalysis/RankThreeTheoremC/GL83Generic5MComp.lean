module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.Walter.W67.CentralExt
import CFSG.RankThree.PartOne.D4RC.Burnside

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

namespace GL83Generic5MComp

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}

theorem center_eq_bot_of_isComponentOf_of_abelian (hcore : primeComplementCore (G := Y) p = ⊥)
    (hab : ∀ Q : Sylow p Y, IsMulCommutative (Q : Subgroup Y)) (hK : IsComponentOf K ⊤) :
    center K = ⊥ := by
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p K))
  obtain ⟨Q, hQ⟩ := (T.isPGroup'.map K.subtype).exists_le_sylow
  have := hab Q
  have hTab : IsMulCommutative (T : Subgroup K) := IsMulCommutative.of_comm fun a b =>
    Subtype.ext (Subtype.ext (setLike_mul_comm (hQ ⟨a, a.2, rfl⟩) (hQ ⟨b, b.2, rfl⟩)))
  have h := CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup T hTab le_rfl
    (isPGroup_center_of_isComponentOf Fact.out hcore hK)
  rwa [hK.2.2.1, inf_top_eq] at h

omit [Fact p.Prime] [Finite Y] in
theorem eq_one_of_mem_of_mem_centralizer (hZ : center K = ⊥) {k : Y} (hk : k ∈ K)
    (hkc : k ∈ centralizer (K : Set Y)) : k = 1 := by
  have hz : (⟨k, hk⟩ : K) ∈ center K :=
    mem_center_iff.mpr fun m => Subtype.ext (mem_centralizer_iff.mp hkc m m.2)
  rw [hZ, mem_bot] at hz
  exact congrArg Subtype.val hz

theorem exists_sylow_le_subgroupOf {E : Subgroup Y} (hE : IsPGroup p E)
    (hEN : E ≤ normalizer (K : Set Y)) :
    ∃ Q : Sylow p Y, E ≤ (Q : Subgroup Y) ∧
      ∃ P : Sylow p K, (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K := by
  obtain ⟨S, hS⟩ := (hE.comap_subtype (K := normalizer (K : Set Y))).exists_le_sylow
  have hSsyl : IsSylowOf p ((S : Subgroup (normalizer (K : Set Y))).map
      (normalizer (K : Set Y)).subtype) (normalizer (K : Set Y)) := ⟨S, rfl⟩
  have hES : E ≤ (S : Subgroup (normalizer (K : Set Y))).map (normalizer (K : Set Y)).subtype :=
    (map_subgroupOf_eq_of_le hEN).ge.trans (map_mono hS)
  obtain ⟨Q, hQ⟩ := hSsyl.isPGroup.exists_le_sylow
  have hSK := hSsyl.inf_of_le_normalizer le_normalizer le_rfl
  have hQK : (Q : Subgroup Y) ⊓ K = (S : Subgroup (normalizer (K : Set Y))).map
      (normalizer (K : Set Y)).subtype ⊓ K :=
    hSK.eq_of_le (inf_le_inf_right K hQ) inf_le_right (Q.isPGroup'.to_le inf_le_left)
  obtain ⟨P, hP⟩ := (hQK ▸ hSK).exists_sylow_eq_subgroupOf
  exact ⟨Q, hES.trans hQ, P, hP.trans (inf_subgroupOf_right _ _)⟩

omit [Fact p.Prime] [Finite Y] in
theorem mem_sylow_iff {Q : Subgroup Y} {P : Sylow p K}
    (hP : (P : Subgroup K) = Q.subgroupOf K) (k : K) : k ∈ (P : Subgroup K) ↔ (k : Y) ∈ Q := by
  rw [hP, mem_subgroupOf]

theorem exists_inv_mul_mem_centralizer (hInn : KFactInnerAction) (hp2 : p ≠ 2)
    (hsimple : IsSimpleGroup K) (hnonab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K)
    {Q : Sylow p Y} (hQab : IsMulCommutative (Q : Subgroup Y)) {P : Sylow p K}
    (hP : (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K) (hP1 : (P : Subgroup K) ≠ ⊥)
    {y : Y} (hyQ : y ∈ (Q : Subgroup Y)) (hyN : y ∈ normalizer (K : Set Y)) (hyp : y ^ p = 1) :
    ∃ r ∈ (Q : Subgroup Y) ⊓ K, r⁻¹ * y ∈ centralizer (K : Set Y) := by
  have hmem := mem_sylow_iff hP
  have := hQab
  set φ : MulAut K := K.normalizerMonoidHom ⟨y, hyN⟩ with hφdef
  have hφ : ∀ k : K, ((φ k : K) : Y) = y * k * y⁻¹ := fun _ => rfl
  have hφp : φ ^ p = 1 := by
    have h1 : (⟨y, hyN⟩ : normalizer (K : Set Y)) ^ p = 1 :=
      Subtype.ext (by rw [coe_pow, coe_one]; exact hyp)
    rw [hφdef, ← map_pow, h1, map_one]
  obtain ⟨g, hgP, hg⟩ := hInn p Fact.out hp2 K hsimple hnonab hcat P hP1
    (IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
      (setLike_mul_comm ((hmem a).mp a.2) ((hmem b).mp b.2))))
    φ ⟨1, by rw [pow_one, hφp]⟩
    (fun g hg => by
      have hyg : y * (g : Y) = g * y := setLike_mul_comm hyQ ((hmem g).mp hg)
      ext m
      change y * ((g : Y) * m * (g : Y)⁻¹) * y⁻¹ = (g : Y) * (y * m * y⁻¹) * (g : Y)⁻¹
      calc y * ((g : Y) * m * (g : Y)⁻¹) * y⁻¹ = (y * g) * m * (y * g)⁻¹ := by group
        _ = (g * y) * m * (g * y)⁻¹ := by rw [hyg]
        _ = (g : Y) * (y * m * y⁻¹) * (g : Y)⁻¹ := by group)
  refine ⟨g, ⟨(hmem g).mp hgP, g.2⟩, mem_centralizer_iff.mpr fun k hk => ?_⟩
  have h1 : y * k * y⁻¹ = (g : Y) * k * (g : Y)⁻¹ := by
    rw [← hφ ⟨k, hk⟩, hg]
    rfl
  calc k * ((g : Y)⁻¹ * y) = (g : Y)⁻¹ * ((g : Y) * k * (g : Y)⁻¹) * y := by group
    _ = (g : Y)⁻¹ * (y * k * y⁻¹) * y := by rw [h1]
    _ = (g : Y)⁻¹ * y * k := by group

omit [Fact p.Prime] [Finite Y] in
theorem exists_conj_eq_zpow (hZ : center K = ⊥) {Q : Subgroup Y} {x : Y}
    (hweak : ∀ g : Y, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hxQ : x ∈ Q) {r : Y} (hrQ : r ∈ Q) (hrK : r ∈ K) (hc : r⁻¹ * x ∈ centralizer (K : Set Y))
    {g : Y} (hgK : g ∈ K) (hgr : g * r * g⁻¹ ∈ Q) :
    ∃ m : ℤ, g * r * g⁻¹ = r ^ m ∧ (r⁻¹ * x) ^ m = r⁻¹ * x := by
  set c := r⁻¹ * x with hcdef
  have hx : x = r * c := by rw [hcdef, mul_inv_cancel_left]
  have hgc : g * c = c * g := mem_centralizer_iff.mp hc g hgK
  have hxg : g * x * g⁻¹ = g * r * g⁻¹ * c :=
    calc g * x * g⁻¹ = g * r * g⁻¹ * (g * c) * g⁻¹ := by rw [hx]; group
      _ = g * r * g⁻¹ * (c * g) * g⁻¹ := by rw [hgc]
      _ = g * r * g⁻¹ * c := by group
  have hmap : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hxg]
    exact mul_mem hgr (mul_mem (inv_mem hrQ) hxQ)
  have hmem : g * x * g⁻¹ ∈ zpowers x := by
    rw [← hweak g hmap, MonoidHom.map_zpowers]
    exact mem_zpowers _
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hmem
  have hrc : Commute r c := mem_centralizer_iff.mp hc r hrK
  have h2 : (r ^ m)⁻¹ * (g * r * g⁻¹) = c ^ m * c⁻¹ := by
    have h1 : g * r * g⁻¹ * c = r ^ m * c ^ m := by rw [← hxg, ← hm, hx, hrc.mul_zpow]
    calc (r ^ m)⁻¹ * (g * r * g⁻¹) = (r ^ m)⁻¹ * (g * r * g⁻¹ * c) * c⁻¹ := by group
      _ = (r ^ m)⁻¹ * (r ^ m * c ^ m) * c⁻¹ := by rw [h1]
      _ = c ^ m * c⁻¹ := by group
  have h3 := eq_one_of_mem_of_mem_centralizer hZ
    (K.mul_mem (K.inv_mem (K.zpow_mem hrK m)) (K.mul_mem (K.mul_mem hgK hrK) (K.inv_mem hgK)))
    (h2 ▸ mul_mem (zpow_mem hc m) (inv_mem hc))
  refine ⟨m, (inv_mul_eq_one.mp h3).symm, ?_⟩
  rw [h2] at h3
  exact mul_inv_eq_one.mp h3

end GL83Generic5MComp

structure GL83Generic5MCompHyp (p : ℕ) [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] (x : Y)
    (U : Subgroup Y) (σ : Y) : Prop where
  five_le : 5 ≤ p
  core_eq_bot : primeComplementCore (G := Y) p = ⊥
  catalog : CatalogSimpleSections Y
  pRank_le : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3
  abelian : ∀ Q : Sylow p Y, IsMulCommutative (Q : Subgroup Y)
  ne_one : x ≠ 1
  pow_eq_one : x ^ p = 1
  weakClosed : ∀ Q : Sylow p Y, x ∈ (Q : Subgroup Y) → ∀ g : Y,
    (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup Y) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x
  perfect_eq_bot : ∀ J : Subgroup Y, J ≤ centralizer ({x} : Set Y) → ⁅J, J⁆ = J → J = ⊥
  isElemAbelian : IsElemAbelian p U
  card_eq : Nat.card U = p ^ 2
  le_centralizer : U ≤ centralizer ({x} : Set Y)
  mem_normalizer : σ ∈ normalizer (U : Set Y)
  moves : ∀ D : Subgroup Y, D ≤ U → Nat.card D = p → ∃ d ∈ D, σ * d * σ⁻¹ ∉ D

namespace GL83Generic5MCompHyp

open GL83Generic5MComp

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {x : Y} {U : Subgroup Y} {σ : Y}
  {K : Subgroup Y}

theorem ne_two (h : GL83Generic5MCompHyp p x U σ) : p ≠ 2 := by
  have := h.five_le
  omega

theorem center_eq_bot (h : GL83Generic5MCompHyp p x U σ) (hK : IsComponentOf K ⊤) :
    center K = ⊥ :=
  center_eq_bot_of_isComponentOf_of_abelian h.core_eq_bot h.abelian hK

theorem not_mem_centralizer (h : GL83Generic5MCompHyp p x U σ) (hK : IsComponentOf K ⊤) :
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

theorem sup_le_normalizer (h : GL83Generic5MCompHyp p x U σ) (hK : IsComponentOf K ⊤) :
    U ⊔ zpowers x ≤ normalizer (K : Set Y) :=
  sup_le (fun _ hu => mem_normalizer_of_isComponentOf_of_pow_eq_one Fact.out h.five_le
      h.core_eq_bot h.pRank_le hK (h.isElemAbelian.2 _ hu))
    (zpowers_le.mpr (mem_normalizer_of_isComponentOf_of_pow_eq_one Fact.out h.five_le
      h.core_eq_bot h.pRank_le hK h.pow_eq_one))

theorem isPGroup_sup (h : GL83Generic5MCompHyp p x U σ) :
    IsPGroup p (U ⊔ zpowers x : Subgroup Y) :=
  CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p _
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p h.isElemAbelian
      (isElemAbelian_zpowers h.pow_eq_one) (le_centralizer_iff.mpr (zpowers_le.mpr
        (mem_centralizer_iff.mpr fun _ hu => mem_centralizer_singleton_iff.mp
          (h.le_centralizer hu)))))

theorem exists_decomp (h : GL83Generic5MCompHyp p x U σ) (hInn : KFactInnerAction)
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

theorem isCyclic_of_decomp (h : GL83Generic5MCompHyp p x U σ) (hWC : KFactWeakClosure)
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

theorem mem_of_decomp (h : GL83Generic5MCompHyp p x U σ) (hK : IsComponentOf K ⊤)
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

theorem mem_of_isComponentOf (h : GL83Generic5MCompHyp p x U σ) (hWC : KFactWeakClosure)
    (hInn : KFactInnerAction) (hK : IsComponentOf K ⊤) : x ∈ K := by
  obtain ⟨Q, -, hxQ, P, hP, hP1, r, hrQK, hc, hro⟩ := h.exists_decomp hInn hK
  exact h.mem_of_decomp hK hxQ hP hP1 (h.isCyclic_of_decomp hWC hK hxQ hP hrQK hc hro) hrQK hc
    hro

theorem eq_of_isComponentOf (h : GL83Generic5MCompHyp p x U σ) (hWC : KFactWeakClosure)
    (hInn : KFactInnerAction) (hK : IsComponentOf K ⊤) {K' : Subgroup Y}
    (hK' : IsComponentOf K' ⊤) : K' = K := by
  by_contra hne
  have hC : K' ≤ centralizer (K : Set Y) := commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK' hK hne)
  exact h.ne_one (eq_one_of_mem_of_mem_centralizer (h.center_eq_bot hK)
    (h.mem_of_isComponentOf hWC hInn hK) (hC (h.mem_of_isComponentOf hWC hInn hK')))

theorem le_centralizer_of_normal (h : GL83Generic5MCompHyp p x U σ) (hInn : KFactInnerAction)
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) {Q : Sylow p Y} (hUQ : U ≤ (Q : Subgroup Y))
    {P : Sylow p K} (hP : (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K)
    (hP1 : (P : Subgroup K) ≠ ⊥) (hPc : IsCyclic (P : Subgroup K)) :
    U ≤ centralizer (K : Set Y) := by
  have hZ := h.center_eq_bot hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hcat := h.catalog.simple_subgroup K hsimple hnonab
  have hUN : U ≤ normalizer (K : Set Y) := by
    have := hKn
    rw [normalizer_eq_top]
    exact le_top
  set D : Subgroup Y := U ⊓ centralizer (K : Set Y) with hD
  have hD1 : D ≠ ⊥ := by
    intro hD1
    let α : U →* MulAut K := K.normalizerMonoidHom.comp (inclusion hUN)
    have hα : α.range ≤ (P : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
      rintro _ ⟨u, rfl⟩
      obtain ⟨r, hrQK, hc⟩ := exists_inv_mul_mem_centralizer hInn h.ne_two hsimple hnonab hcat
        (h.abelian Q) hP hP1 (hUQ u.2) (hUN u.2) (h.isElemAbelian.2 _ u.2)
      refine ⟨⟨r, hrQK.2⟩, (mem_sylow_iff hP _).mpr hrQK.1, ?_⟩
      ext k
      have hk := mem_centralizer_iff.mp hc k k.2
      change r * k * r⁻¹ = u * k * (u : Y)⁻¹
      calc r * k * r⁻¹ = r * (k * (r⁻¹ * u)) * (u : Y)⁻¹ := by group
        _ = r * (r⁻¹ * u * k) * (u : Y)⁻¹ := by rw [hk]
        _ = u * k * (u : Y)⁻¹ := by group
    have hinj : Function.Injective α := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      have hu' : (u : Y) ∈ D := ⟨u.2, mem_centralizer_iff.mpr fun k hk => by
        have h1 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : Y)) (MonoidHom.mem_ker.mp hu)
        change u * k * (u : Y)⁻¹ = k at h1
        calc k * u = u * k * (u : Y)⁻¹ * u := by rw [h1]
          _ = u * k := by group⟩
      rw [hD1, mem_bot] at hu'
      exact mem_bot.mpr (Subtype.ext hu')
    have : IsCyclic ((P : Subgroup K).map (MulAut.conj : K →* MulAut K)) :=
      isCyclic_of_surjective _ ((MulAut.conj : K →* MulAut K).subgroupMap_surjective _)
    have hcyc : IsCyclic U := (MonoidHom.ofInjective hinj).isCyclic.mpr
      ((subgroupOfEquivOfLe hα).isCyclic.mp inferInstance)
    have hexp : Monoid.exponent U ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u =>
      Subtype.ext (by rw [coe_pow, coe_one]; exact h.isElemAbelian.2 _ u.2)
    rw [IsCyclic.exponent_eq_card, h.card_eq] at hexp
    have := Nat.le_of_dvd (Fact.out : p.Prime).pos hexp
    nlinarith [(Fact.out : p.Prime).two_le]
  obtain ⟨k, hk2, hkc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
    (h.card_eq ▸ card_dvd_of_le (inf_le_left : D ≤ U))
  interval_cases k
  · exact absurd (card_eq_one.mp (by rw [hkc, pow_zero])) hD1
  · obtain ⟨d, hdD, hd⟩ := h.moves D inf_le_left (by rw [hkc, pow_one])
    exact absurd ⟨(mem_normalizer_iff.mp h.mem_normalizer d).mp hdD.1,
      (normal_centralizer (H := K)).conj_mem d hdD.2 σ⟩ hd
  · rw [← eq_of_le_of_card_ge (inf_le_left : D ≤ U) (by rw [hkc, h.card_eq])]
    exact inf_le_right

end GL83Generic5MCompHyp

theorem gl83Generic5MComp_holds :
    KFactWeakClosure → KFactInnerAction →
    ∀ {p : ℕ} [Fact p.Prime], 5 ≤ p → ∀ {Y : Type} [Group Y] [Finite Y],
      primeComplementCore (G := Y) p = ⊥ → CatalogSimpleSections Y →
      CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3 →
      (∀ Q : Sylow p Y, IsMulCommutative (Q : Subgroup Y)) →
      ∀ {x : Y}, x ≠ 1 → x ^ p = 1 →
      (∀ Q : Sylow p Y, x ∈ (Q : Subgroup Y) → ∀ g : Y,
          (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup Y) →
            (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) →
      (∀ J : Subgroup Y, J ≤ centralizer ({x} : Set Y) → ⁅J, J⁆ = J → J = ⊥) →
      ∀ {U : Subgroup Y}, IsElemAbelian p U → Nat.card U = p ^ 2 →
        U ≤ centralizer ({x} : Set Y) →
      ∀ {σ : Y}, σ ∈ normalizer (U : Set Y) →
        (∀ D : Subgroup Y, D ≤ U → Nat.card D = p → ∃ d ∈ D, σ * d * σ⁻¹ ∉ D) →
      ∀ {K : Subgroup Y}, IsComponentOf K ⊤ →
        K.Normal ∧ center K = ⊥ ∧ x ∈ K ∧ (∀ R : Sylow p K, IsCyclic (R : Subgroup K)) ∧
          U ≤ centralizer (K : Set Y) ∧ ∀ K' : Subgroup Y, IsComponentOf K' ⊤ → K' = K := by
  intro hWC hInn p _ hp5 Y _ _ hcore hcat hrank hab x hx1 hxp hweak hperf U hU hUc hUx σ hσ hmove
    K hK
  have h : GL83Generic5MCompHyp p x U σ :=
    ⟨hp5, hcore, hcat, hrank, hab, hx1, hxp, hweak, hperf, hU, hUc, hUx, hσ, hmove⟩
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

end CFSG.LocalAnalysis.RankThreeTheoremC
