module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointList
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSignalizer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem exists_orderOf_eq_mem_inf_center {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (R : Sylow p X) {K : Subgroup X} (hKn : K.Normal) {t : X} (htR : t ∈ (R : Subgroup X))
    (htK : t ∈ K) (ht1 : t ≠ 1) :
    ∃ y ∈ (R : Subgroup X) ⊓ K, orderOf y = p ∧ ∀ r ∈ (R : Subgroup X), r * y = y * r := by
  have hp : p.Prime := Fact.out
  have : Group.IsNilpotent (R : Subgroup X) := R.isPGroup'.isNilpotent
  have hH : K.subgroupOf (R : Subgroup X) ≠ ⊥ := by
    intro hbot
    have : (⟨t, htR⟩ : (R : Subgroup X)) ∈ K.subgroupOf (R : Subgroup X) := htK
    rw [hbot, mem_bot] at this
    exact ht1 (congrArg Subtype.val this)
  obtain ⟨m, hm1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH)
  have hmK : (((m : (R : Subgroup X)) : X)) ∈ K := (mem_inf.mp m.2).1
  have hmZ : (m : (R : Subgroup X)) ∈ center (R : Subgroup X) := (mem_inf.mp m.2).2
  set a : X := ((m : (R : Subgroup X)) : X) with ha
  have haR : a ∈ (R : Subgroup X) := (m : (R : Subgroup X)).2
  have ha1 : a ≠ 1 := fun h => hm1 (Subtype.ext (Subtype.ext h))
  have hac : ∀ r ∈ (R : Subgroup X), r * a = a * r := fun r hr =>
    congrArg Subtype.val (mem_center_iff.mp hmZ ⟨r, hr⟩)
  obtain ⟨n, hn⟩ := R.isPGroup' ⟨a, haR⟩
  have hdvd : orderOf a ∣ p ^ n :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact ha1 hj
  refine ⟨a ^ (p ^ (j - 1)), ⟨(R : Subgroup X).pow_mem haR _, K.pow_mem hmK _⟩, ?_, fun r hr => ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hj ▸ pow_dvd_pow p (Nat.sub_le j 1)), hj,
      show p ^ j = p ^ (j - 1) * p by rw [← pow_succ]; congr 1; omega,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  · exact ((Commute.pow_right (show Commute r a from hac r hr) _)).eq

namespace PPointReduced

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G} {x : G}
  {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}

theorem exists_central_pair [Fact p.Prime] (hp2 : p ≠ 2) (h : PPointReduced p M x R K)
    (hZ : center K = ⊥) {z : RedCent p x} (hz : z ∈ center (RedCent p x)) (hzp : orderOf z = p) :
    ∃ y ∈ (R : Subgroup (RedCent p x)) ⊓ K, orderOf y = p ∧
      (∀ r ∈ (R : Subgroup (RedCent p x)), r * y = y * r) ∧ y ∉ zpowers z := by
  have hp : p.Prime := Fact.out
  obtain ⟨t, ⟨htR, htK⟩, htp, -⟩ := exists_mem_sylow_inf_component hp hp2 h.red.core_eq_bot R
    h.component
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at htp
    exact hp.one_lt.ne htp
  obtain ⟨y, hyRK, hyp, hyc⟩ := exists_orderOf_eq_mem_inf_center R h.normal htR htK ht1
  refine ⟨y, hyRK, hyp, hyc, fun hyz => ?_⟩
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyp
    exact hp.one_lt.ne hyp
  have heq : zpowers y = zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyz) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hyp, hzp]
  have hzK : z ∈ K := by
    have : z ∈ zpowers y := heq ▸ mem_zpowers z
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp this
    rw [← hk]
    exact K.zpow_mem hyRK.2 k
  have hzZ : (⟨z, hzK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (mem_center_iff.mp hz k)
  rw [hZ, mem_bot] at hzZ
  have : z = 1 := congrArg Subtype.val hzZ
  rw [this, orderOf_one] at hzp
  exact hp.one_lt.ne hzp

theorem commute_of_coprime [Fact p.Prime] (hp2 : p ≠ 2) (hsig : GL83SignalizerAut)
    (h : PPointReduced p M x R K) {z : RedCent p x} (hz : z ∈ center (RedCent p x))
    (hzp : orderOf z = p) {i : TauCeti.CFSGIndex} (hi : GL83Type24 p i)
    (e : Nonempty (K ≃* i.Group))
    (hin : GL83OuterType24 p i ∨ ∀ g ∈ (R : Subgroup (RedCent p x)), g ^ p = 1 →
      g ∈ K ⊔ centralizer (K : Set (RedCent p x)))
    {E F : Subgroup (RedCent p x)} (hER : E ≤ (R : Subgroup (RedCent p x)))
    (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E) (hF : p.Coprime (Nat.card F))
    (hEF : E ≤ normalizer (F : Set (RedCent p x))) :
    ∀ a ∈ E, ∀ f ∈ F, a * f = f * a :=
  commute_of_coprime_of_card hp2 hsig h.normal hi e (h.isPGroup_centralizer hz hzp)
    (h.isCyclic_centralizer hz hzp) hE hE3
    (hin.imp_right fun h' a ha => h' a (hER ha) (hE.2 a ha)) hF hEF

end PPointReduced

namespace IsPPoint

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem exists_central_of_not_mem_zpowers [Fact p.Prime] (hp2 : p ≠ 2)
    (h243 : GL83ComponentPCoreTrivial) (hS : D1Global G) (hFC : FullCoreLocality G)
    (hloc : D1Local p P M) (h : IsPPoint p P M x) :
    ∃ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G),
      (∀ q ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), q * y = y * q) ∧ orderOf y = p ∧
        y ∉ zpowers x := by
  have hp : p.Prime := Fact.out
  obtain ⟨R, K, hRK, hReq⟩ := h.exists_pPointReduced hFC hloc
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  have hZ := hRK.center_eq_bot hp2 h243 (h.catalogSimpleSections hS hp)
  obtain ⟨y, hyRK, hyp, hyc, hynz⟩ := hRK.exists_central_pair hp2 hZ hzc hzp
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set Q : Subgroup G := (P : Subgroup G) ⊓ C with hQ
  have hQp : IsPGroup p Q := P.isPGroup'.to_inf_left
  have hQ' : IsPGroup p (Q.subgroupOf C) := hQp.comap_subtype
  have hOc : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hyR : y ∈ (Q.subgroupOf C).map (QuotientGroup.mk' O) := hReq ▸ hyRK.1
  obtain ⟨c, hcQ, hcy⟩ := hyR
  refine ⟨(c : G), hcQ, fun q hq => ?_, ?_, fun hmem => ?_⟩
  · have hqQ : (⟨q, hq.2⟩ : C) ∈ Q.subgroupOf C := hq
    have hcomm : QuotientGroup.mk' O ⟨q, hq.2⟩ * QuotientGroup.mk' O c =
        QuotientGroup.mk' O c * QuotientGroup.mk' O ⟨q, hq.2⟩ := by
      rw [hcy]
      exact hyc _ (hReq ▸ ⟨_, hqQ, rfl⟩)
    exact congrArg Subtype.val (commute_of_mk_commute hp O hOc hQ' hqQ hcQ hcomm)
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_of_orderOf_mk_eq hp O hOc hQ' hcQ (by rw [hcy]; exact hyp)
  · obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
    have hcj : c = (⟨x, mem_centralizer_singleton_iff.2 rfl⟩ : C) ^ j :=
      Subtype.ext (by rw [← hj]; simp)
    apply hynz
    rw [← hcy, hcj, map_zpow]
    exact zpow_mem_zpowers _ j

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {C E : Subgroup G} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.subgroupOf C) := CFSG.Open.IsElemAbelian.subgroupOf hE C

theorem commutator_le_primeCore [Fact p.Prime] (hp2 : p ≠ 2) (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut) (hS : D1Global G)
    (hFC : FullCoreLocality G) (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {E F : Subgroup G} (hEQ : E ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G))
    (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E) (hFC' : F ≤ centralizer ({x} : Set G))
    (hF : p.Coprime (Nat.card F)) (hEF : E ≤ normalizer (F : Set G)) :
    ⁅F, E⁆ ≤ GLBPrimeCore p (centralizer ({x} : Set G)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨R, K, hRK, hReq⟩ := h.exists_pPointReduced hFC hloc
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  obtain ⟨i, ⟨e⟩, hi, hio⟩ := hRK.exists_equiv_type hp2 h243 h244
    (h.catalogSimpleSections hS hp) hzc hzp
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set ρ := QuotientGroup.mk' O with hρ
  have hOc : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hEC : E ≤ C := hEQ.trans inf_le_right
  have hEp : IsPGroup p E := CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p E hE
  obtain ⟨φ, -⟩ := exists_mulEquiv_map_mk O hp hOc hEp hEC
  have hEbcard : Nat.card ((E.subgroupOf C).map ρ) = Nat.card E := (Nat.card_congr φ.toEquiv).symm
  have hEbR : (E.subgroupOf C).map ρ ≤ (R : Subgroup (RedCent p x)) := by
    rw [hReq]
    exact Subgroup.map_mono fun a ha => hEQ ha
  have hFb : p.Coprime (Nat.card ((F.subgroupOf C).map ρ)) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (F.subgroupOf C) ρ) ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC').toEquiv]
  have hEbFb : (E.subgroupOf C).map ρ ≤
      normalizer (((F.subgroupOf C).map ρ : Subgroup _) : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    refine Subgroup.le_normalizer_map ρ ⟨a, mem_normalizer_iff.mpr fun g => ?_, rfl⟩
    exact (mem_normalizer_iff.mp (hEF ha)) (g : G)
  have hEb3 : p ^ 3 ≤ Nat.card ((E.subgroupOf C).map ρ) := by rw [hEbcard]; exact hE3
  have key := hRK.commute_of_coprime hp2 hsig hzc hzp hi ⟨e⟩ hio hEbR
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p (isElemAbelian_subgroupOf hE) ρ)
    hEb3 hFb hEbFb
  refine Subgroup.commutator_le.mpr fun f hf a ha => ?_
  have hfC : f ∈ C := hFC' hf
  have haC : a ∈ C := hEC ha
  have hcomm := key (ρ ⟨a, haC⟩) ⟨⟨a, haC⟩, ha, rfl⟩ (ρ ⟨f, hfC⟩) ⟨⟨f, hfC⟩, hf, rfl⟩
  have hker : (⟨f, hfC⟩ * ⟨a, haC⟩ * (⟨f, hfC⟩ : C)⁻¹ * (⟨a, haC⟩ : C)⁻¹ : C) ∈ O := by
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
    change ρ _ = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc ρ ⟨f, hfC⟩ * ρ ⟨a, haC⟩ * (ρ ⟨f, hfC⟩)⁻¹ * (ρ ⟨a, haC⟩)⁻¹
        = ρ ⟨a, haC⟩ * ρ ⟨f, hfC⟩ * (ρ ⟨f, hfC⟩)⁻¹ * (ρ ⟨a, haC⟩)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  have hmem : (⟨f, hfC⟩ * ⟨a, haC⟩ * (⟨f, hfC⟩ : C)⁻¹ * (⟨a, haC⟩ : C)⁻¹ : C) ∈
      (GLBPrimeCore p C).subgroupOf C := by
    rw [glbPrimeCore_subgroupOf]
    exact hker
  exact hmem

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC
