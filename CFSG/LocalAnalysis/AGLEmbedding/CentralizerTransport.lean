module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSL
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Assembly.LowTwoRank Matrix

section Quotient

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ}

theorem commute_of_mk_commute (hp : p.Prime) (O : Subgroup Y) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {T : Subgroup Y} (hT : IsPGroup p T) {a b : Y} (ha : a ∈ T)
    (hb : b ∈ T)
    (hab : QuotientGroup.mk' O a * QuotientGroup.mk' O b =
      QuotientGroup.mk' O b * QuotientGroup.mk' O a) :
    a * b = b * a :=
  eq_of_mk_eq_of_isPGroup hp O hO hT (T.mul_mem ha hb) (T.mul_mem hb ha) (by
    rw [map_mul, map_mul, hab])

theorem orderOf_eq_of_orderOf_mk_eq (hp : p.Prime) (O : Subgroup Y) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {T : Subgroup Y} (hT : IsPGroup p T) {y : Y} (hy : y ∈ T)
    (hyp : orderOf (QuotientGroup.mk' O y) = p) : orderOf y = p := by
  have : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime (eq_of_mk_eq_of_isPGroup hp O hO hT (T.pow_mem hy p) T.one_mem (by
    rw [map_pow, map_one, ← hyp, pow_orderOf_eq_one])) fun h1 => ?_
  rw [h1, map_one, orderOf_one] at hyp
  exact hp.one_lt.ne hyp

end Quotient

section Centralizer

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {C : Subgroup G} (O : Subgroup C) [O.Normal]

theorem mem_zpowers_mk_of_mem_centralizer (hp : p.Prime) (hO : p.Coprime (Nat.card O))
    {P : Subgroup G} (hP : IsPGroup p P) (hPC : P ≤ C) {zC : C}
    (huniq : ∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ P → orderOf y = p →
      y ∈ Subgroup.zpowers (zC : G))
    {y : C ⧸ O} (hy : y ∈ (P.subgroupOf C).map (QuotientGroup.mk' O))
    (hyc : y ∈ Subgroup.centralizer
      (((P.subgroupOf C).map (QuotientGroup.mk' O) : Subgroup (C ⧸ O)) : Set (C ⧸ O)))
    (hyp : orderOf y = p) :
    y ∈ Subgroup.zpowers (QuotientGroup.mk' O zC) := by
  have hP' : IsPGroup p (P.subgroupOf C) := hP.comap_subtype
  obtain ⟨y, hyP, rfl⟩ := hy
  have hyc' : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hxP : (⟨x, hPC hx⟩ : C) ∈ P.subgroupOf C := hx
    exact congrArg Subtype.val (commute_of_mk_commute hp O hO hP' hxP hyP
      (Subgroup.mem_centralizer_iff.mp hyc _ (Subgroup.mem_map_of_mem _ hxP)))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (huniq _ hyc' hyP (by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_of_orderOf_mk_eq hp O hO hP' hyP hyp))
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow]
  exact congrArg _ (Subtype.ext ((Subgroup.coe_zpow _ _ _).trans hk))

theorem pRank_map_inf_centralizer_le (hp : p.Prime) (hO : p.Coprime (Nat.card O))
    {P : Subgroup G} (hP : IsPGroup p P) (hPC : P ≤ C) {v : G} (hv : v ∈ P) :
    Open.pRank p ((P.subgroupOf C).map (QuotientGroup.mk' O) ⊓
        Subgroup.centralizer ({QuotientGroup.mk' O ⟨v, hPC hv⟩} : Set (C ⧸ O))) ≤
      Open.pRank p (P ⊓ Subgroup.centralizer ({v} : Set G)) := by
  have hP' : IsPGroup p (P.subgroupOf C) := hP.comap_subtype
  have hvP : (⟨v, hPC hv⟩ : C) ∈ P.subgroupOf C := hv
  have hle : (P.subgroupOf C).map (QuotientGroup.mk' O) ⊓
      Subgroup.centralizer ({QuotientGroup.mk' O ⟨v, hPC hv⟩} : Set (C ⧸ O)) ≤
      (P.subgroupOf C ⊓ Subgroup.centralizer ({⟨v, hPC hv⟩} : Set C)).map
        (QuotientGroup.mk' O) := by
    rintro _ ⟨⟨y, hyP, rfl⟩, hyc⟩
    exact ⟨y, ⟨hyP, Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mk_commute hp O hO
      hP' hyP hvP (Subgroup.mem_centralizer_singleton_iff.mp hyc))⟩, rfl⟩
  have hle' : (P.subgroupOf C ⊓ Subgroup.centralizer ({⟨v, hPC hv⟩} : Set C)).map C.subtype ≤
      P ⊓ Subgroup.centralizer ({v} : Set G) := by
    rintro _ ⟨y, ⟨hyP, hyc⟩, rfl⟩
    exact ⟨hyP, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyc))⟩
  calc Open.pRank p _ ≤ Open.pRank p ((P.subgroupOf C ⊓
          Subgroup.centralizer ({⟨v, hPC hv⟩} : Set C)).map (QuotientGroup.mk' O)) :=
        PreuniquenessRankFour.Helpers.pRank_mono p hp hle
    _ = Open.pRank p ((P.subgroupOf C ⊓
          Subgroup.centralizer ({⟨v, hPC hv⟩} : Set C)).map C.subtype) :=
        pRank_map_mk_eq_pRank_map_subtype hp O hO _
    _ ≤ _ := PreuniquenessRankFour.Helpers.pRank_mono p hp hle'

theorem exists_mulEquiv_map_mk (hp : p.Prime) (hO : p.Coprime (Nat.card O)) {E : Subgroup G}
    (hE : IsPGroup p E) (hEC : E ≤ C) :
    ∃ φ : E ≃* (E.subgroupOf C).map (QuotientGroup.mk' O),
      ∀ u : E, (φ u : C ⧸ O) = QuotientGroup.mk' O (Subgroup.inclusion hEC u) := by
  have hE' : IsPGroup p (E.subgroupOf C) := hE.comap_subtype
  let f : E →* (E.subgroupOf C).map (QuotientGroup.mk' O) :=
    ((QuotientGroup.mk' O).comp (Subgroup.inclusion hEC)).codRestrict _
      fun u => ⟨Subgroup.inclusion hEC u, u.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u u' huu => Subgroup.inclusion_injective hEC
      (eq_of_mk_eq_of_isPGroup hp O hO hE' u.2 u'.2 (congrArg Subtype.val huu)), ?_⟩
    rintro ⟨_, c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective f hf, fun u => rfl⟩

omit [Finite G] in
theorem map_center_eq_zpowers_mk {E : Subgroup G} (hEC : E ≤ C)
    (φ : E ≃* (E.subgroupOf C).map (QuotientGroup.mk' O))
    (hφ : ∀ u : E, (φ u : C ⧸ O) = QuotientGroup.mk' O (Subgroup.inclusion hEC u)) {zC : C}
    (hEZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers (zC : G)) :
    (Subgroup.center ((E.subgroupOf C).map (QuotientGroup.mk' O))).map
        ((E.subgroupOf C).map (QuotientGroup.mk' O)).subtype =
      Subgroup.zpowers (QuotientGroup.mk' O zC) := by
  have hι : (Subgroup.center E).map (Subgroup.inclusion hEC) = Subgroup.zpowers zC := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_map, Subgroup.subtype_comp_inclusion, hEZ, MonoidHom.map_zpowers]
    rfl
  have hcomp : ((E.subgroupOf C).map (QuotientGroup.mk' O)).subtype.comp φ.toMonoidHom =
      (QuotientGroup.mk' O).comp (Subgroup.inclusion hEC) := MonoidHom.ext hφ
  rw [← map_center_eq_of_mulEquiv φ, Subgroup.map_map, hcomp, ← Subgroup.map_map, hι,
    MonoidHom.map_zpowers]

end Centralizer

section SL

variable {p : ℕ} [Fact p.Prime]

theorem statedSL_le_map_centerQuotientAction_of_mulEquiv {G Y : Type*} [Group G] [Group Y]
    {E L : Subgroup G} {Ebar Lbar : Subgroup Y} (φ : E ≃* Ebar)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set G))).map (centerQuotientAction E e))
    (hlift : ∀ g ∈ L, g ∈ Subgroup.normalizer (E : Set G) → ∃ g' ∈ Lbar,
      g' ∈ Subgroup.normalizer (Ebar : Set Y) ∧
        ∀ u v : E, (v : G) = g * u * g⁻¹ → ((φ v : Ebar) : Y) = g' * φ u * g'⁻¹) :
    StatedSL 2 (ZMod p) ≤ (Lbar.subgroupOf (Subgroup.normalizer (Ebar : Set Y))).map
      (centerQuotientAction Ebar ((QuotientGroup.congr (Subgroup.center E)
        (Subgroup.center Ebar) φ (map_center_eq_of_mulEquiv φ)).symm.trans e)) := by
  refine statedSL_le_map_centerQuotientAction Ebar Lbar _ fun a ha => ?_
  obtain ⟨⟨g, hgN⟩, hgL, hga⟩ := hSL ha
  obtain ⟨g', hg'L, hg'N, hg'⟩ := hlift g hgL hgN
  refine ⟨g', hg'L, hg'N, fun u' v' huv => ?_⟩
  obtain ⟨u, rfl⟩ := φ.surjective u'
  obtain ⟨v, rfl⟩ := φ.surjective v'
  have hw : g * u * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hgN u).mp u.2
  have hvw : v = ⟨_, hw⟩ := φ.injective (Subtype.ext (huv.trans (hg' u ⟨_, hw⟩ rfl).symm))
  have key := centerQuotientAction_mulVec E e ⟨g, hgN⟩ (congrArg Subtype.val hvw)
  rw [hga] at key
  have hmk : ∀ w : E, (QuotientGroup.congr (Subgroup.center E) (Subgroup.center Ebar) φ
      (map_center_eq_of_mulEquiv φ)).symm (φ w : Ebar ⧸ Subgroup.center Ebar) =
        (w : E ⧸ Subgroup.center E) := fun w =>
    (MulEquiv.symm_apply_eq _).mpr (QuotientGroup.congr_mk _ _ _ _ w).symm
  simp only [MulEquiv.trans_apply, hmk]
  exact key.symm

variable {G : Type*} [Group G] {C : Subgroup G} (O : Subgroup C) [O.Normal]

theorem statedSL_le_map_mk {E L : Subgroup G} (hEC : E ≤ C) (hLC : L ≤ C)
    (φ : E ≃* (E.subgroupOf C).map (QuotientGroup.mk' O))
    (hφ : ∀ u : E, (φ u : C ⧸ O) = QuotientGroup.mk' O (Subgroup.inclusion hEC u))
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set G))).map (centerQuotientAction E e)) :
    StatedSL 2 (ZMod p) ≤ (((L.subgroupOf C).map (QuotientGroup.mk' O)).subgroupOf
      (Subgroup.normalizer (((E.subgroupOf C).map (QuotientGroup.mk' O) : Subgroup (C ⧸ O)) :
        Set (C ⧸ O)))).map (centerQuotientAction _ ((QuotientGroup.congr (Subgroup.center E)
          (Subgroup.center _) φ (map_center_eq_of_mulEquiv φ)).symm.trans e)) := by
  refine statedSL_le_map_centerQuotientAction_of_mulEquiv φ e hSL fun g hgL hgN => ?_
  have hgC := hLC hgL
  refine ⟨QuotientGroup.mk' O ⟨g, hgC⟩, ⟨⟨g, hgC⟩, hgL, rfl⟩, Subgroup.le_normalizer_map _
    ⟨⟨g, hgC⟩, Subgroup.le_normalizer_comap C.subtype hgN, rfl⟩, fun u v huv => ?_⟩
  rw [hφ, hφ, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext huv)

end SL

section Elements

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem exists_inf_centralizer_le [Fact p.Prime] {P D : Subgroup G} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) {z : G} (hzD : z ∈ D) (hzp : orderOf z = p)
    (hzc : z ∈ Subgroup.centralizer (P : Set G)) :
    ∃ v ∈ D, orderOf v = p ∧
      P ⊓ Subgroup.centralizer ({v} : Set G) ≤ P ⊓ Subgroup.centralizer (D : Set G) := by
  have hp : p.Prime := Fact.out
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzp]
  obtain ⟨v, hvD, hvz⟩ : ∃ v ∈ D, v ∉ Subgroup.zpowers z := by
    by_contra! hall
    have hle := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers z from hall)
    rw [hDcard, hzcard] at hle
    have := hp.two_le
    nlinarith
  have hvp : orderOf v = p := orderOf_eq_prime (hD.2 v hvD) fun h1 => hvz (h1 ▸ Subgroup.one_mem _)
  have hSD : Subgroup.zpowers z ⊔ Subgroup.zpowers v ≤ D :=
    sup_le (Subgroup.zpowers_le.mpr hzD) (Subgroup.zpowers_le.mpr hvD)
  have hS : Subgroup.zpowers z ⊔ Subgroup.zpowers v = D := by
    refine Subgroup.eq_of_le_of_card_ge hSD ?_
    obtain ⟨k, hk, hkS⟩ := (Nat.dvd_prime_pow hp).mp (hDcard ▸ Subgroup.card_dvd_of_le hSD)
    have hlt : Nat.card (Subgroup.zpowers z) <
        Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers v : Subgroup G) :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hvz (by
        rw [h]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)))
    rw [hzcard, hkS] at hlt
    have hk1 : 1 < k := (pow_lt_pow_iff_right₀ hp.one_lt).mp (by rwa [pow_one])
    rw [hDcard, hkS, show k = 2 by omega]
  refine ⟨v, hvD, hvp, fun x hx => ⟨hx.1, ?_⟩⟩
  have hDx : D ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hS]
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hzc x hx.1).symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm))
  exact Subgroup.mem_centralizer_iff.mpr fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mp (hDx hd)

omit [Finite G] in
theorem centralizer_singleton_ne_top (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz : z ≠ 1) : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
  intro htop
  have hzZ : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hZ | hZ
  · exact hz (Subgroup.mem_bot.mp (hZ ▸ hzZ))
  · obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top b) a)

end Elements

theorem D1Extremal.exists_reduced_centralizer_data {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hglob : D1Global G) {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M)
    {H R : Subgroup G} (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (Rbar : Sylow p X) (X₀ : Subgroup X) (zbar : X),
      ReducedNongeneration p X Rbar X₀ ∧ 4 ≤ Open.pRank p (Rbar : Subgroup X) ∧
      CatalogSimpleSections X ∧ zbar ∈ Subgroup.center X ∧ orderOf zbar = p ∧
      (∀ y ∈ (Rbar : Subgroup X), y ∈ Subgroup.centralizer (Rbar : Set X) → orderOf y = p →
        y ∈ Subgroup.zpowers zbar) ∧
      (∃ K : Subgroup X, IsComponentOf K ⊤ ∧ K.Normal) ∧
      (∃ v ∈ (Rbar : Subgroup X), orderOf v = p ∧
        Open.pRank p ((Rbar : Subgroup X) ⊓ Subgroup.centralizer ({v} : Set X)) ≤ 2) ∧
      ∃ E L : Subgroup X, E ≤ (Rbar : Subgroup X) ∧ Nat.card E = p ^ 3 ∧
        (∀ x ∈ E, x ^ p = 1) ∧ (Subgroup.center E).map E.subtype = Subgroup.zpowers zbar ∧
        ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
          StatedSL 2 (ZMod p) ≤
            (L.subgroupOf (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e) := by
  have hp := h.prime
  obtain ⟨z, -, hzp, hzc, huniq, hCM, hcoreM, -, hlayer,
    ⟨D, hDR, hD, hDcard, hzD, -, hDrank⟩, E, hER, hEcard, hEexp, hEZ, e, hSL⟩ :=
    h.exists_sl_two_of_hasPrimeConstraint hloc hcon
  have hP4 : 4 ≤ Open.pRank p (P : Subgroup G) := betaFour_all_sylows_rank_ge_four hloc.beta P
  obtain ⟨Pbar, hPbar, hred, hzbar⟩ := reducedNongeneration_centralizer_of_not_le hp h.ne_two P
    h.sylow_le h.weakCore_le (by omega) hzc hzp hCM hcoreM
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc x hx)
  let zC : Subgroup.centralizer ({z} : Set G) := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨hzZ, hzbarp⟩ := hzbar zC rfl
  have hEP : E ≤ (P : Subgroup G) := hER.trans h.le_P
  have hEC := hEP.trans hPC
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_mk _ hp hO (P.isPGroup'.to_le hEP) hEC
  obtain ⟨v, hvD, hvp, hvle⟩ := exists_inf_centralizer_le hD hDcard hzD hzp hzc
  have hvP : v ∈ (P : Subgroup G) := h.le_P (hDR hvD)
  refine ⟨_, inferInstance, inferInstance, Pbar, _, QuotientGroup.mk' _ zC, hred, ?_, ?_, hzZ,
    hzbarp, fun y hy hyc hyp => ?_, ?_, ⟨QuotientGroup.mk' _ ⟨v, hPC hvP⟩, ?_, ?_, ?_⟩,
    (E.subgroupOf _).map (QuotientGroup.mk' _),
    ((H ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf _).map (QuotientGroup.mk' _), ?_,
    (Nat.card_congr φ.toEquiv).symm.trans hEcard, ?_, map_center_eq_zpowers_mk _ hEC φ hφ hEZ, _,
    statedSL_le_map_mk _ hEC inf_le_right φ hφ e hSL⟩
  · rw [hPbar, pRank_map_mk_eq_pRank_map_subtype hp _ hO, Subgroup.map_subgroupOf_eq_of_le hPC]
    exact hP4
  · have hz1 : z ≠ 1 := fun hz1 => hp.one_lt.ne (by rw [← hzp, hz1, orderOf_one])
    exact (catalogSimpleSections_of_isKProper hglob.kProper _
      (centralizer_singleton_ne_top hglob.simple hglob.nonab hz1)).quotient _
  · refine mem_zpowers_mk_of_mem_centralizer _ hp hO P.isPGroup' hPC huniq (hPbar ▸ hy) ?_ hyp
    rw [← hPbar]
    exact hyc
  · obtain ⟨K, hK⟩ := exists_isComponentOf_of_layer_ne_bot hlayer
    exact ⟨K, hK, hred.normal_of_isComponentOf_of_center hzZ hzbarp hK⟩
  · rw [hPbar]
    exact ⟨⟨v, hPC hvP⟩, hvP, rfl⟩
  · exact orderOf_mk_of_coprime hp _ hO ((Subgroup.orderOf_coe _).symm.trans hvp)
  · rw [hPbar]
    exact (pRank_map_inf_centralizer_le _ hp hO P.isPGroup' hPC hvP).trans
      ((PreuniquenessRankFour.Helpers.pRank_mono p hp hvle).trans hDrank)
  · rw [hPbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hEP)
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ (Subtype.ext (hEexp c hc))).trans (map_one _)

end CFSG.AGLEmbedding
