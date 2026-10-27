module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedEscape
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux2

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Assembly.LowTwoRank Matrix

section Lift

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ}

theorem exists_mem_normalizer_mk_eq (hp : p.Prime) (O : Subgroup Y) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {E₁ : Subgroup Y} (hE₁ : IsPGroup p E₁)
    (hn : (E₁.map (QuotientGroup.mk' O)).Normal) (x : Y ⧸ O) :
    ∃ g ∈ Subgroup.normalizer (E₁ : Set Y), QuotientGroup.mk' O g = x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O x
  have hle := comap_normalizer_map_le_sup hp O hO hE₁
  rw [Subgroup.normalizer_eq_top_iff.mpr hn, Subgroup.comap_top] at hle
  have hy : y ∈ ((O ⊔ Subgroup.normalizer (E₁ : Set Y) : Subgroup Y) : Set Y) :=
    hle (Subgroup.mem_top y)
  rw [Subgroup.normal_mul, Set.mem_mul] at hy
  obtain ⟨n, hn, g, hg, rfl⟩ := hy
  refine ⟨g, hg, ?_⟩
  have hn1 : QuotientGroup.mk' O n = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hn
  rw [map_mul, hn1, one_mul]

theorem eq_of_mk_eq_of_isPGroup (hp : p.Prime) (O : Subgroup Y) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {T : Subgroup Y} (hT : IsPGroup p T) {a b : Y} (ha : a ∈ T)
    (hb : b ∈ T) (hab : QuotientGroup.mk' O a = QuotientGroup.mk' O b) : a = b := by
  have hmem : a⁻¹ * b ∈ T ⊓ O := ⟨T.mul_mem (T.inv_mem ha) hb, QuotientGroup.eq.mp hab⟩
  rwa [inf_eq_bot_of_isPGroup hp hT hO, Subgroup.mem_bot, inv_mul_eq_one] at hmem

end Lift

section IsolatedVertex

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem pRank_inf_centralizer_le_two_of_normalizer_not_le (hp : p.Prime) (P : Sylow p G)
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M) (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    {D : Subgroup G} (hD : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2) (hDP : D ≤ P)
    (hDN : ¬ Subgroup.normalizer (D : Set G) ≤ M) :
    Open.pRank p ((P : Subgroup G) ⊓ Subgroup.centralizer (D : Set G)) ≤ 2 := by
  by_contra! h3
  exact hDN (normalizer_le_of_centralizer_rank_in_containing_sylow p hp P hPM hWM (hDP.trans hPM)
    (IsPGroup.of_card hDcard) (le_csSup (pRank_bddAbove p hp D) ⟨D, le_rfl, hD, hDcard⟩)
    ((show 3 ≤ Open.pRank p ((P : Subgroup G) ⊓ Subgroup.centralizer (D : Set G)) by omega).trans
      (PreuniquenessRankFour.Helpers.pRank_mono p hp (inf_le_inf_right _ hPM))))

end IsolatedVertex

section SL

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1Escape.exists_sl_two_of_hasPrimeConstraint [Fact p.Prime] (h : D1Escape p P M H R)
    (hcon : HasPrimeConstraint (G := H) p) {z : G} (hzR : z ∈ R)
    (hzc : z ∈ Subgroup.centralizer (R : Set G)) (hzp : orderOf z = p) :
    ∃ E : Subgroup G, E ≤ R ∧ Nat.card E = p ^ 3 ∧ (∀ x ∈ E, x ^ p = 1) ∧
      (Subgroup.center E).map E.subtype = Subgroup.zpowers z ∧
      ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
        StatedSL 2 (ZMod p) ≤ ((H ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf
          (Subgroup.normalizer (E : Set G))).map (centerQuotientAction E e) := by
  have hp := h.prime
  obtain ⟨Rbar, hRbar, hred⟩ := h.reducedNongeneration
  obtain ⟨Q, hQn, hQp, hQc⟩ := hcon
  have : Q.Normal := hQn
  set O := primeComplementCore (G := H) p
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hTp : IsPGroup p (R.subgroupOf H) := h.isPGroup.comap_subtype
  have hinj : ∀ {a b : H}, a ∈ R.subgroupOf H → b ∈ R.subgroupOf H →
      QuotientGroup.mk' O a = QuotientGroup.mk' O b → a = b :=
    fun ha hb hab => eq_of_mk_eq_of_isPGroup hp O hO hTp ha hb hab
  let zH : H := ⟨z, h.le_H hzR⟩
  have hzT : zH ∈ R.subgroupOf H := hzR
  have hzbarc : QuotientGroup.mk' O zH ∈ Subgroup.centralizer (Rbar : Set (H ⧸ O)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : r ∈ (Rbar : Subgroup (H ⧸ O)) := hr
    rw [hRbar] at hr'
    obtain ⟨t, ht, rfl⟩ := hr'
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc t ht))
  have hzbarp : orderOf (QuotientGroup.mk' O zH) = p := by
    have hzHp : orderOf zH = p := (Subgroup.orderOf_mk z _).trans hzp
    have hzHpow : zH ^ p = 1 := by simpa [hzHp] using pow_orderOf_eq_one zH
    refine orderOf_eq_prime (by rw [← map_pow, hzHpow, map_one]) ?_
    intro h1
    have hz1 : zH = 1 := hinj hzT (R.subgroupOf H).one_mem (by rw [h1, map_one])
    rw [hz1, orderOf_one] at hzHp
    exact hp.one_lt.ne hzHp
  obtain ⟨Eb, hEbn, hEbQ, hEbcard, hEbp, hEbZ, eb, hEbSL⟩ :=
    hred.exists_extraspecial_sl_two hQp hQc hzbarc hzbarp
  have hEbT : Eb ≤ (R.subgroupOf H).map (QuotientGroup.mk' O) := by
    have hle := hEbQ.trans (hQp.le_sylow_of_normal Rbar)
    rwa [hRbar] at hle
  set E₁ := Eb.comap (QuotientGroup.mk' O) ⊓ R.subgroupOf H with hE₁
  have hE₁map : E₁.map (QuotientGroup.mk' O) = Eb := map_comap_inf_eq _ hEbT
  set E := E₁.map H.subtype with hE
  have hEH : E ≤ H := Subgroup.map_subtype_le E₁
  have hER : E ≤ R :=
    (Subgroup.map_mono inf_le_right).trans (Subgroup.map_subgroupOf_eq_of_le h.le_H).le
  have hmemE₁ : ∀ u : E, (⟨(u : G), hEH u.2⟩ : H) ∈ E₁ := by
    rintro ⟨_, w, hw, rfl⟩
    exact hw
  let f : E →* Eb := ((QuotientGroup.mk' O).comp (Subgroup.inclusion hEH)).codRestrict Eb
    fun u => (hmemE₁ u).1
  have hfinj : Function.Injective f := by
    intro u u' huu'
    have heq := hinj (hmemE₁ u).2 (hmemE₁ u').2 (congrArg Subtype.val huu')
    exact Subtype.ext (congrArg (fun w : H => (w : G)) heq)
  have hfsurj : Function.Surjective f := by
    intro v
    have hv : (v : H ⧸ O) ∈ E₁.map (QuotientGroup.mk' O) := hE₁map.symm ▸ v.2
    obtain ⟨w, hw, hwv⟩ := hv
    exact ⟨⟨(w : G), w, hw, rfl⟩, Subtype.ext hwv⟩
  let ψ : E ≃* Eb := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hψ : ∀ u : E, ((ψ u : Eb) : H ⧸ O) = QuotientGroup.mk' O ⟨(u : G), hEH u.2⟩ :=
    fun u => rfl
  let e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p) :=
    (QuotientGroup.congr (Subgroup.center E) (Subgroup.center Eb) ψ
      (Subgroup.map_center_eq ψ)).trans eb
  have he : ∀ u : E, e (u : E ⧸ Subgroup.center E) =
      eb ((ψ u : Eb) : Eb ⧸ Subgroup.center Eb) := fun u => rfl
  have hzEb : QuotientGroup.mk' O zH ∈ Eb := by
    have hmem : QuotientGroup.mk' O zH ∈ (Subgroup.center Eb).map Eb.subtype :=
      hEbZ ▸ Subgroup.mem_zpowers _
    obtain ⟨c, -, hc⟩ := hmem
    exact hc ▸ c.2
  have hzE₁ : zH ∈ E₁ := ⟨hzEb, hzT⟩
  have hzE : z ∈ E := ⟨zH, hzE₁, rfl⟩
  refine ⟨E, hER, ?_, ?_, ?_, e, statedSL_le_map_centerQuotientAction E _ e fun a ha => ?_⟩
  · rw [← hEbcard]
    exact Nat.card_congr ψ.toEquiv
  · intro x hx
    have h1 : ψ (⟨x, hx⟩ ^ p) = ψ 1 := by
      rw [map_pow, map_one]
      exact Subtype.ext (hEbp _ (ψ ⟨x, hx⟩).2)
    simpa using congrArg Subtype.val (ψ.injective h1)
  · refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨z, hzE⟩, Subgroup.mem_center_iff.mpr fun v => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hzc v (hER v.2)
    · rw [Subgroup.card_map_of_injective E.subtype_injective, Nat.card_zpowers, hzp,
        Nat.card_congr (Subgroup.centerCongr ψ).toEquiv,
        ← Subgroup.card_map_of_injective Eb.subtype_injective, hEbZ, Nat.card_zpowers, hzbarp]
  · obtain ⟨x, hx, hxu⟩ := hEbSL a ha
    obtain ⟨g, hgN, hgx⟩ :=
      exists_mem_normalizer_mk_eq hp O hO (hTp.to_le inf_le_right) (hE₁map ▸ hEbn) x
    have hgz : g * zH * g⁻¹ = zH := by
      refine hinj ((Subgroup.mem_normalizer_iff.mp hgN zH).mp hzE₁).2 hzT ?_
      rw [map_mul, map_mul, map_inv, hgx, Subgroup.mem_centralizer_singleton_iff.mp hx,
        mul_inv_cancel_right]
    refine ⟨(g : G), ⟨g.2, ?_⟩, Subgroup.le_normalizer_map H.subtype ⟨g, hgN, rfl⟩,
      fun u v huv => ?_⟩
    · change (g : G) ∈ Subgroup.centralizer ({z} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hgz' : (g : G) * z * (g : G)⁻¹ = z := congrArg Subtype.val hgz
      exact mul_inv_eq_iff_eq_mul.mp hgz'
    · rw [he, he]
      apply hxu
      rw [hψ, hψ, ← hgx]
      have huv' : (⟨(v : G), hEH v.2⟩ : H) = g * ⟨(u : G), hEH u.2⟩ * g⁻¹ := Subtype.ext huv
      rw [huv', map_mul, map_mul, map_inv]

end SL

theorem D1Extremal.exists_isolated_vertex_of_hasPrimeConstraint {G : Type} [Group G] [Finite G]
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M)
    {H R : Subgroup G} (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) :
    ∃ z : G, ∃ D : Subgroup G, D ≤ R ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ z ∈ D ∧
      ¬ Subgroup.normalizer (D : Set G) ≤ M ∧
      Open.pRank p ((P : Subgroup G) ⊓ Subgroup.centralizer (D : Set G)) ≤ 2 ∧
      orderOf z = p ∧ z ∈ Subgroup.centralizer (P : Set G) ∧
      (∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ (P : Subgroup G) → orderOf y = p →
        y ∈ Subgroup.zpowers z) ∧
      ¬ Subgroup.centralizer ({z} : Set G) ≤ M ∧
      GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M ∧
      Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) ∧
      CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) ≠ ⊥ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hP4 : 4 ≤ Open.pRank p (P : Subgroup G) := betaFour_all_sylows_rank_ge_four hloc.beta P
  have hRP := h.toD1Escape.ne_sylow_of_hasPrimeConstraint hcon hP4
  obtain ⟨D, hDR, hD, hDcard, hDN⟩ := h.toD1Escape.exists_isElemAbelian_normalizer_not_le hcon
  obtain ⟨z, hzD, hzp, hzc, huniq⟩ := exists_mem_center_of_normalizer_not_le hp h.ne_two P
    h.sylow_le h.weakCore_le (by omega) hD hDcard (hDR.trans h.le_P) hDN
  have hzR := hDR hzD
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc x hx)
  have hCM := h.toD1Escape.centralizer_not_le_of_hasPrimeConstraint hcon (by omega) hzR hzc hzp
  have hcoreM : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M :=
    intersecting_local_primeCore_le p hp P h.sylow_le h.weakCore_le
      ((show 3 ≤ Open.pRank p (P : Subgroup G) by omega).trans
        (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf hPC h.sylow_le)))
  refine ⟨z, D, hDR, hD, hDcard, hzD, hDN,
    pRank_inf_centralizer_le_two_of_normalizer_not_le hp P h.sylow_le h.weakCore_le hD hDcard
      (hDR.trans h.le_P) hDN, hzp, hzc, huniq, hCM, hcoreM, ?_, ?_⟩
  · exact odd_card_of_twoLocals_le hp P.isPGroup' hPC hCM (glbPrimeCore_le p _)
      (glbPrimeCore_normal p _) (glbPrimeCore_coprime p _) hcoreM
      fun T hT hT1 hPT => h.normalizer_le_of_sylow_le hRP hT hT1 hPT
  · refine layer_ne_bot_of_four_le_pRank hp h.ne_two P h.sylow_le h.weakCore_le hCM
      (P.subtype hPC) ?_ ?_ hcoreM
    · rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC]
    · rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC]
      exact hP4

theorem D1Extremal.exists_sl_two_of_hasPrimeConstraint {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M)
    {H R : Subgroup G} (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) :
    ∃ z : G, z ∈ R ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (P : Set G) ∧
      (∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ (P : Subgroup G) → orderOf y = p →
        y ∈ Subgroup.zpowers z) ∧
      ¬ Subgroup.centralizer ({z} : Set G) ≤ M ∧
      GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M ∧
      Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) ∧
      CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) ≠ ⊥ ∧
      (∃ D : Subgroup G, D ≤ R ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ z ∈ D ∧
        ¬ Subgroup.normalizer (D : Set G) ≤ M ∧
        Open.pRank p ((P : Subgroup G) ⊓ Subgroup.centralizer (D : Set G)) ≤ 2) ∧
      ∃ E : Subgroup G, E ≤ R ∧ Nat.card E = p ^ 3 ∧ (∀ x ∈ E, x ^ p = 1) ∧
        (Subgroup.center E).map E.subtype = Subgroup.zpowers z ∧
        ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
          StatedSL 2 (ZMod p) ≤ ((H ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf
            (Subgroup.normalizer (E : Set G))).map (centerQuotientAction E e) := by
  obtain ⟨z, D, hDR, hD, hDcard, hzD, hDN, hDrank, hzp, hzc, huniq, hCM, hcoreM, hodd,
    hlayer⟩ := h.exists_isolated_vertex_of_hasPrimeConstraint hloc hcon
  exact ⟨z, hDR hzD, hzp, hzc, huniq, hCM, hcoreM, hodd, hlayer,
    ⟨D, hDR, hD, hDcard, hzD, hDN, hDrank⟩,
    h.toD1Escape.exists_sl_two_of_hasPrimeConstraint hcon (hDR hzD)
      (Subgroup.centralizer_le h.le_P hzc) hzp⟩

end CFSG.AGLEmbedding
