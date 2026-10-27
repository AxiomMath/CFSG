module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2GSeries
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedFocal
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 CentSeries)

section Transport

theorem szh2_orderOf_map {H Y : Type*} [Group H] [Group Y] (φ : H →* Y) {Q : Subgroup H}
    (hinj : Set.InjOn φ (Q : Set H)) {a : H} (ha : a ∈ Q) : orderOf (φ a) = orderOf a := by
  refine Nat.dvd_antisymm (orderOf_map_dvd φ a) ?_
  apply orderOf_dvd_of_pow_eq_one
  have h1 : a ^ orderOf (φ a) ∈ Q := Q.pow_mem ha _
  have h2 : φ (a ^ orderOf (φ a)) = φ 1 := by rw [map_pow, pow_orderOf_eq_one, map_one]
  exact hinj h1 Q.one_mem h2

theorem szh2_pres_map {H Y : Type*} [Group H] [Group Y] (φ : H →* Y) {Q : Subgroup H} {a c y x : H}
    (hinj : Set.InjOn φ (Q : Set H)) (h : Sz32QPres Q a c y x) :
    Sz32QPres (Q.map φ) (φ a) (φ c) (φ y) (φ x) where
  a_mem := Subgroup.mem_map_of_mem φ h.a_mem
  c_mem := Subgroup.mem_map_of_mem φ h.c_mem
  y_mem := Subgroup.mem_map_of_mem φ h.y_mem
  gen := by
    conv_lhs => rw [h.gen]
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
  ord_a := by rw [szh2_orderOf_map φ hinj h.a_mem]; exact h.ord_a
  ord_c := by
    obtain ⟨m, hm, hc⟩ := h.ord_c
    exact ⟨m, hm, by rw [szh2_orderOf_map φ hinj h.c_mem]; exact hc⟩
  ac := by rw [← map_mul, ← map_mul, h.ac]
  inf := by
    rw [eq_bot_iff]
    intro z hz
    rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers] at hz
    obtain ⟨⟨u, hu, rfl⟩, ⟨v, hv, huv⟩⟩ := (show z ∈ (Subgroup.zpowers a).map φ ⊓ (Subgroup.zpowers c).map φ from hz)
    have huQ : u ∈ Q := (Subgroup.zpowers_le.mpr h.a_mem) hu
    have hvQ : v ∈ Q := (Subgroup.zpowers_le.mpr h.c_mem) hv
    have : v = u := hinj hvQ huQ huv
    have hmem : u ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c := ⟨hu, this ▸ hv⟩
    rw [h.inf, Subgroup.mem_bot] at hmem
    simp [hmem]
  y5 := by rw [← map_pow, h.y5, map_one]
  y_not := by
    intro hy
    rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, ← Subgroup.map_sup] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    have hwQ : w ∈ Q := by
      have : Subgroup.zpowers a ⊔ Subgroup.zpowers c ≤ Q :=
        sup_le (Subgroup.zpowers_le.mpr h.a_mem) (Subgroup.zpowers_le.mpr h.c_mem)
      exact this hw
    have : w = y := hinj hwQ h.y_mem hwy
    exact h.y_not (this ▸ hw)
  ya := by
    obtain ⟨n, hn, h5, h25⟩ := h.ya
    exact ⟨n, by rw [← map_inv, ← map_mul, ← map_mul, hn, map_zpow], h5, h25⟩
  yc := by
    obtain ⟨n, hn, h5⟩ := h.yc
    exact ⟨n, by rw [← map_inv, ← map_mul, ← map_mul, hn, map_zpow], h5⟩
  x_mem := by
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem φ h.x_mem
  x_ord := by
    rw [szh2_orderOf_map φ hinj ((Subgroup.zpowers_le.mpr h.c_mem) h.x_mem)]
    exact h.x_ord


theorem szh2_pres_subgroupOf {G : Type*} [Group G] {Q : Subgroup G} {a c y x : G} (M : Subgroup G)
    (hQM : Q ≤ M) (ha : a ∈ M) (hc : c ∈ M) (hy : y ∈ M) (hx : x ∈ M) (h : Sz32QPres Q a c y x) :
    Sz32QPres (Q.subgroupOf M) (⟨a, ha⟩ : M) ⟨c, hc⟩ ⟨y, hy⟩ ⟨x, hx⟩ where
  a_mem := Subgroup.mem_subgroupOf.mpr h.a_mem
  c_mem := Subgroup.mem_subgroupOf.mpr h.c_mem
  y_mem := Subgroup.mem_subgroupOf.mpr h.y_mem
  gen := by
    apply Subgroup.map_injective (f := M.subtype) Subtype.coe_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hQM, Subgroup.map_sup, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact h.gen
  ord_a := by rw [Subgroup.orderOf_mk]; exact h.ord_a
  ord_c := by
    obtain ⟨m, hm, h'⟩ := h.ord_c
    exact ⟨m, hm, by rw [Subgroup.orderOf_mk]; exact h'⟩
  ac := Subtype.ext h.ac
  inf := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := (show z ∈ Subgroup.zpowers (⟨a, ha⟩ : M) ⊓ Subgroup.zpowers (⟨c, hc⟩ : M) from hz)
    have h1 : (z : G) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c := by
      refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
      · rw [← hm]; simp
      · rw [← hn]; simp
    rw [h.inf, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  y5 := Subtype.ext (by simpa using h.y5)
  y_not := by
    intro hy'
    apply h.y_not
    have := Subgroup.mem_map_of_mem M.subtype hy'
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
    simpa using this
  ya := by
    obtain ⟨n, hn, h5, h25⟩ := h.ya
    exact ⟨n, Subtype.ext (by simpa using hn), h5, h25⟩
  yc := by
    obtain ⟨n, hn, h5⟩ := h.yc
    exact ⟨n, Subtype.ext (by simpa using hn), h5⟩
  x_mem := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.x_mem
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
  x_ord := by rw [Subgroup.orderOf_mk]; exact h.x_ord

end Transport

section Quot

theorem szh2_injOn_mk {p : ℕ} {H : Type*} [Group H] [Finite H] (hp : p.Prime) (O : Subgroup H)
    [O.Normal] (hO : p.Coprime (Nat.card O)) {A : Subgroup H} (hA : IsPGroup p A) :
    Set.InjOn (QuotientGroup.mk' O) (A : Set H) := by
  intro a ha b hb hab
  have h1 : a⁻¹ * b ∈ O := QuotientGroup.eq.mp hab
  have h2 : a⁻¹ * b ∈ A ⊓ O := ⟨A.mul_mem (A.inv_mem ha) hb, h1⟩
  rw [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hp hA hO, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2

theorem szh2_rank_quot {p : ℕ} {G : Type} [Group G] [Finite G] (hp : p.Prime) (M : Subgroup G)
    (hrank : CFSG.Open.pRank p M ≤ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p)) ≤ 3 := by
  have h1 := CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hp
    (primeComplementCore (G := ↥M) p) (primeComplementCore_coprime p) ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  exact hrank

theorem szh2_wc_mk {p : ℕ} {H : Type*} [Group H] [Finite H] [Fact p.Prime]
    (O : Subgroup H) [O.Normal] {P : Subgroup H} (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) {A : Subgroup H}
    (hA : IsPGroup p A)
    (hwc : ∀ g : H, A.map (MulAut.conj g).toMonoidHom ≤ P → A.map (MulAut.conj g).toMonoidHom = A)
    (g : H ⧸ O)
    (hg : (A.map (QuotientGroup.mk' O)).map (MulAut.conj g).toMonoidHom ≤ P.map (QuotientGroup.mk' O)) :
    (A.map (QuotientGroup.mk' O)).map (MulAut.conj g).toMonoidHom = A.map (QuotientGroup.mk' O) := by
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective O g
  set π := QuotientGroup.mk' O with hπ
  set K : Subgroup H := (P.map π).comap π with hK
  have hPK : P ≤ K := Subgroup.le_comap_map π P
  set Q : Subgroup H := A.map (MulAut.conj g₁).toMonoidHom with hQ
  have hQp : IsPGroup p Q := hA.map _
  have hQK : Q ≤ K := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hq
    have : π ((MulAut.conj g₁).toMonoidHom y) ∈
        (A.map π).map (MulAut.conj (π g₁)).toMonoidHom :=
      ⟨π y, Subgroup.mem_map_of_mem π hy, by simp⟩
    exact hg this
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p P K := hP.of_le hPK le_top
  obtain ⟨S, hS⟩ := (hQp.comap_subtype (K := K)).exists_le_sylow
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf p ((S : Subgroup K).map K.subtype) K := ⟨S, rfl⟩
  have hQS : Q ≤ (S : Subgroup K).map K.subtype := by
    intro q hq
    exact ⟨⟨q, hQK hq⟩, hS (show (⟨q, hQK hq⟩ : K) ∈ Q.comap K.subtype from hq), rfl⟩
  obtain ⟨k, hkK, hk⟩ := hPsyl.exists_mem_conj hSsyl
  obtain ⟨p₁, hp₁, hp₁k⟩ := hkK
  set r : H := k * p₁⁻¹ with hr
  have hrO : π r = 1 := by simp [hr, hp₁k]
  have h3 : ∀ y ∈ A, (r⁻¹ * g₁) * y * (r⁻¹ * g₁)⁻¹ ∈ P := by
    intro y hy
    have h1 : g₁ * y * g₁⁻¹ ∈ (S : Subgroup K).map K.subtype :=
      hQS ⟨y, hy, by simp⟩
    have h2 : k⁻¹ * (g₁ * y * g₁⁻¹) * k ∈ P := (hk _).mp h1
    have : (r⁻¹ * g₁) * y * (r⁻¹ * g₁)⁻¹ = p₁ * (k⁻¹ * (g₁ * y * g₁⁻¹) * k) * p₁⁻¹ := by
      simp only [hr]; group
    rw [this]
    exact P.mul_mem (P.mul_mem hp₁ h2) (P.inv_mem hp₁)
  have h4 := hwc (r⁻¹ * g₁) (by
    rintro _ ⟨y, hy, rfl⟩
    exact h3 y hy)
  have h6 : ∀ y ∈ A, π g₁ * π y * (π g₁)⁻¹ ∈ A.map π := by
    intro y hy
    have h5 : (r⁻¹ * g₁) * y * (r⁻¹ * g₁)⁻¹ ∈ A := by
      rw [← h4]
      exact ⟨y, hy, rfl⟩
    have := Subgroup.mem_map_of_mem π h5
    simpa [map_mul, map_inv, hrO] using this
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using h6 y hy
  · exact le_of_eq (Subgroup.card_map_of_injective
      (f := (MulAut.conj (π g₁)).toMonoidHom) (MulAut.conj (π g₁)).injective).symm

end Quot

theorem szh2_centSeries_quot {p : ℕ} {G : Type} [Group G] [Finite G] (hp : p.Prime) {M P N : Subgroup G}
    {x : G} (hxM : x ∈ M) (hx : orderOf x = p)
    (hser : CentSeries p (M ⊓ Subgroup.centralizer ({x} : Set G)) P N) :
    ∃ N' : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p),
      CentSeries p (Subgroup.centralizer
          ({QuotientGroup.mk' (primeComplementCore (G := ↥M) p) ⟨x, hxM⟩} :
            Set (↥M ⧸ primeComplementCore (G := ↥M) p)))
        ((P.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p))) N' := by
  have hao : orderOf (⟨x, hxM⟩ : ↥M) = p := by rw [Subgroup.orderOf_mk]; exact hx
  have hPM : P ≤ M := fun y hy => (hser.P_le hy).1
  have hNM : N ≤ M := fun y hy => (hser.N_le hy).1
  have himg : ∀ c : ↥M, (c : G) ∈ Subgroup.centralizer ({x} : Set G) →
      QuotientGroup.mk' (primeComplementCore (G := ↥M) p) c ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (primeComplementCore (G := ↥M) p) ⟨x, hxM⟩} :
          Set (↥M ⧸ primeComplementCore (G := ↥M) p)) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hc)
  have hlift : ∀ c ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (primeComplementCore (G := ↥M) p) ⟨x, hxM⟩} :
          Set (↥M ⧸ primeComplementCore (G := ↥M) p)),
      ∃ c₀ : ↥M, (c₀ : G) ∈ M ⊓ Subgroup.centralizer ({x} : Set G) ∧
        QuotientGroup.mk' (primeComplementCore (G := ↥M) p) c₀ = c := by
    intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := centralizer_mk_le_map hp hao hc
    refine ⟨c₀, ⟨c₀.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc₀)
  refine ⟨((N.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p))), ?_⟩
  exact {
    P_le := by
      rintro _ ⟨c, hc, rfl⟩
      exact himg c (hser.P_le (show (c : G) ∈ P from hc)).2
    N_le := by
      rintro _ ⟨c, hc, rfl⟩
      exact himg c (hser.N_le (show (c : G) ∈ N from hc)).2
    N_norm := by
      intro c hc n hn
      obtain ⟨c₀, hc₀, rfl⟩ := hlift c hc
      obtain ⟨n₀, hn₀, rfl⟩ := hn
      refine ⟨c₀ * n₀ * c₀⁻¹, ?_, by simp⟩
      exact hser.N_norm (c₀ : G) hc₀ (n₀ : G) hn₀
    PN_norm := by
      intro c hc q hq
      obtain ⟨c₀, hc₀, rfl⟩ := hlift c hc
      have hPN : (P.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)) ⊔
          (N.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)) =
          ((P ⊔ N).subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)) := by
        rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hPM hNM]
      rw [hPN] at hq ⊢
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      exact ⟨c₀ * q₀ * c₀⁻¹, hser.PN_norm (c₀ : G) hc₀ (q₀ : G) hq₀, by simp⟩
    N_cop := by
      rintro _ ⟨n₀, hn₀, rfl⟩
      have h1 : orderOf (QuotientGroup.mk' (primeComplementCore (G := ↥M) p) n₀) ∣
          orderOf (n₀ : G) := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_map_dvd _ n₀
      exact Nat.Coprime.coprime_dvd_right h1 (hser.N_cop (n₀ : G) hn₀) }




section DataY

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem szh2_isSylowOf_top_subgroupOf {p : ℕ} [Fact p.Prime] (P : Sylow p G) {M : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G).subgroupOf M) (⊤ : Subgroup M) := by
  obtain ⟨T, hT⟩ := szh2_sylow_subgroupOf P hPM
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right, ← hT]
  exact ⟨le_top, T.isPGroup', T.not_dvd_index⟩

theorem szh2_injOn_P {O : Subgroup ↥M} [O.Normal] (hO : Nat.Coprime 5 (Nat.card O)) :
    Set.InjOn (QuotientGroup.mk' O) (((P : Subgroup G).subgroupOf M : Subgroup ↥M) : Set ↥M) :=
  szh2_injOn_mk (by norm_num) O hO P.isPGroup'.comap_subtype

theorem szh2_pres_Y {O : Subgroup ↥M} [O.Normal] (hO : Nat.Coprime 5 (Nat.card O)) {a c y : G}
    (hP : Sz32Struct P x J a c y) (hPM : (P : Subgroup G) ≤ M) (ha : a ∈ M) (hcM : c ∈ M) (hyM : y ∈ M) :
    Sz32QPres (((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' O)) (QuotientGroup.mk' O ⟨a, ha⟩)
      (QuotientGroup.mk' O ⟨c, hcM⟩) (QuotientGroup.mk' O ⟨y, hyM⟩) (QuotientGroup.mk' O ⟨c, hcM⟩ ^ 5) := by
  have hpres := hP.pres_P
  have hco : orderOf c = 25 := hP.facts.ord_c
  have hc5 : orderOf (c ^ 5) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hco]; norm_num), hco]
  have hpres5 : Sz32QPres (P : Subgroup G) a c y (c ^ 5) :=
    { hpres with
      x_mem := Subgroup.pow_mem _ (Subgroup.mem_zpowers c) 5
      x_ord := hc5 }
  have hpresM := szh2_pres_subgroupOf M hPM ha hcM hyM (M.pow_mem hcM 5) hpres5
  have hY := szh2_pres_map (QuotientGroup.mk' O) (szh2_injOn_P hO) hpresM
  have hx5 : (⟨c ^ 5, M.pow_mem hcM 5⟩ : M) = (⟨c, hcM⟩ : M) ^ 5 := Subtype.ext (by simp)
  rwa [hx5, map_pow] at hY


theorem szh2_zpowers_eq_of_val {M : Subgroup G} (u v : ↥M)
    (h : Subgroup.zpowers (u : G) = Subgroup.zpowers (v : G)) :
    Subgroup.zpowers u = Subgroup.zpowers v := by
  apply Subgroup.map_injective (f := M.subtype) Subtype.coe_injective
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  exact h

theorem szh2_swap_Y {O : Subgroup ↥M} [O.Normal] {a c y : G}
    (hP : Sz32Struct P x J a c y) (hL : Sz32Lines P x (a ^ 5))
    (hNM : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M)
    (ha : a ∈ M) (hcM : c ∈ M) :
    ∃ g ∈ Subgroup.normalizer ((((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' O) : Subgroup _) :
        Set (↥M ⧸ O)),
      (Subgroup.zpowers (QuotientGroup.mk' O ⟨c, hcM⟩ ^ 5)).map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers (QuotientGroup.mk' O ⟨a, ha⟩ ^ 5) := by
  obtain ⟨g, hgN, hgswap⟩ := hL.swap
  have hgM : g ∈ M := hNM hgN
  refine ⟨QuotientGroup.mk' O ⟨g, hgM⟩, ?_, ?_⟩
  · have h1 : (⟨g, hgM⟩ : ↥M) ∈ Subgroup.normalizer
        ((((P : Subgroup G).subgroupOf M : Subgroup ↥M)) : Set ↥M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have := Subgroup.mem_normalizer_iff.mp hgN (h : G)
      show (h : G) ∈ (P : Subgroup G) ↔ g * (h : G) * g⁻¹ ∈ (P : Subgroup G)
      exact this
    exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ h1)
  ·
    have hG : Subgroup.zpowers (g * c ^ 5 * g⁻¹) = Subgroup.zpowers (a ^ 5) := by
      have := hgswap
      rw [hP.facts.x_eq, MonoidHom.map_zpowers] at this
      simpa [MulAut.conj_apply] using this
    have hM' : Subgroup.zpowers ((⟨g, hgM⟩ : ↥M) * ⟨c ^ 5, M.pow_mem hcM 5⟩ * (⟨g, hgM⟩ : ↥M)⁻¹) =
        Subgroup.zpowers (⟨a ^ 5, M.pow_mem ha 5⟩ : ↥M) :=
      szh2_zpowers_eq_of_val _ _ hG
    have hY := congrArg (Subgroup.map (QuotientGroup.mk' O)) hM'
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hY
    have e1 : (⟨c ^ 5, M.pow_mem hcM 5⟩ : M) = (⟨c, hcM⟩ : M) ^ 5 := Subtype.ext (by simp)
    have e2 : (⟨a ^ 5, M.pow_mem ha 5⟩ : M) = (⟨a, ha⟩ : M) ^ 5 := Subtype.ext (by simp)
    rw [e1, e2, map_mul, map_mul, map_inv, map_pow, map_pow] at hY
    rw [MonoidHom.map_zpowers]
    exact hY


theorem szh2_Z_eq {a c y : G} (hP : Sz32Struct P x J a c y) :
    (Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x : Subgroup G) = sz32Z a c := by
  unfold sz32Z
  rw [hP.facts.x_eq]

theorem szh2_Z_le_P {a c y : G} (hP : Sz32Struct P x J a c y) : sz32Z a c ≤ (P : Subgroup G) := by
  have hpres := hP.pres_P
  exact sup_le (Subgroup.zpowers_le.mpr ((P : Subgroup G).pow_mem hpres.a_mem 5))
    (Subgroup.zpowers_le.mpr ((P : Subgroup G).pow_mem hpres.c_mem 5))

theorem szh2_Z_subgroupOf {M : Subgroup G} {a c : G} (hZM : sz32Z a c ≤ M) (ha : a ∈ M) (hcM : c ∈ M) :
    (sz32Z a c).subgroupOf M =
      sz32Z (⟨a, ha⟩ : ↥M) (⟨c, hcM⟩ : ↥M) := by
  apply Subgroup.map_injective (f := M.subtype) Subtype.coe_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hZM]
  unfold sz32Z
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

theorem szh2_wc_Y {O : Subgroup ↥M} [O.Normal] (hO : Nat.Coprime 5 (Nat.card O)) {a c y : G}
    (hP : Sz32Struct P x J a c y) (hZ : Sz32ZFacts P M x (a ^ 5)) (hPM : (P : Subgroup G) ≤ M)
    (ha : a ∈ M) (hcM : c ∈ M) :
    ∀ g : ↥M ⧸ O,
      (sz32Z (QuotientGroup.mk' O ⟨a, ha⟩) (QuotientGroup.mk' O ⟨c, hcM⟩)).map
          (MulAut.conj g).toMonoidHom ≤ ((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' O) →
        (sz32Z (QuotientGroup.mk' O ⟨a, ha⟩) (QuotientGroup.mk' O ⟨c, hcM⟩)).map
          (MulAut.conj g).toMonoidHom =
        sz32Z (QuotientGroup.mk' O ⟨a, ha⟩) (QuotientGroup.mk' O ⟨c, hcM⟩) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hZP := szh2_Z_le_P hP
  have hZM : sz32Z a c ≤ M := hZP.trans hPM
  have hZY : ((sz32Z a c).subgroupOf M).map (QuotientGroup.mk' O) =
      sz32Z (QuotientGroup.mk' O ⟨a, ha⟩) (QuotientGroup.mk' O ⟨c, hcM⟩) := by
    rw [szh2_Z_subgroupOf hZM ha hcM]
    unfold sz32Z
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← map_pow, ← map_pow]
  have hZ' : IsPGroup 5 ((sz32Z a c).subgroupOf M) :=
    (P.isPGroup'.to_le hZP).comap_subtype
  have hZwc := hZ.Z_wc
  rw [szh2_Z_eq hP] at hZwc
  have hwcM : ∀ g : ↥M, ((sz32Z a c).subgroupOf M).map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G).subgroupOf M →
      ((sz32Z a c).subgroupOf M).map (MulAut.conj g).toMonoidHom = (sz32Z a c).subgroupOf M := by
    intro g hle
    have hleG : (sz32Z a c).map (MulAut.conj (g : G)).toMonoidHom ≤ (P : Subgroup G) := by
      rintro _ ⟨t, ht, rfl⟩
      have htM : t ∈ M := hZM ht
      have h1 : (⟨t, htM⟩ : ↥M) ∈ (sz32Z a c).subgroupOf M := ht
      have h2 := hle ⟨_, h1, rfl⟩
      exact h2
    have heq := hZwc (g : G) hleG
    have hle2 : ((sz32Z a c).subgroupOf M).map (MulAut.conj g).toMonoidHom ≤ (sz32Z a c).subgroupOf M := by
      rintro _ ⟨z, hz, rfl⟩
      have h1 : (MulAut.conj (g : G)).toMonoidHom (z : G) ∈ sz32Z a c := by
        rw [← heq]
        exact ⟨(z : G), hz, rfl⟩
      exact h1
    exact Subgroup.eq_of_le_of_card_ge hle2
      (le_of_eq (Subgroup.card_map_of_injective
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).symm)
  intro g hg
  rw [← hZY] at hg ⊢
  exact szh2_wc_mk O (szh2_isSylowOf_top_subgroupOf P hPM) hZ' hwcM g hg


theorem szh2_irr_Y {O : Subgroup ↥M} [O.Normal] {a c y : G}
    (hP : Sz32Struct P x J a c y) (hZ : Sz32ZFacts P M x (a ^ 5)) (hPM : (P : Subgroup G) ≤ M)
    (ha : a ∈ M) (hcM : c ∈ M) :
    ∀ L : Subgroup (↥M ⧸ O),
      L ≤ sz32Z (QuotientGroup.mk' O ⟨a, ha⟩) (QuotientGroup.mk' O ⟨c, hcM⟩) →
      Subgroup.normalizer ((sz32Z (QuotientGroup.mk' O ⟨a, ha⟩) (QuotientGroup.mk' O ⟨c, hcM⟩) :
          Subgroup (↥M ⧸ O)) : Set (↥M ⧸ O)) ≤ Subgroup.normalizer (L : Set (↥M ⧸ O)) →
        L = ⊥ ∨ L = sz32Z (QuotientGroup.mk' O ⟨a, ha⟩) (QuotientGroup.mk' O ⟨c, hcM⟩) := by
  intro L hL hnorm
  have hZP := szh2_Z_le_P hP
  have hZM : sz32Z a c ≤ M := hZP.trans hPM
  have hZY : ((sz32Z a c).subgroupOf M).map (QuotientGroup.mk' O) =
      sz32Z (QuotientGroup.mk' O ⟨a, ha⟩) (QuotientGroup.mk' O ⟨c, hcM⟩) := by
    rw [szh2_Z_subgroupOf hZM ha hcM]
    unfold sz32Z
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← map_pow, ← map_pow]
  have hZirr := hZ.Z_irr
  have hNZ := hZ.NZ_le
  rw [szh2_Z_eq hP] at hZirr hNZ
  set Z' : Subgroup ↥M := (sz32Z a c).subgroupOf M with hZ'
  rw [← hZY] at hL hnorm ⊢
  set L' : Subgroup ↥M := L.comap (QuotientGroup.mk' O) ⊓ Z' with hL'
  set L₀ : Subgroup G := L'.map M.subtype with hL₀
  have hL₀le : L₀ ≤ sz32Z a c := by
    rintro _ ⟨u, hu, rfl⟩
    exact hu.2
  have hkey : ∀ h : ↥M, h ∈ Subgroup.normalizer (Z' : Set ↥M) →
      QuotientGroup.mk' O h ∈ Subgroup.normalizer (L : Set (↥M ⧸ O)) →
      ∀ u : ↥M, u ∈ L' → h * u * h⁻¹ ∈ L' := by
    intro h hZh hLh u hu
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hZh u).mp hu.2⟩
    show QuotientGroup.mk' O (h * u * h⁻¹) ∈ L
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hLh (QuotientGroup.mk' O u)).mp hu.1
  have hnormG : Subgroup.normalizer ((sz32Z a c : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L₀ : Set G) := by
    intro g hg
    have hgM : g ∈ M := hNZ hg
    have hgZ : (⟨g, hgM⟩ : ↥M) ∈ Subgroup.normalizer (Z' : Set ↥M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have := Subgroup.mem_normalizer_iff.mp hg (u : G)
      show (u : G) ∈ sz32Z a c ↔ g * (u : G) * g⁻¹ ∈ sz32Z a c
      exact this
    have hgL : QuotientGroup.mk' O ⟨g, hgM⟩ ∈ Subgroup.normalizer (L : Set (↥M ⧸ O)) := by
      apply hnorm
      exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hgZ)
    have hgZ' : (⟨g, hgM⟩ : ↥M)⁻¹ ∈ Subgroup.normalizer (Z' : Set ↥M) := Subgroup.inv_mem _ hgZ
    have hgL' : QuotientGroup.mk' O (⟨g, hgM⟩ : ↥M)⁻¹ ∈ Subgroup.normalizer (L : Set (↥M ⧸ O)) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hgL
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hkey _ hgZ hgL u hu, rfl⟩
    · rintro ⟨u', hu', hu'e⟩
      refine ⟨_, hkey _ hgZ' hgL' u' hu', ?_⟩
      have h1 : (u' : G) = g * t * g⁻¹ := hu'e
      have e1 : ((⟨g, hgM⟩ : ↥M)⁻¹ * u' * (⟨g, hgM⟩ : ↥M)⁻¹⁻¹ : ↥M).val = g⁻¹ * (u' : G) * g := by
        simp
      show ((⟨g, hgM⟩ : ↥M)⁻¹ * u' * (⟨g, hgM⟩ : ↥M)⁻¹⁻¹ : ↥M).val = t
      rw [e1, h1]; group
  rcases hZirr L₀ hL₀le hnormG with h0 | h1
  · left
    rw [eq_bot_iff]
    intro l hl
    obtain ⟨z, hz, rfl⟩ := hL hl
    have hzL' : z ∈ L' := ⟨hl, hz⟩
    have : (z : G) ∈ L₀ := ⟨z, hzL', rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    have hz1 : z = 1 := Subtype.ext this
    rw [Subgroup.mem_bot, hz1, map_one]
  · right
    refine le_antisymm hL ?_
    rintro _ ⟨z, hz, rfl⟩
    have : (z : G) ∈ L₀ := by
      rw [h1]
      exact hz
    obtain ⟨u, hu, hue⟩ := this
    have huz : u = z := Subtype.ext hue
    rw [← huz]
    exact hu.1


theorem szh2_perf_Y (hS : Setting G) (hU0 : FullCoreLocal G) (hc : PointConfig IsSz32Type G 5 P M x J) :
    ∀ N : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) 5), N.Normal → (∃ k : ℕ, N.index = 5 ^ k) →
      N = ⊤ := by
  intro N hN ⟨k, hk⟩
  have hsurj := QuotientGroup.mk'_surjective (primeComplementCore (G := ↥M) 5)
  set N' : Subgroup ↥M := N.comap (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) with hN'
  haveI : N'.Normal := hN.comap _
  have hidx : N'.index = N.index := Subgroup.index_comap_of_surjective N hsurj
  set N₁ : Subgroup G := N'.map M.subtype with hN₁
  have hN₁M : N₁ ≤ M := Subgroup.map_subtype_le N'
  have hN₁sub : N₁.subgroupOf M = N' :=
    Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective N'
  have h := sz32_shared_oP_eq_self hS hU0 hc.sigma hc.core N₁ hN₁M (by rw [hN₁sub]; infer_instance)
    ⟨k, by rw [Subgroup.relIndex, hN₁sub, hidx, hk]⟩
  have hN'top : N' = ⊤ := by
    rw [← hN₁sub, h, Subgroup.subgroupOf_self]
  have h2 : N.comap (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) = ⊤ := hN'top
  rw [← Subgroup.map_comap_eq_self_of_surjective hsurj N, h2, Subgroup.map_top_of_surjective _ hsurj]


theorem szh2_series_Y {a c y : G} (hP : Sz32Struct P x J a c y) {N : Subgroup G}
    (hser : CentSeries 5 (M ⊓ Subgroup.centralizer ({x} : Set G)) (P : Subgroup G) N) (hcM : c ∈ M) :
    ∃ N' : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) 5),
      CentSeries 5 (Subgroup.centralizer
          ({QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) ⟨c, hcM⟩ ^ 5} :
            Set (↥M ⧸ primeComplementCore (G := ↥M) 5)))
        (((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5))) N' := by
  have hco : orderOf c = 25 := hP.facts.ord_c
  have hc5 : orderOf (c ^ 5) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hco]; norm_num), hco]
  have hCeq : Subgroup.centralizer ({c ^ 5} : Set G) = Subgroup.centralizer ({x} : Set G) := by
    have h1 := congrArg (fun H : Subgroup G => Subgroup.centralizer (H : Set G)) hP.facts.x_eq
    simp only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h1
    exact h1.symm
  have hser' : CentSeries 5 (M ⊓ Subgroup.centralizer ({c ^ 5} : Set G)) (P : Subgroup G) N := by
    rw [hCeq]; exact hser
  obtain ⟨N', hN'⟩ := szh2_centSeries_quot (by norm_num) (M.pow_mem hcM 5) hc5 hser'
  refine ⟨N', ?_⟩
  have hx5 : (⟨c ^ 5, M.pow_mem hcM 5⟩ : M) = (⟨c, hcM⟩ : M) ^ 5 := Subtype.ext (by simp)
  rwa [hx5, map_pow] at hN'

end DataY

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
