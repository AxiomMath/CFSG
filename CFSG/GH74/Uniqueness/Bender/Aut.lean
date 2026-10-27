module

public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

theorem BenderType.lemma_3_6_a
    {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) (Q : Sylow 2 K) (σ : MulAut K)
    (hσ : ∀ x ∈ (Q : Subgroup K), σ x = x) :
    ∃ r ∈ rootCenter (Q : Subgroup K), ∀ k : K, σ k = r * k * r⁻¹ := by
  have hB : CFSG.BenderSuzuki.IsBenderGroup K := isBenderGroup_iff_exists_benderType.mpr ⟨n, i, e, h⟩
  obtain ⟨r, hr, hσr⟩ := (CFSG.ProperTwoGeneratedCore.TheoremC.benderBorelFactsHold K hB Q).aut_inner σ hσ
  refine ⟨r, mem_rootCenter_iff.mpr ⟨hr, fun p hp => ?_⟩, hσr⟩
  have h1 := hσ p hp
  rw [hσr p] at h1
  calc p * r = r * p * r⁻¹ * r := by rw [h1]
    _ = r * p := by group

theorem odd_index_conj_range_of_mulEquiv {K G : Type*} [Group K] [Group G] (e : K ≃* G)
    (hodd : Odd (MulAut.conj : G →* MulAut G).range.index) :
    Odd (MulAut.conj : K →* MulAut K).range.index := by
  let φ : MulAut K ≃* MulAut G := MulAut.congr e
  have hmap : (MulAut.conj : K →* MulAut K).range.map φ.toMonoidHom =
      (MulAut.conj : G →* MulAut G).range := by
    ext x
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      refine ⟨e k, ?_⟩
      ext g
      simp [φ, MulAut.congr_apply, MulAut.conj_apply]
    · rintro ⟨g, rfl⟩
      refine ⟨φ.symm (MulAut.conj g), ⟨e.symm g, ?_⟩, by simp⟩
      apply φ.injective
      ext g'
      simp [φ, MulAut.congr_apply, MulAut.conj_apply]
  rw [← Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective, hmap]
  exact hodd

theorem BenderType.lemma_3_1_b_suzuki
    {K : Type} [Group K] {n e : ℕ} (h : BenderType K n 2 e) :
    Odd (MulAut.conj : K →* MulAut K).range.index := by
  cases h with
  | suzuki a ha e' =>
    have hodd := CFSG.ProperTwoGeneratedCore.HighRankPair.suzukiOuterOdd a ha
    exact odd_index_conj_range_of_mulEquiv
      (e'.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a)))
      hodd

section Consequences

theorem BenderType.center_eq_bot {K : Type*} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) : center K = ⊥ := by
  have := h.isSimple
  have hnc := h.isSimpleBenderGroup.not_commutative
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with hbot | htop
  · exact hbot
  · exfalso
    apply hnc
    intro x y
    have : x ∈ center K := by rw [htop]; trivial
    exact (Subgroup.mem_center_iff.mp this y).symm

theorem BenderType.centralizer_sylow_eq
    {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) (Q : Sylow 2 K) :
    centralizer ((Q : Subgroup K) : Set K) = rootCenter (Q : Subgroup K) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := h.lemma_3_6_a Q (MulAut.conj x) (fun p hp => by
      have := (Subgroup.mem_centralizer_iff.mp hx) p hp
      simp [MulAut.conj_apply, ← this])
    have hcentral : r⁻¹ * x ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      have h0 : x * k * x⁻¹ = r * k * r⁻¹ := by simpa [MulAut.conj_apply] using hxr k
      have h1 : x * k = r * k * r⁻¹ * x := by
        calc x * k = (x * k * x⁻¹) * x := by group
          _ = r * k * r⁻¹ * x := by rw [h0]
      calc k * (r⁻¹ * x) = r⁻¹ * (r * k * r⁻¹ * x) := by group
        _ = r⁻¹ * (x * k) := by rw [h1]
        _ = r⁻¹ * x * k := by group
    rw [h.center_eq_bot, Subgroup.mem_bot] at hcentral
    have hxr' : x = r := by
      calc x = r * (r⁻¹ * x) := by group
        _ = r := by rw [hcentral, mul_one]
    rw [hxr']
    exact hr
  · intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun p hp => (mem_rootCenter_iff.mp hx).2 p hp

theorem normal_range_conj (K : Type*) [Group K] :
    ((MulAut.conj : K →* MulAut K).range).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨v, rfl⟩ g
  refine ⟨g v, ?_⟩
  ext k
  simp [MulAut.conj_apply]

theorem BenderType.exists_inner_of_sq_eq_one_suzuki
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 2 e) (σ : MulAut K) (hσ : σ * σ = 1) :
    ∃ v : K, v * v = 1 ∧ ∀ k, σ k = v * k * v⁻¹ := by
  have hodd := h.lemma_3_1_b_suzuki
  have := normal_range_conj K
  set R : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range with hR
  have hord : orderOf (QuotientGroup.mk σ : MulAut K ⧸ R) = 1 := by
    have h2 : orderOf (QuotientGroup.mk σ : MulAut K ⧸ R) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [sq, ← QuotientGroup.mk_mul, hσ]
      exact QuotientGroup.mk_one R
    have hN : orderOf (QuotientGroup.mk σ : MulAut K ⧸ R) ∣ Nat.card (MulAut K ⧸ R) :=
      orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hN
      have hodd' : Odd (Nat.card (MulAut K ⧸ R)) := by
        rw [← Subgroup.index]
        exact hodd
      exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr hN)
  have hσR : σ ∈ R := by
    rw [orderOf_eq_one_iff] at hord
    exact (QuotientGroup.eq_one_iff σ).mp hord
  obtain ⟨v, hv⟩ := hσR
  refine ⟨v, ?_, fun k => by rw [← hv]; simp [MulAut.conj_apply]⟩
  have hvv : MulAut.conj (v * v) = 1 := by rw [map_mul, hv, hσ]
  have hcen : v * v ∈ center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    have := congrArg (fun a : MulAut K => a k) hvv
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc k * (v * v) = (v * v * k * (v * v)⁻¹) * (v * v) := by rw [this]
      _ = v * v * k := by group
  rw [h.center_eq_bot, Subgroup.mem_bot] at hcen
  exact hcen

theorem BenderType.aut_eq_conj_cartan_linear
    {K : Type} [Group K] [Finite K] {n : ℕ}
    (h : BenderType K n 1 1) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hσD : ∀ d ∈ cartan (Q : Subgroup K) t, σ d = d) :
    ∃ d₀ ∈ cartan (Q : Subgroup K) t, ∀ k, σ k = d₀ * k * d₀⁻¹ := by
  have hc := h.benderCore Q ht htQ
  obtain ⟨z₀, hz₀, hz₀1⟩ := hc.exists_involution
  have hσz₀ : σ z₀ ∈ rootCenter (Q : Subgroup K) ∧ σ z₀ ≠ 1 := by
    refine ⟨hc.mem_rootCenter_of_mul_self (hσQ z₀ (rootCenter_le _ hz₀)) ?_, ?_⟩
    · rw [← map_mul, hc.center_sq z₀ hz₀, map_one]
    · intro h1
      apply hz₀1
      apply σ.injective
      rw [h1, map_one]
  obtain ⟨d, hd, hdσ⟩ := hc.exists_cartan_conj hz₀ hz₀1 hσz₀.1 hσz₀.2
  have hZ : ∀ z ∈ rootCenter (Q : Subgroup K), σ z = d⁻¹ * z * d := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; simp
    · obtain ⟨e, he, hez⟩ := hc.exists_cartan_conj hz₀ hz₀1 hz hz1
      have hσe : σ e = e := hσD e he
      have hσe' : σ e⁻¹ = e⁻¹ := hσD e⁻¹ ((cartan _ t).inv_mem he)
      have hcomm : d⁻¹ * e = e * d⁻¹ :=
        hc.cartan_comm ((cartan _ t).inv_mem hd) he
      calc σ z = σ (e⁻¹ * z₀ * e) := by rw [hez]
        _ = e⁻¹ * σ z₀ * e := by rw [map_mul, map_mul, hσe, hσe']
        _ = e⁻¹ * (d⁻¹ * z₀ * d) * e := by rw [hdσ]
        _ = d⁻¹ * (e⁻¹ * z₀ * e) * d := by
          have hc2 : e⁻¹ * d⁻¹ = d⁻¹ * e⁻¹ := by
            have := hc.cartan_comm ((cartan _ t).inv_mem he) ((cartan _ t).inv_mem hd)
            exact this
          have hc3 : d * e = e * d := hc.cartan_comm hd he
          calc e⁻¹ * (d⁻¹ * z₀ * d) * e = (e⁻¹ * d⁻¹) * z₀ * (d * e) := by group
            _ = (d⁻¹ * e⁻¹) * z₀ * (e * d) := by rw [hc2, hc3]
            _ = d⁻¹ * (e⁻¹ * z₀ * e) * d := by group
        _ = d⁻¹ * z * d := by rw [hez]
  have hQZ : rootCenter (Q : Subgroup K) = (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
      (by rw [hc.card_eq, hc.card_center, pow_one])
  set σ'' : MulAut K := MulAut.conj d * σ with hσ''
  have hσ''app : ∀ k, σ'' k = d * σ k * d⁻¹ := fun k => by
    simp [hσ'', MulAut.conj_apply]
  have hcen : ∀ x ∈ (Q : Subgroup K), σ'' x = x := by
    intro x hx
    have hxZ : x ∈ rootCenter (Q : Subgroup K) := by rw [hQZ]; exact hx
    rw [hσ''app, hZ x hxZ]
    group
  obtain ⟨r, hr, hσr⟩ := h.lemma_3_6_a Q σ'' hcen
  have hr1 : r = 1 := by
    by_contra hr1
    have hDle : cartan (Q : Subgroup K) t ≤ centralizer ({r} : Set K) := by
      intro d' hd'
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      have h1 : σ'' d' = d' := by
        rw [hσ''app, hσD d' hd']
        have := hc.cartan_comm hd hd'
        calc d * d' * d⁻¹ = d' * d * d⁻¹ := by rw [this]
          _ = d' := by group
      have h2 := hσr d'
      rw [h1] at h2
      calc a * d' = (a * d' * a⁻¹) * a := by group
        _ = d' * a := by rw [← h2]
    have hbot : cartan (Q : Subgroup K) t = ⊥ := by
      have := hc.cartan_inf_centralizer_eq hr hr1
      rw [hc.fixCartan_eq_bot, inf_eq_left.mpr hDle] at this
      exact this
    have hcard := hc.card_cartan
    rw [hbot, Subgroup.card_bot] at hcard
    have hn2 := h.two_le.2
    have hq4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  refine ⟨d⁻¹, (cartan _ t).inv_mem hd, fun k => ?_⟩
  calc σ k = d⁻¹ * (d * σ k * d⁻¹) * d := by group
    _ = d⁻¹ * k * d := by rw [← hσ''app k, hσr k, hr1]; group
    _ = d⁻¹ * k * d⁻¹⁻¹ := by rw [inv_inv]

end Consequences

end CFSG.GH74.Uniqueness.Bender
