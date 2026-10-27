module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16R7
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RN
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYL3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem EB_index_le : (actOn E (L ⊓ centralizer ({t} : Set G))
    c.hyp.wFacts.cent_le_normalizer).range.index ≤ 2 := by
  set A := (actOn E (L ⊓ centralizer ({t} : Set G)) c.hyp.wFacts.cent_le_normalizer).range with hA
  have h960 : 960 ≤ Nat.card ↥A := c.hyp.wFacts.le_card_range_cent c.hyp.outerE.t_order
  have h1 := Subgroup.card_mul_index A
  rw [c.hyp.autE] at h1
  have hpos : 0 < A.index := Nat.pos_of_ne_zero (by
    intro h
    rw [h] at h1
    omega)
  by_contra hgt
  push_neg at hgt
  have : 960 * 3 ≤ Nat.card ↥A * A.index := Nat.mul_le_mul h960 hgt
  omega

theorem EB_orbit_two (hE69 : EFacts69 E t) {x y : G} (hx : x ∈ E) (hy : y ∈ E)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxt : x ≠ t) (hy2 : y * y = 1) (hy1 : y ≠ 1) (hyt : y ≠ t) :
    ∃ g ∈ L ⊓ centralizer ({t} : Set G), g * x * g⁻¹ = y := by
  obtain ⟨φ, ⟨g, hg⟩, hφ⟩ := hE69.orbit_two _ c.EB_index_le ⟨x, hx⟩ ⟨y, hy⟩ hx2 hx1 hxt hy2 hy1 hyt
  refine ⟨g, g.2, ?_⟩
  have := congrArg Subtype.val hφ
  rw [← hg] at this
  simpa [actOn_apply] using this

theorem EB_orbit_four (hE69 : EFacts69 E t) {x y : G} (hx : x ∈ E) (hy : y ∈ E)
    (hx2 : x * x = t) (hy2 : y * y = t) :
    ∃ g ∈ L ⊓ centralizer ({t} : Set G), g * x * g⁻¹ = y := by
  obtain ⟨φ, ⟨g, hg⟩, hφ⟩ := hE69.orbit_four _ c.EB_index_le ⟨x, hx⟩ ⟨y, hy⟩ hx2 hy2
  refine ⟨g, g.2, ?_⟩
  have := congrArg Subtype.val hφ
  rw [← hg] at this
  simpa [actOn_apply] using this

theorem conj_z_form {s : G} (hS : S16Gen S s z t) :
    ∀ s' ∈ S, ∃ k : ℕ, s' * z * s'⁻¹ = s ^ (2 * k) * z := by
  intro s' hs'
  obtain ⟨i, j, rfl⟩ := hS.hgen s' hs'
  have hconjz : ∀ k : ℕ, s ^ k * z * (s ^ k)⁻¹ = s ^ (2 * k) * z := by
    intro k
    have h1 : (s ^ k)⁻¹ = s ^ (7 * k) := by
      rw [← inv_pow, inv_s_eq_pow hS.hs8, ← pow_mul, mul_comm]
    have h2 : z * s ^ (7 * k) = s ^ (7 * (7 * k)) * z := z_mul_pow_s hS.hz2 hS.hzs hS.hs8 _
    calc s ^ k * z * (s ^ k)⁻¹ = s ^ k * (z * s ^ (7 * k)) := by rw [h1]; group
      _ = s ^ k * (s ^ (7 * (7 * k)) * z) := by rw [h2]
      _ = s ^ (k + 7 * (7 * k)) * z := by rw [← mul_assoc, ← pow_add]
      _ = s ^ (2 * k) * z := by
        have : k + 7 * (7 * k) = 2 * k + 8 * (6 * k) := by ring
        rw [this, pow_add, pow_mul s 8 (6 * k), hS.hs8, one_pow, mul_one]
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [z_pow_two_mul hS.hz2 r, mul_one]
    exact ⟨i, hconjz i⟩
  · rw [z_pow_two_mul_add_one hS.hz2 r]
    refine ⟨i, ?_⟩
    calc s ^ i * z * z * (s ^ i * z)⁻¹ = s ^ i * z * (s ^ i)⁻¹ := by group
      _ = s ^ (2 * i) * z := hconjz i

theorem involutions_W_conj (hE69 : EFacts69 E t) {s σ v ξ : G} (hS : S16Gen S s z t)
    (hD : S16LData G L z t β E σ v ξ) {K0 : Subgroup G}
    (hcls : ∀ k ∈ centralizer ({β} : Set G), k * k = 1 → k ≠ 1 →
      (k ∈ K0 → ∃ g : G, g * t * g⁻¹ = k) ∧ (k ∉ K0 → ∃ g : G, g * z * g⁻¹ = k)) :
    ∀ w ∈ Dsub s z ⊔ E, w * w = 1 → w ≠ 1 → ∃ g : G, g * t * g⁻¹ = w := by
  classical
  have hcfg := c.hyp.outerE.cfg
  have ht2 := hcfg.t_sq
  have ht1 := hcfg.t_ne
  have hELL : E ≤ L := c.hyp.wFacts.E_le
  have hDS : Dsub s z ≤ S := Dsub_le hS.hs hS.hzS
  have htD : t ∈ Dsub s z := t_mem_Dsub hS.hs4
  have hβB : β ∈ B := c.hyp.outerB.beta_mem
  have hβS : ∀ y ∈ S, y ∈ centralizer ({β} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.2 (c.BS β hβB y hy).symm
  have htβ : t ∈ centralizer ({β} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (c.hyp.outerB.B_cent hβB)).symm
  have hLK0 : ∀ k ∈ L, k ∈ centralizer ({β} : Set G) → k * k = 1 → k ≠ 1 → k ∈ K0 := by
    intro k hkL hkβ hk2 hk1
    by_contra hk
    obtain ⟨g, hg⟩ := (hcls k hkβ hk2 hk1).2 hk
    exact c.hyp.z_not_L g (hg ▸ hkL)
  have hvvE : v * v ∈ E := by
    have : v * v ∈ closure ({v * v, v * ξ} : Set G) := subset_closure (by simp)
    rw [hD.CE_eq] at this
    exact this.1
  have hvξE : v * ξ ∈ E := by
    have : v * ξ ∈ closure ({v * v, v * ξ} : Set G) := subset_closure (by simp)
    rw [hD.CE_eq] at this
    exact this.1
  have hvβ' : v * β⁻¹ * v⁻¹ = β := by
    calc v * β⁻¹ * v⁻¹ = (v * β * v⁻¹)⁻¹ := by group
      _ = β := by rw [hD.v_β, inv_inv]
  have hξinv : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right hD.ξ_sq
  have hξv' : ξ * v * ξ = v⁻¹ := by rw [← hξinv] at hD; simpa [hξinv] using hD.ξ_v
  have hvvβ : v * v ∈ centralizer ({β} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc v * v * β = (v * β⁻¹ * v⁻¹) * (v * v) * 1 := by
          calc v * v * β = v * (v * β * v⁻¹) * v := by group
            _ = v * β⁻¹ * v := by rw [hD.v_β]
            _ = (v * β⁻¹ * v⁻¹) * (v * v) * 1 := by group
      _ = β * (v * v) := by rw [hvβ']; group
  have hvξβ : v * ξ ∈ centralizer ({β} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : v * ξ * β * (v * ξ)⁻¹ = β := by
      calc v * ξ * β * (v * ξ)⁻¹ = v * (ξ * β * ξ⁻¹) * v⁻¹ := by group
        _ = v * β⁻¹ * v⁻¹ := by rw [hD.ξ_β]
        _ = β := hvβ'
    calc v * ξ * β = (v * ξ * β * (v * ξ)⁻¹) * (v * ξ) := by group
      _ = β * (v * ξ) := by rw [h1]
  have hvξ2 : (v * ξ) * (v * ξ) = 1 := by
    calc v * ξ * (v * ξ) = v * (ξ * v * ξ) := by group
      _ = 1 := by rw [hξv']; group
  have hv4' : v * v * (v * v) = t := by
    rw [← hD.v4, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  have hv2ne : v * v ≠ 1 := by
    intro h
    have : t = 1 := by rw [← hv4', h, one_mul]
    exact ht1 this
  have hvξne1 : v * ξ ≠ 1 := by
    intro h
    have hξ : ξ = v⁻¹ := by
      calc ξ = v⁻¹ * (v * ξ) := by group
        _ = v⁻¹ := by rw [h, mul_one]
    have h2 := hD.ξ_sq
    rw [hξ] at h2
    apply hv2ne
    calc v * v = (v⁻¹ * v⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      _ = 1 := by rw [h2, inv_one]
  have hvξnet : v * ξ ≠ t := by
    intro h
    have hξ : ξ = v⁻¹ * t := by
      calc ξ = v⁻¹ * (v * ξ) := by group
        _ = v⁻¹ * t := by rw [h]
    have hvt' : v⁻¹ * t = t * v⁻¹ := by
      calc v⁻¹ * t = v⁻¹ * (t * v) * v⁻¹ := by group
        _ = v⁻¹ * (v * t) * v⁻¹ := by rw [hD.v_t]
        _ = t * v⁻¹ := by group
    have h2 := hD.ξ_sq
    rw [hξ] at h2
    apply hv2ne
    calc v * v = (v⁻¹ * v⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      _ = 1 := by
        have : v⁻¹ * t * (v⁻¹ * t) = v⁻¹ * v⁻¹ * (t * t) := by
          calc v⁻¹ * t * (v⁻¹ * t) = v⁻¹ * (t * v⁻¹) * t := by group
            _ = v⁻¹ * (v⁻¹ * t) * t := by rw [hvt']
            _ = v⁻¹ * v⁻¹ * (t * t) := by group
        rw [this, ht2, mul_one] at h2
        rw [h2, inv_one]
  have hvξK0 : v * ξ ∈ K0 := hLK0 _ (hELL hvξE) hvξβ hvξ2 hvξne1
  have hba : (v * ξ) * (v * v) * (v * ξ)⁻¹ = (v * v)⁻¹ := by
    have e1 : ξ * v * ξ⁻¹ = v⁻¹ := hD.ξ_v
    calc v * ξ * (v * v) * (v * ξ)⁻¹ = v * (ξ * v * ξ⁻¹) * (ξ * v * ξ⁻¹) * v⁻¹ := by group
      _ = v * v⁻¹ * v⁻¹ * v⁻¹ := by rw [e1]
      _ = (v * v)⁻¹ := by group
  have hi2sq : (v * v * (v * ξ)) * (v * v * (v * ξ)) = 1 := by
    calc v * v * (v * ξ) * (v * v * (v * ξ))
        = (v * v) * ((v * ξ) * (v * v) * (v * ξ)⁻¹) * ((v * ξ) * (v * ξ)) := by group
      _ = 1 := by rw [hba, hvξ2]; group
  have hi2ne1 : v * v * (v * ξ) ≠ 1 := by
    intro h
    have h1 : v * v = v * ξ := by
      calc v * v = (v * v * (v * ξ)) * (v * ξ) := by
            calc v * v = (v * v) * ((v * ξ) * (v * ξ)) := by rw [hvξ2, mul_one]
              _ = (v * v * (v * ξ)) * (v * ξ) := by group
        _ = v * ξ := by rw [h, one_mul]
    have h2 : v = ξ := mul_left_cancel h1
    apply hv2ne
    rw [← hD.ξ_sq, ← h2]
  have hi2E : v * v * (v * ξ) ∈ E := mul_mem hvvE hvξE
  have hi2β : v * v * (v * ξ) ∈ centralizer ({β} : Set G) := mul_mem hvvβ hvξβ
  have hi2K0 : v * v * (v * ξ) ∈ K0 := hLK0 _ (hELL hi2E) hi2β hi2sq hi2ne1
  have hvvK0 : v * v ∈ K0 := by
    have : v * v = (v * v * (v * ξ)) * (v * ξ) := by
      calc v * v = (v * v) * ((v * ξ) * (v * ξ)) := by rw [hvξ2, mul_one]
        _ = (v * v * (v * ξ)) * (v * ξ) := by group
    rw [this]
    exact mul_mem hi2K0 hvξK0
  have hDinvK0 : ∀ d ∈ Dsub s z, d * d = 1 → d ≠ 1 → d ∈ K0 := by
    intro d hd hd2 hd1
    by_contra hdK
    obtain ⟨g, hg⟩ := (hcls d (hβS d (hDS hd)) hd2 hd1).2 hdK
    have hgS : g * z * g⁻¹ ∈ S := hg ▸ hDS hd
    obtain ⟨s', hs', hs'g⟩ := c.zconj g hgS
    obtain ⟨k, hk⟩ := c.conj_z_form hS s' hs'
    have hdeq : d = s ^ (2 * k) * z := by rw [← hg, hs'g, hk]
    have hs2k : s ^ (2 * k) ∈ Dsub s z := by
      rw [pow_mul, pow_two]
      exact pow_mem a_mem_Dsub k
    apply z_not_mem_Dsub hS.hz2 hS.hs8 hS.hzs hS.hord hS.hzns
    have h3 : (s ^ (2 * k))⁻¹ * d = z := by rw [hdeq]; group
    have hz' : (s ^ (2 * k))⁻¹ * d ∈ Dsub s z := mul_mem (inv_mem hs2k) hd
    rw [h3] at hz'
    exact hz'
  have hDK0 : Dsub s z ≤ K0 := by
    have h := Dsub_eq_closure_invol hS.hz2 hS.hzs
    calc Dsub s z = closure {y | y ∈ Dsub s z ∧ y * y = 1} := h
      _ ≤ K0 := by
        rw [Subgroup.closure_le]
        rintro y ⟨hy, hy2⟩
        by_cases hy1 : y = 1
        · rw [hy1]; exact one_mem _
        · exact hDinvK0 y hy hy2 hy1
  have hDE : ∀ y ∈ Dsub s z, y ∈ E → y = 1 ∨ y = t := fun y hyD hyE =>
    c.hyp.wFacts.cent y (hELL hyE) fun e he => (mem_centralizer_iff.1 (c.SC (hDS hyD)) e he).symm
  have hED : E ≤ centralizer ((Dsub s z : Subgroup G) : Set G) := fun e he =>
    mem_centralizer_iff.2 fun d hd => (mem_centralizer_iff.1 (c.SC (hDS hd)) e he).symm
  have hfinal : ∀ (g : G) (d e0 : G), d ∈ Dsub s z → e0 ∈ E → d * d * (e0 * e0) = 1 →
      e0 ∈ K0 → e0 ≠ 1 → (d ∈ Dsub s z → d * e0 ≠ 1) → e0 ∈ centralizer ({β} : Set G) →
      g ∈ L ⊓ centralizer ({t} : Set G) → ∃ g' : G, g' * t * g'⁻¹ = g * (d * e0) * g⁻¹ := by
    intro g d e0 hd he0E hsq he0K0 he01 hne he0β hg
    have hdβ : d ∈ centralizer ({β} : Set G) := hβS d (hDS hd)
    have hde : d * e0 = e0 * d := (mem_centralizer_iff.1 (c.SC (hDS hd)) e0 he0E).symm
    have hk2 : d * e0 * (d * e0) = 1 := by
      calc d * e0 * (d * e0) = d * (e0 * d) * e0 := by group
        _ = d * (d * e0) * e0 := by rw [← hde]
        _ = d * d * (e0 * e0) := by group
        _ = 1 := hsq
    obtain ⟨g', hg'⟩ := (hcls (d * e0) (mul_mem hdβ he0β) hk2 (hne hd)).1
      (mul_mem (hDK0 hd) he0K0)
    refine ⟨g * g', ?_⟩
    calc (g * g') * t * (g * g')⁻¹ = g * (g' * t * g'⁻¹) * g⁻¹ := by group
      _ = g * (d * e0) * g⁻¹ := by rw [hg']
  have hne_gen : ∀ d ∈ Dsub s z, ∀ e0 ∈ E, e0 ≠ 1 → e0 ≠ t → d * e0 ≠ 1 := by
    intro d hd e0 he0 he01 he0t h
    have h1 : e0 = d⁻¹ := by
      calc e0 = d⁻¹ * (d * e0) := by group
        _ = d⁻¹ := by rw [h, mul_one]
    have hD' : e0 ∈ Dsub s z := by rw [h1]; exact inv_mem hd
    rcases hDE e0 hD' he0 with h1 | h1
    · exact he01 h1
    · exact he0t h1
  intro w hw hw2 hw1
  obtain ⟨d, hd, e, he, rfl⟩ := exists_mul_of_mem_sup_comm' hED hw
  have hde : d * e = e * d := (mem_centralizer_iff.1 (c.SC (hDS hd)) e he).symm
  have hww : d * d * (e * e) = 1 := by
    calc d * d * (e * e) = d * (d * e) * e := by group
      _ = d * (e * d) * e := by rw [hde]
      _ = (d * e) * (d * e) := by group
      _ = 1 := hw2
  rcases hE69.sq e he with he2 | he2
  · have hd2 : d * d = 1 := by rw [he2, mul_one] at hww; exact hww
    by_cases hcentral : e = 1 ∨ e = t
    · have hwD : d * e ∈ Dsub s z := by
        rcases hcentral with h | h
        · rw [h, mul_one]; exact hd
        · rw [h]; exact mul_mem hd htD
      exact (hcls (d * e) (hβS _ (hDS hwD)) hw2 hw1).1 (hDK0 hwD)
    · push_neg at hcentral
      obtain ⟨g, hg, hge⟩ := c.EB_orbit_two hE69 hvξE he hvξ2 hvξne1 hvξnet he2 hcentral.1
        hcentral.2
      have hdg : d * g = g * d := mem_centralizer_iff.1 (c.EB_le_centS hg) d (hDS hd)
      have hwconj : d * e = g * (d * (v * ξ)) * g⁻¹ := by
        calc d * e = d * (g * (v * ξ) * g⁻¹) := by rw [hge]
          _ = (d * g) * (v * ξ) * g⁻¹ := by group
          _ = (g * d) * (v * ξ) * g⁻¹ := by rw [hdg]
          _ = g * (d * (v * ξ)) * g⁻¹ := by group
      obtain ⟨g', hg'⟩ := hfinal g d (v * ξ) hd hvξE (by rw [hd2, hvξ2, one_mul]) hvξK0 hvξne1
        (fun _ => hne_gen d hd (v * ξ) hvξE hvξne1 hvξnet) hvξβ hg
      exact ⟨g', by rw [hg', hwconj]⟩
  · have hd2 : d * d = t := by
      have h := hww
      rw [he2] at h
      calc d * d = d * d * t * t := by rw [mul_assoc (d * d) t t, ht2, mul_one]
        _ = t := by rw [h, one_mul]
    obtain ⟨g, hg, hge⟩ := c.EB_orbit_four hE69 hvvE he hv4' he2
    have hdg : d * g = g * d := mem_centralizer_iff.1 (c.EB_le_centS hg) d (hDS hd)
    have hwconj : d * e = g * (d * (v * v)) * g⁻¹ := by
      calc d * e = d * (g * (v * v) * g⁻¹) := by rw [hge]
        _ = (d * g) * (v * v) * g⁻¹ := by group
        _ = (g * d) * (v * v) * g⁻¹ := by rw [hdg]
        _ = g * (d * (v * v)) * g⁻¹ := by group
    have hvvt : v * v ≠ t := by
      intro h
      rw [h] at hv4'
      have : t = 1 := by
        calc t = t * t * t⁻¹ := by group
          _ = 1 := by rw [hv4', mul_inv_cancel]
      exact ht1 this
    obtain ⟨g', hg'⟩ := hfinal g d (v * v) hd hvvE (by rw [hd2, hv4', ht2]) hvvK0 hv2ne
      (fun _ => hne_gen d hd (v * v) hvvE hv2ne hvvt) hvvβ hg
    exact ⟨g', by rw [hg', hwconj]⟩

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b
