module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallChar

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}

@[expose] def sqHom (hR : U3R2 G L T₁ R₂ t f) : R₂ →* G where
  toFun r := (r : G) ^ 2
  map_one' := by simp
  map_mul' r r' := by
    have hc : Commute (r : G) r' := hR.comm _ r.2 _ r'.2
    simp only [coe_mul]
    exact hc.mul_pow 2

theorem exists_sq_eq_of_omega (hR : U3R2 G L T₁ R₂ t f) (hA₁ : Nat.card (szA₁ T₁) = 2 ^ f)
    (hΩ : ∀ r ∈ R₂, r ^ 2 = 1 → r ∈ szA₁ T₁) {b : G} (hb : b ∈ szA₁ T₁) :
    ∃ r ∈ R₂, r ^ 2 = b := by
  have hker : (hR.sqHom).ker = (szA₁ T₁).subgroupOf R₂ := by
    ext r
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact ⟨fun h1 => hΩ r r.2 h1, fun h1 => hR.sq_A₁ r h1⟩
  have hrange : (hR.sqHom).range ≤ szA₁ T₁ := by
    rintro _ ⟨r, rfl⟩
    exact hR.sq_mem r r.2
  have hcard := Subgroup.card_ker_mul_card_range hR.sqHom
  rw [hker, Nat.card_congr (subgroupOfEquivOfLe hR.le).toEquiv, hA₁, hR.card] at hcard
  have hrc : Nat.card (hR.sqHom).range = 2 ^ f := by
    have hq : 0 < 2 ^ f := by positivity
    have : 2 ^ f * Nat.card (hR.sqHom).range = 2 ^ f * 2 ^ f := by rw [hcard]; ring
    exact Nat.eq_of_mul_eq_mul_left hq this
  have heq : (hR.sqHom).range = szA₁ T₁ :=
    eq_of_le_of_card_ge hrange (by rw [hrc, hA₁])
  have hb' : b ∈ (hR.sqHom).range := heq ▸ hb
  obtain ⟨r, hr⟩ := hb'
  exact ⟨r, r.2, hr⟩

theorem exists_sq_eq_one (hR : U3R2 G L T₁ R₂ t f) (hA₁ : Nat.card (szA₁ T₁) = 2 ^ f)
    (hsq : ∀ y ∈ T₁, y ^ 2 ∈ szA₁ T₁) {y : G} (hy : y ∈ T₁) :
    ((∀ r ∈ R₂, r ^ 2 = 1) ∧ ∃ r ∈ R₂, r * t * r⁻¹ * t = y ^ 2 ∧ (y * r * t) ^ 2 = 1) ∨
      ((∀ r ∈ R₂, r ^ 2 = 1 → r ∈ szA₁ T₁) ∧ ∃ r ∈ R₂, r ^ 2 = y ^ 2 ∧ (y * r) ^ 2 = 1) := by
  have hy2 := hsq y hy
  have hy4 : (y ^ 2) ^ 2 = 1 := hR.sq_A₁ _ hy2
  rcases hR.sq_eq_one_or with hel | hΩ
  · left
    obtain ⟨r, hr, hρ⟩ := hR.rho_onto _ hy2
    refine ⟨hel, r, hr, hρ, ?_⟩
    have hyr : y * r = r * y := hR.commT₁ y hy r hr
    have hyt : y * t = t * y := hR.t_comm y hy
    have hri : r⁻¹ = r := by
      have := hel r hr
      rw [sq] at this
      exact inv_eq_of_mul_eq_one_right this
    have e : (y * r * t) ^ 2 = y ^ 2 * (r * t * r⁻¹ * t) := by
      rw [hri, sq, sq]
      calc y * r * t * (y * r * t) = y * r * (t * y) * r * t := by group
        _ = y * r * (y * t) * r * t := by rw [hyt]
        _ = y * (r * y) * t * r * t := by group
        _ = y * (y * r) * t * r * t := by rw [hyr]
        _ = y * y * (r * t * r * t) := by group
    rw [e, hρ, ← sq, hy4]
  · right
    obtain ⟨r, hr, hr2⟩ := hR.exists_sq_eq_of_omega hA₁ hΩ hy2
    refine ⟨hΩ, r, hr, hr2, ?_⟩
    have hyr : Commute y r := hR.commT₁ y hy r hr
    rw [hyr.mul_pow, hr2, ← sq, hy4]

end U3R2

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem mem_szA₁_iff_of_normalizer (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hTR : T ≤ normalizer (R₂ : Set G)) {E : Type} [Field E]
    [Finite E] [CharP E 2] {σ : E →+* E} {u v : G → E} (hS : U3SemilinearCoords L T f σ u v)
    {z : G} :
    z ∈ szA₁ (szT₁ L T) ↔
      z ∈ T ⊔ R₂ ∧ z ^ 2 = 1 ∧ ∀ s ∈ T ⊔ R₂, s ^ 2 = 1 → z * s = s * z := by
  have hc := hS.coords
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, -, hsq, hinvT₁, -, -⟩ := h.facts_of_card_sylow hS2
  have hdec : ∀ s ∈ T ⊔ R₂, ∃ x ∈ T, ∃ r ∈ R₂, s = x * r := by
    intro s hs
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right T R₂ hTR] at hs
    obtain ⟨x, hx, r, hr, rfl⟩ := hs
    exact ⟨x, hx, r, hr, rfl⟩
  have hTRA : ∀ r ∈ R₂, r ∈ T → r ∈ szA₁ (szT₁ L T) := fun r hr hrT =>
    hR.rho_ker r hr (mem_centralizer_singleton_iff.mp (h.le hrT))
  have hconjR : ∀ x ∈ T, ∀ r ∈ R₂, x * r * x⁻¹ ∈ R₂ := fun x hx r hr =>
    (mem_normalizer_iff.mp (hTR hx) r).mp hr
  have hinvA : ∀ s ∈ T ⊔ R₂, s ^ 2 = 1 → ∀ a ∈ szA₁ (szT₁ L T), a * s = s * a := by
    intro s hs hs2 a ha
    obtain ⟨x, hxT, r, hr, rfl⟩ := hdec s hs
    have hx2R : x ^ 2 ∈ R₂ := by
      have h1 : x * (r * x * r) = 1 := by
        rw [← hs2, sq]
        group
      have hx' : (r * x * r)⁻¹ = x := (eq_inv_of_mul_eq_one_left h1).symm
      have e : x ^ 2 = (x * r⁻¹ * x⁻¹) * r⁻¹ := by
        calc x ^ 2 = x * x := sq x
          _ = x * (r * x * r)⁻¹ := by rw [hx']
          _ = (x * r⁻¹ * x⁻¹) * r⁻¹ := by group
      rw [e]
      exact mul_mem (hconjR x hxT r⁻¹ (inv_mem hr)) (inv_mem hr)
    have hx2A : x ^ 2 ∈ szA₁ (szT₁ L T) := hTRA _ hx2R (pow_mem hxT 2)
    have hxa : x * a = a * x := by
      by_cases hxS : x ∈ szT₁ L T ⊔ zpowers t
      · obtain ⟨y, hy, w, hw, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hxS
        have hya : y * a = a * y := mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy
        have hwa : a * w = w * a :=
          commute_of_mem_zpowers hw (mem_centralizer_iff.mp h.mem_centralizer_szT₁ a
            (szA₁_le _ ha))
        calc y * w * a = y * (w * a) := by group
          _ = y * (a * w) := by rw [hwa]
          _ = (y * a) * w := by group
          _ = (a * y) * w := by rw [hya]
          _ = a * (y * w) := by group
      · exact (hS.comm_szA₁_and_exists_u_of_sq_mem h hS2 hxT hxS
          (mem_sup_left (szA₁_le _ hx2A))).1 a ha
    have hra : r * a = a * r := hR.comm r hr a (hR.le ha)
    calc a * (x * r) = (a * x) * r := by group
      _ = (x * a) * r := by rw [hxa]
      _ = x * (a * r) := by group
      _ = x * (r * a) := by rw [hra]
      _ = x * r * a := by group
  constructor
  · intro ha
    exact ⟨mem_sup_right (hR.le ha), hR.sq_A₁ z ha, fun s hs hs2 => hinvA s hs hs2 z ha⟩
  rintro ⟨hz, hz2, hzc⟩
  have hzt : z * t = t * z := hzc t (mem_sup_left htT) h.sq_eq_one
  have hzT : z ∈ T := by
    obtain ⟨x, hxT, r, hr, rfl⟩ := hdec z hz
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (h.le hxT)
    have hrt : r * t = t * r := by
      have h1 : x * (r * t) = x * (t * r) := by
        calc x * (r * t) = x * r * t := by group
          _ = t * (x * r) := hzt
          _ = (t * x) * r := by group
          _ = (x * t) * r := by rw [hxt]
          _ = x * (t * r) := by group
      exact mul_left_cancel h1
    exact mul_mem hxT (szT₁_le_left L T (szA₁_le _ (hR.rho_ker r hr hrt)))
  have hzN := hTN₁ hzT
  have hzy : ∀ y ∈ szT₁ L T, u (z * y * z⁻¹) = 1 * u y := by
    intro y hy
    have hzyT : z * y * z⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hzN y).mp hy
    obtain ⟨r, hr, hrel⟩ : ∃ r ∈ R₂, (z * y * z⁻¹) * (z * r * z⁻¹) = y * r := by
      rcases hR.exists_sq_eq_one hA₁card hsq hy with ⟨-, r, hr, -, hs⟩ | ⟨-, r, hr, -, hs⟩
      · refine ⟨r, hr, ?_⟩
        have hsS : y * r * t ∈ T ⊔ R₂ :=
          mul_mem (mul_mem (mem_sup_left (szT₁_le_left L T hy)) (mem_sup_right hr))
            (mem_sup_left htT)
        have h1 := hzc _ hsS hs
        have hzt' : z⁻¹ * t = t * z⁻¹ := by
          calc z⁻¹ * t = z⁻¹ * (t * z) * z⁻¹ := by group
            _ = z⁻¹ * (z * t) * z⁻¹ := by rw [hzt]
            _ = t * z⁻¹ := by group
        have h2 : (z * y * z⁻¹) * (z * r * z⁻¹) * t = y * r * t := by
          calc (z * y * z⁻¹) * (z * r * z⁻¹) * t = z * (y * r) * (z⁻¹ * t) := by group
            _ = z * (y * r) * (t * z⁻¹) := by rw [hzt']
            _ = z * (y * r * t) * z⁻¹ := by group
            _ = y * r * t := by rw [h1, mul_inv_cancel_right]
        exact mul_right_cancel h2
      · refine ⟨r, hr, ?_⟩
        have hsS : y * r ∈ T ⊔ R₂ :=
          mul_mem (mem_sup_left (szT₁_le_left L T hy)) (mem_sup_right hr)
        have h1 := hzc _ hsS hs
        calc (z * y * z⁻¹) * (z * r * z⁻¹) = z * (y * r) * z⁻¹ := by group
          _ = y * r := by rw [h1, mul_inv_cancel_right]
    have hmem : y⁻¹ * (z * y * z⁻¹) ∈ szA₁ (szT₁ L T) := by
      rw [← hR.inf]
      refine mem_inf.mpr ⟨mul_mem (inv_mem hy) hzyT, ?_⟩
      have e : y⁻¹ * (z * y * z⁻¹) = r * (z * r * z⁻¹)⁻¹ := by
        calc y⁻¹ * (z * y * z⁻¹) = y⁻¹ * ((z * y * z⁻¹) * (z * r * z⁻¹)) * (z * r * z⁻¹)⁻¹ := by
              group
          _ = y⁻¹ * (y * r) * (z * r * z⁻¹)⁻¹ := by rw [hrel]
          _ = r * (z * r * z⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem hr (inv_mem (hconjR z hzT r hr))
    have h0 := (hS.mem_szA₁_iff _ (mul_mem (inv_mem hy) hzyT)).mp hmem
    rw [hc.u_mul_inv hy hzyT] at h0
    rw [one_mul]
    linear_combination h0
  have hzS := hS.mem_sup_of_u_conj_eq_mul h hS2 hzT hzy
  obtain ⟨y₀, hy₀, w, hw, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hzS
  have hy₀w : y₀ * w = w * y₀ :=
    commute_of_mem_zpowers hw (mem_centralizer_iff.mp h.mem_centralizer_szT₁ y₀ hy₀)
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hw with hw1 | hwt
  · rw [hw1, mul_one] at hz2 ⊢
    exact hinvT₁ y₀ hy₀ hz2
  · exfalso
    rw [hwt] at hz2 hy₀w hzc
    have hy₀2 : y₀ ^ 2 = 1 := by
      have e : (y₀ * t) ^ 2 = y₀ ^ 2 * t ^ 2 := (Commute.mul_pow hy₀w 2)
      rw [e, h.sq_eq_one, mul_one] at hz2
      exact hz2
    have hy₀A := hinvT₁ y₀ hy₀ hy₀2
    have htc : ∀ s ∈ T ⊔ R₂, s ^ 2 = 1 → t * s = s * t := by
      intro s hs hs2
      have h1 := hzc s hs hs2
      have h2 := hinvA s hs hs2 y₀ hy₀A
      have h3 : y₀ * (t * s) = y₀ * (s * t) := by
        calc y₀ * (t * s) = y₀ * t * s := by group
          _ = s * (y₀ * t) := h1
          _ = (s * y₀) * t := by group
          _ = (y₀ * s) * t := by rw [h2]
          _ = y₀ * (s * t) := by group
      exact mul_left_cancel h3
    rcases hR.sq_eq_one_or with hel | hΩ
    ·
      have hle : R₂ ≤ szA₁ (szT₁ L T) := fun r hr =>
        hR.rho_ker r hr (htc r (mem_sup_right hr) (hel r hr)).symm
      have h1 := card_le_of_le hle
      rw [hR.card, hA₁card] at h1
      have : 2 ^ f < (2 ^ f) ^ 2 := by
        have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
        nlinarith
      omega
    ·
      have hall : ∀ y ∈ szT₁ L T, y ∈ szA₁ (szT₁ L T) := by
        intro y hy
        refine hinvT₁ y hy ?_
        rcases hR.exists_sq_eq_one hA₁card hsq hy with ⟨hel', -⟩ | ⟨-, r, hr, hr2, hs⟩
        · obtain ⟨r, hr, hrA⟩ : ∃ r ∈ R₂, r ∉ szA₁ (szT₁ L T) := by
            by_contra hne
            push Not at hne
            have h1 := card_le_of_le (show R₂ ≤ szA₁ (szT₁ L T) from hne)
            rw [hR.card, hA₁card] at h1
            have : 2 ^ f < (2 ^ f) ^ 2 := by
              have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
              nlinarith
            omega
          exact absurd (hΩ r hr (hel' r hr)) hrA
        · have hsS : y * r ∈ T ⊔ R₂ :=
            mul_mem (mem_sup_left (szT₁_le_left L T hy)) (mem_sup_right hr)
          have h1 := htc _ hsS hs
          have hyt : y * t = t * y := hR.t_comm y hy
          have hrt : r * t = t * r := by
            have h2 : y * (t * r) = y * (r * t) := by
              calc y * (t * r) = (y * t) * r := by group
                _ = (t * y) * r := by rw [hyt]
                _ = t * (y * r) := by group
                _ = y * r * t := h1
                _ = y * (r * t) := by group
            exact (mul_left_cancel h2).symm
          rw [← hr2]
          exact hR.sq_A₁ r (hR.rho_ker r hr hrt)
      have h1 := card_le_of_le (show szT₁ L T ≤ szA₁ (szT₁ L T) from hall)
      rw [hT₁card, hA₁card] at h1
      have : 2 ^ f < (2 ^ f) ^ 3 := by
        have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
        calc 2 ^ f = 2 ^ f * 1 := (mul_one _).symm
          _ < 2 ^ f * (2 ^ f * 2 ^ f) := Nat.mul_lt_mul_of_pos_left (by nlinarith) (by positivity)
          _ = (2 ^ f) ^ 3 := by ring
      omega

theorem normalizer_S₁_le_normalizer_szA₁_of_normalizer
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) (hTR : T ≤ normalizer (R₂ : Set G)) :
    normalizer ((T ⊔ R₂ : Subgroup G) : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) := by
  obtain ⟨E, _, _, _, σ, u, v, hS⟩ := h.exists_semilinearCoords_of_card_sylow hS2
  have key : ∀ n ∈ normalizer ((T ⊔ R₂ : Subgroup G) : Set G), ∀ z ∈ szA₁ (szT₁ L T),
      n * z * n⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro n hn z hz
    obtain ⟨hzS, hz2, hzc⟩ := (h.mem_szA₁_iff_of_normalizer hS2 hR hTR hS).mp hz
    refine (h.mem_szA₁_iff_of_normalizer hS2 hR hTR hS).mpr
      ⟨(mem_normalizer_iff.mp hn z).mp hzS, ?_, fun s hs hs2 => ?_⟩
    · calc (n * z * n⁻¹) ^ 2 = n * z ^ 2 * n⁻¹ := by rw [sq, sq]; group
        _ = 1 := by rw [hz2]; group
    · have hs' : n⁻¹ * s * n ∈ T ⊔ R₂ := (mem_normalizer_iff''.mp hn s).mp hs
      have hs2' : (n⁻¹ * s * n) ^ 2 = 1 := by
        calc (n⁻¹ * s * n) ^ 2 = n⁻¹ * s ^ 2 * n := by rw [sq, sq]; group
          _ = 1 := by rw [hs2]; group
      have e := hzc _ hs' hs2'
      calc n * z * n⁻¹ * s = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by rw [e]
        _ = s * (n * z * n⁻¹) := by group
  intro n hn
  refine mem_normalizer_iff.mpr fun x => ⟨key n hn x, fun hx => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

section Certificates


theorem normalizer_S₁_le_normalizer_szA₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    normalizer ((T ⊔ R₂ : Subgroup G) : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) := by
  obtain ⟨-, -, -, -, hNR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  exact h.normalizer_S₁_le_normalizer_szA₁_of_normalizer hS2 hR (hTA.trans hNR₂)

end Certificates

end U3Start

section Certificates


theorem u3FourNormalizerInput_holds : U3FourNormalizerInput :=
  fun _ _ _ _ _ _ _ h hS2 hR => h.normalizer_S₁_le_normalizer_szA₁_of_card_sylow hS2 hR

end Certificates

end CFSG.SeitzReduction.RankOne
