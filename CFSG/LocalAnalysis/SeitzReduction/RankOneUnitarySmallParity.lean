module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryOmegaRegular

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem map_sum_add_card_nsmul_eq {Ω E : Type*} [Fintype Ω] [AddCommGroup E] (κ : Ω → E)
    (s : Equiv.Perm Ω) (φ : E →+ E) (c : E) (hs : ∀ X, κ (s X) = φ (κ X) + c) :
    φ (∑ X, κ X) + Fintype.card Ω • c = ∑ X, κ X := by
  calc φ (∑ X, κ X) + Fintype.card Ω • c = ∑ X, (φ (κ X) + c) := by
        rw [map_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    _ = ∑ X, κ (s X) := by simp only [hs]
    _ = ∑ X, κ X := Equiv.sum_comp s κ

theorem odd_nsmul_eq_self_of_add_self {E : Type*} [AddCommGroup E] (h2 : ∀ a : E, a + a = 0)
    {n : ℕ} (hn : Odd n) (c : E) : n • c = c := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, two_mul, add_nsmul, ← nsmul_add, h2, nsmul_zero, zero_add, one_nsmul]

theorem U3RootCoords.exists_addMonoidHom_conj_sup {G : Type*} [Group G] {E : Type*} [Field E]
    {T₁ R₂ A₁ : Subgroup G} {σ : E →+* E} {u v : G → E} (hc : U3RootCoords T₁ σ u v)
    (hA : ∀ y ∈ T₁, y ∈ A₁ ↔ u y = 0) (hinf : T₁ ⊓ R₂ ≤ A₁) (hAR : A₁ ≤ R₂)
    (hcomm : ∀ x ∈ T₁, ∀ r ∈ R₂, x * r = r * x)
    (hmem : ∀ x, x ∈ T₁ ⊔ R₂ → ∃ w ∈ T₁, ∃ r ∈ R₂, w * r = x)
    {y : G} (hyH : y ∈ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G))
    (hyR : y ∈ normalizer (R₂ : Set G)) :
    ∃ φ : E →+ E, ∀ w ∈ T₁, ∀ w' ∈ T₁, ∀ r' ∈ R₂, y * w * y⁻¹ = w' * r' → u w' = φ (u w) := by
  classical
  choose s hsT hsu using hc.u_surj
  have hdec : ∀ a : E, ∃ w' ∈ T₁, ∃ r' ∈ R₂, w' * r' = y * s a * y⁻¹ := fun a =>
    hmem _ ((mem_normalizer_iff.mp hyH _).mp (mem_sup_left (hsT a)))
  choose w' hw'T r' hr'R hw'r' using hdec
  have key : ∀ w ∈ T₁, ∀ w₁ ∈ T₁, ∀ r₁ ∈ R₂, y * w * y⁻¹ = w₁ * r₁ →
      u w₁ = u (w' (u w)) := by
    intro w hw w₁ hw₁ r₁ hr₁ he
    have hsw : (s (u w))⁻¹ * w ∈ T₁ := mul_mem (inv_mem (hsT (u w))) hw
    have hz : (s (u w))⁻¹ * w ∈ A₁ := (hA _ hsw).mpr
      (by rw [hc.u_mul_inv (hsT (u w)) hw, hsu, sub_self])
    have hz' : y * ((s (u w))⁻¹ * w) * y⁻¹ ∈ R₂ := (mem_normalizer_iff.mp hyR _).mp (hAR hz)
    have e : (w' (u w))⁻¹ * w₁ = r' (u w) * (y * ((s (u w))⁻¹ * w) * y⁻¹) * r₁⁻¹ := by
      have e1 : w₁ = y * w * y⁻¹ * r₁⁻¹ := by rw [he]; group
      have e2 : y * w * y⁻¹ = (w' (u w) * r' (u w)) * (y * ((s (u w))⁻¹ * w) * y⁻¹) := by
        rw [hw'r']; group
      rw [e1, e2]; group
    have hwT : (w' (u w))⁻¹ * w₁ ∈ T₁ := mul_mem (inv_mem (hw'T (u w))) hw₁
    have hwR : (w' (u w))⁻¹ * w₁ ∈ R₂ := by
      rw [e]; exact mul_mem (mul_mem (hr'R (u w)) hz') (inv_mem hr₁)
    have hmemA : (w' (u w))⁻¹ * w₁ ∈ A₁ := hinf ⟨hwT, hwR⟩
    have h0 := (hA _ hwT).mp hmemA
    rw [hc.u_mul_inv (hw'T (u w)) hw₁] at h0
    exact sub_eq_zero.mp h0
  refine ⟨AddMonoidHom.mk' (fun a => u (w' a)) fun a b => ?_, fun w hw w₁ hw₁ r₁ hr₁ he => ?_⟩
  · have hab : u (s a * s b) = a + b := by rw [hc.mul_u _ (hsT a) _ (hsT b), hsu, hsu]
    have he : y * (s a * s b) * y⁻¹ = (w' a * w' b) * (r' a * r' b) := by
      have e1 : y * (s a * s b) * y⁻¹ = (y * s a * y⁻¹) * (y * s b * y⁻¹) := by group
      rw [e1, ← hw'r', ← hw'r']
      have hc' := hcomm (w' b) (hw'T b) (r' a) (hr'R a)
      calc w' a * r' a * (w' b * r' b) = w' a * (r' a * w' b) * r' b := by group
        _ = w' a * (w' b * r' a) * r' b := by rw [hc']
        _ = w' a * w' b * (r' a * r' b) := by group
    have := key _ (mul_mem (hsT a) (hsT b)) _ (mul_mem (hw'T a) (hw'T b)) _
      (mul_mem (hr'R a) (hr'R b)) he
    rw [hab, hc.mul_u _ (hw'T a) _ (hw'T b)] at this
    exact this.symm
  · exact key w hw w₁ hw₁ r₁ hr₁ he

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem mem_szA₁_of_conj_mem_of_torus (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {d w : G}
    (hd : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b ≠ 1 → b' ≠ 1 →
      ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b')
    (hw : w ∈ szT₁ L T) (hdw : w⁻¹ * (d * w * d⁻¹) ∈ szA₁ (szT₁ L T)) :
    w ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, hA₁card, -, hsq, hinv, hA2, -⟩ := h.facts_of_card_sylow hS2
  have hzc : w * (w⁻¹ * (d * w * d⁻¹)) = (w⁻¹ * (d * w * d⁻¹)) * w :=
    mem_centralizer_iff.mp (mem_szA₁.mp hdw).2 w hw
  have hdw2 : d * w ^ 2 * d⁻¹ = w ^ 2 := by
    set z := w⁻¹ * (d * w * d⁻¹) with hz
    have e1 : d * w * d⁻¹ = w * z := by rw [hz]; group
    calc d * w ^ 2 * d⁻¹ = (d * w * d⁻¹) * (d * w * d⁻¹) := by rw [sq]; group
      _ = (w * z) * (w * z) := by rw [e1]
      _ = w * (z * w) * z := by group
      _ = w * (w * z) * z := by rw [← hzc]
      _ = w ^ 2 * z ^ 2 := by rw [sq, sq]; group
      _ = w ^ 2 := by rw [hA2 z hdw, mul_one]
  have hdw2' : d⁻¹ * w ^ 2 * d = w ^ 2 := by
    calc d⁻¹ * w ^ 2 * d = d⁻¹ * (d * w ^ 2 * d⁻¹) * d := by rw [hdw2]
      _ = w ^ 2 := by group
  have hpow : ∀ n : ℕ, (d ^ n)⁻¹ * w ^ 2 * d ^ n = w ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (d ^ (n + 1))⁻¹ * w ^ 2 * d ^ (n + 1) =
            d⁻¹ * ((d ^ n)⁻¹ * w ^ 2 * d ^ n) * d := by rw [pow_succ]; group
        _ = w ^ 2 := by rw [ih, hdw2']
  by_contra hwA
  have hw2 : w ^ 2 ≠ 1 := fun h1 => hwA (hinv w hw h1)
  have hsub : (szA₁ (szT₁ L T) : Set G) ⊆ {1, w ^ 2} := by
    intro b hb
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    · obtain ⟨n, hn⟩ := hd _ (hsq w hw) b hb hw2 hb1
      rw [hpow n] at hn
      exact Or.inr hn.symm
  have h1 : Nat.card (szA₁ (szT₁ L T)) ≤ 2 := by
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq] at h2
    refine h2.trans ((Set.ncard_insert_le _ _).trans ?_)
    rw [Set.ncard_singleton]
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  rw [hA₁card] at h1
  omega

section Certificates


theorem conj_mem_of_odd_ncard_u3Omega_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hodd : Odd (u3Omega L T R₂ t).ncard) :
    ∀ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∈ R₂ ⊔ zpowers t := by
  classical
  obtain ⟨E, hE, hEfin, hch, σ, -, -, -, u, v, hc, hA₁u⟩ := h.exists_rootCoords_of_card_sylow hS2
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  have hfin : (u3Omega L T R₂ t).Finite :=
    (Set.finite_range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁)).subset
      (h.u3Omega_subset_range_of_card_sylow hS2 hR)
  let : Fintype (u3Omega L T R₂ t) := hfin.fintype
  have hcard : Fintype.card (u3Omega L T R₂ t) = (u3Omega L T R₂ t).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hpt : ∀ X : u3Omega L T R₂ t, ∃ w, w ∈ szT₁ L T ∧
      (X : Subgroup G) = R₂ ⊔ zpowers (w * t) := by
    intro X
    obtain ⟨q, hq⟩ := h.u3Omega_subset_range_of_card_sylow hS2 hR X.2
    induction q using QuotientGroup.induction_on with | H w => ?_
    exact ⟨w, w.2, by rw [← hq, u3OmegaPoint_mk]⟩
  choose wX hwXT hwX using hpt
  have huniq : ∀ X : u3Omega L T R₂ t, ∀ w ∈ szT₁ L T,
      (X : Subgroup G) = R₂ ⊔ zpowers (w * t) → u w = u (wX X) := by
    intro X w hw hXw
    have h1 : u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁ (QuotientGroup.mk ⟨w, hw⟩) =
        u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁ (QuotientGroup.mk ⟨wX X, hwXT X⟩) := by
      rw [u3OmegaPoint_mk, u3OmegaPoint_mk, ← hXw, ← hwX X]
    have h2 := h.u3OmegaPoint_injective_of_card_sylow hS2 hR h1
    rw [QuotientGroup.eq, mem_subgroupOf] at h2
    have h2' : w⁻¹ * wX X ∈ szA₁ (szT₁ L T) := by simpa using h2
    have h3 := (hA₁u _ (mul_mem (inv_mem hw) (hwXT X))).mp h2'
    rw [hc.u_mul_inv hw (hwXT X)] at h3
    exact (sub_eq_zero.mp h3).symm
  have haff : ∀ y : normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      ∃ φ : E →+ E, (∀ w ∈ szT₁ L T, ∀ w' ∈ szT₁ L T, ∀ r' ∈ R₂,
        (y : G) * w * (y : G)⁻¹ = w' * r' → u w' = φ (u w)) ∧
      ∃ wy ∈ szT₁ L T, ∃ ry ∈ R₂, (y : G) * t * (y : G)⁻¹ = wy * ry * t ∧
        ∀ X, u (wX (u3OmegaAction L T R₂ t y X)) = φ (u (wX X)) + u wy := by
    intro y
    have hyH := (mem_inf.mp (hNR₁ y.2)).1
    have hyR := (mem_inf.mp (hNR₁ y.2)).2
    obtain ⟨φ, hφ⟩ := hc.exists_addMonoidHom_conj_sup hA₁u hR.inf.le hR.le hR.commT₁
      (fun x hx => hR.mem_sup_iff.mp hx) hyH hyR
    obtain ⟨wy, hwy, ry, hry, hyt⟩ :=
      h.exists_mul_of_mem_normalizer_szR_of_card_sylow hS2 hR y.2
    refine ⟨φ, hφ, wy, hwy, ry, hry, hyt, fun X => ?_⟩
    obtain ⟨w₁, hw₁, r₁, hr₁, he₁⟩ :=
      hR.mem_sup_iff.mp ((mem_normalizer_iff.mp hyH _).mp (mem_sup_left (hwXT X)))
    have hpoint : ((u3OmegaAction L T R₂ t y X : u3Omega L T R₂ t) : Subgroup G) =
        R₂ ⊔ zpowers ((w₁ * wy) * t) := by
      rw [u3OmegaAction_apply, hwX X, map_conj_sup_zpowers hyR]
      have e : (y : G) * (wX X * t) * (y : G)⁻¹ =
          (w₁ * wy) * t * (t⁻¹ * (r₁ * ry) * t) := by
        have e1 : (y : G) * (wX X * t) * (y : G)⁻¹ =
            ((y : G) * wX X * (y : G)⁻¹) * ((y : G) * t * (y : G)⁻¹) := by group
        rw [e1, ← he₁, hyt]
        have hc1 : r₁ * wy = wy * r₁ := (hR.commT₁ wy hwy r₁ hr₁).symm
        calc w₁ * r₁ * (wy * ry * t) = w₁ * (r₁ * wy) * ry * t := by group
          _ = w₁ * (wy * r₁) * ry * t := by rw [hc1]
          _ = w₁ * wy * t * (t⁻¹ * (r₁ * ry) * t) := by group
      have htr : t⁻¹ * (r₁ * ry) * t ∈ R₂ := by
        have := hR.tN _ (mul_mem hr₁ hry)
        rw [hR.t_inv] at this ⊢
        exact this
      rw [e, sup_zpowers_mul_eq htr]
    rw [← huniq _ _ (mul_mem hw₁ hwy) hpoint, hc.mul_u _ hw₁ _ hwy,
      hφ (wX X) (hwXT X) w₁ hw₁ r₁ hr₁ he₁.symm]
  have hoddc : Odd (Fintype.card (u3Omega L T R₂ t)) := by rw [hcard]; exact hodd
  have hbar : ∀ y : normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      ∀ φ : E →+ E, ∀ c : E,
      (∀ X, u (wX (u3OmegaAction L T R₂ t y X)) = φ (u (wX X)) + c) →
      φ (∑ X, u (wX X)) + c = ∑ X, u (wX X) := by
    intro y φ c hyc
    have := map_sum_add_card_nsmul_eq (fun X => u (wX X)) (u3OmegaAction L T R₂ t y) φ c hyc
    rwa [odd_nsmul_eq_self_of_add_self (fun a => CharTwo.add_self_eq_zero a) hoddc c] at this
  obtain ⟨d, hdt, hdR, hdT, hdA⟩ := hR.torus
  have hdtN : d ∈ normalizer ((zpowers t : Subgroup G) : Set G) := by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    exact ((Commute.zpow_right hdt k).eq).symm
  have hdY : d ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_inf (mem_normalizer_sup_of_mem_inf hdT hdR) hdtN
  obtain ⟨φd, hφd, wd, hwd, rd, hrd, hdt', hdX⟩ := haff ⟨d, hdY⟩
  have hwd0 : u wd = 0 := by
    have e : wd = rd⁻¹ := by
      have h1 : d * t * d⁻¹ = t := by rw [hdt, mul_inv_cancel_right]
      have h2 : wd * rd * t = t := by rw [← hdt']; exact h1
      have h3 : wd * rd = 1 := by simpa using h2
      exact eq_inv_of_mul_eq_one_left h3
    have hwdR : wd ∈ R₂ := by rw [e]; exact inv_mem hrd
    have hwdA : wd ∈ szA₁ (szT₁ L T) := hR.inf.le (mem_inf.mpr ⟨hwd, hwdR⟩)
    exact (hA₁u wd hwd).mp hwdA
  have hfpf : ∀ a : E, φd a = a → a = 0 := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := hc.u_surj a
    have hdwT : d * w * d⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hdT w).mp hw
    have h1 : u (d * w * d⁻¹) = φd (u w) :=
      hφd w hw _ hdwT 1 (one_mem _) (by rw [mul_one])
    have h2 : w⁻¹ * (d * w * d⁻¹) ∈ szA₁ (szT₁ L T) := by
      refine (hA₁u _ (mul_mem (inv_mem hw) hdwT)).mpr ?_
      rw [hc.u_mul_inv hw hdwT, h1, ha, sub_self]
    exact (hA₁u w hw).mp (h.mem_szA₁_of_conj_mem_of_torus hS2 hdA hw h2)
  have hb : ∑ X, u (wX X) = 0 := by
    have := hbar ⟨d, hdY⟩ φd (u wd) hdX
    rw [hwd0, add_zero] at this
    exact hfpf _ this
  intro y hy
  obtain ⟨φ, -, wy, hwy, ry, hry, hyt, hyX⟩ := haff ⟨y, hy⟩
  have h1 := hbar ⟨y, hy⟩ φ (u wy) hyX
  rw [hb, map_zero, zero_add] at h1
  have hwyA : wy ∈ szA₁ (szT₁ L T) := (hA₁u wy hwy).mpr h1
  rw [hyt]
  exact mul_mem (mem_sup_left (mul_mem (hR.le hwyA) hry)) (mem_sup_right (mem_zpowers t))

theorem even_ncard_u3Omega_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hmove : ∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t) : Even (u3Omega L T R₂ t).ncard := by
  rcases Nat.even_or_odd (u3Omega L T R₂ t).ncard with he | ho
  · exact he
  · obtain ⟨y, hy, hyt⟩ := hmove
    exact absurd (h.conj_mem_of_odd_ncard_u3Omega_of_card_sylow hS2 hR ho y hy) hyt

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
