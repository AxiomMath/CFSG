module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallOmegaOdd
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Coords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallTwoLines

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem exists_kappa_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {E : Type*} [Field E] {σ : E →+* E} {u v : G → E}
    (hc : U3RootCoords (szT₁ L T) σ u v)
    (hA₁u : ∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)) :
    ∃ κ : u3Omega L T R₂ t → E, Function.Injective κ ∧
      (∀ X : u3Omega L T R₂ t, ∃ w ∈ szT₁ L T, (X : Subgroup G) = R₂ ⊔ zpowers (w * t)) ∧
      (∀ X : u3Omega L T R₂ t, ∀ w ∈ szT₁ L T, (X : Subgroup G) = R₂ ⊔ zpowers (w * t) →
        κ X = u w) ∧
      ∀ y : normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
        ∃ φ : E →+ E, Function.Injective φ ∧
          (∀ w ∈ szT₁ L T, ∀ w' ∈ szT₁ L T, ∀ r' ∈ R₂,
            (y : G) * w * (y : G)⁻¹ = w' * r' → u w' = φ (u w)) ∧ ∃ c : E,
          ∀ X, κ (u3OmegaAction L T R₂ t y X) = φ (κ X) + c := by
  classical
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  have hpt : ∀ X : u3Omega L T R₂ t, ∃ w ∈ szT₁ L T,
      (X : Subgroup G) = R₂ ⊔ zpowers (w * t) := by
    intro X
    obtain ⟨q, hq⟩ := h.u3Omega_subset_range_of_card_sylow hS2 hR X.2
    induction q using QuotientGroup.induction_on with | H w => ?_
    exact ⟨w, w.2, by rw [← hq, u3OmegaPoint_mk]⟩
  choose wX hwXT hwX using hpt
  have hrep : ∀ w ∈ szT₁ L T, ∀ w' ∈ szT₁ L T,
      R₂ ⊔ zpowers (w * t) = R₂ ⊔ zpowers (w' * t) → u w = u w' := by
    intro w hw w' hw' he
    have h1 : u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁ (QuotientGroup.mk ⟨w, hw⟩) =
        u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁ (QuotientGroup.mk ⟨w', hw'⟩) := by
      rw [u3OmegaPoint_mk, u3OmegaPoint_mk]
      exact he
    have h2 := h.u3OmegaPoint_injective_of_card_sylow hS2 hR h1
    rw [QuotientGroup.eq, mem_subgroupOf] at h2
    have h2' : w⁻¹ * w' ∈ szA₁ (szT₁ L T) := by simpa using h2
    have h3 := (hA₁u _ (mul_mem (inv_mem hw) hw')).mp h2'
    rw [hc.u_mul_inv hw hw'] at h3
    exact (sub_eq_zero.mp h3).symm
  have huniq : ∀ X : u3Omega L T R₂ t, ∀ w ∈ szT₁ L T,
      (X : Subgroup G) = R₂ ⊔ zpowers (w * t) → u (wX X) = u w := fun X w hw hXw =>
    hrep _ (hwXT X) _ hw ((hwX X).symm.trans hXw)
  refine ⟨fun X => u (wX X), fun X X' hXX' => ?_, fun X => ⟨wX X, hwXT X, hwX X⟩, huniq,
    fun y => ?_⟩
  ·
    have hA : (wX X)⁻¹ * wX X' ∈ szA₁ (szT₁ L T) := by
      refine (hA₁u _ (mul_mem (inv_mem (hwXT X)) (hwXT X'))).mpr ?_
      rw [hc.u_mul_inv (hwXT X) (hwXT X')]
      exact sub_eq_zero.mpr hXX'.symm
    apply Subtype.ext
    rw [hwX X, hwX X']
    have hcomm : ((wX X)⁻¹ * wX X') * t = t * ((wX X)⁻¹ * wX X') :=
      hR.t_comm _ (mul_mem (inv_mem (hwXT X)) (hwXT X'))
    have e : wX X' * t = wX X * t * ((wX X)⁻¹ * wX X') := by
      calc wX X' * t = wX X * (((wX X)⁻¹ * wX X') * t) := by group
        _ = wX X * (t * ((wX X)⁻¹ * wX X')) := by rw [hcomm]
        _ = wX X * t * ((wX X)⁻¹ * wX X') := by group
    rw [e, sup_zpowers_mul_eq (hR.le hA)]
  ·
    have hyH := (mem_inf.mp (hNR₁ y.2)).1
    have hyR := (mem_inf.mp (hNR₁ y.2)).2
    obtain ⟨φ, hφ⟩ := hc.exists_addMonoidHom_conj_sup hA₁u hR.inf.le hR.le hR.commT₁
      (fun x hx => hR.mem_sup_iff.mp hx) hyH hyR
    obtain ⟨wy, hwy, ry, hry, hyt⟩ :=
      h.exists_mul_of_mem_normalizer_szR_of_card_sylow hS2 hR y.2
    refine ⟨φ, ?_, hφ, u wy, fun X => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨w, hw, rfl⟩ := hc.u_surj a
      obtain ⟨w₁, hw₁, r₁, hr₁, he₁⟩ :=
        hR.mem_sup_iff.mp ((mem_normalizer_iff.mp hyH _).mp (mem_sup_left hw))
      have h1 : u w₁ = 0 := by rw [hφ w hw w₁ hw₁ r₁ hr₁ he₁.symm, ha]
      have hw₁R : w₁ ∈ R₂ := hR.le ((hA₁u w₁ hw₁).mpr h1)
      have hyw : (y : G) * w * (y : G)⁻¹ ∈ R₂ := he₁ ▸ mul_mem hw₁R hr₁
      have hwR : w ∈ R₂ := by
        have := (mem_normalizer_iff''.mp hyR _).mp hyw
        rwa [show (y : G)⁻¹ * ((y : G) * w * (y : G)⁻¹) * (y : G) = w by group] at this
      exact (hA₁u w hw).mp (hR.inf.le (mem_inf.mpr ⟨hw, hwR⟩))
    · obtain ⟨w₁, hw₁, r₁, hr₁, he₁⟩ :=
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
      show u (wX _) = φ (u (wX X)) + u wy
      rw [huniq _ _ (mul_mem hw₁ hwy) hpoint, hc.mul_u _ hw₁ _ hwy,
        hφ (wX X) (hwXT X) w₁ hw₁ r₁ hr₁ he₁.symm]
end Certificates

end U3Start

theorem sq_sub_one_eq_sub_one_mul_add_one (n : ℕ) (hn : 1 ≤ n) : n ^ 2 - 1 = (n - 1) * (n + 1) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (p + 1) ^ 2 = p * (p + 1 + 1) + 1 by ring, Nat.add_sub_cancel]

theorem sub_one_dvd_div_gcd (q : ℕ) (hq : 1 ≤ q) : q - 1 ∣ (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  set g := Nat.gcd 3 (q + 1) with hgdef
  obtain ⟨r, hr⟩ : g ∣ q + 1 := Nat.gcd_dvd_right 3 (q + 1)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have e : q ^ 2 - 1 = g * ((q - 1) * r) := by
    rw [sq_sub_one_eq_sub_one_mul_add_one q hq, hr]
    ring
  rw [e, Nat.mul_div_cancel_left _ hg]
  exact Dvd.intro r rfl

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem ncard_u3Omega_two_pow_or_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    (∃ j : ℕ, (u3Omega L T R₂ t).ncard = 2 ^ j) ∨
      2 * ((u3Omega L T R₂ t).ncard - 1) = (2 ^ f - 1) * (2 ^ f + 2) := by
  classical
  obtain ⟨E, hE, hEfin, hch, σ, hEcard, hσ, u, v, hc, hA₁u, d, hdL, hdT, μ, hμ0, hμord, hdμ⟩ :=
    h.exists_rootCoords_cartan_of_card_sylow hS2
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨κ, hκinj, hrep, hκ, haff⟩ := h.exists_kappa_of_card_sylow hS2 hR hc hA₁u
  obtain ⟨-, -, -, hNA, hNR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hdvd : 2 ^ f - 1 ∣ orderOf μ := by
    rw [hμord]
    exact sub_one_dvd_div_gcd (2 ^ f) (by omega)
  have hμpos : orderOf μ ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    have h1 := hμord
    rw [h0] at h1
    have h2 : (2 ^ f) ^ 2 - 1 < Nat.gcd 3 (2 ^ f + 1) :=
      (Nat.div_eq_zero_iff_lt (Nat.gcd_pos_of_pos_left _ (by norm_num))).mp h1.symm
    have h3 : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have h4 : 2 ^ f ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hF : Nat.card {x : E // σ x = x} = 2 ^ f :=
    LineCount.card_fixed_of_orderOf hσ (by omega) (orderOf_pow_orderOf_div hμpos hdvd)
  have hfin : (u3Omega L T R₂ t).Finite :=
    (Set.finite_range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁)).subset
      (h.u3Omega_subset_range_of_card_sylow hS2 hR)
  let : Fintype (u3Omega L T R₂ t) := hfin.fintype
  set S : Finset E := Finset.univ.image κ with hSdef
  have hScard : S.card = (u3Omega L T R₂ t).ncard := by
    rw [hSdef, Finset.card_image_of_injective _ hκinj, Finset.card_univ,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  set x₀ : u3Omega L T R₂ t := ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩ with hx₀
  have hκx₀ : κ x₀ = 0 := by
    rw [hκ x₀ 1 (one_mem _) (by rw [one_mul]), hc.u_one]
  have h0 : (0 : E) ∈ S := Finset.mem_image.mpr ⟨x₀, Finset.mem_univ _, hκx₀⟩
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  have hdA : d ∈ normalizer (szA L T t : Set G) := by
    have hdA₁ : d ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
      normalizer_le_normalizer_inf_centralizer (szT₁ L T) hdT
    have hdtN : d ∈ normalizer ((zpowers t : Subgroup G) : Set G) := by
      refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      exact ((Commute.zpow_right hdt k).eq).symm
    exact mem_normalizer_sup_of_mem_inf hdA₁ hdtN
  have hdY := hNA hdA
  have hμS : ∀ s ∈ S, μ * s ∈ S := by
    intro s hs
    obtain ⟨X, -, rfl⟩ := Finset.mem_image.mp hs
    refine Finset.mem_image.mpr ⟨u3OmegaAction L T R₂ t ⟨d, hdY⟩ X, Finset.mem_univ _, ?_⟩
    obtain ⟨w, hw, hXw⟩ := hrep X
    have hdw : d * w * d⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hdT w).mp hw
    have hpt : ((u3OmegaAction L T R₂ t ⟨d, hdY⟩ X : u3Omega L T R₂ t) : Subgroup G) =
        R₂ ⊔ zpowers ((d * w * d⁻¹) * t) := by
      rw [u3OmegaAction_apply, hXw, map_conj_sup_zpowers (hNR₂ hdA)]
      have e : d * (w * t) * d⁻¹ = (d * w * d⁻¹) * t := by
        calc d * (w * t) * d⁻¹ = (d * w * d⁻¹) * (d * t * d⁻¹) := by group
          _ = (d * w * d⁻¹) * t := by rw [hdt, mul_inv_cancel_right]
      rw [e]
    rw [hκ _ _ hdw hpt, hdμ w hw, hκ X w hw hXw]
  have hμpow : ∀ i : ℕ, ∀ s ∈ S, μ ^ i * s ∈ S := by
    intro i
    induction i with
    | zero => intro s hs; rwa [pow_zero, one_mul]
    | succ i ih => intro s hs; rw [pow_succ', mul_assoc]; exact hμS _ (ih s hs)
  have hSF : ∀ l, σ l = l → ∀ z ∈ S, l * z ∈ S := by
    intro l hl z hz
    by_cases hl0 : l = 0
    · rw [hl0, zero_mul]
      exact h0
    obtain ⟨i, rfl⟩ := LineCount.exists_pow_eq_of_fixed hσ (by omega) hμpos hdvd hl hl0
    exact hμpow i z hz
  have hlines := LineCount.card_erase_zero hσ (by omega) hF hSF
  rw [Finset.card_erase_of_mem h0, hScard] at hlines
  by_cases hk : 2 ^ f + 2 = 2 * (LineCount.lines (2 ^ f) S).card
  · right
    rw [hlines]
    calc 2 * ((LineCount.lines (2 ^ f) S).card * (2 ^ f - 1)) =
        (2 * (LineCount.lines (2 ^ f) S).card) * (2 ^ f - 1) := by ring
      _ = (2 ^ f - 1) * (2 ^ f + 2) := by rw [← hk]; ring
  · left
    have hadd : ∀ z ∈ S, ∀ c ∈ S, z + c ∈ S := by
      intro z hz c hc'
      obtain ⟨X, -, rfl⟩ := Finset.mem_image.mp hc'
      obtain ⟨y, hy, hyX⟩ := X.2
      have hyx₀ : u3OmegaAction L T R₂ t ⟨y, hy⟩ x₀ = X := by
        apply Subtype.ext
        rw [u3OmegaAction_apply]
        exact hyX.symm
      obtain ⟨φ, hφinj, -, c, hφc⟩ := haff ⟨y, hy⟩
      have hc0 : c = κ X := by rw [← hyx₀, hφc x₀, hκx₀, map_zero, zero_add]
      have hg : ∀ s ∈ S, φ s + c ∈ S := by
        intro s hs
        obtain ⟨X', -, rfl⟩ := Finset.mem_image.mp hs
        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hφc X'⟩
      have := LineCount.add_mem_of_affine hσ (by omega) hEcard hF hSF h0 hk φ hφinj c hg z hz
      rwa [hc0] at this
    have hEcard' : Nat.card E = 2 ^ (f * 2) := by rw [hEcard, pow_mul]
    obtain ⟨j, hj⟩ := LineCount.exists_card_eq_two_pow hEcard' h0 hadd
    exact ⟨j, hScard ▸ hj⟩

end Certificates

end U3Start

theorem not_two_pow_or_of_degree {f : ℕ} (hf : 2 ≤ f) :
    (¬ ∃ j : ℕ, ((2 ^ f) ^ 2 + 2) / 3 = 2 ^ j) ∧
      2 * (((2 ^ f) ^ 2 + 2) / 3 - 1) ≠ (2 ^ f - 1) * (2 ^ f + 2) := by
  set a := 2 ^ f with ha
  have ha4 : 4 ≤ a := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have e4 : a ^ 2 = 4 ^ f := by
    rw [ha, ← pow_mul, mul_comm, pow_mul]
    norm_num
  have h3 : 3 ∣ a ^ 2 + 2 := by
    rw [e4, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod]
    norm_num
  obtain ⟨N, hN⟩ := h3
  have hNd : (a ^ 2 + 2) / 3 = N := by rw [hN, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hNd]
  have h4 : a ^ 2 % 4 = 0 := by
    rw [e4, Nat.pow_mod, Nat.mod_self, zero_pow (by omega), Nat.zero_mod]
  have ha2 : 16 ≤ a ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · rintro ⟨j, rfl⟩
    rcases j with _ | _ | j
    · omega
    · omega
    · have : 2 ^ (j + 2) % 4 = 0 := by rw [pow_add]; norm_num
      omega
  · intro h
    have hN1 : 1 ≤ N := by omega
    have h5 : (a : ℤ) ^ 2 + 2 = 3 * N := by exact_mod_cast hN
    have h6 : 2 * ((N : ℤ) - 1) = ((a : ℤ) - 1) * ((a : ℤ) + 2) := by
      have : 2 * (N - 1) = (a - 1) * (a + 2) := h
      have ha1 : 1 ≤ a := by omega
      have e1 : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by push_cast [hN1]; ring
      have e2 : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by push_cast [ha1]; ring
      rw [← e1, ← e2]
      exact_mod_cast this
    have ha' : (4 : ℤ) ≤ a := by exact_mod_cast ha4
    nlinarith

section Certificates

theorem u3OmegaOddDegreeInput_holds : U3OmegaOddDegreeInput := by
  intro G _ _ L f t T R₂ h hS2 hR _ _ _ hN
  obtain ⟨hpow, hlin⟩ := not_two_pow_or_of_degree h.two_le
  rcases h.ncard_u3Omega_two_pow_or_of_card_sylow hS2 hR with ⟨j, hj⟩ | heq
  · exact hpow ⟨j, hN ▸ hj⟩
  · exact hlin (hN ▸ heq)

end Certificates

end CFSG.SeitzReduction.RankOne
