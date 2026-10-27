module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingComm
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearCentralizer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_semilinearCoords_cartan_odd_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (σ : E →+* E) (u w : G → E),
      U3SemilinearCoords L T f σ u w ∧
      ∃ d ∈ L, d ∈ normalizer (szT₁ L T : Set G) ∧ Odd (orderOf d) ∧ ∃ μ : E, μ ≠ 0 ∧
        orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) ∧
        ∀ y ∈ szT₁ L T, u (d * y * d⁻¹) = μ * u y := by
  obtain ⟨E, hE, hF, hch, σ, hcard, hσ, hfix, u, w, hc, hA, hborel, d₀, hd₀L, hd₀T, μ, hμ0, hμ,
    hd₀⟩ := h.exists_rootCoords_borel_of_card_sylow hS2
  have hS : U3SemilinearCoords L T f σ u w := ⟨hcard, hσ, hfix, hc, hA, fun x hxL hxT =>
    hc.exists_semilinear h.two_le hσ hcard hfix hA hborel hd₀L hd₀T hμ hd₀ hxL hxT⟩
  have hn0 : orderOf d₀ ≠ 0 := (orderOf_pos d₀).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hμodd : Odd (orderOf μ) := by
    have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hg : Nat.gcd 3 (2 ^ f + 1) ∣ (2 ^ f) ^ 2 - 1 := by
      refine (Nat.gcd_dvd_right 3 (2 ^ f + 1)).trans ⟨2 ^ f - 1, ?_⟩
      zify [hq, show 1 ≤ (2 ^ f) ^ 2 from Nat.one_le_pow _ _ (by omega)]
      ring
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      have hf0 : f ≠ 0 := by
        rintro rfl
        have := h.two_le
        omega
      have h2 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 hf0) two_ne_zero
      have h4 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
      obtain ⟨c, hc⟩ := h2
      exact ⟨c - 1, by omega⟩
    rw [hμ]
    exact Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd hg)
  refine ⟨E, hE, hF, hch, σ, u, w, hS, d₀ ^ 2 ^ k, pow_mem hd₀L _, pow_mem hd₀T _, ?_, μ ^ 2 ^ k,
    pow_ne_zero _ hμ0, ?_, fun y hy => U3RootCoords.u_conj_pow hd₀T hd₀ _ y hy⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hkm⟩, hkm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact hm
  · rw [Nat.Coprime.orderOf_pow (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hμodd)), hμ]

end U3Start

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem exists_tcoord (hU : U3U1Data G L f t T R₂ U₁) (hR : U3R2 G L (szT₁ L T) R₂ t f)
    {E : Type*} [Field E] {σ : E →+* E} {u w : G → E} (hc : U3RootCoords (szT₁ L T) σ u w)
    (hA₁u : ∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)) :
    ∃ a : G → E, (∀ x ∈ U₁, ∀ y ∈ U₁, a (x * y) = a x + a y) ∧
      (∀ x ∈ U₁, (a x = 0 ↔ x * (t * x * t⁻¹) ∈ R₂)) ∧
      (∀ x ∈ U₁, ∀ y ∈ szT₁ L T, ∀ r ∈ R₂, y * r = x * (t * x * t⁻¹) → a x = u y) ∧
      (∀ x ∈ U₁, a (t * x * t⁻¹) = a x) ∧
      ∀ n ∈ normalizer (szT₁ L T : Set G), n ∈ normalizer (R₂ : Set G) → n * t = t * n →
        ∀ φ : E → E, (∀ y ∈ szT₁ L T, u (n * y * n⁻¹) = φ (u y)) →
          ∀ x ∈ U₁, a (n * x * n⁻¹) = φ (a x) := by
  classical
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have hA₁R : szA₁ (szT₁ L T) ≤ R₂ := hR.le
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  have hUR : ∀ x ∈ U₁, ∀ r ∈ R₂, x * r = r * x := fun x hx r hr =>
    (mem_centralizer_iff.mp (hU.le_centralizer hx) r hr).symm
  have hkey : ∀ x : G, t * (t * x * t⁻¹) * t⁻¹ = x := by
    intro x
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt]; group
  have hdecTR : ∀ z ∈ szT₁ L T ⊔ R₂, ∃ y ∈ szT₁ L T, ∃ r ∈ R₂, y * r = z := fun z hz =>
    hR.mem_sup_iff.mp hz
  choose! yT hyT rT hrT hyr using hdecTR
  have hũeq : ∀ z ∈ szT₁ L T ⊔ R₂, ∀ y ∈ szT₁ L T, ∀ r ∈ R₂, y * r = z → u (yT z) = u y := by
    intro z hz y hy r hr hyrz
    have h1 : y⁻¹ * yT z = r * (rT z)⁻¹ := by
      calc y⁻¹ * yT z = y⁻¹ * (yT z * rT z) * (rT z)⁻¹ := by group
        _ = y⁻¹ * (y * r) * (rT z)⁻¹ := by rw [hyr z hz, hyrz]
        _ = r * (rT z)⁻¹ := by group
    have h2 : y⁻¹ * yT z ∈ szA₁ (szT₁ L T) := by
      rw [← hR.inf]
      exact mem_inf.mpr ⟨mul_mem (inv_mem hy) (hyT z hz), h1 ▸ mul_mem hr (inv_mem (hrT z hz))⟩
    have h3 := (hA₁u _ (szA₁_le _ h2)).mp h2
    rw [hc.u_mul_inv hy (hyT z hz)] at h3
    linear_combination h3
  have hũmul : ∀ z ∈ szT₁ L T ⊔ R₂, ∀ z' ∈ szT₁ L T ⊔ R₂,
      u (yT (z * z')) = u (yT z) + u (yT z') := by
    intro z hz z' hz'
    have e : (yT z * yT z') * (rT z * rT z') = z * z' := by
      calc (yT z * yT z') * (rT z * rT z') = yT z * (yT z' * rT z) * rT z' := by group
        _ = yT z * (rT z * yT z') * rT z' := by rw [hR.commT₁ _ (hyT z' hz') _ (hrT z hz)]
        _ = (yT z * rT z) * (yT z' * rT z') := by group
        _ = z * z' := by rw [hyr z hz, hyr z' hz']
    rw [hũeq (z * z') (mul_mem hz hz') _ (mul_mem (hyT z hz) (hyT z' hz')) _
      (mul_mem (hrT z hz) (hrT z' hz')) e, hc.mul_u _ (hyT z hz) _ (hyT z' hz')]
  have hũR : ∀ z ∈ szT₁ L T ⊔ R₂, (u (yT z) = 0 ↔ z ∈ R₂) := by
    intro z hz
    constructor
    · intro h0
      have hyA : yT z ∈ szA₁ (szT₁ L T) := (hA₁u _ (hyT z hz)).mpr h0
      rw [← hyr z hz]
      exact mul_mem (hA₁R hyA) (hrT z hz)
    · intro hzR
      refine (hA₁u _ (hyT z hz)).mp ?_
      rw [← hR.inf]
      have e : yT z = z * (rT z)⁻¹ := by
        calc yT z = (yT z * rT z) * (rT z)⁻¹ := by group
          _ = z * (rT z)⁻¹ := by rw [hyr z hz]
      exact mem_inf.mpr ⟨hyT z hz, e ▸ mul_mem hzR (inv_mem (hrT z hz))⟩
  have hũn : ∀ n ∈ normalizer (szT₁ L T : Set G), n ∈ normalizer (R₂ : Set G) → ∀ φ : E → E,
      (∀ y ∈ szT₁ L T, u (n * y * n⁻¹) = φ (u y)) →
      ∀ z ∈ szT₁ L T ⊔ R₂, u (yT (n * z * n⁻¹)) = φ (u (yT z)) := by
    intro n hnT hnR φ hφ z hz
    have hy' : n * yT z * n⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hnT _).mp (hyT z hz)
    have hr' : n * rT z * n⁻¹ ∈ R₂ := (mem_normalizer_iff.mp hnR _).mp (hrT z hz)
    have e : (n * yT z * n⁻¹) * (n * rT z * n⁻¹) = n * z * n⁻¹ := by
      calc (n * yT z * n⁻¹) * (n * rT z * n⁻¹) = n * (yT z * rT z) * n⁻¹ := by group
        _ = n * z * n⁻¹ := by rw [hyr z hz]
    rw [hũeq _ (e ▸ mul_mem (mem_sup_left hy') (mem_sup_right hr')) _ hy' _ hr' e,
      hφ _ (hyT z hz)]
  have hψ : ∀ x ∈ U₁, x * (t * x * t⁻¹) ∈ szT₁ L T ⊔ R₂ := by
    intro x hx
    have hx' : t * x * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp htU _).mp hx
    refine hU.mem_sup_of_comm_mem hR htt (mul_mem hx hx') ?_
    have e : x * (t * x * t⁻¹) * t * (x * (t * x * t⁻¹))⁻¹ * t⁻¹ =
        x * (t * x * t⁻¹) * x⁻¹ * (t * x * t⁻¹)⁻¹ := by
      calc x * (t * x * t⁻¹) * t * (x * (t * x * t⁻¹))⁻¹ * t⁻¹
          = x * (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹)⁻¹ * (t * x * t⁻¹)⁻¹ := by group
        _ = x * (t * x * t⁻¹) * x⁻¹ * (t * x * t⁻¹)⁻¹ := by rw [hkey]
    rw [e]
    exact hU.comm_mem x hx _ hx'
  have hψmul : ∀ x ∈ U₁, ∀ x' ∈ U₁, ∃ c ∈ R₂, (x * x') * (t * (x * x') * t⁻¹) =
      (x * (t * x * t⁻¹)) * (x' * (t * x' * t⁻¹)) * c := by
    intro x hx x' hx'
    have hy : t * x * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp htU _).mp hx
    have hy' : t * x' * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp htU _).mp hx'
    have hcR := hU.comm_mem _ (inv_mem hx') _ (inv_mem hy)
    refine ⟨x'⁻¹ * (t * x * t⁻¹)⁻¹ * x'⁻¹⁻¹ * (t * x * t⁻¹)⁻¹⁻¹, hcR, ?_⟩
    have hcy := hUR _ hy' _ hcR
    calc (x * x') * (t * (x * x') * t⁻¹)
        = x * (t * x * t⁻¹) * x' * ((x'⁻¹ * (t * x * t⁻¹)⁻¹ * x'⁻¹⁻¹ * (t * x * t⁻¹)⁻¹⁻¹) *
            (t * x' * t⁻¹)) := by group
      _ = x * (t * x * t⁻¹) * x' * ((t * x' * t⁻¹) *
            (x'⁻¹ * (t * x * t⁻¹)⁻¹ * x'⁻¹⁻¹ * (t * x * t⁻¹)⁻¹⁻¹)) := by rw [hcy]
      _ = _ := by group
  refine ⟨fun x => u (yT (x * (t * x * t⁻¹))), fun x hx x' hx' => ?_, fun x hx => hũR _ (hψ x hx),
    fun x hx y hy r hr hyr => hũeq _ (hψ x hx) y hy r hr hyr, fun x hx => ?_,
    fun n hnT hnR hnt φ hφ x hx => ?_⟩
  · obtain ⟨c, hcR, hce⟩ := hψmul x hx x' hx'
    beta_reduce
    rw [hce, hũmul _ (mul_mem (hψ x hx) (hψ x' hx')) c (mem_sup_right hcR),
      (hũR c (mem_sup_right hcR)).mpr hcR, add_zero, hũmul _ (hψ x hx) _ (hψ x' hx')]
  · have hx' : t * x * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp htU _).mp hx
    have hc : (t * x * t⁻¹)⁻¹ * x⁻¹ * (t * x * t⁻¹)⁻¹⁻¹ * x⁻¹⁻¹ ∈ R₂ :=
      hU.comm_mem _ (inv_mem hx') _ (inv_mem hx)
    have e : (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) =
        (x * (t * x * t⁻¹)) * ((t * x * t⁻¹)⁻¹ * x⁻¹ * (t * x * t⁻¹)⁻¹⁻¹ * x⁻¹⁻¹) := by
      rw [hkey]
      group
    beta_reduce
    rw [e, hũmul _ (hψ x hx) _ (mem_sup_right hc), (hũR _ (mem_sup_right hc)).mpr hc, add_zero]
  · have htn : t * (n * x * n⁻¹) * t⁻¹ = n * (t * x * t⁻¹) * n⁻¹ := by
      calc t * (n * x * n⁻¹) * t⁻¹ = (t * n) * x * (t * n)⁻¹ := by group
        _ = (n * t) * x * (n * t)⁻¹ := by rw [hnt]
        _ = n * (t * x * t⁻¹) * n⁻¹ := by group
    have e : (n * x * n⁻¹) * (t * (n * x * n⁻¹) * t⁻¹) = n * (x * (t * x * t⁻¹)) * n⁻¹ := by
      rw [htn]
      group
    beta_reduce
    rw [e, hũn n hnT hnR φ hφ _ (hψ x hx)]

end U3U1Data

theorem U3R2.exists_chi_of_odd {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G}
    {f : ℕ} (hR : U3R2 G L T₁ R₂ t f) (hR2 : ∀ r ∈ R₂, r ^ 2 = 1) (hf : 1 ≤ f) {E : Type*}
    [Field E] [Finite E] [CharP E 2] {σ : E →+* E} {u w : G → E} (hc : U3RootCoords T₁ σ u w)
    (hσ : ∀ x, σ x = x ^ (2 ^ f)) (hE : Nat.card E = (2 ^ f) ^ 2)
    (hA₁u : ∀ y ∈ T₁, (y ∈ szA₁ T₁ ↔ u y = 0)) {d : G} (hdodd : Odd (orderOf d))
    (hdT : d ∈ normalizer (T₁ : Set G)) (hdR : d ∈ normalizer (R₂ : Set G)) (hdt : d * t = t * d)
    {μ : E} (hdu : ∀ y ∈ T₁, u (d * y * d⁻¹) = μ * u y) :
    ∃ χ₁ χ₂ : G → E, (∀ r ∈ R₂, ∀ r' ∈ R₂, χ₁ (r * r') = χ₁ r + χ₁ r') ∧
      (∀ r ∈ R₂, ∀ r' ∈ R₂, χ₂ (r * r') = χ₂ r + χ₂ r') ∧
      (∀ r ∈ R₂, χ₁ r = 0 → χ₂ r = 0 → r = 1) ∧
      (∀ r ∈ R₂, χ₁ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ₁ r) ∧
      (∀ r ∈ R₂, χ₂ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ₂ r) ∧
      (∀ b ∈ szA₁ T₁, χ₁ b = 0) ∧ (∀ b ∈ szA₁ T₁, χ₂ b = w b) ∧
      (∀ r ∈ R₂, χ₁ (t * r * t⁻¹) = χ₁ r) ∧ (∀ r ∈ R₂, χ₂ (t * r * t⁻¹) = χ₁ r + χ₂ r) ∧
      (∀ r ∈ R₂, σ (χ₁ r) = χ₁ r) ∧ (∀ r ∈ R₂, σ (χ₂ r) = χ₂ r) := by
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hA₁R : szA₁ T₁ ≤ R₂ := hR.le
  have hdA : d ∈ normalizer (szA₁ T₁ : Set G) := mem_normalizer_szA₁_of_mem_normalizer hdT
  have hNμ : μ * σ μ = μ ^ (2 ^ f + 1) := by rw [hσ, pow_succ']
  have hdv : ∀ b ∈ szA₁ T₁, w (d * b * d⁻¹) = μ ^ (2 ^ f + 1) * w b := by
    intro b hb
    rw [← hNμ]
    exact hc.v_conj_of_u_eq_zero hσ hE hq2 hdT hdu (szA₁_le _ hb) ((hA₁u b (szA₁_le _ hb)).mp hb)
  have hvadd : ∀ b ∈ szA₁ T₁, ∀ b' ∈ szA₁ T₁, w (b * b') = w b + w b' :=
    fun b hb b' hb' => hc.v_mul_of_u_eq_zero (szA₁_le _ hb) (szA₁_le _ hb')
      ((hA₁u b (szA₁_le _ hb)).mp hb)
  have hv1 : w 1 = 0 := by
    have := hvadd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    linear_combination -this
  have hvinj : ∀ b ∈ szA₁ T₁, w b = 0 → b = 1 := by
    intro b hb hvb
    exact hc.inj _ (szA₁_le _ hb) _ (one_mem _)
      (by rw [(hA₁u b (szA₁_le _ hb)).mp hb, hc.u_one]) (by rw [hvb, hv1])
  have hρmul : ∀ r ∈ R₂, ∀ r' ∈ R₂, (r * r') * t * (r * r')⁻¹ * t =
      (r * t * r⁻¹ * t) * (r' * t * r'⁻¹ * t) := by
    intro r hr r' hr'
    have e1 : r' * t * r'⁻¹ * t * t = r' * t * r'⁻¹ := by
      rw [mul_assoc (r' * t * r'⁻¹) t t, htt, mul_one]
    calc (r * r') * t * (r * r')⁻¹ * t = r * (r' * t * r'⁻¹) * r⁻¹ * t := by group
      _ = r * (r' * t * r'⁻¹ * t * t) * r⁻¹ * t := by rw [e1]
      _ = (r * (r' * t * r'⁻¹ * t)) * t * r⁻¹ * t := by group
      _ = ((r' * t * r'⁻¹ * t) * r) * t * r⁻¹ * t := by
          rw [hR.comm r hr _ (hA₁R (hR.rho_mem r' hr'))]
      _ = (r' * t * r'⁻¹ * t) * (r * t * r⁻¹ * t) := by group
      _ = (r * t * r⁻¹ * t) * (r' * t * r'⁻¹ * t) :=
          hR.comm _ (hA₁R (hR.rho_mem r' hr')) _ (hA₁R (hR.rho_mem r hr))
  have hρd : ∀ r : G, (d * r * d⁻¹) * t * (d * r * d⁻¹)⁻¹ * t = d * (r * t * r⁻¹ * t) * d⁻¹ := by
    intro r
    have hdtd : d⁻¹ * t * d = t := by rw [mul_assoc, ← hdt, inv_mul_cancel_left]
    calc (d * r * d⁻¹) * t * (d * r * d⁻¹)⁻¹ * t =
        d * r * (d⁻¹ * t * d) * r⁻¹ * (d⁻¹ * t * d) * d⁻¹ := by group
      _ = d * (r * t * r⁻¹ * t) * d⁻¹ := by rw [hdtd]; group
  obtain ⟨π, hπA, hπid, hπmul, hπd⟩ := exists_proj_of_odd hA₁R hR.comm hR2 hdodd hdR hdA
  refine ⟨fun r => w (r * t * r⁻¹ * t), fun r => w (π r), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro r hr r' hr'
    beta_reduce
    rw [hρmul r hr r' hr', hvadd _ (hR.rho_mem r hr) _ (hR.rho_mem r' hr')]
  · intro r hr r' hr'
    beta_reduce
    rw [hπmul r hr r' hr', hvadd _ (hπA r hr) _ (hπA r' hr')]
  · intro r hr h1 h2
    beta_reduce at h1 h2
    have hρ1 : r * t * r⁻¹ * t = 1 := hvinj _ (hR.rho_mem r hr) h1
    have hrt : r * t = t * r := by
      calc r * t = (r * t * r⁻¹ * t) * t⁻¹ * r := by group
        _ = t * r := by rw [hρ1, one_mul, htinv]
    have hrA := hR.rho_ker r hr hrt
    rw [hπid r hrA] at h2
    exact hvinj r hrA h2
  · intro r hr
    beta_reduce
    rw [hρd r, hdv _ (hR.rho_mem r hr)]
  · intro r hr
    beta_reduce
    rw [hπd r hr, hdv _ (hπA r hr)]
  · intro b hb
    beta_reduce
    have hbt : b * t = t * b := hR.szA₁_comm_t hb
    rw [show b * t * b⁻¹ * t = 1 by rw [hbt, mul_inv_cancel_right, htt], hv1]
  · intro b hb
    beta_reduce
    rw [hπid b hb]
  · intro r hr
    beta_reduce
    have hρt := hR.szA₁_comm_t (hR.rho_mem r hr)
    rw [show (t * r * t⁻¹) * t * (t * r * t⁻¹)⁻¹ * t = t * (r * t * r⁻¹ * t) * t⁻¹ by group,
      ← hρt, mul_inv_cancel_right]
  · intro r hr
    beta_reduce
    have hρA := hR.rho_mem r hr
    have hρinv : (r * t * r⁻¹ * t)⁻¹ = r * t * r⁻¹ * t :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hR.sq_A₁ _ hρA)
    have e : t * r * t⁻¹ = (r * t * r⁻¹ * t) * r := by
      rw [← hρinv, show (r * t * r⁻¹ * t)⁻¹ * r = t⁻¹ * r * t⁻¹ by group, htinv]
    rw [e, hπmul _ (hA₁R hρA) _ hr, hπid _ hρA, hvadd _ hρA _ (hπA r hr)]
  · intro r hr
    have hρA := hR.rho_mem r hr
    exact hc.sigma_v_of_u_eq_zero (szA₁_le _ hρA) ((hA₁u _ (szA₁_le _ hρA)).mp hρA)
  · intro r hr
    have hπr := hπA r hr
    exact hc.sigma_v_of_u_eq_zero (szA₁_le _ hπr) ((hA₁u _ (szA₁_le _ hπr)).mp hπr)

structure U3PencilCoords {G : Type} [Group G] (L T R₂ U₁ : Subgroup G) (t : G) (f : ℕ)
    {E : Type} [Field E] (σ : E →+* E) (u w : G → E) (d : G) (μ : E) (a χ₁ χ₂ : G → E) :
    Prop where
  semilinear : U3SemilinearCoords L T f σ u w
  mu_ne_zero : μ ≠ 0
  orderOf_mu : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)
  d_mem : d ∈ L
  d_mem_normalizer : d ∈ normalizer (szT₁ L T : Set G)
  odd_orderOf_d : Odd (orderOf d)
  d_comm : d * t = t * d
  d_mem_normalizer_R₂ : d ∈ normalizer (R₂ : Set G)
  d_mem_normalizer_U₁ : d ∈ normalizer (U₁ : Set G)
  u_conj_d : ∀ y ∈ szT₁ L T, u (d * y * d⁻¹) = μ * u y
  a_mul : ∀ x ∈ U₁, ∀ y ∈ U₁, a (x * y) = a x + a y
  a_eq_zero_iff : ∀ x ∈ U₁, (a x = 0 ↔ x * (t * x * t⁻¹) ∈ R₂)
  a_spec : ∀ x ∈ U₁, ∀ y ∈ szT₁ L T, ∀ r ∈ R₂, y * r = x * (t * x * t⁻¹) → a x = u y
  a_conj_t : ∀ x ∈ U₁, a (t * x * t⁻¹) = a x
  a_conj : ∀ n ∈ normalizer (szT₁ L T : Set G), n ∈ normalizer (R₂ : Set G) → n * t = t * n →
    ∀ φ : E → E, (∀ y ∈ szT₁ L T, u (n * y * n⁻¹) = φ (u y)) →
      ∀ x ∈ U₁, a (n * x * n⁻¹) = φ (a x)
  chi₁_mul : ∀ r ∈ R₂, ∀ r' ∈ R₂, χ₁ (r * r') = χ₁ r + χ₁ r'
  chi₂_mul : ∀ r ∈ R₂, ∀ r' ∈ R₂, χ₂ (r * r') = χ₂ r + χ₂ r'
  chi_inj : ∀ r ∈ R₂, χ₁ r = 0 → χ₂ r = 0 → r = 1
  chi₁_conj : ∀ r ∈ R₂, χ₁ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ₁ r
  chi₂_conj : ∀ r ∈ R₂, χ₂ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ₂ r
  chi₁_of_mem_szA₁ : ∀ b ∈ szA₁ (szT₁ L T), χ₁ b = 0
  chi₂_of_mem_szA₁ : ∀ b ∈ szA₁ (szT₁ L T), χ₂ b = w b
  chi₁_conj_t : ∀ r ∈ R₂, χ₁ (t * r * t⁻¹) = χ₁ r
  chi₂_conj_t : ∀ r ∈ R₂, χ₂ (t * r * t⁻¹) = χ₁ r + χ₂ r
  sigma_chi₁ : ∀ r ∈ R₂, σ (χ₁ r) = χ₁ r
  sigma_chi₂ : ∀ r ∈ R₂, σ (χ₂ r) = χ₂ r

namespace U3PencilCoords

variable {G : Type} [Group G] {L T R₂ U₁ : Subgroup G} {t : G} {f : ℕ} {E : Type} [Field E]
  {σ : E →+* E} {u w : G → E} {d : G} {μ : E} {a χ₁ χ₂ : G → E}

theorem a_one (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂) : a 1 = 0 := by
  have h := hP.a_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  linear_combination -h

theorem a_inv (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂) {x : G} (hx : x ∈ U₁) :
    a x⁻¹ = -a x := by
  have h := hP.a_mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, hP.a_one] at h
  linear_combination -h

theorem a_eq_zero_of_mem (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂)
    (hRU : R₂ ≤ U₁) (htR : ∀ r ∈ R₂, t * r * t⁻¹ ∈ R₂) {r : G} (hr : r ∈ R₂) : a r = 0 :=
  (hP.a_eq_zero_iff r (hRU hr)).mpr (mul_mem hr (htR r hr))

theorem a_conj_d (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂) {x : G} (hx : x ∈ U₁) :
    a (d * x * d⁻¹) = μ * a x :=
  hP.a_conj d hP.d_mem_normalizer hP.d_mem_normalizer_R₂ hP.d_comm (fun z => μ * z) hP.u_conj_d x hx

theorem chi₁_one (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂) : χ₁ 1 = 0 := by
  have h := hP.chi₁_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  linear_combination -h

theorem chi₂_one (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂) : χ₂ 1 = 0 := by
  have h := hP.chi₂_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  linear_combination -h

theorem eq_of_chi_eq [CharP E 2] (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂)
    (hR2 : ∀ r ∈ R₂, r ^ 2 = 1) {r r' : G} (hr : r ∈ R₂) (hr' : r' ∈ R₂) (h₁ : χ₁ r = χ₁ r')
    (h₂ : χ₂ r = χ₂ r') : r = r' := by
  have hinv : r'⁻¹ = r' := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hR2 r' hr')
  have e1 : χ₁ (r * r'⁻¹) = 0 := by
    rw [hinv, hP.chi₁_mul r hr r' hr', h₁]
    exact CharTwo.add_self_eq_zero _
  have e2 : χ₂ (r * r'⁻¹) = 0 := by
    rw [hinv, hP.chi₂_mul r hr r' hr', h₂]
    exact CharTwo.add_self_eq_zero _
  have h1 := hP.chi_inj _ (mul_mem hr (inv_mem hr')) e1 e2
  rw [← mul_inv_eq_one]
  exact h1

theorem exists_conj_outer [Finite E] [CharP E 2] [Finite G]
    (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G} (hxT : x ∈ T)
    (hx : x ∉ szT₁ L T ⊔ zpowers t) (hx2 : x ^ 2 ∈ szT₁ L T ⊔ zpowers t)
    (hxR : x ∈ normalizer (R₂ : Set G)) :
    ∃ m : E, m * σ m = 1 ∧ ∀ y ∈ U₁, a (x * y * x⁻¹) = m * σ (a y) := by
  have hxN : x ∈ normalizer (szT₁ L T : Set G) := (h.start_of_card_sylow hS2).2.2.2.1 hxT
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (h.le hxT)
  obtain ⟨m, -, τ, e, hxd⟩ := hP.semilinear.semilinear x (h.le_normalizer hxT) hxN
  obtain ⟨hτ, hN⟩ := hP.semilinear.sigma_of_sq_mem h hS2 hxT hx hx2 hxd
  exact ⟨m, hN, hP.a_conj x hxN hxR hxt (fun z => m * σ z) fun y hy => by
    rw [(hxd y hy).1, hτ]⟩

end U3PencilCoords

section Certificates


namespace U3EndingData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}
  {s : G}

theorem exists_pencilCoords (hD : U3EndingData G L f t T R₂ U₁ s) :
    ∃ (E : Type) (_ : Field E) (_ : Fintype E) (_ : CharP E 2) (σ : E →+* E) (u w : G → E)
      (d : G) (μ : E) (a χ₁ χ₂ : G → E), U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂ := by
  classical
  have h := hD.start
  obtain ⟨E, hF, hFin, hch, σ, u, w, hS, d, hdL, hdT, hdodd, μ, hμ0, hμ, hdu⟩ :=
    h.exists_semilinearCoords_cartan_odd_of_card_sylow hD.card_sylow
  let _ : Fintype E := Fintype.ofFinite E
  obtain ⟨hdR, hdU⟩ := hD.mem_normalizer_of_mem_borel hdL hdT
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  obtain ⟨a, ha_mul, ha0, haspec, hat, haconj⟩ :=
    hD.u1.exists_tcoord hD.r2 hS.coords hS.mem_szA₁_iff
  obtain ⟨χ₁, χ₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    hD.r2.exists_chi_of_odd hD.u1.sq_R₂ (by have := h.two_le; omega) hS.coords hS.sigma hS.card
      hS.mem_szA₁_iff hdodd hdT hdR hdt hdu
  exact ⟨E, hF, inferInstance, hch, σ, u, w, d, μ, a, χ₁, χ₂, hS, hμ0, hμ, hdL, hdT, hdodd, hdt,
    hdR, hdU, hdu, ha_mul, ha0, haspec, hat, haconj, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end U3EndingData

end Certificates

end CFSG.SeitzReduction.RankOne
