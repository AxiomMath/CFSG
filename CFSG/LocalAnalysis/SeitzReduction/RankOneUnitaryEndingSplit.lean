module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingDecomp
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSplitComm
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSplitCompl
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearField
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEnding

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ : Subgroup G} {σ : E →+* E}
  {u v : G → E}

theorem v_conj_of_u_eq_zero [Finite E] [CharP E 2] (hc : U3RootCoords T₁ σ u v) {q : ℕ}
    (hσ : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2) (hq : 2 ≤ q) {n : G}
    (hnT : n ∈ normalizer (T₁ : Set G)) {μ : E} (hnu : ∀ y ∈ T₁, u (n * y * n⁻¹) = μ * u y)
    {b : G} (hb : b ∈ T₁) (hbu : u b = 0) : v (n * b * n⁻¹) = μ * σ μ * v b := by
  have hσb : σ (v b) = v b := hc.sigma_v_of_u_eq_zero hb hbu
  obtain ⟨c, hcc⟩ := SemilinearField.exists_mul_sigma_eq hσ hE hq hσb
  obtain ⟨y, hy, hyu⟩ := hc.u_surj c
  have hy2 : y ^ 2 = b := hc.inj _ (pow_mem hy 2) _ hb (by rw [(hc.sq hy).1, hbu])
    (by rw [(hc.sq hy).2, hyu, hcc])
  have hny : n * y * n⁻¹ ∈ T₁ := (mem_normalizer_iff.mp hnT y).mp hy
  have e : n * b * n⁻¹ = (n * y * n⁻¹) ^ 2 := by
    rw [← hy2, pow_two, pow_two]
    group
  rw [e, (hc.sq hny).2, hnu y hy, hyu, map_mul, ← hcc]
  ring

end U3RootCoords

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_rootCoords_cartan_odd_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (σ : E →+* E),
      Nat.card E = (2 ^ f) ^ 2 ∧ (∀ x, σ x = x ^ (2 ^ f)) ∧
      ∃ u v : G → E, U3RootCoords (szT₁ L T) σ u v ∧
        (∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)) ∧
        ∃ d ∈ L, d ∈ normalizer (szT₁ L T : Set G) ∧ Odd (orderOf d) ∧ ∃ μ : E, μ ≠ 0 ∧
          orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) ∧
          ∀ y ∈ szT₁ L T, u (d * y * d⁻¹) = μ * u y := by
  obtain ⟨E, hF, hFin, hch, σ, hE, hσ, u, v, hc, hA, d₀, hd₀L, hd₀T, μ, hμ0, hμ, hd₀⟩ :=
    h.exists_rootCoords_cartan_of_card_sylow hS2
  have hn0 : orderOf d₀ ≠ 0 := (orderOf_pos d₀).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hpow : ∀ j : ℕ, ∀ y ∈ szT₁ L T, d₀ ^ j * y * (d₀ ^ j)⁻¹ ∈ szT₁ L T ∧
      u (d₀ ^ j * y * (d₀ ^ j)⁻¹) = μ ^ j * u y := by
    intro j
    induction j with
    | zero => intro y hy; simp [hy]
    | succ j ih =>
      intro y hy
      obtain ⟨h1, h2⟩ := ih y hy
      have e : d₀ ^ (j + 1) * y * (d₀ ^ (j + 1))⁻¹ = d₀ * (d₀ ^ j * y * (d₀ ^ j)⁻¹) * d₀⁻¹ := by
        group
      rw [e]
      refine ⟨(mem_normalizer_iff.mp hd₀T _).mp h1, ?_⟩
      rw [hd₀ _ h1, h2, pow_succ]
      ring
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
  refine ⟨E, hF, hFin, hch, σ, hE, hσ, u, v, hc, hA, d₀ ^ 2 ^ k, pow_mem hd₀L _,
    pow_mem hd₀T _, ?_, μ ^ 2 ^ k, pow_ne_zero _ hμ0, ?_, fun y hy => (hpow _ y hy).2⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hkm⟩, hkm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact hm
  · rw [Nat.Coprime.orderOf_pow (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hμodd)), hμ]

end U3Start

namespace U3EndingData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}
  {s : G}

theorem exists_coords_of_split
    (hD : U3EndingData G L f t T R₂ U₁ s) {J₁ J₂ : Subgroup G} (hJ : J₁ ⊔ J₂ = U₁)
    (hJinf : J₁ ⊓ J₂ = R₂) (ht₁ : ∀ x ∈ J₁, t * x * t⁻¹ ∈ J₂) (ht₂ : ∀ x ∈ J₂, t * x * t⁻¹ ∈ J₁)
    (hK : ∀ k ∈ L, k ∈ normalizer (szT₁ L T : Set G) → Odd (orderOf k) →
      k ∈ normalizer (J₁ : Set G)) :
    ∃ (E : Type) (_ : Field E) (_ : Fintype E) (d : G) (μ : E) (a χ₁ χ₂ : G → E),
      Fintype.card E = (2 ^ f) ^ 2 ∧ μ ≠ 0 ∧
      orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) ∧
      d ∈ L ∧ d ∈ normalizer (szT₁ L T : Set G) ∧ Odd (orderOf d) ∧
      d ∈ normalizer (J₁ : Set G) ∧ d ∈ normalizer (R₂ : Set G) ∧
      (∀ x ∈ U₁, ∀ y ∈ U₁, a (x * y) = a x + a y) ∧ (∀ r ∈ R₂, a r = 0) ∧
      (∀ x ∈ J₁, a x = 0 → x ∈ R₂) ∧
      (∀ z : E, ∃ x ∈ J₁, a x = z) ∧ (∀ x ∈ U₁, a (d * x * d⁻¹) = μ * a x) ∧
      (∀ r ∈ R₂, ∀ r' ∈ R₂, χ₁ (r * r') = χ₁ r + χ₁ r') ∧
      (∀ r ∈ R₂, ∀ r' ∈ R₂, χ₂ (r * r') = χ₂ r + χ₂ r') ∧
      (∀ r ∈ R₂, χ₁ r = 0 → χ₂ r = 0 → r = 1) ∧
      (∀ r ∈ R₂, χ₁ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ₁ r) ∧
      (∀ r ∈ R₂, χ₂ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ₂ r) := by
  classical
  have h := hD.start
  have hS2 := hD.card_sylow
  have hR := hD.r2
  have hU := hD.u1
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hf : 2 ≤ f := h.two_le
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hJ₁U : J₁ ≤ U₁ := hJ ▸ le_sup_left
  have hRJ₁ : R₂ ≤ J₁ := hJinf ▸ inf_le_left
  have hRJ₂ : R₂ ≤ J₂ := hJinf ▸ inf_le_right
  have hUR : ∀ x ∈ U₁, ∀ r ∈ R₂, x * r = r * x := fun x hx r hr =>
    (mem_centralizer_iff.mp (hU.le_centralizer hx) r hr).symm
  have hA₁R : szA₁ (szT₁ L T) ≤ R₂ := hR.le
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  have hkey : ∀ x : G, t * (t * x * t⁻¹) * t⁻¹ = x := by
    intro x
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt]; group
  obtain ⟨E, _, _, _, σ, hcardE, hσ, u, v, hc, hA₁u, d, hdL, hdT, hdodd, μ, hμ0, hμ, hdu⟩ :=
    h.exists_rootCoords_cartan_odd_of_card_sylow hS2
  let _ : Fintype E := Fintype.ofFinite E
  have hKE : Fintype.card E = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hcardE]
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  have hdJ₁ : d ∈ normalizer (J₁ : Set G) := hK d hdL hdT hdodd
  have hdJ₂ : d ∈ normalizer (J₂ : Set G) := by
    have key : ∀ c : G, c * t = t * c → c ∈ normalizer (J₁ : Set G) →
        ∀ x ∈ J₂, c * x * c⁻¹ ∈ J₂ := by
      intro c hct hc' x hx
      have hx' : t⁻¹ * x * t ∈ J₁ := by
        have := ht₂ x hx
        rw [htinv] at this ⊢
        exact this
      have h1 := ht₁ _ ((mem_normalizer_iff.mp hc' _).mp hx')
      have hctc : t * c * t⁻¹ = c := by rw [← hct, mul_inv_cancel_right]
      have e : t * (c * (t⁻¹ * x * t) * c⁻¹) * t⁻¹ = (t * c * t⁻¹) * x * (t * c * t⁻¹)⁻¹ := by
        group
      rw [e, hctc] at h1
      exact h1
    have hdt' : d⁻¹ * t = t * d⁻¹ := by
      calc d⁻¹ * t = d⁻¹ * (t * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * t) * d⁻¹ := by rw [hdt]
        _ = t * d⁻¹ := by group
    refine mem_normalizer_iff.mpr fun x => ⟨fun hx => key d hdt hdJ₁ x hx, fun hx => ?_⟩
    have := key d⁻¹ hdt' (inv_mem hdJ₁) _ hx
    rwa [show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group] at this
  have hdR : d ∈ normalizer (R₂ : Set G) := by
    rw [← hJinf]
    refine mem_normalizer_iff.mpr fun x => ?_
    exact and_congr (mem_normalizer_iff.mp hdJ₁ x) (mem_normalizer_iff.mp hdJ₂ x)
  have hdA : d ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    mem_normalizer_szA₁_of_mem_normalizer hdT
  have hNμ : μ * σ μ = μ ^ (2 ^ f + 1) := by rw [hσ, pow_succ']
  have hdv : ∀ b ∈ szA₁ (szT₁ L T), v (d * b * d⁻¹) = μ ^ (2 ^ f + 1) * v b := by
    intro b hb
    rw [← hNμ]
    exact hc.v_conj_of_u_eq_zero hσ hcardE hq2 hdT hdu (szA₁_le _ hb)
      ((hA₁u b (szA₁_le _ hb)).mp hb)
  have hvadd : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), v (b * b') = v b + v b' :=
    fun b hb b' hb' => hc.v_mul_of_u_eq_zero (szA₁_le _ hb) (szA₁_le _ hb')
      ((hA₁u b (szA₁_le _ hb)).mp hb)
  have hv1 : v 1 = 0 := by
    have := hvadd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    linear_combination -this
  have hvinj : ∀ b ∈ szA₁ (szT₁ L T), v b = 0 → b = 1 := by
    intro b hb hvb
    exact hc.inj _ (szA₁_le _ hb) _ (one_mem _)
      (by rw [(hA₁u b (szA₁_le _ hb)).mp hb, hc.u_one]) (by rw [hvb, hv1])
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
  have hũR : ∀ r ∈ R₂, u (yT r) = 0 := fun r hr => by
    rw [hũeq r (mem_sup_right hr) 1 (one_mem _) r hr (one_mul r), hc.u_one]
  have hũd : ∀ z ∈ szT₁ L T ⊔ R₂, u (yT (d * z * d⁻¹)) = μ * u (yT z) := by
    intro z hz
    have hy' : d * yT z * d⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hdT _).mp (hyT z hz)
    have hr' : d * rT z * d⁻¹ ∈ R₂ := (mem_normalizer_iff.mp hdR _).mp (hrT z hz)
    have e : (d * yT z * d⁻¹) * (d * rT z * d⁻¹) = d * z * d⁻¹ := by
      calc (d * yT z * d⁻¹) * (d * rT z * d⁻¹) = d * (yT z * rT z) * d⁻¹ := by group
        _ = d * z * d⁻¹ := by rw [hyr z hz]
    rw [hũeq _ (e ▸ mul_mem (mem_sup_left hy') (mem_sup_right hr')) _ hy' _ hr' e,
      hdu _ (hyT z hz)]
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
  set a : G → E := fun x => u (yT (x * (t * x * t⁻¹))) with ha_def
  have ha_add : ∀ x ∈ U₁, ∀ x' ∈ U₁, a (x * x') = a x + a x' := by
    intro x hx x' hx'
    obtain ⟨c, hcR, hce⟩ := hψmul x hx x' hx'
    simp only [ha_def]
    rw [hce, hũmul _ (mul_mem (hψ x hx) (hψ x' hx')) c (mem_sup_right hcR), hũR c hcR, add_zero,
      hũmul _ (hψ x hx) _ (hψ x' hx')]
  have ha1 : a 1 = 0 := by
    have := ha_add 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    linear_combination -this
  have hainv : ∀ x ∈ U₁, a x⁻¹ = -a x := by
    intro x hx
    have := ha_add x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, ha1] at this
    linear_combination -this
  have hda : ∀ x ∈ U₁, a (d * x * d⁻¹) = μ * a x := by
    intro x hx
    have htd : t * (d * x * d⁻¹) * t⁻¹ = d * (t * x * t⁻¹) * d⁻¹ := by
      calc t * (d * x * d⁻¹) * t⁻¹ = (t * d) * x * (t * d)⁻¹ := by group
        _ = (d * t) * x * (d * t)⁻¹ := by rw [hdt]
        _ = d * (t * x * t⁻¹) * d⁻¹ := by group
    have e : (d * x * d⁻¹) * (t * (d * x * d⁻¹) * t⁻¹) = d * (x * (t * x * t⁻¹)) * d⁻¹ := by
      rw [htd]
      group
    simp only [ha_def]
    rw [e, hũd _ (hψ x hx)]
  have haR : ∀ x ∈ J₁, a x = 0 → x ∈ R₂ := by
    intro x hx hax
    have hxU := hJ₁U hx
    have hz := hψ x hxU
    have hyA : yT (x * (t * x * t⁻¹)) ∈ szA₁ (szT₁ L T) := (hA₁u _ (hyT _ hz)).mpr hax
    have hψR : x * (t * x * t⁻¹) ∈ R₂ := by
      rw [← hyr _ hz]
      exact mul_mem (hA₁R hyA) (hrT _ hz)
    have hx' : t * x * t⁻¹ ∈ J₁ := by
      have := mul_mem (inv_mem hx) (hRJ₁ hψR)
      rwa [inv_mul_cancel_left] at this
    have hx'' : t * x * t⁻¹ ∈ R₂ := by
      rw [← hJinf]
      exact mem_inf.mpr ⟨hx', ht₁ x hx⟩
    have := hR.tN _ hx''
    rwa [hkey] at this
  let Aim : AddSubgroup E :=
    { carrier := {z | ∃ x ∈ J₁, a x = z}
      zero_mem' := ⟨1, one_mem _, ha1⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
        exact ⟨x * x', mul_mem hx hx', ha_add x (hJ₁U hx) x' (hJ₁U hx')⟩
      neg_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x⁻¹, inv_mem hx, hainv x (hJ₁U hx)⟩ }
  have hAim : ∀ z ∈ Aim, μ * z ∈ Aim := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨d * x * d⁻¹, (mem_normalizer_iff.mp hdJ₁ x).mp hx, hda x (hJ₁U hx)⟩
  have hasurj : ∀ z : E, ∃ x ∈ J₁, a x = z := by
    rcases SemilinearField.eq_bot_or_eq_top_of_orderOf hf hcardE hμ Aim hAim with hbot | htop
    · exfalso
      have hJ₁R : J₁ ≤ R₂ := fun x hx => haR x hx (by
        have hm : a x ∈ Aim := ⟨x, hx, rfl⟩
        rw [hbot] at hm
        exact (AddSubgroup.mem_bot).mp hm)
      obtain ⟨y, hy, hyu⟩ := hc.u_surj 1
      have hyU : y ∈ U₁ := hU.le (mem_sup_left hy)
      have hyJ₂ : y ∈ J₂ := by
        rw [← hJ] at hyU
        exact (sup_le (hJ₁R.trans hRJ₂) le_rfl) hyU
      have hyt : t * y * t⁻¹ = y := by rw [← hR.t_comm y hy, mul_inv_cancel_right]
      have hyR : y ∈ R₂ := hJ₁R (hyt ▸ ht₂ y hyJ₂)
      have hyA : y ∈ szA₁ (szT₁ L T) := by
        rw [← hR.inf]
        exact mem_inf.mpr ⟨hy, hyR⟩
      have h0 := (hA₁u y hy).mp hyA
      rw [hyu] at h0
      exact one_ne_zero h0
    · intro z
      have hm : z ∈ Aim := htop ▸ AddSubgroup.mem_top z
      exact hm
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
  obtain ⟨π, hπA, hπid, hπmul, hπd⟩ := exists_proj_of_odd hA₁R hR.comm hU.sq_R₂ hdodd hdR hdA
  refine ⟨E, inferInstance, inferInstance, d, μ, a, fun r => v (r * t * r⁻¹ * t),
    fun r => v (π r), hKE, hμ0, hμ, hdL, hdT, hdodd, hdJ₁, hdR, ha_add, ?_, haR, hasurj, hda,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have hrt : t * r * t⁻¹ ∈ R₂ := hR.tN r hr
    exact hũR _ (mul_mem hr hrt)
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

theorem card_commutator_le_of_split
    (hD : U3EndingData G L f t T R₂ U₁ s) {J₁ J₂ : Subgroup G} (hJ : J₁ ⊔ J₂ = U₁)
    (hJinf : J₁ ⊓ J₂ = R₂) (ht₁ : ∀ x ∈ J₁, t * x * t⁻¹ ∈ J₂) (ht₂ : ∀ x ∈ J₂, t * x * t⁻¹ ∈ J₁)
    (hK : ∀ k ∈ L, k ∈ normalizer (szT₁ L T : Set G) → Odd (orderOf k) →
      k ∈ normalizer (J₁ : Set G)) :
    Nat.card (⁅J₁, J₁⁆ : Subgroup G) ≤ 2 ^ f := by
  obtain ⟨E, _, _, d, μ, a, χ₁, χ₂, hKE, hμ0, hμ, -, -, -, hdJ₁, -, ha_add, -, haR, hasurj, hda,
    hχ₁, hχ₂, hχ, hdχ₁, hdχ₂⟩ := hD.exists_coords_of_split hJ hJinf ht₁ ht₂ hK
  have hU := hD.u1
  have hJ₁U : J₁ ≤ U₁ := hJ ▸ le_sup_left
  have hUR : ∀ x ∈ U₁, ∀ r ∈ R₂, x * r = r * x := fun x hx r hr =>
    (mem_centralizer_iff.mp (hU.le_centralizer hx) r hr).symm
  exact card_commutator_le_of_weights hD.start.two_le hKE (J := J₁) (R := R₂)
    (fun x hx y hy => hU.comm_mem x (hJ₁U hx) y (hJ₁U hy))
    (fun x hx r hr => hUR x (hJ₁U hx) r hr) hD.r2.comm hU.sq_R₂ a
    (fun x hx y hy => ha_add x (hJ₁U hx) y (hJ₁U hy)) haR hasurj χ₁ χ₂ hχ₁ hχ₂ hχ hμ0 hμ
    (fun x hx => (mem_normalizer_iff.mp hdJ₁ x).mp hx) (fun x hx => hda x (hJ₁U hx)) hdχ₁ hdχ₂

theorem commutator_ne_of_split
    (hD : U3EndingData G L f t T R₂ U₁ s) {J₁ J₂ : Subgroup G} (hJ : J₁ ⊔ J₂ = U₁)
    (hJinf : J₁ ⊓ J₂ = R₂) (ht₁ : ∀ x ∈ J₁, t * x * t⁻¹ ∈ J₂) (ht₂ : ∀ x ∈ J₂, t * x * t⁻¹ ∈ J₁)
    (hK : ∀ k ∈ L, k ∈ normalizer (szT₁ L T : Set G) → Odd (orderOf k) →
      k ∈ normalizer (J₁ : Set G)) :
    ⁅J₁, J₁⁆ ≠ R₂ := by
  intro heq
  have h1 := hD.card_commutator_le_of_split hJ hJinf ht₁ ht₂ hK
  rw [heq, hD.r2.card] at h1
  have hf : 2 ≤ f := hD.start.two_le
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

end U3EndingData

end CFSG.SeitzReduction.RankOne
