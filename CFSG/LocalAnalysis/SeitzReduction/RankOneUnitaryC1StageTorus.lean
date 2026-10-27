module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageFpf
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Coords

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

namespace U3C1Torus

theorem conj_pow {G : Type*} [Group G] {M : Type*} [Monoid M] {H : Subgroup G} {φ : G → M}
    {c : G} (hc : c ∈ normalizer (H : Set G)) {κ : M}
    (hκ : ∀ y ∈ H, φ (c * y * c⁻¹) = κ * φ y) (k : ℕ) :
    ∀ y ∈ H, φ (c ^ k * y * (c ^ k)⁻¹) = κ ^ k * φ y := by
  induction k with
  | zero => intro y _; simp
  | succ k ih =>
    intro y hy
    have hk : c ^ k * y * (c ^ k)⁻¹ ∈ H := (mem_normalizer_iff.mp (pow_mem hc k) y).mp hy
    have e : c ^ (k + 1) * y * (c ^ (k + 1))⁻¹ = c * (c ^ k * y * (c ^ k)⁻¹) * c⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      simp only [mul_assoc]
    rw [e, hκ _ hk, ih y hy, pow_succ', mul_assoc]

section Coords

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ : Subgroup G} {σ : E →+* E}
  {u v : G → E}

theorem coords_v_one (hc : U3RootCoords T₁ σ u v) : v 1 = 0 := by
  have h := hc.mul_v 1 (one_mem _) 1 (one_mem _)
  rw [mul_one, hc.u_one, zero_mul, sub_zero] at h
  linear_combination -h

theorem coords_v_inv (hc : U3RootCoords T₁ σ u v) {z : G} (hz : z ∈ T₁) :
    v z⁻¹ = -v z - u z * σ (u z) := by
  have h := hc.mul_v z hz z⁻¹ (inv_mem hz)
  rw [mul_inv_cancel, coords_v_one hc, hc.u_inv hz, map_neg] at h
  linear_combination -h

theorem coords_commutator (hc : U3RootCoords T₁ σ u v) {y y' : G} (hy : y ∈ T₁)
    (hy' : y' ∈ T₁) : u ⁅y, y'⁆ = 0 ∧ v ⁅y, y'⁆ = u y' * σ (u y) - u y * σ (u y') := by
  have h2 : y * y' ∈ T₁ := mul_mem hy hy'
  have h3 : y * y' * y⁻¹ ∈ T₁ := mul_mem h2 (inv_mem hy)
  rw [commutatorElement_def]
  refine ⟨?_, ?_⟩
  · rw [hc.mul_u _ h3 _ (inv_mem hy'), hc.mul_u _ h2 _ (inv_mem hy), hc.mul_u _ hy _ hy',
      hc.u_inv hy, hc.u_inv hy']
    ring
  · rw [hc.mul_v _ h3 _ (inv_mem hy'), hc.mul_v _ h2 _ (inv_mem hy), hc.mul_v _ hy _ hy',
      hc.mul_u _ h2 _ (inv_mem hy), hc.mul_u _ hy _ hy', coords_v_inv hc hy,
      coords_v_inv hc hy', hc.u_inv hy, hc.u_inv hy']
    simp only [map_neg]
    ring

theorem conj_of_mem_commutator (hc : U3RootCoords T₁ σ u v) {c : G}
    (hcT : c ∈ normalizer (T₁ : Set G)) {κ : E} (hκ : ∀ y ∈ T₁, u (c * y * c⁻¹) = κ * u y)
    {b : G} (hb : b ∈ ⁅T₁, T₁⁆) : b ∈ T₁ ∧ u b = 0 ∧ v (c * b * c⁻¹) = κ * σ κ * v b := by
  have hconj : ∀ y ∈ T₁, c * y * c⁻¹ ∈ T₁ := fun y hy => (mem_normalizer_iff.mp hcT y).mp hy
  rw [Subgroup.commutator_def] at hb
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, hy, y', hy', rfl⟩ := hx
    have e : c * ⁅y, y'⁆ * c⁻¹ = ⁅c * y * c⁻¹, c * y' * c⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    obtain ⟨h1, h2⟩ := coords_commutator hc hy hy'
    obtain ⟨-, h3⟩ := coords_commutator hc (hconj y hy) (hconj y' hy')
    refine ⟨?_, h1, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hy hy') (inv_mem hy)) (inv_mem hy')
    · rw [e, h3, h2, hκ y hy, hκ y' hy']
      simp only [map_mul]
      ring
  | one =>
    refine ⟨one_mem _, hc.u_one, ?_⟩
    rw [mul_one, mul_inv_cancel, coords_v_one hc, mul_zero]
  | mul x y _ _ ihx ihy =>
    obtain ⟨hx, hux, hvx⟩ := ihx
    obtain ⟨hy, huy, hvy⟩ := ihy
    have hux' : u (c * x * c⁻¹) = 0 := by rw [hκ x hx, hux, mul_zero]
    have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    refine ⟨mul_mem hx hy, by rw [hc.mul_u _ hx _ hy, hux, huy, add_zero], ?_⟩
    rw [e, hc.v_mul_of_u_eq_zero (hconj x hx) (hconj y hy) hux', hvx, hvy,
      hc.v_mul_of_u_eq_zero hx hy hux]
    ring
  | inv x _ ihx =>
    obtain ⟨hx, hux, hvx⟩ := ihx
    have hux' : u (c * x * c⁻¹) = 0 := by rw [hκ x hx, hux, mul_zero]
    have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    refine ⟨inv_mem hx, by rw [hc.u_inv hx, hux, neg_zero], ?_⟩
    rw [e, coords_v_inv hc (hconj x hx), coords_v_inv hc hx, hux', hux, hvx]
    ring

theorem u3A₁Coords [CharP E 2] (hc : U3RootCoords T₁ σ u v) {A₁ : Subgroup G} (hA₁ : A₁ ≤ T₁)
    (hA : ∀ y ∈ T₁, (y ∈ A₁ ↔ u y = 0)) {K : Subfield E} (hK : ∀ x, x ∈ K ↔ σ x = x)
    {w : G → K} (hw : ∀ b ∈ A₁, (w b : E) = v b) {d : G} (hdA : ∀ b ∈ A₁, d⁻¹ * b * d ∈ A₁)
    {ν : K} (hdv : ∀ b ∈ A₁, v (d⁻¹ * b * d) = ν * v b) : U3A₁Coords A₁ d w ν where
  mul b hb b' hb' := by
    apply Subtype.ext
    rw [Subfield.coe_add, hw _ (mul_mem hb hb'), hw b hb, hw b' hb',
      hc.v_mul_of_u_eq_zero (hA₁ hb) (hA₁ hb') ((hA b (hA₁ hb)).mp hb)]
  inj b hb b' hb' h := by
    refine hc.inj b (hA₁ hb) b' (hA₁ hb') ?_ ?_
    · rw [(hA b (hA₁ hb)).mp hb, (hA b' (hA₁ hb')).mp hb']
    · rw [← hw b hb, ← hw b' hb', h]
  surj β := by
    have hβ : σ β = β := (hK β).mp β.2
    obtain ⟨y, hy, hu, hv⟩ := hc.surj 0 β (by
      rw [hβ, CharTwo.add_self_eq_zero, zero_mul, add_zero])
    have hyA : y ∈ A₁ := (hA y hy).mpr hu
    exact ⟨y, hyA, Subtype.ext (by rw [hw y hyA, hv])⟩
  conj_mem := hdA
  conj b hb := by
    apply Subtype.ext
    rw [Subfield.coe_mul, hw _ (hdA b hb), hw b hb, hdv b hb]

end Coords

theorem pow_facts {M : Type*} [Monoid M] {f : ℕ} (hf : 2 ≤ f) {ℓ : M}
    (hℓ : orderOf ℓ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)) :
    Odd (orderOf ℓ) ∧ ℓ ^ (2 ^ f - 1) ≠ 1 ∧ orderOf (ℓ ^ (2 ^ f + 1)) = 2 ^ f - 1 := by
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2q : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  generalize 2 ^ f = q at hq4 h2q hℓ ⊢
  have hg3 : Nat.gcd 3 (q + 1) ∣ 3 := Nat.gcd_dvd_left _ _
  obtain ⟨s, hs⟩ : Nat.gcd 3 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
  generalize Nat.gcd 3 (q + 1) = g at hg3 hs hℓ
  have hg : g = 1 ∨ g = 3 := (Nat.dvd_prime Nat.prime_three).mp hg3
  have hs2 : 2 ≤ s := by rcases hg with rfl | rfl <;> omega
  have hgpos : 0 < g := by rcases hg with rfl | rfl <;> norm_num
  have hn : orderOf ℓ = (q - 1) * s := by
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    have e1 : (p + 1) ^ 2 - 1 = g * ((p + 1 - 1) * s) := by
      rw [Nat.add_sub_cancel]
      refine Nat.sub_eq_of_eq_add ?_
      rw [show g * (p * s) = p * (g * s) by ring, ← hs]
      ring
    rw [hℓ, e1, Nat.mul_div_cancel_left _ hgpos]
  have hcop : Nat.Coprime (q - 1) g := by
    rcases hg with rfl | rfl
    · exact Nat.coprime_one_right _
    · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)).symm
  refine ⟨?_, fun h => ?_, ?_⟩
  · rw [hn]
    have hodd : Odd (q + 1) := ⟨q / 2, by omega⟩
    rw [hs] at hodd
    exact Nat.odd_mul.mpr ⟨⟨q / 2 - 1, by omega⟩, (Nat.odd_mul.mp hodd).2⟩
  · have h1 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h)
    rw [hn] at h1
    have h3 : (q - 1) * 2 ≤ (q - 1) * s := Nat.mul_le_mul_left _ hs2
    omega
  · rw [orderOf_pow' (n := q + 1) ℓ (by omega), hn, hs, Nat.gcd_mul_right, hcop.gcd_eq_one,
      one_mul, Nat.mul_div_cancel _ (show 0 < s by omega)]

theorem exists_pow_eq_of_orderOf {K : Type*} [Field K] [Finite K] {μ : K} (hμ0 : μ ≠ 0)
    (hμ : orderOf μ = Nat.card K - 1) {w : K} (hw : w ≠ 0) : ∃ m : ℕ, μ ^ m = w := by
  have h1 : orderOf (Units.mk0 μ hμ0) = Nat.card Kˣ := by
    rw [← orderOf_units, Units.val_mk0, hμ, Nat.card_units]
  have h2 : zpowers (Units.mk0 μ hμ0) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h1])
  have h3 : Units.mk0 w hw ∈ Submonoid.powers (Units.mk0 μ hμ0) :=
    mem_powers_iff_mem_zpowers.mpr (by rw [h2]; exact Subgroup.mem_top _)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp h3
  refine ⟨m, ?_⟩
  have h4 := congrArg Units.val hm
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0] at h4

end U3C1Torus

section Certificates

theorem u3C1TorusFullInput : U3C1TorusFullInput := by
  classical
  intro G _ _ L f t T R₂ h hS2 hR
  obtain ⟨E, _, _, _, σ, hE, hσ, u, v, hc, hA, d₀, hd₀L, hd₀T, μ₀, hμ₀, hμ₀o, hd₀u⟩ :=
    h.exists_rootCoords_cartan_of_card_sylow hS2
  obtain ⟨-, hA₁card, hA₁comm, -⟩ := h.facts_of_card_sylow hS2
  have hA₁T : szA₁ (szT₁ L T) ≤ szT₁ L T := szA₁_le _
  obtain ⟨d, hdL, hdT, hdodd, ℓ, hℓ0, hℓo, hdu⟩ : ∃ d ∈ L, d ∈ normalizer (szT₁ L T : Set G) ∧
      Odd (orderOf d) ∧ ∃ ℓ : E, ℓ ≠ 0 ∧
        orderOf ℓ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) ∧
        ∀ y ∈ szT₁ L T, u (d * y * d⁻¹) = ℓ * u y := by
    obtain ⟨a, m', hm', hn₀⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d₀).ne'
    refine ⟨d₀ ^ 2 ^ a, pow_mem hd₀L _, pow_mem hd₀T _, ?_, μ₀ ^ 2 ^ a, pow_ne_zero _ hμ₀, ?_,
      U3C1Torus.conj_pow hd₀T hd₀u _⟩
    · rw [orderOf_pow_of_dvd (n := 2 ^ a) (pow_ne_zero _ two_ne_zero) ⟨m', hn₀⟩, hn₀,
        Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
      exact hm'
    · rw [Nat.Coprime.orderOf_pow
        ((Odd.coprime_two_right (U3C1Torus.pow_facts h.two_le hμ₀o).1).pow_right a), hμ₀o]
  obtain ⟨-, hℓq, hNo⟩ := U3C1Torus.pow_facts h.two_le hℓo
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  have hconjT : ∀ y ∈ szT₁ L T, d * y * d⁻¹ ∈ szT₁ L T := fun y hy =>
    (mem_normalizer_iff.mp hdT y).mp hy
  have hdA : d ∈ normalizer (szA₁ (szT₁ L T) : Set G) := by
    refine mem_normalizer_iff.mpr fun b => ⟨fun hb => ?_, fun hb => ?_⟩
    · have hbT := hA₁T hb
      exact (hA _ (hconjT b hbT)).mpr (by rw [hdu b hbT, (hA b hbT).mp hb, mul_zero])
    · have hbT : b ∈ szT₁ L T := (mem_normalizer_iff.mp hdT b).mpr (hA₁T hb)
      have h1 := (hA _ (hA₁T hb)).mp hb
      rw [hdu b hbT] at h1
      exact (hA b hbT).mpr ((mul_eq_zero.mp h1).resolve_left hℓ0)
  have htA : t ∈ centralizer (szA₁ (szT₁ L T) : Set G) :=
    centralizer_le hA₁T h.mem_centralizer_szT₁
  have hdR : d ∈ normalizer (R₂ : Set G) :=
    (h.u3R2_canonical_of_card_sylow hS2 hR).2.2.2.2.1
      (SzPartition.mem_normalizer_sup_zpowers htA hdA hdt)
  have hdv : ∀ b ∈ szA₁ (szT₁ L T), v (d * b * d⁻¹) = ℓ * σ ℓ * v b := fun b hb =>
    (U3C1Torus.conj_of_mem_commutator hc hdT hdu (hA₁comm.le hb)).2.2
  have : Fintype E := Fintype.ofFinite E
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    have hcardE : Fintype.card E = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hE]
    rw [hσ, hσ, ← pow_mul, ← sq, ← hcardE, FiniteField.pow_card]
  have hN : ℓ * σ ℓ = ℓ ^ (2 ^ f + 1) := by rw [hσ, pow_succ']
  have hσN : σ (ℓ * σ ℓ) = ℓ * σ ℓ := by rw [map_mul, hσσ, mul_comm]
  have hN0 : ℓ * σ ℓ ≠ 0 := mul_ne_zero hℓ0 ((map_ne_zero σ).mpr hℓ0)
  have hN1 : (ℓ * σ ℓ) ^ (2 ^ f - 1) = 1 := by
    rw [hN, ← hNo]
    exact pow_orderOf_eq_one _
  have hdAinv : ∀ b ∈ szA₁ (szT₁ L T), d⁻¹ * b * d ∈ szA₁ (szT₁ L T) := fun b hb => by
    have h1 := (mem_normalizer_iff.mp (inv_mem hdA) b).mp hb
    rwa [inv_inv] at h1
  have hdv' : ∀ b ∈ szA₁ (szT₁ L T), v (d⁻¹ * b * d) = (ℓ * σ ℓ)⁻¹ * v b := by
    intro b hb
    have h1 := hdv _ (hdAinv b hb)
    rw [show d * (d⁻¹ * b * d) * d⁻¹ = b by group] at h1
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  obtain ⟨K, hK⟩ : ∃ K : Subfield E, ∀ x, x ∈ K ↔ σ x = x :=
    ⟨RingHom.eqLocusField σ (RingHom.id E), fun x => by
      rw [RingHom.mem_eqLocusField, RingHom.id_apply]⟩
  have hNK : (ℓ * σ ℓ)⁻¹ ∈ K := (hK _).mpr (by rw [map_inv₀, hσN])
  have hNK' : ℓ * σ ℓ ∈ K := (hK _).mpr hσN
  obtain ⟨w, hw⟩ : ∃ w : G → K, ∀ b ∈ szA₁ (szT₁ L T), (w b : E) = v b := by
    refine ⟨fun g => if hg : σ (v g) = v g then ⟨v g, (hK _).mpr hg⟩ else 0, fun b hb => ?_⟩
    have hσb : σ (v b) = v b := hc.sigma_v_of_u_eq_zero (hA₁T hb) ((hA b (hA₁T hb)).mp hb)
    show ((if hg : σ (v b) = v b then (⟨v b, (hK _).mpr hg⟩ : K) else 0 : K) : E) = v b
    rw [dite_eq_left hσb]
  have hcoords : U3A₁Coords (szA₁ (szT₁ L T)) d w ⟨(ℓ * σ ℓ)⁻¹, hNK⟩ :=
    U3C1Torus.u3A₁Coords hc hA₁T hA hK hw hdAinv hdv'
  have hKcard : Nat.card K = 2 ^ f := by
    rw [← hA₁card]
    refine (Nat.card_eq_of_bijective (fun b : szA₁ (szT₁ L T) => w b)
      ⟨fun b b' hbb' => Subtype.ext (hcoords.inj _ b.2 _ b'.2 hbb'), fun c => ?_⟩).symm
    obtain ⟨b, hb, hbc⟩ := hcoords.surj c
    exact ⟨⟨b, hb⟩, hbc⟩
  have hgen : ∀ x : K, x ≠ 0 → ∃ m : ℕ, (⟨(ℓ * σ ℓ)⁻¹, hNK⟩ : K) ^ m = x := by
    have hNo' : orderOf (⟨ℓ * σ ℓ, hNK'⟩ : K) = Nat.card K - 1 := by
      rw [← orderOf_injective K.subtype.toMonoidHom (fun a b hab => Subtype.ext hab), hKcard,
        ← hNo, ← hN]
      rfl
    have hNK0 : (⟨ℓ * σ ℓ, hNK'⟩ : K) ≠ 0 := fun h0 => hN0 (congrArg Subtype.val h0)
    intro x hx
    obtain ⟨m, hm⟩ := U3C1Torus.exists_pow_eq_of_orderOf hNK0 hNo' (inv_ne_zero hx)
    refine ⟨m, ?_⟩
    have e : (⟨(ℓ * σ ℓ)⁻¹, hNK⟩ : K) = (⟨ℓ * σ ℓ, hNK'⟩ : K)⁻¹ :=
      Subtype.ext (by rw [Subfield.coe_inv])
    rw [e, inv_pow, hm, inv_inv]
  refine ⟨d, hdodd, hdR, hdT, hdt, ⟨2 ^ f - 1, fun b hb => ?_, fun y hy hyA => ?_⟩,
    ⟨E, inferInstance, inferInstance, inferInstance, σ, hE, hσ, u, v, hc, hA, ℓ, hℓ0, hℓo, hdu⟩,
    K, inferInstance, inferInstance, inferInstance, w, ⟨(ℓ * σ ℓ)⁻¹, hNK⟩,
    by rw [← Nat.card_eq_fintype_card, hKcard], hcoords, hgen⟩
  ·
    have hdmA : d ^ (2 ^ f - 1) * b * (d ^ (2 ^ f - 1))⁻¹ ∈ szA₁ (szT₁ L T) :=
      (mem_normalizer_iff.mp (pow_mem hdA _) b).mp hb
    refine hc.inj _ (hA₁T hdmA) _ (hA₁T hb) ?_ ?_
    · rw [(hA _ (hA₁T hdmA)).mp hdmA, (hA _ (hA₁T hb)).mp hb]
    · rw [U3C1Torus.conj_pow hdA hdv _ b hb, hN1, one_mul]
  ·
    have hdmT : d ^ (2 ^ f - 1) * y * (d ^ (2 ^ f - 1))⁻¹ ∈ szT₁ L T :=
      (mem_normalizer_iff.mp (pow_mem hdT _) y).mp hy
    have h1 := (hA _ (mul_mem (inv_mem hy) hdmT)).mp hyA
    rw [hc.u_mul_inv hy hdmT, U3C1Torus.conj_pow hdT hdu _ y hy] at h1
    have h2 : (ℓ ^ (2 ^ f - 1) - 1) * u y = 0 := by linear_combination h1
    exact (hA y hy).mpr ((mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hℓq))

end Certificates

end CFSG.SeitzReduction.RankOne
