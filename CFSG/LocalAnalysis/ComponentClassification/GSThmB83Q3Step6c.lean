module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step6

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Eight

theorem exists_conj_mem_mul {G : Type*} [Group G] [Finite G] {C₀ E : Subgroup G}
    (hE : ∀ k ∈ C₀, IsPGroup 2 (zpowers k) → k ∈ E) {u w : G} (hu : u * u = 1)
    (hw : w * w = 1) (huw : u * w ∈ C₀) : ∃ l ∈ C₀, ∃ e ∈ E, l * w * l⁻¹ = u * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (u * w)).ne'
  have hcop : Nat.Coprime (2 ^ i) m := (Nat.coprime_two_left.mpr hm).pow_left i
  have hbez : ((2 ^ i : ℕ) : ℤ) * Nat.gcdA (2 ^ i) m + (m : ℤ) * Nat.gcdB (2 ^ i) m = 1 := by
    have := Nat.gcd_eq_gcd_ab (2 ^ i) m
    rw [hcop.gcd_eq_one, Nat.cast_one] at this
    exact this.symm
  set k := u * w with hk
  have hk1 : k ^ ((2 ^ i * m : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hnm, pow_orderOf_eq_one]
  obtain ⟨z₁, z₂, hz₁, hz₂, hz⟩ : ∃ z₁ z₂ : ℤ, (k ^ z₁) ^ m = 1 ∧ (k ^ z₂) ^ (2 ^ i) = 1 ∧
      z₁ + z₂ = 1 := by
    refine ⟨((2 ^ i : ℕ) : ℤ) * Nat.gcdA (2 ^ i) m, (m : ℤ) * Nat.gcdB (2 ^ i) m, ?_, ?_, hbez⟩
    · rw [← zpow_natCast, ← zpow_mul, show ((2 ^ i : ℕ) : ℤ) * Nat.gcdA (2 ^ i) m * (m : ℤ) =
        ((2 ^ i * m : ℕ) : ℤ) * Nat.gcdA (2 ^ i) m by push_cast; ring, zpow_mul, hk1, one_zpow]
    · rw [← zpow_natCast, ← zpow_mul, show (m : ℤ) * Nat.gcdB (2 ^ i) m * ((2 ^ i : ℕ) : ℤ) =
        ((2 ^ i * m : ℕ) : ℤ) * Nat.gcdB (2 ^ i) m by push_cast; ring, zpow_mul, hk1, one_zpow]
  have he2 : IsPGroup 2 (zpowers (k ^ z₂)) := by
    have hdvd : orderOf (k ^ z₂) ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hz₂
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have heE : k ^ z₂ ∈ E := hE _ (zpow_mem huw z₂) he2
  have hinvk : u * k * u⁻¹ = k⁻¹ := by
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
    rw [hk, mul_inv_rev, hu', hw']
    calc u * (u * w) * u = (u * u) * w * u := by group
      _ = w * u := by rw [hu, one_mul]
  have hinv : ∀ z : ℤ, u * k ^ z * u⁻¹ = (k ^ z)⁻¹ := by
    intro z
    have h1 := map_zpow (MulAut.conj u) k z
    simp only [MulAut.conj_apply] at h1
    rw [h1, hinvk, inv_zpow]
  set z₃ : ℤ := z₁ * (((m + 1) / 2 : ℕ) : ℤ) with hz₃
  have ho'2 : k ^ z₃ * k ^ z₃ = k ^ z₁ := by
    obtain ⟨r, hr⟩ := hm
    have h2 : (m + 1) / 2 + (m + 1) / 2 = m + 1 := by omega
    rw [hz₃, zpow_mul, zpow_natCast, ← pow_add, h2, pow_succ, hz₁, one_mul]
  have hou : k ^ z₃ * u = u * (k ^ z₃)⁻¹ := by
    have h2 : u * (k ^ z₃)⁻¹ * u⁻¹ = k ^ z₃ := by
      have := hinv (-z₃)
      rwa [zpow_neg, inv_inv] at this
    calc k ^ z₃ * u = u * (k ^ z₃)⁻¹ * u⁻¹ * u := by rw [h2]
      _ = u * (k ^ z₃)⁻¹ := by group
  have hcomm : k ^ z₃ * k ^ z₂ = k ^ z₂ * k ^ z₃ := ((Commute.refl k).zpow_zpow z₃ z₂).eq
  have hkoe : k = k ^ z₁ * k ^ z₂ := by rw [← zpow_add, hz, zpow_one]
  have hwuk : w = u * k := by rw [hk, ← mul_assoc, hu, one_mul]
  refine ⟨k ^ z₃, zpow_mem huw z₃, k ^ z₂, heE, ?_⟩
  calc k ^ z₃ * w * (k ^ z₃)⁻¹ = k ^ z₃ * (u * (k ^ z₃ * k ^ z₃ * k ^ z₂)) * (k ^ z₃)⁻¹ := by
        rw [ho'2, ← hkoe, ← hwuk]
    _ = (k ^ z₃ * u) * k ^ z₃ * (k ^ z₃ * k ^ z₂) * (k ^ z₃)⁻¹ := by group
    _ = (u * (k ^ z₃)⁻¹) * k ^ z₃ * (k ^ z₂ * k ^ z₃) * (k ^ z₃)⁻¹ := by rw [hou, hcomm]
    _ = u * k ^ z₂ := by group

theorem isConj_of_even_involution {σ τ : Equiv.Perm (Fin 6)} (hσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hσs : Equiv.Perm.sign σ = 1) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hτs : Equiv.Perm.sign τ = 1) : IsConj σ τ := by
  have key : ∀ ρ : Equiv.Perm (Fin 6), ρ * ρ = 1 → ρ ≠ 1 → Equiv.Perm.sign ρ = 1 →
      ρ.cycleType = Multiset.replicate 2 2 := by
    intro ρ hρ hρ1 hρs
    have hord : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hρ])
    have h2 : ∀ n ∈ ρ.cycleType, n = 2 := fun n hn => by
      have h3 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans hord
      have h4 := Equiv.Perm.two_le_of_mem_cycleType hn
      have h5 := Nat.le_of_dvd (by norm_num) h3
      omega
    have hrep := Multiset.eq_replicate.mpr ⟨rfl, h2⟩
    set c := Multiset.card ρ.cycleType with hc
    have hsum : ρ.cycleType.sum = 2 * c := by
      rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
    have hle : ρ.cycleType.sum ≤ 6 := by
      rw [Equiv.Perm.sum_cycleType]
      exact (Finset.card_le_univ _).trans (by simp)
    have hc0 : c ≠ 0 := by
      intro h0
      apply hρ1
      rw [← Equiv.Perm.cycleType_eq_zero, hrep, h0, Multiset.replicate_zero]
    have hsign := Equiv.Perm.sign_of_cycleType ρ
    rw [hρs, hsum, ← hc] at hsign
    have hc2 : c = 2 := by
      have hc3 : c ≤ 3 := by omega
      interval_cases c
      · exact absurd rfl hc0
      · norm_num at hsign
      · rfl
      · norm_num at hsign
    rw [hrep, hc2]
  rw [Equiv.Perm.isConj_iff_cycleType_eq, key σ hσ hσ1 hσs, key τ hτ hτ1 hτs]

namespace E32Base

variable {X : Type} [Group X] [Finite X] (C : E32Base X)

theorem card_centralizer (n : ↥C.N) :
    Nat.card ↥(C.E ⊓ centralizer ({(n : X)} : Set X)) = S6M.fixlen [C.π n] := by
  have h1 : ((C.E ⊓ centralizer ({(n : X)} : Set X) : Subgroup X) : Set X) =
      C.θ '' {v | S6M.act (C.π n) v = v} := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxE, hxc⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨v, rfl⟩ := C.mem_E_iff.mp hxE
      exact ⟨v, (C.comm_iff n v).mp (mem_centralizer_singleton_iff.mp hxc).symm, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨C.θ_mem v,
        mem_centralizer_singleton_iff.mpr ((C.comm_iff n v).mpr hv).symm⟩
  have h2 : {v | S6M.act (C.π n) v = v} =
      {v | ([C.π n].all fun t => S6M.veq (S6M.act t v) v) = true} := by
    ext v
    simp [S6M.veq_iff]
  show Nat.card ↥((C.E ⊓ centralizer ({(n : X)} : Set X) : Subgroup X) : Set X) = _
  rw [h1, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ C.θ_injective, h2,
    S6M.ncard_eq_length]
  rfl

end E32Base

end Eight

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace Q3Data

variable (d : Q3Data H)
include d

theorem a_mem_RM : h.a ∈ d.RM := d.Q1_le_RM ⟨H.a_mem_Q, h.a_mem_M3⟩

theorem a_mem_NE : h.a ∈ d.NE := d.R_le_normalizer_E (d.RM_le_R d.a_mem_RM)

theorem rh_congr {x x' : X} (hxx : x = x') (hx : x ∈ d.RM) (hx' : x' ∈ d.RM) :
    d.rh x hx = d.rh x' hx' := by
  subst hxx
  rfl

theorem ca_eq : d.c.a = d.rh h.a d.a_mem_RM := by
  rw [d.c_a]

theorem card_E0_centralizer_a (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    8 ≤ Nat.card ↥(d.E0 ⊓ centralizer ({h.a} : Set X)) := by
  have haR := d.a_mem_RM
  have haN := d.RM_le_normalizer_E0 haR
  have hconj : ∀ e ∈ d.E0, h.a * e * h.a⁻¹ ∈ d.E0 := fun e he =>
    (mem_normalizer_iff.mp haN e).mp he
  let φ : ↥d.E0 →* X :=
    { toFun := fun e => (e : X) * (h.a * e * h.a⁻¹)
      map_one' := by simp
      map_mul' := fun e f => by
        have hc := d.E0_comm hCF1 hCF2 (hconj e e.2) f.2
        show (e : X) * f * (h.a * (e * f) * h.a⁻¹) =
          (e : X) * (h.a * e * h.a⁻¹) * (f * (h.a * f * h.a⁻¹))
        calc (e : X) * f * (h.a * (e * f) * h.a⁻¹) =
              e * (f * (h.a * e * h.a⁻¹)) * (h.a * f * h.a⁻¹) := by group
          _ = e * ((h.a * e * h.a⁻¹) * f) * (h.a * f * h.a⁻¹) := by rw [hc]
          _ = (e : X) * (h.a * e * h.a⁻¹) * (f * (h.a * f * h.a⁻¹)) := by group }
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [d.card_E0 hCF1 hCF2] at h1
  have hkereq : φ.ker.map d.E0.subtype = d.E0 ⊓ centralizer ({h.a} : Set X) := by
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      have he' : (e : X) * (h.a * e * h.a⁻¹) = 1 := he
      refine Subgroup.mem_inf.mpr ⟨e.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h2 : h.a * e * h.a⁻¹ = (e : X)⁻¹ := eq_inv_of_mul_eq_one_right he'
      rw [inv_eq_of_mul_eq_one_right (d.E0_sq hCF1 hCF2 e.2)] at h2
      calc (e : X) * h.a = h.a * e * h.a⁻¹ * h.a := by rw [h2]
        _ = h.a * e := by group
    · intro hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      refine ⟨⟨x, hx1⟩, ?_, rfl⟩
      show x * (h.a * x * h.a⁻¹) = 1
      rw [← mem_centralizer_singleton_iff.mp hx2, mul_inv_cancel_right]
      exact d.E0_sq hCF1 hCF2 hx1
  have hker : Nat.card φ.ker = Nat.card ↥(d.E0 ⊓ centralizer ({h.a} : Set X)) := by
    rw [← card_map_of_injective d.E0.subtype_injective, hkereq]
  have hsub : ∀ y ∈ φ.range, y ∈ d.E0 := by
    rintro _ ⟨e, rfl⟩
    exact mul_mem e.2 (hconj e e.2)
  have hcomm : ∀ y (hy : y ∈ φ.range), d.rh y (d.E0_le_RM (hsub y hy)) ∈
      (⁅d.E0hat, zpowers d.c.a⁆ : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K))) := by
    rintro _ ⟨e, rfl⟩
    have he2 := d.E0_le_RM e.2
    have hc := d.E0_le_RM (hconj e e.2)
    have hinv : (d.rh e he2)⁻¹ = d.rh e he2 := by
      rw [← d.rh_inv he2]
      exact d.rh_congr (inv_eq_of_mul_eq_one_right (d.E0_sq hCF1 hCF2 e.2)) _ _
    have hφe : φ e = (e : X) * (h.a * e * h.a⁻¹) := rfl
    have hea : d.rh (φ e) (d.E0_le_RM (hsub _ (MonoidHom.mem_range.mpr ⟨e, rfl⟩))) =
        ⁅d.rh e he2, d.c.a⁆ := by
      rw [d.rh_congr hφe _ (mul_mem he2 hc), d.rh_mul he2 hc,
        d.rh_mul (mul_mem haR he2) (inv_mem haR), d.rh_mul haR he2, d.rh_inv haR, d.ca_eq,
        commutatorElement_def, hinv]
      group
    rw [hea]
    exact commutator_mem_commutator (d.rh_mem_E0hat e.2) (mem_zpowers _)
  have hrange : Nat.card φ.range ≤ 2 := by
    let ψ : ↥φ.range → ↥(⁅d.E0hat, zpowers d.c.a⁆ :
        Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K))) := fun y =>
      ⟨d.rh y (d.E0_le_RM (hsub y y.2)), hcomm y y.2⟩
    have hψ : Function.Injective ψ := by
      intro y y' hyy
      have := congrArg Subtype.val hyy
      exact Subtype.ext (d.rho_inj hCF1 hCF2 (d.E0_le_RM (hsub y y.2))
        (d.E0_le_RM (hsub y' y'.2)) this)
    have := Nat.card_le_card_of_injective ψ hψ
    rwa [d.card_commutator_E0hat] at this
  rw [← hker]
  by_contra hlt
  push Not at hlt
  have : Nat.card φ.ker * Nat.card φ.range ≤ 7 * 2 := Nat.mul_le_mul (by omega) hrange
  omega

theorem card_E_centralizer_a (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    16 ≤ Nat.card ↥(d.E ⊓ centralizer ({h.a} : Set X)) := by
  have hle : (d.E0 ⊓ centralizer ({h.a} : Set X)) ⊔ h.B ≤ d.E ⊓ centralizer ({h.a} : Set X) := by
    refine sup_le (inf_le_inf_right _ d.E0_le_E) ?_
    rw [d.B_eq, zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨d.b_mem_E, mem_centralizer_singleton_iff.mpr d.ba⟩
  have h1 := d.card_sup_B hCF1 hCF2 (inf_le_left.trans d.E0_le_M3 :
    d.E0 ⊓ centralizer ({h.a} : Set X) ≤ h.M3)
  have h2 := card_le_of_le hle
  have h3 := d.card_E0_centralizer_a hCF1 hCF2
  omega

theorem azt_sq (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    h.a * d.z * d.tau * (h.a * d.z * d.tau) = 1 := by
  have hza : d.z * h.a = h.a * d.z := d.z_comm_a
  have hta : d.tau * h.a = h.a * d.tau := d.tau_comm_a
  have htz : d.tau * d.z = d.z * d.tau := d.tau_comm_z hCF1 hCF2
  calc h.a * d.z * d.tau * (h.a * d.z * d.tau)
      = h.a * d.z * (d.tau * h.a) * d.z * d.tau := by group
    _ = h.a * d.z * (h.a * d.tau) * d.z * d.tau := by rw [hta]
    _ = h.a * (d.z * h.a) * (d.tau * d.z) * d.tau := by group
    _ = h.a * (h.a * d.z) * (d.z * d.tau) * d.tau := by rw [hza, htz]
    _ = (h.a * h.a) * (d.z * d.z) * (d.tau * d.tau) := by group
    _ = 1 := by rw [Six.a_mul_a_self h, d.z_sq, d.tau_sq]; group

theorem aE_conj (hq : h.IsQ3) (hF : Cat8.Q3Facts) {e : X} (he : e ∈ d.E)
    (h2 : h.a * e * (h.a * e) = 1) :
    (∃ g : X, g⁻¹ * h.a * g = h.a * e) ∨ (∃ g : X, g⁻¹ * d.b * g = h.a * e) ∨
      ∃ g : X, g⁻¹ * (d.b * d.z) * g = h.a * e := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  obtain ⟨e₀, he₀, hee⟩ := d.mem_E_cases he
  have he₀M := d.E0_le_M3 he₀
  have haM := h.a_mem_M3
  have hae2 : h.a * e₀ * (h.a * e₀) = 1 := by
    rcases hee with rfl | rfl
    · exact h2
    · have hb1 : h.a * e₀ * d.b = d.b * (h.a * e₀) := d.b_comm_of_mem_M3 (mul_mem haM he₀M)
      have key : h.a * (e₀ * d.b) * (h.a * (e₀ * d.b)) =
          h.a * e₀ * (h.a * e₀) * (d.b * d.b) := by
        calc h.a * (e₀ * d.b) * (h.a * (e₀ * d.b)) =
              h.a * e₀ * (d.b * (h.a * e₀)) * d.b := by group
          _ = h.a * e₀ * ((h.a * e₀) * d.b) * d.b := by rw [hb1]
          _ = h.a * e₀ * (h.a * e₀) * (d.b * d.b) := by group
      rw [key, d.b_mul_self, mul_one] at h2
      exact h2
  set m : ↥h.M3 := ⟨h.a * e₀, mul_mem haM he₀M⟩ with hm
  have hm2 : m * m = 1 := Subtype.ext hae2
  have hmout : H.rho m ∉ Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) := by
    intro hin
    have h3 : h.a * e₀ ∈ h.K := (H.mem_K_iff hCF1 hCF2 m).mpr hin
    have h4 : h.a ∈ h.K := by
      have := mul_mem h3 (inv_mem (d.E0_le_K hCF1 hCF2 he₀))
      rwa [mul_inv_cancel_right] at this
    exact H.a_not_mem_K hCF1 hCF2 h4
  have hrm2 : H.rho m * H.rho m = 1 := by rw [← map_mul, hm2, map_one]
  have hv : IsPGroup 2 (zpowers m) := isPGroup_zpowers_of_mul_self hm2
  have hcb : ∀ c : ↥h.M3, (c : X)⁻¹ * d.b * c = d.b := fun c => by
    rw [mul_assoc, ← d.b_comm_of_mem_M3 c.2, inv_mul_cancel_left]
  rcases d.c_props.outer_classes _ hrm2 hmout with ⟨y, hy⟩ | ⟨y, hy⟩
  ·
    obtain ⟨y', rfl⟩ := H.rho_surjective hq hCF1 hCF2 hF.out y
    have hu : IsPGroup 2 (zpowers h.aM) := isPGroup_zpowers_of_mul_self h.aM_mul_self
    obtain ⟨c, -, hc⟩ := Eight.exists_conj_eq_of_map hker hu hv y'
      (by rw [← hy, d.c_a, H.rho_aM])
    have hc' : h.a * e₀ = (c : X)⁻¹ * h.a * c := congrArg Subtype.val hc
    rcases hee with rfl | rfl
    · left
      exact ⟨c, hc'.symm⟩
    ·
      right; left
      refine ⟨h.x * c, ?_⟩
      calc (h.x * (c : X))⁻¹ * d.b * (h.x * c) = (c : X)⁻¹ * (h.x⁻¹ * d.b * h.x) * c := by group
        _ = (c : X)⁻¹ * (h.a * d.b) * c := by rw [d.xbx]
        _ = (c : X)⁻¹ * h.a * c * ((c : X)⁻¹ * d.b * c) := by group
        _ = h.a * e₀ * d.b := by rw [← hc', hcb c]
        _ = h.a * (e₀ * d.b) := by group
  ·
    obtain ⟨y', rfl⟩ := H.rho_surjective hq hCF1 hCF2 hF.out y
    set u : ↥h.M3 := ⟨h.a * d.z * d.tau, mul_mem (mul_mem haM d.z_mem_M3) d.tau_mem.2⟩ with hu
    have hzt : u = h.aM * ⟨d.z, d.z_mem_M3⟩ * ⟨d.tau, d.tau_mem.2⟩ := rfl
    have hu' : IsPGroup 2 (zpowers u) :=
      isPGroup_zpowers_of_mul_self (Subtype.ext (d.azt_sq hCF1 hCF2))
    obtain ⟨c, -, hc⟩ := Eight.exists_conj_eq_of_map hker hu' hv y' (by
      rw [← hy, hzt, map_mul, map_mul, H.rho_aM, ← d.c_a, ← d.c_z, d.rho_tau])
    have hc' : h.a * e₀ = (c : X)⁻¹ * (h.a * d.z * d.tau) * c := congrArg Subtype.val hc
    have hx1 : h.x⁻¹ * (h.a * d.z * d.tau) * h.x = h.a * d.tau := by
      rw [show h.x⁻¹ * (h.a * d.z * d.tau) * h.x =
        (h.x⁻¹ * h.a * h.x) * (h.x⁻¹ * d.z * h.x) * (h.x⁻¹ * d.tau * h.x) by group, H.a_x,
        d.z_x hq hCF1 hCF2 hF.l0 hF.sylowCent, d.tz_eq_conj hq hF,
        show h.a * d.z * (d.tau * d.z) = h.a * (d.z * d.tau) * d.z by group,
        ← d.tau_comm_z hCF1 hCF2,
        show h.a * (d.tau * d.z) * d.z = h.a * d.tau * (d.z * d.z) by group, d.z_sq, mul_one]
    rcases hee with rfl | rfl
    · left
      refine ⟨d.g * h.x⁻¹ * c, ?_⟩
      calc (d.g * h.x⁻¹ * c)⁻¹ * h.a * (d.g * h.x⁻¹ * c) =
            (c : X)⁻¹ * (h.x * (d.g⁻¹ * h.a * d.g) * h.x⁻¹) * c := by group
        _ = (c : X)⁻¹ * (h.x * (h.a * d.tau) * h.x⁻¹) * c := by rw [d.a_g]
        _ = (c : X)⁻¹ * (h.a * d.z * d.tau) * c := by rw [← hx1]; group
        _ = h.a * e := hc'.symm
    ·
      right; right
      have hx2 : h.x⁻¹ * (h.a * d.z * d.tau * d.b) * h.x = d.tau * d.b := by
        rw [show h.x⁻¹ * (h.a * d.z * d.tau * d.b) * h.x =
          (h.x⁻¹ * (h.a * d.z * d.tau) * h.x) * (h.x⁻¹ * d.b * h.x) by group, hx1, d.xbx,
          show h.a * d.tau * (h.a * d.b) = h.a * (d.tau * h.a) * d.b by group, d.tau_comm_a,
          show h.a * (h.a * d.tau) * d.b = (h.a * h.a) * d.tau * d.b by group,
          Six.a_mul_a_self h, one_mul]
      have hxgx := d.bz_conj_xgx hq hF
      refine ⟨(h.x * d.g * h.x) * h.x⁻¹ * c, ?_⟩
      calc ((h.x * d.g * h.x) * h.x⁻¹ * c)⁻¹ * (d.b * d.z) * ((h.x * d.g * h.x) * h.x⁻¹ * c) =
            (c : X)⁻¹ * (h.x * ((h.x * d.g * h.x)⁻¹ * (d.b * d.z) * (h.x * d.g * h.x)) *
              h.x⁻¹) * c := by group
        _ = (c : X)⁻¹ * (h.x * (d.tau * d.b) * h.x⁻¹) * c := by rw [hxgx]
        _ = (c : X)⁻¹ * (h.a * d.z * d.tau * d.b) * c := by rw [← hx2]; group
        _ = (c : X)⁻¹ * (h.a * d.z * d.tau) * c * ((c : X)⁻¹ * d.b * c) := by group
        _ = h.a * e₀ * d.b := by rw [← hc', hcb c]
        _ = h.a * (e₀ * d.b) := by group

end Q3Data

namespace Q3Data.LClass

variable {d : Q3Data H} (L : d.LClass)

theorem πa_isSwap (hq : h.IsQ3) (hF : Cat8.Q3Facts)
    (hW : L.πN ⟨h.a, d.a_mem_NE⟩ ∈ Eight.S6M.Wsub) : (L.πN ⟨h.a, d.a_mem_NE⟩).IsSwap := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  set B := L.base hq hF with hB
  have hBE : B.E = d.E := L.Eof_eq
  have haN : h.a ∈ B.N := by
    show h.a ∈ normalizer ((Eight.Eof L.c : Subgroup X) : Set X)
    rw [L.normalizer_Eof]
    exact d.a_mem_NE
  have hcard := B.card_centralizer ⟨h.a, haN⟩
  have hπ : B.π ⟨h.a, haN⟩ = L.πN ⟨h.a, d.a_mem_NE⟩ := rfl
  rw [hπ] at hcard
  have h16 : 16 ≤ Eight.S6M.fixlen [L.πN ⟨h.a, d.a_mem_NE⟩] := by
    rw [← hcard]
    have := d.card_E_centralizer_a hCF1 hCF2
    rwa [← hBE] at this
  have hWl : L.πN ⟨h.a, d.a_mem_NE⟩ ∈ Eight.S6M.Wlist := hW
  have h1 := List.all_eq_true.mp Eight.S6M.Wlist_fix8 _ hWl
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exfalso
    have hc := (L.πN_eq_one_iff ⟨h.a, d.a_mem_NE⟩).mp h1
    have haE := d.mem_E_of_comm hCF1 hCF2
      (isPGroup_zpowers_of_mul_self (Six.a_mul_a_self h)) fun e he => (hc e he).symm
    exact d.a_not_conj_E hq hF 1 haE (by group)
  · exact Eight.S6M.isSwap_of_mem h1
  · omega

theorem exists_conj_aE (hq : h.IsQ3) (hF : Cat8.Q3Facts)
    (ha : (L.πN ⟨h.a, d.a_mem_NE⟩).IsSwap) {w : X} (hwN : w ∈ d.NE) (hw2 : w * w = 1)
    (hsw : (L.πN ⟨w, hwN⟩).IsSwap) : ∃ m ∈ d.NE, ∃ e ∈ d.E, m * w * m⁻¹ = h.a * e := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  obtain ⟨x, y, hxy, hxy'⟩ := hsw
  obtain ⟨x', y', hxy₂, hxy₂'⟩ := ha
  obtain ⟨σ, hσ⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hxy hxy₂)
  obtain ⟨m₁, hm₁⟩ := L.πN_surjective hq hF σ
  set w' : X := (m₁ : X) * w * (m₁ : X)⁻¹ with hw'
  have hw'N : w' ∈ d.NE := mul_mem (mul_mem m₁.2 hwN) (inv_mem m₁.2)
  have hπw' : L.πN ⟨w', hw'N⟩ = L.πN ⟨h.a, d.a_mem_NE⟩ := by
    rw [show (⟨w', hw'N⟩ : ↥d.NE) = m₁ * ⟨w, hwN⟩ * m₁⁻¹ from rfl, map_mul, map_mul, map_inv,
      hm₁, hxy', hxy₂', hσ]
  have haw : h.a * w' ∈ d.CNE := by
    have hN : h.a * w' ∈ d.NE := mul_mem d.a_mem_NE hw'N
    refine Subgroup.mem_inf.mpr ⟨hN, mem_centralizer_iff.mpr fun e he => ?_⟩
    have h1 : L.πN ⟨h.a * w', hN⟩ = 1 := by
      rw [show (⟨h.a * w', hN⟩ : ↥d.NE) = ⟨h.a, d.a_mem_NE⟩ * ⟨w', hw'N⟩ from rfl, map_mul,
        hπw', hxy₂', Equiv.swap_mul_self]
    exact (L.πN_eq_one_iff _).mp h1 e he
  have hw'2 : w' * w' = 1 := by
    rw [hw', show (m₁ : X) * w * (m₁ : X)⁻¹ * ((m₁ : X) * w * (m₁ : X)⁻¹) =
      (m₁ : X) * (w * w) * (m₁ : X)⁻¹ by group, hw2, mul_one, mul_inv_cancel]
  obtain ⟨l, hl, e, he, hle⟩ := Eight.exists_conj_mem_mul (C₀ := d.CNE) (E := d.E)
    (fun k hk hk2 => d.mem_E_of_comm hCF1 hCF2 hk2 fun e he =>
      (mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2 e he).symm)
    (Six.a_mul_a_self h) hw'2 haw
  refine ⟨l * m₁, mul_mem (Subgroup.mem_inf.mp hl).1 m₁.2, e, he, ?_⟩
  rw [← hle, hw']
  group

end Q3Data.LClass

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
