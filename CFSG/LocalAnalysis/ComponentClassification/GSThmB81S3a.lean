module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9d

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

theorem Three81.comm_of_odd_of_comm_mem {G : Type*} [Group G] {Q₀ : Subgroup G}
    (hQ₀ : IsPGroup 2 Q₀) {y q : G} (ho : Odd (orderOf y)) (hc : y * q * y⁻¹ * q⁻¹ ∈ Q₀)
    (hcy : ∀ w ∈ Q₀, y * w = w * y) : y * q = q * y := by
  set c := y * q * y⁻¹ * q⁻¹ with hcdef
  have hyc : y * c * y⁻¹ = c := by rw [hcy c hc]; group
  have hk : ∀ k : ℕ, y ^ k * q * (y ^ k)⁻¹ = c ^ k * q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : y * c ^ k * y⁻¹ = c ^ k := by rw [← conj_pow, hyc]
      calc y ^ (k + 1) * q * (y ^ (k + 1))⁻¹ = y * (y ^ k * q * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = (y * c ^ k * y⁻¹) * (y * q * y⁻¹) := by rw [ih]; group
        _ = c ^ (k + 1) * q := by rw [hck, pow_succ, hcdef]; group
  have h1 := hk (orderOf y)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, right_eq_mul] at h1
  obtain ⟨m, hm⟩ := hQ₀ ⟨c, hc⟩
  have h2 : orderOf c ∣ 2 ^ m :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hm)
  have h3 : orderOf c ∣ orderOf y := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf c = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr ho)) h2 h3
  rw [orderOf_eq_one_iff, hcdef] at h4
  calc y * q = y * q * y⁻¹ * q⁻¹ * (q * y) := by group
    _ = q * y := by rw [h4, one_mul]

theorem Three81.comm_of_hasNormalPComplement {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : HasNormalPComplement 2 Γ) {x r : Γ} (hx : Odd (orderOf x))
    (hc : ∃ k : ℕ, (x * r * x⁻¹ * r⁻¹) ^ 2 ^ k = 1) : x * r = r * x := by
  obtain ⟨N, hN, hcop, hq⟩ := hΓ
  have hxN : x ∈ N := by
    obtain ⟨k, hk⟩ := hq (QuotientGroup.mk x)
    have h1 : orderOf (QuotientGroup.mk (s := N) x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (QuotientGroup.mk (s := N) x) ∣ orderOf x :=
      orderOf_map_dvd (QuotientGroup.mk' N) x
    have h3 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx))
      h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  have hcN : x * r * x⁻¹ * r⁻¹ ∈ N := by
    rw [show x * r * x⁻¹ * r⁻¹ = x * (r * x⁻¹ * r⁻¹) by group]
    exact mul_mem hxN (hN.conj_mem _ (inv_mem hxN) r)
  obtain ⟨k, hk⟩ := hc
  have h1 : orderOf (x * r * x⁻¹ * r⁻¹) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (x * r * x⁻¹ * r⁻¹) ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk _ hcN]
    exact orderOf_dvd_natCard _
  have h3 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hcop) h1 h2
  rw [orderOf_eq_one_iff] at h3
  calc x * r = x * r * x⁻¹ * r⁻¹ * (r * x) := by group
    _ = r * x := by rw [h3, one_mul]

theorem Three81.eq_one_of_mem_oddCoreIn {G : Type*} [Group G] [Finite G] {J : Subgroup G}
    {w : G} (hw : w ∈ oddCoreIn J) {k : ℕ} (hk : w ^ 2 ^ k = 1) : w = 1 := by
  have h1 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf w ∣ Nat.card (oddCoreIn J) := by
    rw [← Subgroup.orderOf_mk _ hw]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime 2 (Nat.card (oddCoreIn J)) := by
    rw [show oddCoreIn J = (pPrimeCore 2 ↥J).map J.subtype from rfl,
      card_map_of_injective J.subtype_injective]
    exact pPrimeCore_coprime_card
  have h3 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hcop) h1 h2
  rwa [orderOf_eq_one_iff] at h3

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

namespace Data

variable {H₁ : h.L81Hyp} (d : Data H₁)

theorem b_comm_z : d.b * d.z = d.z * d.b := mem_centralizer_iff.mp d.z_S d.b d.b_mem_S

theorem b_comm_a : d.b * h.a = h.a * d.b := H₁.NP_eq.2.2 d.b d.b_mem_B

theorem b_ne_a : d.b ≠ h.a := by
  intro hba
  have h1 : d.b ∈ h.B ⊓ zpowers h.a := mem_inf.mpr ⟨d.b_mem_B, hba ▸ mem_zpowers _⟩
  rw [H₁.NP_eq.2.1, mem_bot] at h1
  have h2 := d.b_ord
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem comm_b_mem_oddCoreIn {r : H} (hr : r ∈ coreActionKernel h.J)
    (hrc : (d.b * d.z) * r = r * (d.b * d.z)) : d.b⁻¹ * r⁻¹ * d.b * r ∈ oddCoreIn h.J := by
  have hz : d.z⁻¹ * r⁻¹ * d.z * r ∈ oddCoreIn h.J := (mem_coreActionKernel.mp hr).2 d.z d.z_mem_J
  have h1 : r⁻¹ * (d.b * d.z) * r = d.b * d.z := by
    rw [mul_assoc, hrc, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 : d.b⁻¹ * r⁻¹ * d.b * r = d.z * (d.z⁻¹ * r⁻¹ * d.z * r)⁻¹ * d.z⁻¹ := by
    calc d.b⁻¹ * r⁻¹ * d.b * r = d.b⁻¹ * (r⁻¹ * (d.b * d.z) * r) * (r⁻¹ * d.z⁻¹ * r) := by group
      _ = d.b⁻¹ * (d.b * d.z) * (r⁻¹ * d.z⁻¹ * r) := by rw [h1]
      _ = d.z * (d.z⁻¹ * r⁻¹ * d.z * r)⁻¹ * d.z⁻¹ := by group
  rw [h2]
  exact (mem_normalizer_iff.mp (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.J
    (pPrimeCore 2 ↥h.J) (le_normalizer d.z_mem_J)) _).mp (inv_mem hz)

theorem exists_four_of_le_kernel {Q₀ : Subgroup H} (hQ₀ : IsPGroup 2 Q₀)
    (hle : Q₀ ≤ Y9 h ⊓ centralizer ({d.b * d.z} : Set H)) :
    ∃ e : H, e * e = 1 ∧ e * h.a = h.a * e ∧
      ∀ w ∈ Q₀, w = 1 ∨ w = h.a ∨ w = e ∨ w = h.a * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Y9 h ⊓ centralizer ({d.b * d.z} : Set H) with hK
  have hbK : d.b ∈ K := by
    refine mem_inf.mpr ⟨P_le_Y9 h d.b_mem_P, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [mul_assoc, ← d.b_comm_z, ← mul_assoc]
  have hb2 : IsPGroup 2 ((zpowers d.b).subgroupOf K) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, d.b_ord, pow_one])).comap_subtype
  obtain ⟨R₀, hR₀⟩ := hb2.exists_le_sylow
  set R : Subgroup H := (R₀ : Subgroup ↥K).map K.subtype with hR
  have hR2 : IsPGroup 2 R := R₀.isPGroup'.map _
  have hRK : R ≤ K := map_subtype_le _
  have hbR : d.b ∈ R := ⟨⟨d.b, hbK⟩, hR₀ (mem_subgroupOf.mpr (mem_zpowers _)), rfl⟩
  have hRb : ∀ r ∈ R, r * d.b = d.b * r := by
    intro r hr
    obtain ⟨hrY, hrc⟩ := mem_inf.mp (hRK hr)
    have h1 := d.comm_b_mem_oddCoreIn (mem_inf.mp hrY).2
      (mem_centralizer_singleton_iff.mp hrc).symm
    have h2 : d.b⁻¹ * r⁻¹ * d.b * r ∈ R :=
      mul_mem (mul_mem (mul_mem (inv_mem hbR) (inv_mem hr)) hbR) hr
    obtain ⟨k, hk⟩ := hR2 ⟨_, h2⟩
    have h3 := Three81.eq_one_of_mem_oddCoreIn h1 (k := k) (by simpa using congrArg Subtype.val hk)
    calc r * d.b = d.b * r * (d.b⁻¹ * r⁻¹ * d.b * r)⁻¹ := by group
      _ = d.b * r := by rw [h3, inv_one, mul_one]
  obtain ⟨g, hgY, hgR⟩ := exists_conjugate_le_of_sylow (P_sylow_Y9 H₁)
    (hRK.trans inf_le_left) hR2
  have hconj : ∀ r ∈ R, g⁻¹ * r * g ∈ h.P := fun r hr => hgR (by
    rw [mem_conjugate_iff, show g * (g⁻¹ * r * g) * g⁻¹ = r by group]
    exact hr)
  have hga1 := mem_centralizer_singleton_iff.mp (mem_inf.mp hgY).1
  have hga : g⁻¹ * h.a * g = h.a := by rw [mul_assoc, ← hga1, inv_mul_cancel_left]
  have hga' : g * h.a * g⁻¹ = h.a := by rw [hga1, mul_inv_cancel_right]
  obtain ⟨β, hPres⟩ := d.pres
  have hpa : d.p ^ (orderOf d.p / 2) = h.a := d.p_a
  have heP : g⁻¹ * d.b * g ∈ h.P := hconj _ hbR
  have he2 : g⁻¹ * d.b * g * (g⁻¹ * d.b * g) = 1 := by
    rw [show g⁻¹ * d.b * g * (g⁻¹ * d.b * g) = g⁻¹ * (d.b * d.b) * g by group, d.b_mul_self]
    group
  have hep : g⁻¹ * d.b * g ∉ zpowers d.p := by
    intro hm
    rcases hPres.eq_one_or_a hm he2 with h1 | h1
    · have h2 := d.b_ord
      rw [show d.b = 1 by
        calc d.b = g * (g⁻¹ * d.b * g) * g⁻¹ := by group
          _ = 1 := by rw [h1]; group, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · apply d.b_ne_a
      calc d.b = g * (g⁻¹ * d.b * g) * g⁻¹ := by group
        _ = g * h.a * g⁻¹ := by rw [h1, hpa]
        _ = h.a := hga'
  obtain ⟨i, hi | hi⟩ := hPres.mem_cases heP
  · exact absurd (hi ▸ zpow_mem (mem_zpowers _) i) hep
  have hRsub : ∀ r ∈ R, r = 1 ∨ r = h.a ∨ r = d.b ∨ r = h.a * d.b := by
    intro r hr
    have h1 : g⁻¹ * r * g * (d.p ^ i * d.b) = d.p ^ i * d.b * (g⁻¹ * r * g) := by
      rw [← hi, show g⁻¹ * r * g * (g⁻¹ * d.b * g) = g⁻¹ * (r * d.b) * g by group, hRb r hr]
      group
    have hback : ∀ u : H, g⁻¹ * r * g = u → r = g * u * g⁻¹ := fun u hu => by
      rw [← hu]; group
    rcases hPres.mem_of_comm i (hconj r hr) h1 with h2 | h2 | h2 | h2
    · left
      rw [hback _ h2]; group
    · right; left
      rw [hback _ h2, hpa, hga']
    · right; right; left
      rw [hback _ h2, ← hi]; group
    · right; right; right
      rw [hback _ h2, hpa, ← hi, show g * (h.a * (g⁻¹ * d.b * g)) * g⁻¹ =
        (g * h.a * g⁻¹) * d.b by group, hga']
  have hR₀eq : (R₀ : Subgroup ↥K) = R.subgroupOf K := by
    rw [hR]
    exact (comap_map_eq_self_of_injective K.subtype_injective _).symm
  obtain ⟨k, hkK, hkQ⟩ := exists_conjugate_le_of_sylow ⟨R₀, hR₀eq⟩ hle hQ₀
  have hka : k * h.a * k⁻¹ = h.a := by
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hkK).1).1
    rw [h1, mul_inv_cancel_right]
  refine ⟨k * d.b * k⁻¹, ?_, ?_, ?_⟩
  · rw [show k * d.b * k⁻¹ * (k * d.b * k⁻¹) = k * (d.b * d.b) * k⁻¹ by group, d.b_mul_self]
    group
  · calc k * d.b * k⁻¹ * h.a = k * d.b * (k⁻¹ * h.a * k) * k⁻¹ := by group
      _ = k * (d.b * h.a) * k⁻¹ := by
          rw [show k⁻¹ * h.a * k = h.a by
            calc k⁻¹ * h.a * k = k⁻¹ * (k * h.a * k⁻¹) * k := by rw [hka]
              _ = h.a := by group]
          group
      _ = k * (h.a * d.b) * k⁻¹ := by rw [d.b_comm_a]
      _ = (k * h.a * k⁻¹) * (k * d.b * k⁻¹) := by group
      _ = h.a * (k * d.b * k⁻¹) := by rw [hka]
  · intro w hw
    have h1 : k⁻¹ * w * k ∈ R := hkQ (by
      rw [mem_conjugate_iff, show k * (k⁻¹ * w * k) * k⁻¹ = w by group]
      exact hw)
    have hw' : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
    rcases hRsub _ h1 with h2 | h2 | h2 | h2 <;> rw [hw', h2]
    · left; group
    · right; left; exact hka
    · right; right; left; rfl
    · right; right; right
      rw [show k * (h.a * d.b) * k⁻¹ = (k * h.a * k⁻¹) * (k * d.b * k⁻¹) by group, hka]

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
