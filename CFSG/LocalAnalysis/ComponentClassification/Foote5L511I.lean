module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57H

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem dihedral_r_half_central {m : ℕ} (hm : 1 ≤ m) (g : DihedralGroup (2 ^ m)) :
    g * DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) =
      DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) * g := by
  rcases g with i | i
  · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
    congr 1
    have h2 : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
      rw [← Nat.cast_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hm, ZMod.natCast_self]
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left h2]

theorem dihedral_r_half_ne_one {m : ℕ} (hm : 1 ≤ m) :
    DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ 1 := by
  intro h1
  rw [DihedralGroup.one_def] at h1
  have h2 := DihedralGroup.r.inj h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  have h3 := Nat.le_of_dvd (by positivity) h2
  have h4 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
include h

theorem t_mul_self : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]

theorem exists_conj_mul_t_R (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {x : G}
    (hx : x ∈ S ⊓ L) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    ∃ d ∈ S ⊓ L, d * x * d⁻¹ = t * x := by
  classical
  obtain ⟨m, hm1, ⟨e⟩⟩ := h.exists_dihedral_R
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm : m = 1 := by omega
    subst hm
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    apply hab
    have hcomm : ∀ u v : DihedralGroup (2 ^ 1), u * v = v * u := by decide
    have h1 := hcomm (e ⟨a, ha⟩) (e ⟨b, hb⟩)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  set d := e ⟨x, hx⟩ with hd
  have hd2 : d * d = 1 := by rw [hd, ← map_mul, ← map_one e]; congr 1; exact Subtype.ext hx2
  have hdc : d ∉ center (DihedralGroup (2 ^ m)) := by
    intro hdZ
    have h1 : ∀ ρ ∈ S ⊓ L, x * ρ = ρ * x := by
      intro ρ hρ
      have h2 := (mem_center_iff.mp hdZ) (e ⟨ρ, hρ⟩)
      rw [hd, ← map_mul, ← map_mul] at h2
      exact (congrArg Subtype.val (e.injective h2)).symm
    rcases h.center_R hna hx h1 with h2 | h2
    · exact hx1 h2
    · exact hxt h2
  have hc := dihedral_conj_eq_mul hm2 hd2 hdc
  set ρD := DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) with hρD
  set tD := DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) with htD
  have htt : ((e.symm tD : ↥(S ⊓ L)) : G) = t := by
    have h1 : ∀ ρ ∈ S ⊓ L, ((e.symm tD : ↥(S ⊓ L)) : G) * ρ = ρ * (e.symm tD : ↥(S ⊓ L)) := by
      intro ρ hρ
      have h2 := dihedral_r_half_central (by omega) (e ⟨ρ, hρ⟩)
      have h3 := congrArg e.symm h2
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h3
      exact (congrArg Subtype.val h3).symm
    rcases h.center_R hna (e.symm tD).2 h1 with h2 | h2
    · exfalso
      apply dihedral_r_half_ne_one (m := m) (by omega)
      have h3 : e.symm tD = 1 := Subtype.ext h2
      rw [← htD, ← MulEquiv.apply_symm_apply e tD, h3, map_one]
    · exact h2
  set ρ := ((e.symm ρD : ↥(S ⊓ L)) : G) with hρ
  have hxρ : x * ρ * x⁻¹ = ρ * t := by
    have h1 := congrArg e.symm hc
    rw [map_mul, map_mul, map_inv, hd, MulEquiv.symm_apply_apply, map_mul] at h1
    have h2 := congrArg Subtype.val h1
    simp only [coe_mul, coe_inv] at h2
    rw [htt] at h2
    exact h2
  refine ⟨ρ⁻¹, inv_mem (e.symm ρD).2, ?_⟩
  calc ρ⁻¹ * x * ρ⁻¹⁻¹ = ρ⁻¹ * ((x * ρ * x⁻¹) * x) := by group
    _ = ρ⁻¹ * ((ρ * t) * x) := by rw [hxρ]
    _ = t * x := by group

theorem exists_conj_t_of_noncentral (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {x : G}
    (hx : x ∈ S ⊓ L) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    ∃ y : G, y * x * y⁻¹ = x ∧ y * t * y⁻¹ = x * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 := h.t_mul_self
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  obtain ⟨k, hkL, hk⟩ := h.exists_conj_t hx hxo
  have hxtc : x * t = t * x := (h.tZ x (mem_inf.mp hx).1)
  set A := kleinFourOfCommutingInvolutions x t hx2 ht2 hxtc with hAdef
  have hA4 : Nat.card A = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions x t hx2 ht2 hx1 h.t_ne_one hxt hxtc).card_four
  have hAR : A ≤ S ⊓ L := fun a ha => by
    rcases (mem_kleinFour_iff hx2 ht2 hxtc).mp ha with rfl | rfl | rfl | rfl
    · exact mul_mem hx h.tR
    · exact hx
    · exact h.tR
    · exact one_mem _
  have hAx : ∀ a ∈ A, a * x = x * a := fun a ha => by
    rcases (mem_kleinFour_iff hx2 ht2 hxtc).mp ha with rfl | rfl | rfl | rfl
    · rw [mul_assoc, ← hxtc, ← mul_assoc]
    · rfl
    · exact hxtc.symm
    · rw [one_mul, mul_one]
  set A' := conjugate A k with hA'def
  have hA'X : A' ≤ L ⊓ centralizer ({t} : Set G) := by
    intro a ha
    rw [hA'def, mem_conjugate_iff] at ha
    refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · have h1 := mul_mem (mul_mem (inv_mem hkL) (mem_inf.mp (hAR ha)).2) hkL
      rwa [show k⁻¹ * (k * a * k⁻¹) * k = a by group] at h1
    · have h1 := hAx _ ha
      calc a * t = k⁻¹ * ((k * a * k⁻¹) * x) * k := by rw [← hk]; group
        _ = k⁻¹ * (x * (k * a * k⁻¹)) * k := by rw [h1]
        _ = t * a := by rw [← hk]; group
  have hA'2 : IsPGroup 2 A' := IsPGroup.of_card (n := 2) (by
    rw [hA'def, card_conjugate_eq_card, hA4]
    norm_num)
  have hRX : IsSylowOf 2 (S ⊓ L) (L ⊓ centralizer ({t} : Set G)) :=
    h.R_sylow.of_le (le_inf inf_le_right fun ρ hρ =>
      mem_centralizer_singleton_iff.mpr (h.tZ ρ (mem_inf.mp hρ).1)) inf_le_left
  obtain ⟨c, hcX, hc⟩ := exists_conj_le_of_isSylowOf hRX hA'X hA'2
  have hct : c * t = t * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hcX).2
  set g := k * c with hg
  have hgx : g⁻¹ * x * g = t := by
    calc g⁻¹ * x * g = c⁻¹ * (k⁻¹ * x * k) * c := by rw [hg]; group
      _ = c⁻¹ * (t * c) := by rw [hk, mul_assoc]
      _ = t := by rw [← hct]; group
  have ht₁ : g⁻¹ * t * g ∈ S ⊓ L := by
    have h1 := hc (k⁻¹ * t * k) (by
      rw [hA'def, mem_conjugate_iff, show k * (k⁻¹ * t * k) * k⁻¹ = t by group]
      exact (mem_kleinFour_iff hx2 ht2 hxtc).mpr (Or.inr (Or.inr (Or.inl rfl))))
    rwa [show c⁻¹ * (k⁻¹ * t * k) * c = g⁻¹ * t * g by rw [hg]; group] at h1
  have ht₁2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    rw [show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht2]
    group
  have ht₁1 : g⁻¹ * t * g ≠ 1 := fun h1 => h.t_ne_one (by
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have ht₁t : g⁻¹ * t * g ≠ t := fun h1 => hxt (by
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [hgx, h1]
      _ = t := by group)
  obtain ⟨d₀, hd₀, hd₀c⟩ := h.exists_conj_mul_t_R hna ht₁ ht₁2 ht₁1 ht₁t
  have hd₀t : d₀ * t = t * d₀ := h.tZ d₀ (mem_inf.mp hd₀).1
  have hgt : g * t * g⁻¹ = x := by
    calc g * t * g⁻¹ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hgx]
      _ = x := by group
  refine ⟨g * d₀ * g⁻¹, ?_, ?_⟩
  · calc g * d₀ * g⁻¹ * x * (g * d₀ * g⁻¹)⁻¹ = g * (d₀ * (g⁻¹ * x * g) * d₀⁻¹) * g⁻¹ := by
          group
      _ = g * (d₀ * t * d₀⁻¹) * g⁻¹ := by rw [hgx]
      _ = g * t * g⁻¹ := by rw [hd₀t, mul_inv_cancel_right]
      _ = x := hgt
  · calc g * d₀ * g⁻¹ * t * (g * d₀ * g⁻¹)⁻¹ = g * (d₀ * (g⁻¹ * t * g) * d₀⁻¹) * g⁻¹ := by
          group
      _ = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by rw [hd₀c]
      _ = (g * t * g⁻¹) * t := by group
      _ = x * t := by rw [hgt]

end Sec5

end CFSG.ComponentClassification.Foote5
