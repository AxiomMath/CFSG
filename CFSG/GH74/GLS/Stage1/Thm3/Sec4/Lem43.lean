module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct3

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {O : Subgroup G → Subgroup G}
  {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop} {z : G} {S K₁ K₂ : Subgroup G}

namespace M4

variable [Finite G]

theorem not_mem_ZsK' (h : M4 O FA SD z S K₁ K₂) {w : G} (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hwz : w ≠ z) : w ∉ ZsM O (K₁ ⊔ K₂) := by
  intro hmem
  rcases h.inv_ZsK hmem hw2 with h1 | h1
  · exact hw1 h1
  · exact hwz h1

omit [Finite G] in
theorem conj_data {t g : G} (hg : g⁻¹ * z * g = t) (htC : t ∈ centralizer ({z} : Set G)) :
    (g * z * g⁻¹) * z = z * (g * z * g⁻¹) ∧ g⁻¹ * (g * z * g⁻¹) * g = z := by
  have e2 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
  refine ⟨?_, e2⟩
  have e1 : g⁻¹ * ((g * z * g⁻¹) * z) * g = z * t := by
    calc g⁻¹ * ((g * z * g⁻¹) * z) * g = (g⁻¹ * (g * z * g⁻¹) * g) * (g⁻¹ * z * g) := by group
      _ = z * t := by rw [e2, hg]
  have e1' : g⁻¹ * (z * (g * z * g⁻¹)) * g = z * t := by
    calc g⁻¹ * (z * (g * z * g⁻¹)) * g = (g⁻¹ * z * g) * (g⁻¹ * (g * z * g⁻¹) * g) := by group
      _ = t * z := by rw [e2, hg]
      _ = z * t := centralizer_comm htC
  have := mul_right_cancel (e1.trans e1'.symm)
  exact mul_left_cancel this

end M4

namespace M43

open M4

variable [Finite G]

theorem comp43 (h : M43 O FA SD z S K₁ K₂) (hA : H4A O z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) {t : G} (htS : t ∈ S) (htz : IsConj z t) (htne : t ≠ z)
    (htn : t ∈ normalizer (K : Set G)) : SD (Pm S K₁ K₂ ⊓ K ⊔ zpowers t) := by
  by_contra hSD
  obtain ⟨c0, hc0⟩ := isConj_iff.1 htz
  have ht2 : t * t = 1 := by
    rw [← hc0]
    calc c0 * z * c0⁻¹ * (c0 * z * c0⁻¹) = c0 * (z * z) * c0⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  have ht1 : t ≠ 1 := by
    intro h1
    apply h.z_ne
    have : c0 * z * c0⁻¹ = 1 := by rw [hc0, h1]
    calc z = c0⁻¹ * (c0 * z * c0⁻¹) * c0 := by group
      _ = 1 := by rw [this]; group
  have htC : t ∈ centralizer ({z} : Set G) := h.S_syl.1 htS
  have htnot := h.not_mem_ZsK' ht2 ht1 htne
  have hFA := h.he t htC htz htnot K hK
  rcases h.f19 K hK t htS (orderOf_two_iff.2 ⟨ht2, ht1⟩) htn hFA with
    hsd | ⟨u, huK, hut, hu4, hu2⟩
  · exact hSD hsd
  have hPpg : IsPGroup 2 ↥(Pm S K₁ K₂ ⊓ K) := h.P_pgroup.to_inf_left
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hPpg
  have hord : orderOf u ∣ 2 ^ a := ⟨2, by rw [← ha, ← hu2]; ring⟩
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hupg : IsPGroup 2 ↥(zpowers u) := IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have huz : u ∉ zpowers z := by
    intro hmem
    have hz2 : orderOf z = 2 := orderOf_two_iff.2 ⟨h.z_sq, h.z_ne⟩
    rcases (mem_zpowers_of_sq h.z_sq).1 hmem with h1 | h1
    · rw [h1, orderOf_one] at hu4; omega
    · rw [h1, hz2] at hu4; omega
  obtain ⟨g, hg⟩ := exists_conj_inv htz
  have hrecu : ∀ L, (L = K₁ ∨ L = K₂) → u ∈ normalizer (cj L g : Set G) := fun L hL =>
    h.rec1b t g hg htC K L hK hL htn u huK hupg huz hut.symm
  have huniq : ∀ x ∈ zpowers u, x * x = 1 → x = 1 ∨ x = z := fun x hx hx2 =>
    h.inv_comp hK ((zpowers_le.2 huK) hx) hx2
  obtain ⟨w, hwu, hw2⟩ := exists_sq_eq_of_unique_inv hupg huniq (Subgroup.mem_zpowers u) huz
  have hwn : ∀ L, (L = K₁ ∨ L = K₂) → w ∈ normalizer (cj L g : Set G) := fun L hL =>
    (zpowers_le.2 (hrecu L hL)) hwu
  obtain ⟨w', hw'⟩ : ∃ w', w' = g * z * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨hw'z, he2⟩ := conj_data hg htC
  rw [← hw'] at hw'z he2
  have hw'2 : w' * w' = 1 := by
    rw [hw']
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  have hw'1 : w' ≠ 1 := by
    intro h1
    apply h.z_ne
    calc z = g⁻¹ * w' * g := he2.symm
      _ = 1 := by rw [h1]; group
  have hw'ne : w' ≠ z := by
    intro h1
    apply htne
    calc t = g⁻¹ * z * g := hg.symm
      _ = g⁻¹ * w' * g := by rw [h1]
      _ = z := he2
  have hw'C : w' ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hw'z
  have hw'conj : IsConj z w' := isConj_iff.2 ⟨g, hw'.symm⟩
  have hw'not := h.not_mem_ZsK' hw'2 hw'1 hw'ne
  have hFA' : ∀ L, (L = K₁ ∨ L = K₂) → ¬ FA w' L := fun L hL => h.he w' hw'C hw'conj hw'not L hL
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = g * w * g⁻¹ := ⟨_, rfl⟩
  have hy₀2 : y₀ * y₀ = w' := by
    rw [hy₀, hw']
    calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hw2]
  have hy₀pg : IsPGroup 2 ↥(zpowers y₀) := by
    rw [hy₀]; exact isPGroup_zpowers_conj g (isPGroup_zpowers_of_mem hupg hwu)
  have hy₀n : ∀ L, (L = K₁ ∨ L = K₂) → y₀ ∈ normalizer (L : Set G) := fun L hL => by
    rw [hy₀]; exact mem_normalizer_cj (hwn L hL)
  have hw'ord : orderOf (y₀ * y₀) = 2 := by rw [hy₀2]; exact orderOf_two_iff.2 ⟨hw'2, hw'1⟩
  obtain ⟨k₁, hk₁, hk₁s⟩ := h.f12f K₁ (Or.inl rfl) y₀ hy₀pg (hy₀n K₁ (Or.inl rfl)) hw'ord
    (by rw [hy₀2]; exact hFA' K₁ (Or.inl rfl))
  obtain ⟨k₂, hk₂, hk₂s⟩ := h.f12f K₂ (Or.inr rfl) y₀ hy₀pg (hy₀n K₂ (Or.inr rfl)) hw'ord
    (by rw [hy₀2]; exact hFA' K₂ (Or.inr rfl))
  rw [hy₀2] at hk₁s hk₂s
  have hk₁C : k₁ ∈ centralizer ({z} : Set G) := h.K₁_le hk₁
  have hk₂C : k₂ ∈ centralizer ({z} : Set G) := h.K₂_le hk₂
  obtain ⟨c, hc⟩ : ∃ c, c = w' * k₁⁻¹ * k₂⁻¹ := ⟨_, rfl⟩
  have hcC : c ∈ centralizer ({z} : Set G) := by
    rw [hc]; exact mul_mem (mul_mem hw'C (inv_mem hk₁C)) (inv_mem hk₂C)
  have hu₁C : w' * k₁⁻¹ ∈ centralizer ({z} : Set G) := mul_mem hw'C (inv_mem hk₁C)
  have hu₂C : w' * k₂⁻¹ ∈ centralizer ({z} : Set G) := mul_mem hw'C (inv_mem hk₂C)
  have hc1 : ∀ x ∈ K₁, ⁅x, c⁆ ∈ O (K₁ ⊔ K₂) := by
    intro x hx
    have e : ⁅x, c⁆ = ⁅x, w' * k₁⁻¹⁆ * ((w' * k₁⁻¹) * ⁅x, k₂⁻¹⁆ * (w' * k₁⁻¹)⁻¹) := by
      simp only [commutatorElement_def, hc]; group
    rw [e]
    have h1 : ⁅x, w' * k₁⁻¹⁆ ∈ O (K₁ ⊔ K₂) := h.O_le_OK (Or.inl rfl) (hk₁s.2.2 x hx)
    have h2 : ⁅x, k₂⁻¹⁆ ∈ O (K₁ ⊔ K₂) :=
      h.O_le_OK (Or.inl rfl) ((h.cs₁ (inv_mem hk₂)).2.2 x hx)
    exact mul_mem h1 (h.C_norm_OK hu₁C h2)
  have hc2 : ∀ y ∈ K₂, ⁅y, c⁆ ∈ O (K₁ ⊔ K₂) := by
    intro y hy
    have hk₁' : k₂ * k₁⁻¹ * k₂⁻¹ ∈ K₁ :=
      (Subgroup.mem_normalizer_iff.1 (h.n₂₁ hk₂) _).1 (inv_mem hk₁)
    have e : ⁅y, c⁆ = ⁅y, w' * k₂⁻¹⁆ *
        ((w' * k₂⁻¹) * ⁅y, k₂ * k₁⁻¹ * k₂⁻¹⁆ * (w' * k₂⁻¹)⁻¹) := by
      simp only [commutatorElement_def, hc]; group
    rw [e]
    have h1 : ⁅y, w' * k₂⁻¹⁆ ∈ O (K₁ ⊔ K₂) := h.O_le_OK (Or.inr rfl) (hk₂s.2.2 y hy)
    have h2 : ⁅y, k₂ * k₁⁻¹ * k₂⁻¹⁆ ∈ O (K₁ ⊔ K₂) :=
      h.O_le_OK (Or.inr rfl) ((h.cs₂ hk₁').2.2 y hy)
    exact mul_mem h1 (h.C_norm_OK hu₂C h2)
  have hcsec : c ∈ secCent (K₁ ⊔ K₂) (O (K₁ ⊔ K₂)) := h.secCent_of_gen hcC hc1 hc2
  have hcE : c ∈ Em O z K₁ K₂ := ⟨hcsec, hcC⟩
  have hw'dec : w' = c * (k₂ * k₁) := by rw [hc]; group
  obtain ⟨P'', hP'', hw'P''⟩ := exists_syl2In_ge (isPGroup_zpowers_of_sq hw'2 hw'1)
    (zpowers_le.2 hw'C : zpowers w' ≤ centralizer ({z} : Set G))
  obtain ⟨c', hc'C, hcP''⟩ := h.S_syl.exists_conj hP''
  have hwS : c' * w' * c'⁻¹ ∈ S := by
    have : w' ∈ P'' := hw'P'' (Subgroup.mem_zpowers w')
    rw [hcP'', mem_cj] at this
    exact this
  have hwKE : c' * w' * c'⁻¹ ∈ (K₁ ⊔ K₂) ⊔ Em O z K₁ K₂ := by
    rw [hw'dec]
    have e : c' * (c * (k₂ * k₁)) * c'⁻¹ =
        (c' * c * c'⁻¹) * ((c' * k₂ * c'⁻¹) * (c' * k₁ * c'⁻¹)) := by group
    rw [e]
    exact mul_mem (mem_sup_right (h.E_norm hc'C hcE))
      (mem_sup_left (mul_mem (h.C_norm_K hc'C (mem_sup_right hk₂))
        (h.C_norm_K hc'C (mem_sup_left hk₁))))
  have hR := h.R_char hwS hwKE
  have hconj : IsConj z (c' * w' * c'⁻¹) := hw'conj.trans (isConj_iff.2 ⟨c', rfl⟩)
  have hz' := hA _ hR hconj
  apply hw'ne
  have hcz : c' * z = z * c' := centralizer_comm hc'C
  calc w' = c'⁻¹ * (c' * w' * c'⁻¹) * c' := by group
    _ = c'⁻¹ * z * c' := by rw [hz']
    _ = z := by
      calc c'⁻¹ * z * c' = c'⁻¹ * (z * c') := by group
        _ = c'⁻¹ * (c' * z) := by rw [hcz]
        _ = z := by group

theorem lemma43 (h : M43 O FA SD z S K₁ K₂) (hA : H4A O z S K₁ K₂) {t : G} (htS : t ∈ S)
    (htz : IsConj z t) (htne : t ≠ z) :
    Intch t K₁ K₂ ∨
      (SD (Pm S K₁ K₂ ⊓ K₁ ⊔ zpowers t) ∧ SD (Pm S K₁ K₂ ⊓ K₂ ⊔ zpowers t)) := by
  have htC : t ∈ centralizer ({z} : Set G) := h.S_syl.1 htS
  rcases h.perm t htC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right
    exact ⟨h.comp43 hA (Or.inl rfl) htS htz htne (cj_eq_iff_normalizer.1 h1),
      h.comp43 hA (Or.inr rfl) htS htz htne (cj_eq_iff_normalizer.1 h2)⟩
  · left; exact ⟨h1, h2⟩

end M43

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
