module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue77a

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

namespace Cfg7

theorem core77 (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) (hc73 : Concl73 z S K₁ K₂)
    (hΩ : ∀ x ∈ S, orderOf x = 2 → x ∈ Pz S z ⊔ zpowers t) {d₀ y : G} (hyS₁ : y ∈ S1 S K₁)
    (hyP : y ∉ Pz S z) (hyt : y * t = t * y) (hyy : y * y = d₀) (hd₀2 : d₀ * d₀ = 1) (hd₀1 : d₀ ≠ 1)
    (hconj : IsConj z (z * d₀ * t))
    (hno : ∀ t₁ ∈ ({t, z * d₀ * t} : Set G), ∀ y₁ ∈ ({y, y * z} : Set G), ∀ g : G,
      g⁻¹ * t₁ * g = z → g⁻¹ * y₁ * g ∉ Pz S z) : False := by
  have hyS : y ∈ S := hyS₁.1
  have hzS : z ∈ S := h.z_mem_S hII
  have htS : t ∈ S := h.ch.t_mem
  have hzP : z ∈ Pz S z := h.z_mem_Pz hII
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII hyS)
  have hzy : z * y = y * z := hyz.symm
  have hty : t * y = y * t := hyt.symm
  have hz2 := h.z_sq
  have ht2 := h.t_sq
  have hy4 : y ^ 4 = 1 := by
    have e4 : y ^ 4 = (y * y) * (y * y) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [e4, hyy, hd₀2]
  have hy2 : y ^ 2 ≠ 1 := by
    intro hh
    apply hd₀1
    rw [← hyy, ← pow_two]
    exact hh
  have hyo : orderOf y = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := y) (by simpa using hy2) (by simpa using hy4)
    simpa using this
  have hS₀S : Pz S z ⊔ zpowers t ≤ S := by
    rw [h.Pz_eq_sup hII]
    exact h.Y0_le hII
  have hyS₀ : y ∉ Pz S z ⊔ zpowers t := by
    intro hy
    rcases h.S₀_elems hII hy with hP | ⟨p, hp, hpe⟩
    · exact hyP hP
    · apply h.t_nS1
      have : p⁻¹ * y ∈ S1 S K₁ :=
        (S1 S K₁).mul_mem ((S1 S K₁).inv_mem (h.Pz_le_S1 hII hp)) hyS₁
      rwa [hpe, inv_mul_cancel_left] at this
  have hS₀idx : (Pz S z ⊔ zpowers t).relIndex S = 2 := by
    have hle : (Pz S z ⊔ zpowers t).relIndex S ≤ 2 := by
      rw [h.Pz_eq_sup hII]
      exact h.Y0_relIndex hII hc73
    have hpos := C73.relIndex_pos (Pz S z ⊔ zpowers t) S
    have hne : (Pz S z ⊔ zpowers t).relIndex S ≠ 1 := fun h1 =>
      hyS₀ (Subgroup.relIndex_eq_one.1 h1 hyS)
    omega
  have hord : ∀ w ∈ S, w ∉ Pz S z ⊔ zpowers t → orderOf y ≤ orderOf w := by
    intro w hw hwn
    rw [hyo]
    apply four_le_orderOf (h.S_pgroup hII) hw
    · rintro rfl
      exact hwn (one_mem _)
    · intro h2
      exact hwn (hΩ w hw h2)
  obtain ⟨g, hgy, hgC⟩ := h.transfer_gen hII (Pz S z ⊔ zpowers t) y hS₀S hS₀idx hyS hyS₀ hord
  have hyd : d₀ * y = y * d₀ := by rw [← hyy]; group
  have hd₀S : d₀ ∈ S := by rw [← hyy]; exact S.mul_mem hyS hyS
  have hzd₀t : z * d₀ * t ∈ S := S.mul_mem (S.mul_mem hzS hd₀S) htS
  have hzd₀ty : z * d₀ * t * y = y * (z * d₀ * t) := by
    calc z * d₀ * t * y = z * d₀ * (t * y) := by group
      _ = z * d₀ * (y * t) := by rw [hty]
      _ = z * (d₀ * y) * t := by group
      _ = z * (y * d₀) * t := by rw [hyd]
      _ = (z * y) * d₀ * t := by group
      _ = (y * z) * d₀ * t := by rw [hzy]
      _ = y * (z * d₀ * t) := by group
  have hgz : g⁻¹ * z * g ∈ S := hgC z hzS hzy
  have hgt : g⁻¹ * t * g ∈ S := hgC t htS hty
  have hgzdt : g⁻¹ * (z * d₀ * t) * g ∈ S := hgC _ hzd₀t hzd₀ty
  have hgzo : orderOf (g⁻¹ * z * g) = 2 :=
    orderOf_eq_two_of_isConj h.std.std.orderOf_z (isConj_iff.2 ⟨g⁻¹, by group⟩)
  have hgto : orderOf (g⁻¹ * t * g) = 2 :=
    orderOf_eq_two_of_isConj h.t_ord (isConj_iff.2 ⟨g⁻¹, by group⟩)
  have hgzdto : orderOf (g⁻¹ * (z * d₀ * t) * g) = 2 :=
    orderOf_eq_two_of_isConj (orderOf_eq_two_of_isConj h.std.std.orderOf_z hconj)
      (isConj_iff.2 ⟨g⁻¹, by group⟩)
  have claim1 : ∀ y₁ ∈ ({y, y * z} : Set G), g⁻¹ * y₁ * g ∉ Pz S z := by
    intro y₁ hy₁ hy₁P
    have hcase : y₁ = y ∨ y₁ = y * z := by simpa using hy₁
    have hy₁sq : y₁ * y₁ = d₀ := by
      rcases hcase with rfl | rfl
      · exact hyy
      · calc y * z * (y * z) = y * (z * y) * z := by group
          _ = y * (y * z) * z := by rw [hzy]
          _ = (y * y) * (z * z) := by group
          _ = d₀ := by rw [hyy, hz2, mul_one]
    have hy₁S : y₁ ∈ S := by
      rcases hcase with rfl | rfl
      · exact hyS
      · exact S.mul_mem hyS hzS
    have hy₁nP : y₁ ∉ Pz S z := by
      rcases hcase with rfl | rfl
      · exact hyP
      · intro hh
        apply hyP
        have := (Pz S z).mul_mem hh ((Pz S z).inv_mem hzP)
        simpa using this
    have hdg : g⁻¹ * d₀ * g ∈ Pz S z := by
      have : g⁻¹ * d₀ * g = (g⁻¹ * y₁ * g) * (g⁻¹ * y₁ * g) := by rw [← hy₁sq]; group
      rw [this]
      exact (Pz S z).mul_mem hy₁P hy₁P
    have hnotP : ∀ t₁ ∈ ({t, z * d₀ * t} : Set G), g⁻¹ * t₁ * g ∉ Pz S z := by
      intro t₁ ht₁ ht₁P
      have hct : IsConj z t₁ := by
        rcases (show t₁ = t ∨ t₁ = z * d₀ * t by simpa using ht₁) with rfl | rfl
        · exact h.ch.t_conj
        · exact hconj
      have hcg : IsConj z (g⁻¹ * t₁ * g) := hct.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
      exact hno t₁ ht₁ y₁ hy₁ g (h.std.nonfused _ ht₁P hcg) hy₁P
    obtain ⟨p₁, hp₁, e₁⟩ : ∃ p ∈ Pz S z, g⁻¹ * t * g = p * t := by
      rcases h.S₀_elems hII (hΩ _ hgt hgto) with hP | ⟨p, hp, e⟩
      · exact absurd hP (hnotP t (by simp))
      · exact ⟨p, hp, e⟩
    obtain ⟨p₂, hp₂, e₂⟩ : ∃ p ∈ Pz S z, g⁻¹ * (z * d₀ * t) * g = p * t := by
      rcases h.S₀_elems hII (hΩ _ hgzdt hgzdto) with hP | ⟨p, hp, e⟩
      · exact absurd hP (hnotP (z * d₀ * t) (by simp))
      · exact ⟨p, hp, e⟩
    have hzd : g⁻¹ * (z * d₀) * g ∈ Pz S z := by
      have e : g⁻¹ * (z * d₀) * g = (g⁻¹ * (z * d₀ * t) * g) * (g⁻¹ * t * g) := by
        calc g⁻¹ * (z * d₀) * g = g⁻¹ * (z * d₀ * (t * t)) * g := by rw [ht2, mul_one]
          _ = (g⁻¹ * (z * d₀ * t) * g) * (g⁻¹ * t * g) := by group
      rw [e, e₁, e₂]
      have : p₂ * t * (p₁ * t) = p₂ * (t * p₁ * t⁻¹) := by
        calc p₂ * t * (p₁ * t) = p₂ * (t * p₁ * t) := by group
          _ = p₂ * (t * p₁ * t⁻¹) := by rw [h.t_inv]
      rw [this]
      exact (Pz S z).mul_mem hp₂ (h.normP hII t htS p₁ hp₁)
    have hgzP : g⁻¹ * z * g ∈ Pz S z := by
      have e : g⁻¹ * z * g = (g⁻¹ * (z * d₀) * g) * (g⁻¹ * d₀ * g)⁻¹ := by group
      rw [e]
      exact (Pz S z).mul_mem hzd ((Pz S z).inv_mem hdg)
    have hgz_eq : g⁻¹ * z * g = z := h.std.nonfused _ hgzP (isConj_iff.2 ⟨g⁻¹, by group⟩)
    exact hy₁nP (h.P_of_conj hII hc73 hy₁S hgz_eq hy₁P)
  have hy1 := claim1 y (by simp)
  have hy2 := claim1 (y * z) (by simp)
  obtain ⟨p₁, hp₁, e₁⟩ : ∃ p ∈ Pz S z, g⁻¹ * y * g = p * t := by
    rcases h.S₀_elems hII hgy with hP | ⟨p, hp, e⟩
    · exact absurd hP hy1
    · exact ⟨p, hp, e⟩
  have hyzg : g⁻¹ * (y * z) * g ∈ Pz S z ⊔ zpowers t := by
    have : g⁻¹ * (y * z) * g = (g⁻¹ * y * g) * (g⁻¹ * z * g) := by group
    rw [this]
    exact (Pz S z ⊔ zpowers t).mul_mem hgy (hΩ _ hgz hgzo)
  obtain ⟨p₂, hp₂, e₂⟩ : ∃ p ∈ Pz S z, g⁻¹ * (y * z) * g = p * t := by
    rcases h.S₀_elems hII hyzg with hP | ⟨p, hp, e⟩
    · exact absurd hP hy2
    · exact ⟨p, hp, e⟩
  have hgzP : g⁻¹ * z * g ∈ Pz S z := by
    have e : g⁻¹ * z * g = t * (p₁⁻¹ * p₂) * t⁻¹ := by
      calc g⁻¹ * z * g = (g⁻¹ * y * g)⁻¹ * (g⁻¹ * (y * z) * g) := by group
        _ = (p₁ * t)⁻¹ * (p₂ * t) := by rw [e₁, e₂]
        _ = t⁻¹ * (p₁⁻¹ * p₂) * t := by group
        _ = t * (p₁⁻¹ * p₂) * t⁻¹ := by rw [h.t_inv]
    rw [e]
    exact h.normP hII t htS _ ((Pz S z).mul_mem ((Pz S z).inv_mem hp₁) hp₂)
  have hgz_eq : g⁻¹ * z * g = z := h.std.nonfused _ hgzP (isConj_iff.2 ⟨g⁻¹, by group⟩)
  have hyg : g⁻¹ * y * g ∈ S1 S K₁ := h.S1_conj hII hyS₁ hgz_eq (hS₀S hgy)
  apply h.t_nS1
  have : p₁⁻¹ * (g⁻¹ * y * g) ∈ S1 S K₁ :=
    (S1 S K₁).mul_mem ((S1 S K₁).inv_mem (h.Pz_le_S1 hII hp₁)) hyg
  rwa [e₁, inv_mul_cancel_left] at this

end Cfg7

theorem lemma_7_7 (hII : II4_4_4_center) (hL76 : L76_struct) (hL77 : L77_no_conj) : Lemma7_7 := by
  intro G _ _ z S K₁ K₂ t u q h hc73 hc74 hidx D hD
  rcases hD.dih_or_sd with hdih | hsd
  · exact hdih
  · exfalso
    have h16 : 16 ≤ Nat.card ↥(Pof S K₁) := h.sd_card_ge hII hidx hD hsd
    obtain ⟨u₁, hu₁P, hu₁sq, -, hcen, ⟨y, hyD, hyP, hyy, -⟩, hΩ⟩ :=
      hL76 G z S K₁ K₂ t u q h hidx D hD hsd h16
    have hc76 := lemma_7_6 hII hL76 G z S K₁ K₂ t u q h hc73 hc74 hidx D hD hsd h16 _ hcen
    obtain ⟨hw₀sq, hw₀ne⟩ := h.w₀_facts hII hu₁P hu₁sq
    have hno := hL77 G z S K₁ K₂ t u q h hidx D hD hsd h16 _ y hcen hyD hyP hyy
    have hDE : D ≤ S ⊓ centralizer ({t} : Set G) := le_sup_right.trans hD.prod.1.le
    have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.1 (hDE hyD).2
    exact h.core77 hII hc73 hΩ (hD.le hyD) hyP hyt hyy hw₀sq hw₀ne hc76.1 hno

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
