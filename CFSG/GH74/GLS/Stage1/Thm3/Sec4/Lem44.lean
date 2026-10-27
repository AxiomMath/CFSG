module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Lem43

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {O : Subgroup G → Subgroup G}
  {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop} {z : G} {S K₁ K₂ : Subgroup G}

namespace M4

variable [Finite G]

omit [Finite G] in
theorem norm_of_not_intch (h : M4 O FA SD z S K₁ K₂) {t : G}
    (htC : t ∈ centralizer ({z} : Set G)) (hni : ¬ Intch t K₁ K₂) :
    cj K₁ t = K₁ ∧ cj K₂ t = K₂ := by
  rcases h.perm t htC with h1 | h2
  · exact h1
  · exact absurd h2 hni

theorem sq_of_inter (h : M4 O FA SD z S K₁ K₂) {x : G} (hxS : x ∈ S) (hx₁ : x ∈ K₁)
    (hx₂ : x ∈ K₂) : x * x = 1 := by
  have hsec : x ∈ secCent K₁ (O K₁) := h.cs₁ hx₂
  have : x ∈ S ⊓ ZsM O K₁ := ⟨hxS, hx₁, hsec⟩
  rw [(h.S_inf_Zs_comp (Or.inl rfl)).2] at this
  rcases (mem_zpowers_of_sq h.z_sq).1 this with h1 | h1
  · rw [h1]; simp
  · rw [h1]; exact h.z_sq

end M4

namespace M44

open M4

variable [Finite G]

theorem sd_data (h : M44 O FA SD z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) {t : G}
    (htS : t ∈ S) (ht2 : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ z) (htn : cj K t = K)
    (hsd : SD (Pm S K₁ K₂ ⊓ K ⊔ zpowers t)) :
    (∃ u₁ ∈ Pm S K₁ K₂ ⊓ K, u₁ * u₁ = z ∧ t * u₁ * t = u₁⁻¹ ∧
        ∃ x ∈ Pm S K₁ K₂ ⊓ K, x⁻¹ * t * x = t * u₁) ∧
      ∃ y ∈ Pm S K₁ K₂ ⊓ K, y⁻¹ * t * y = t * z := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htK : ∀ x ∈ K, t * x * t ∈ K := by
    intro x hx
    have : x ∈ cj K t := by rw [htn]; exact hx
    have h2 := mem_cj.1 this
    simpa [htinv] using h2
  refine h.fsd (Pm S K₁ K₂ ⊓ K) t h.P_pgroup.to_inf_left ⟨h.z_mem_P, h.z_mem_comp hK⟩
    (fun x hx => centralizer_comm (h.K_le_C (h.comp_le hK hx.2)))
    (fun x hx hx2 => h.inv_comp hK hx.2 hx2) ht2 ?_ ?_ hsd
  · intro htP
    rcases h.inv_comp hK htP.2 ht2 with h1 | h1
    · exact ht1 h1
    · exact htz h1
  · intro x hx
    have hxS : x ∈ S := hx.1.1
    have htS' : t * x * t ∈ S := mul_mem (mul_mem htS hxS) htS
    have hxK : x ∈ K₁ ⊔ K₂ := hx.1.2
    have h3 : t * x * t ∈ K₁ ⊔ K₂ := by
      have := h.C_norm_K (h.S_syl.1 htS) hxK
      simpa [htinv] using this
    exact ⟨⟨htS', h3⟩, htK x hx.2⟩

theorem lemma44 (h : M44 O FA SD z S K₁ K₂) (hA : H4A O z S K₁ K₂)
    (hZ : ∀ P : Subgroup G, Syl2In P ⊤ → ∀ x ∈ P, x * x = 1 → x ≠ 1 →
      (∀ s ∈ P, x * s = s * x) → ∃ g : G, g⁻¹ * x * g ∈ P ∧ g⁻¹ * x * g ≠ x) :
    ∃ t ∈ S, IsConj z t ∧ t ≠ z ∧ Intch t K₁ K₂ := by
  by_contra hno
  push Not at hno
  obtain ⟨g0, hg0S, hg0ne⟩ := hZ S h.S_top z h.z_mem_S h.z_sq h.z_ne
    (fun s hs => (centralizer_comm (h.S_syl.1 hs)).symm)
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ = g0⁻¹ * z * g0 := ⟨_, rfl⟩
  rw [← ht₀] at hg0S hg0ne
  have ht₀conj : IsConj z t₀ := isConj_iff.2 ⟨g0⁻¹, by rw [ht₀]; simp⟩
  have ht₀2 : t₀ * t₀ = 1 := by
    rw [ht₀]
    calc g0⁻¹ * z * g0 * (g0⁻¹ * z * g0) = g0⁻¹ * (z * z) * g0 := by group
      _ = 1 := by rw [h.z_sq]; group
  have ht₀1 : t₀ ≠ 1 := by
    intro h1
    apply h.z_ne
    calc z = g0 * (g0⁻¹ * z * g0) * g0⁻¹ := by group
      _ = 1 := by rw [← ht₀, h1]; group
  have ht₀C : t₀ ∈ centralizer ({z} : Set G) := h.S_syl.1 hg0S
  have hni₀ := hno t₀ hg0S ht₀conj hg0ne
  obtain ⟨hn₁, hn₂⟩ := h.norm_of_not_intch ht₀C hni₀
  have hsd : SD (Pm S K₁ K₂ ⊓ K₁ ⊔ zpowers t₀) ∧ SD (Pm S K₁ K₂ ⊓ K₂ ⊔ zpowers t₀) := by
    rcases h.lemma43 hA hg0S ht₀conj hg0ne with hI | hsd
    · exact absurd hI hni₀
    · exact hsd
  obtain ⟨⟨u₁, hu₁, hu₁2, hu₁t, x₁, hx₁, hx₁t⟩, -⟩ :=
    h.sd_data (Or.inl rfl) hg0S ht₀2 ht₀1 hg0ne hn₁ hsd.1
  obtain ⟨⟨u₂, hu₂, hu₂2, hu₂t, x₂, hx₂, hx₂t⟩, -⟩ :=
    h.sd_data (Or.inr rfl) hg0S ht₀2 ht₀1 hg0ne hn₂ hsd.2
  have hu₁K : u₁ ∈ K₁ := hu₁.2
  have hu₂K : u₂ ∈ K₂ := hu₂.2
  have hu₁S : u₁ ∈ S := hu₁.1.1
  have hu₂S : u₂ ∈ S := hu₂.1.1
  have hcomm₁₂ : u₁ * u₂ = u₂ * u₁ := h.comm_of_S hu₁K hu₂K hu₁S hu₂S
  obtain ⟨u, hu⟩ : ∃ u, u = u₁ * u₂ := ⟨_, rfl⟩
  have huP : u ∈ Pm S K₁ K₂ := by rw [hu]; exact mul_mem hu₁.1 hu₂.1
  have hu2 : u * u = 1 := by
    rw [hu]
    calc u₁ * u₂ * (u₁ * u₂) = (u₁ * u₁) * (u₂ * u₂) := by
          rw [mul_assoc, ← mul_assoc u₂ u₁ u₂, ← hcomm₁₂]; group
      _ = 1 := by rw [hu₁2, hu₂2, h.z_sq]
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 : u₂ = u₁⁻¹ := by
      have : u₁ * u₂ = 1 := by rw [← hu]; exact h1
      exact eq_inv_of_mul_eq_one_right this
    have hx : u₁ ∈ K₂ := by
      have : u₁⁻¹ ∈ K₂ := by rw [← h2]; exact hu₂K
      simpa using inv_mem this
    have := h.sq_of_inter hu₁S hu₁K hx
    rw [hu₁2] at this
    exact h.z_ne this
  have huz : u ≠ z := by
    intro h1
    have h2 : u₂ = u₁⁻¹ * z := by
      have : u₁ * u₂ = z := by rw [← hu]; exact h1
      calc u₂ = u₁⁻¹ * (u₁ * u₂) := by group
        _ = u₁⁻¹ * z := by rw [this]
    have hx : u₂ ∈ K₁ := by
      rw [h2]; exact mul_mem (inv_mem hu₁K) (h.z_mem_comp (Or.inl rfl))
    have := h.sq_of_inter hu₂S hx hu₂K
    rw [hu₂2] at this
    exact h.z_ne this
  have hut : t₀ * u * t₀ = u := by
    have h1 : t₀ * u * t₀ = (t₀ * u₁ * t₀) * (t₀ * u₂ * t₀) := by
      rw [hu]; calc t₀ * (u₁ * u₂) * t₀ = t₀ * u₁ * (t₀ * t₀) * u₂ * t₀ := by rw [ht₀2]; group
        _ = _ := by group
    rw [h1, hu₁t, hu₂t]
    calc u₁⁻¹ * u₂⁻¹ = (u₂ * u₁)⁻¹ := by group
      _ = (u₁ * u₂)⁻¹ := by rw [hcomm₁₂]
      _ = u⁻¹ := by rw [hu]
      _ = u := inv_eq_of_mul_eq_one_right hu2
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ = t₀ * u := ⟨_, rfl⟩
  have hv₀2 : v₀ * v₀ = 1 := by
    rw [hv₀]
    calc t₀ * u * (t₀ * u) = (t₀ * u * t₀) * u := by group
      _ = 1 := by rw [hut, hu2]
  have hv₀t : v₀ * t₀ = t₀ * v₀ := by
    rw [hv₀]
    calc t₀ * u * t₀ = u := hut
      _ = t₀ * (t₀ * u) := by rw [← mul_assoc, ht₀2, one_mul]
  have hv₀1 : v₀ ≠ t₀ := by
    intro h1
    apply hu1
    have : t₀ * u = t₀ * 1 := by rw [← hv₀, h1, mul_one]
    exact mul_left_cancel this
  have hx₂u₁ : x₂⁻¹ * u₁ * x₂ = u₁ := by
    have := h.comm_of_S hu₁K hx₂.2 hu₁S hx₂.1.1
    calc x₂⁻¹ * u₁ * x₂ = x₂⁻¹ * (u₁ * x₂) := by group
      _ = x₂⁻¹ * (x₂ * u₁) := by rw [this]
      _ = u₁ := by group
  have ht₀v₀ : IsConj t₀ v₀ := by
    refine isConj_iff.2 ⟨(x₁ * x₂)⁻¹, ?_⟩
    rw [hv₀, hu]
    calc (x₁ * x₂)⁻¹ * t₀ * (x₁ * x₂)⁻¹⁻¹ = x₂⁻¹ * (x₁⁻¹ * t₀ * x₁) * x₂ := by group
      _ = x₂⁻¹ * (t₀ * u₁) * x₂ := by rw [hx₁t]
      _ = (x₂⁻¹ * t₀ * x₂) * (x₂⁻¹ * u₁ * x₂) := by group
      _ = (t₀ * u₂) * u₁ := by rw [hx₂t, hx₂u₁]
      _ = t₀ * (u₁ * u₂) := by rw [mul_assoc, hcomm₁₂]
  have hzv₀ : IsConj z v₀ := ht₀conj.trans ht₀v₀
  have hv₀t' : v₀ * t₀ = u := by rw [hv₀]; exact hut
  have hv₀ne : v₀ ≠ 1 := by
    intro h1
    have h2 : t₀ * u = 1 := by rw [← hv₀]; exact h1
    have h3 : u = t₀⁻¹ := eq_inv_of_mul_eq_one_right h2
    have h4 : u = t₀ := by rw [h3]; exact inv_eq_of_mul_eq_one_right ht₀2
    have hRu : t₀ ∈ Rm O S K₁ K₂ := by
      rw [← h4]; exact (le_sup_left : Pm S K₁ K₂ ≤ Rm O S K₁ K₂) huP
    exact hg0ne (hA t₀ hRu ht₀conj)
  obtain ⟨w, hw⟩ : ∃ w, w = g0 * v₀ * g0⁻¹ := ⟨_, rfl⟩
  have hzt : z = g0 * t₀ * g0⁻¹ := by rw [ht₀]; group
  have hwz : w * z = z * w := by
    rw [hw, hzt]
    calc g0 * v₀ * g0⁻¹ * (g0 * t₀ * g0⁻¹) = g0 * (v₀ * t₀) * g0⁻¹ := by group
      _ = g0 * (t₀ * v₀) * g0⁻¹ := by rw [hv₀t]
      _ = g0 * t₀ * g0⁻¹ * (g0 * v₀ * g0⁻¹) := by group
  have hwC : w ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hwz
  have hw2 : w * w = 1 := by
    rw [hw]
    calc g0 * v₀ * g0⁻¹ * (g0 * v₀ * g0⁻¹) = g0 * (v₀ * v₀) * g0⁻¹ := by group
      _ = 1 := by rw [hv₀2]; group
  have hw1 : w ≠ 1 := by
    intro h1
    apply hv₀ne
    calc v₀ = g0⁻¹ * w * g0 := by rw [hw]; group
      _ = 1 := by rw [h1]; group
  have hwz' : w * z = g0 * u * g0⁻¹ := by
    rw [hw]
    calc g0 * v₀ * g0⁻¹ * z = g0 * v₀ * g0⁻¹ * (g0 * t₀ * g0⁻¹) := by rw [← hzt]
      _ = g0 * (v₀ * t₀) * g0⁻¹ := by group
      _ = g0 * u * g0⁻¹ := by rw [hv₀t']
  obtain ⟨P'', hP'', hwP''⟩ := exists_syl2In_ge (isPGroup_zpowers_of_sq hw2 hw1)
    (zpowers_le.2 hwC : zpowers w ≤ centralizer ({z} : Set G))
  obtain ⟨c', hc'C, hcP''⟩ := h.S_syl.exists_conj hP''
  obtain ⟨w', hw'⟩ : ∃ w', w' = c' * w * c'⁻¹ := ⟨_, rfl⟩
  have hw'S : w' ∈ S := by
    have : w ∈ P'' := hwP'' (Subgroup.mem_zpowers w)
    rw [hcP'', mem_cj] at this
    rw [hw']; exact this
  have hcz : c' * z = z * c' := centralizer_comm hc'C
  have hcz' : c'⁻¹ * z = z * c'⁻¹ := by
    calc c'⁻¹ * z = c'⁻¹ * z * (c' * c'⁻¹) := by group
      _ = c'⁻¹ * (z * c') * c'⁻¹ := by group
      _ = c'⁻¹ * (c' * z) * c'⁻¹ := by rw [hcz]
      _ = z * c'⁻¹ := by group
  have hw'2 : w' * w' = 1 := by
    rw [hw']
    calc c' * w * c'⁻¹ * (c' * w * c'⁻¹) = c' * (w * w) * c'⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  have hw'1 : w' ≠ 1 := by
    intro h1
    apply hw1
    calc w = c'⁻¹ * w' * c' := by rw [hw']; group
      _ = 1 := by rw [h1]; group
  have hw'ne : w' ≠ z := by
    intro h1
    apply hv₀1
    have hwz2 : w = z := by
      calc w = c'⁻¹ * w' * c' := by rw [hw']; group
        _ = c'⁻¹ * z * c' := by rw [h1]
        _ = z := by rw [hcz']; group
    calc v₀ = g0⁻¹ * w * g0 := by rw [hw]; group
      _ = g0⁻¹ * z * g0 := by rw [hwz2]
      _ = t₀ := ht₀.symm
  have hvw : IsConj v₀ w := isConj_iff.2 ⟨g0, hw.symm⟩
  have hww' : IsConj w w' := isConj_iff.2 ⟨c', hw'.symm⟩
  have hzw' : IsConj z w' := (hzv₀.trans hvw).trans hww'
  have hni' := hno w' hw'S hzw' hw'ne
  obtain ⟨hn₁', -⟩ := h.norm_of_not_intch (h.S_syl.1 hw'S) hni'
  have hsd' : SD (Pm S K₁ K₂ ⊓ K₁ ⊔ zpowers w') := by
    rcases h.lemma43 hA hw'S hzw' hw'ne with hI | hsd
    · exact absurd hI hni'
    · exact hsd.1
  obtain ⟨-, y, -, hyw⟩ := h.sd_data (Or.inl rfl) hw'S hw'2 hw'1 hw'ne hn₁' hsd'
  have hw'z : w' * z = (c' * g0) * u * (c' * g0)⁻¹ := by
    calc w' * z = c' * w * c'⁻¹ * z := by rw [hw']
      _ = c' * (w * z) * c'⁻¹ := by
        calc c' * w * c'⁻¹ * z = c' * w * (c'⁻¹ * z) := by group
          _ = c' * w * (z * c'⁻¹) := by rw [hcz']
          _ = c' * (w * z) * c'⁻¹ := by group
      _ = c' * (g0 * u * g0⁻¹) * c'⁻¹ := by rw [hwz']
      _ = (c' * g0) * u * (c' * g0)⁻¹ := by group
  have hu_w'z : IsConj u (w' * z) := isConj_iff.2 ⟨c' * g0, hw'z.symm⟩
  have hw'_w'z : IsConj w' (w' * z) := isConj_iff.2 ⟨y⁻¹, by simpa using hyw⟩
  have hzu : IsConj z u := (hzw'.trans hw'_w'z).trans hu_w'z.symm
  have hRu : u ∈ Rm O S K₁ K₂ := (le_sup_left : Pm S K₁ K₂ ≤ Rm O S K₁ K₂) huP
  exact huz (hA u hRu hzu)

end M44

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
