module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

variable {G : Type*} [Group G] [Finite G]

theorem no_fusion_contradiction {S U : Subgroup G} {z d u x₀ w₁ : G}
    (hSyl : Syl2In S (centralizer ({z} : Set G)))
    (hS4 : ∀ s ∈ S, s ^ 4 ∈ U) (hUe : ∀ c ∈ U, c = 1 ∨ c = z ∨ c = u ∨ c = u * z)
    (hzU : z ∈ U) (huU : u ∈ U) (hU4 : Nat.card ↥U = 4)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu2 : u * u = 1) (huz : u ≠ z) (hdz : d ≠ z)
    (hdc : IsConj z d) (huc : IsConj z u)
    (hx₀S : x₀ ∈ S) (hx₀d : x₀ * d = d * x₀) (hx₀4 : x₀ ^ 4 = z)
    (hw₁S : w₁ ∈ S) (hw₁u : w₁ * u = u * w₁) (hw₁4 : w₁ ^ 4 = z)
    (hZ : ∀ c ∈ S, (∀ s ∈ S, s * c = c * s) → c = 1 ∨ c = z)
    (hno : ∀ b : G, b⁻¹ * d * b = u → b * z = z * b → False) : False := by
  obtain ⟨T₁, hT₁, hST₁⟩ := exists_syl2In_ge (A := S ⊓ centralizer ({d} : Set G))
    (H := centralizer ({d} : Set G)) hSyl.2.1.to_inf_left inf_le_right
  obtain ⟨T₂, hT₂, hST₂⟩ := exists_syl2In_ge (A := S ⊓ centralizer ({u} : Set G))
    (H := centralizer ({u} : Set G)) hSyl.2.1.to_inf_left inf_le_right
  have hx₀T₁ : x₀ ∈ T₁ :=
    hST₁ ⟨hx₀S, Subgroup.mem_centralizer_singleton_iff.2 hx₀d⟩
  have hw₁T₂ : w₁ ∈ T₂ :=
    hST₂ ⟨hw₁S, Subgroup.mem_centralizer_singleton_iff.2 hw₁u⟩
  obtain ⟨c₂, hc₂⟩ := isConj_iff.1 huc
  have hCu' : cj (centralizer ({z} : Set G)) c₂⁻¹ = centralizer ({u} : Set G) := by
    have e : (c₂⁻¹)⁻¹ * z * c₂⁻¹ = u := by rw [inv_inv]; exact hc₂
    rw [cj_centralizer, e]
  have hSyl₂ : Syl2In (cj S c₂⁻¹) (centralizer ({u} : Set G)) := by
    have := syl2In_cj hSyl c₂⁻¹
    rwa [hCu'] at this
  obtain ⟨c, hcCu, hcT⟩ := hSyl₂.exists_conj hT₂
  have hT₂eq : T₂ = cj S (c₂⁻¹ * c) := by rw [hcT, cj_cj]
  have hmemT₂ : ∀ x, x ∈ T₂ ↔ (c₂⁻¹ * c) * x * (c₂⁻¹ * c)⁻¹ ∈ S := fun x => by
    rw [hT₂eq]
    exact mem_cj
  have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.1 hcCu
  have hgu : (c₂⁻¹ * c) * u * (c₂⁻¹ * c)⁻¹ = z := by
    calc (c₂⁻¹ * c) * u * (c₂⁻¹ * c)⁻¹ = c₂⁻¹ * (c * u * c⁻¹) * c₂ := by group
      _ = c₂⁻¹ * u * c₂ := by
          have : c * u * c⁻¹ = u := by rw [hcu]; group
          rw [this]
      _ = z := by rw [← hc₂]; group
  have hconj4 : ∀ x ∈ T₂, (c₂⁻¹ * c) * x ^ 4 * (c₂⁻¹ * c)⁻¹ ∈ U := fun x hx => by
    rw [← conj_pow]
    exact hS4 _ ((hmemT₂ x).1 hx)
  have hz_cj : (c₂⁻¹ * c) * z * (c₂⁻¹ * c)⁻¹ ∈ U := by
    have := hconj4 w₁ hw₁T₂
    rwa [hw₁4] at this
  have hUle : U ≤ cj U (c₂⁻¹ * c) := by
    have hzc : z ∈ cj U (c₂⁻¹ * c) := hz_cj
    have huc' : u ∈ cj U (c₂⁻¹ * c) := by
      show (c₂⁻¹ * c) * u * (c₂⁻¹ * c)⁻¹ ∈ U
      rw [hgu]
      exact hzU
    intro x hx
    rcases hUe x hx with h1 | h1 | h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact hzc
    · rw [h1]; exact huc'
    · rw [h1]; exact mul_mem huc' hzc
  have hUeq : U = cj U (c₂⁻¹ * c) :=
    Subgroup.eq_of_le_of_card_ge hUle (cj_card _ _).le
  have hU4pow : ∀ x ∈ T₂, x ^ 4 ∈ U := fun x hx => by
    have : x ^ 4 ∈ cj U (c₂⁻¹ * c) := hconj4 x hx
    rwa [← hUeq] at this
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 hdc
  have hb₀d : (c₀ * c₂⁻¹)⁻¹ * d * (c₀ * c₂⁻¹) = u := by
    calc (c₀ * c₂⁻¹)⁻¹ * d * (c₀ * c₂⁻¹) = c₂ * (c₀⁻¹ * d * c₀) * c₂⁻¹ := by group
      _ = c₂ * z * c₂⁻¹ := by rw [← hc₀]; group
      _ = u := hc₂
  have hSyl₁ : Syl2In (cj T₁ (c₀ * c₂⁻¹)) (centralizer ({u} : Set G)) := by
    have := syl2In_cj hT₁ (c₀ * c₂⁻¹)
    have e : cj (centralizer ({d} : Set G)) (c₀ * c₂⁻¹) = centralizer ({u} : Set G) := by
      rw [cj_centralizer, hb₀d]
    rwa [e] at this
  obtain ⟨c', hc'Cu, hc'T⟩ := hSyl₁.exists_conj hT₂
  have hT₂b : ∀ x, x ∈ T₂ ↔ ((c₀ * c₂⁻¹) * c') * x * ((c₀ * c₂⁻¹) * c')⁻¹ ∈ T₁ := fun x => by
    rw [hc'T, cj_cj]
    exact mem_cj
  have hc'u : c' * u = u * c' := Subgroup.mem_centralizer_singleton_iff.1 hc'Cu
  have hbd : ((c₀ * c₂⁻¹) * c')⁻¹ * d * ((c₀ * c₂⁻¹) * c') = u := by
    calc ((c₀ * c₂⁻¹) * c')⁻¹ * d * ((c₀ * c₂⁻¹) * c')
        = c'⁻¹ * ((c₀ * c₂⁻¹)⁻¹ * d * (c₀ * c₂⁻¹)) * c' := by group
      _ = c'⁻¹ * u * c' := by rw [hb₀d]
      _ = u := by
          calc c'⁻¹ * u * c' = c'⁻¹ * (u * c') := by group
            _ = c'⁻¹ * (c' * u) := by rw [hc'u]
            _ = u := by group
  generalize (c₀ * c₂⁻¹) * c' = b at hT₂b hbd
  have hz4 : b⁻¹ * z * b ∈ U := by
    have hy : b⁻¹ * x₀ * b ∈ T₂ := (hT₂b _).2 (by
      have : b * (b⁻¹ * x₀ * b) * b⁻¹ = x₀ := by group
      rwa [this])
    have h4 := hU4pow _ hy
    have e := conj_pow (a := b⁻¹) (b := x₀) (i := 4)
    simp only [inv_inv] at e
    rw [hx₀4] at e
    rwa [e] at h4
  have hne1 : b⁻¹ * z * b ≠ 1 := fun h' => hz1 (by
    have : z = b * (b⁻¹ * z * b) * b⁻¹ := by group
    rw [this, h']
    group)
  have hneu : b⁻¹ * z * b ≠ u := fun h' => hdz (by
    have : d = b * u * b⁻¹ := by rw [← hbd]; group
    rw [this, ← h']
    group)
  have hzT₂ : z ∈ T₂ := by
    rw [← hw₁4]
    exact pow_mem hw₁T₂ 4
  rcases hUe _ hz4 with h1 | h1 | h1 | h1
  · exact hne1 h1
  · exact hno b hbd (by
      calc b * z = b * (b⁻¹ * z * b) := by rw [h1]
        _ = z * b := by group)
  · exact hneu h1
  ·
    obtain ⟨c₃, hc₃T, hc₃z⟩ : ∃ c₃ ∈ T₂, c₃ * z ≠ z * c₃ := by
      by_contra hcon
      have hall : ∀ c₃ ∈ T₂, c₃ * z = z * c₃ := fun c₃ hc₃ => by
        by_contra h'
        exact hcon ⟨c₃, hc₃, h'⟩
      have hzS : (c₂⁻¹ * c) * z * (c₂⁻¹ * c)⁻¹ ∈ S := (hmemT₂ z).1 hzT₂
      have hcen : ∀ s ∈ S, s * ((c₂⁻¹ * c) * z * (c₂⁻¹ * c)⁻¹) =
          ((c₂⁻¹ * c) * z * (c₂⁻¹ * c)⁻¹) * s := by
        intro s hs
        have ht : (c₂⁻¹ * c)⁻¹ * s * (c₂⁻¹ * c) ∈ T₂ := by
          rw [hmemT₂]
          have : (c₂⁻¹ * c) * ((c₂⁻¹ * c)⁻¹ * s * (c₂⁻¹ * c)) * (c₂⁻¹ * c)⁻¹ = s := by group
          rwa [this]
        have h2 := hall _ ht
        calc s * ((c₂⁻¹ * c) * z * (c₂⁻¹ * c)⁻¹)
            = (c₂⁻¹ * c) * (((c₂⁻¹ * c)⁻¹ * s * (c₂⁻¹ * c)) * z) * (c₂⁻¹ * c)⁻¹ := by group
          _ = (c₂⁻¹ * c) * (z * ((c₂⁻¹ * c)⁻¹ * s * (c₂⁻¹ * c))) * (c₂⁻¹ * c)⁻¹ := by rw [h2]
          _ = ((c₂⁻¹ * c) * z * (c₂⁻¹ * c)⁻¹) * s := by group
      rcases hZ _ hzS hcen with h' | h'
      · apply hz1
        have : z = (c₂⁻¹ * c)⁻¹ * ((c₂⁻¹ * c) * z * (c₂⁻¹ * c)⁻¹) * (c₂⁻¹ * c) := by group
        rw [this, h']
        group
      · apply huz
        have hu' : u = (c₂⁻¹ * c)⁻¹ * z * (c₂⁻¹ * c) := by
          rw [← hgu]
          group
        have hzz' : (c₂⁻¹ * c)⁻¹ * z * (c₂⁻¹ * c) = z := by
          calc (c₂⁻¹ * c)⁻¹ * z * (c₂⁻¹ * c)
              = (c₂⁻¹ * c)⁻¹ * ((c₂⁻¹ * c) * z * (c₂⁻¹ * c)⁻¹) * (c₂⁻¹ * c) := by rw [h']
            _ = z := by group
        rw [hu', hzz']
    have hc₃u : c₃ * u = u * c₃ := Subgroup.mem_centralizer_singleton_iff.1 (hT₂.1 hc₃T)
    have hc₃u' : c₃ * u * c₃⁻¹ = u := by rw [hc₃u]; group
    have hc₃wz : c₃ * z * c₃⁻¹ ∈ U := by
      have hc₃w : c₃ * w₁ * c₃⁻¹ ∈ T₂ := mul_mem (mul_mem hc₃T hw₁T₂) (inv_mem hc₃T)
      have h4 := hU4pow _ hc₃w
      rwa [conj_pow, hw₁4] at h4
    have hc₃uz : c₃ * z * c₃⁻¹ = u * z := by
      rcases hUe _ hc₃wz with h' | h' | h' | h'
      · exfalso
        apply hz1
        have : z = c₃⁻¹ * (c₃ * z * c₃⁻¹) * c₃ := by group
        rw [this, h']
        group
      · exfalso
        apply hc₃z
        calc c₃ * z = (c₃ * z * c₃⁻¹) * c₃ := by group
          _ = z * c₃ := by rw [h']
      · exfalso
        apply huz
        have hz' : z = c₃⁻¹ * (c₃ * z * c₃⁻¹) * c₃ := by group
        rw [h'] at hz'
        have hcc : c₃⁻¹ * u * c₃ = u := by
          calc c₃⁻¹ * u * c₃ = c₃⁻¹ * (u * c₃) := by group
            _ = c₃⁻¹ * (c₃ * u) := by rw [hc₃u]
            _ = u := by group
        rw [hcc] at hz'
        exact hz'.symm
      · exact h'
    have hb'z : (b * c₃⁻¹)⁻¹ * z * (b * c₃⁻¹) = z := by
      calc (b * c₃⁻¹)⁻¹ * z * (b * c₃⁻¹) = c₃ * (b⁻¹ * z * b) * c₃⁻¹ := by group
        _ = c₃ * (u * z) * c₃⁻¹ := by rw [h1]
        _ = (c₃ * u * c₃⁻¹) * (c₃ * z * c₃⁻¹) := by group
        _ = u * (u * z) := by rw [hc₃u', hc₃uz]
        _ = z := by rw [← mul_assoc, hu2, one_mul]
    have hb'd : (b * c₃⁻¹)⁻¹ * d * (b * c₃⁻¹) = u := by
      calc (b * c₃⁻¹)⁻¹ * d * (b * c₃⁻¹) = c₃ * (b⁻¹ * d * b) * c₃⁻¹ := by group
        _ = c₃ * u * c₃⁻¹ := by rw [hbd]
        _ = u := hc₃u'
    exact hno (b * c₃⁻¹) hb'd (by
      calc (b * c₃⁻¹) * z = (b * c₃⁻¹) * ((b * c₃⁻¹)⁻¹ * z * (b * c₃⁻¹)) := by rw [hb'z]
        _ = z * (b * c₃⁻¹) := by group)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
