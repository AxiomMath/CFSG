module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KE
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KCong

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo

namespace L2K

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
variable {F : Type} [Field F] [Finite F]

theorem mem_normalizer_L2E {z w k d : X} (h₁ : d * z * d⁻¹ ∈ L2E z w t k)
    (h₂ : d * w * d⁻¹ ∈ L2E z w t k) (h₃ : d * t * d⁻¹ ∈ L2E z w t k)
    (h₄ : d * k * d⁻¹ ∈ L2E z w t k) : d ∈ normalizer (L2E z w t k : Set X) := by
  refine mem_normalizer_of_conj_mem fun e he => ?_
  have hle : L2E z w t k ≤ (L2E z w t k).comap (MulAut.conj d).toMonoidHom := by
    rw [L2E, closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hs with rfl | rfl | rfl | rfl
    exacts [h₁, h₂, h₃, h₄]
  exact hle he

theorem facts_core (C : A.CaseK) (S : Gens A) (Fr₁ : Frame A F C.k)
    (Fr₂ : Frame A F (S.z * C.k)) {w₁ w₂ : X} (hw₁V : w₁ ∈ Fr₁.V) (hw₂V : w₂ ∈ Fr₂.V)
    (hw₁2 : w₁ ^ 2 = 1) (hw₂2 : w₂ ^ 2 = 1) (hw₁1 : w₁ ≠ 1) (hw₁z : w₁ ≠ S.z) (hw₂1 : w₂ ≠ 1)
    (hw₂z : w₂ ≠ S.z) (hc₁ : Nat.card Fr₁.V = 4) (hc₂ : Nat.card Fr₂.V = 4)
    (hV₁ : ∀ v, v ∈ Fr₁.V ↔ v = 1 ∨ v = S.z ∨ v = w₁ ∨ v = S.z * w₁)
    (hV₂ : ∀ v, v ∈ Fr₂.V ↔ v = 1 ∨ v = S.z ∨ v = w₂ ∨ v = S.z * w₂) :
    (∃ d ∈ centralizer ({t} : Set X),
        d ∈ normalizer (L2E S.z w₁ t C.k : Set X) ∧ d * S.z * d⁻¹ = w₁ ∧
          d * w₁ * d⁻¹ = S.z * w₁ ∧ d * C.k * d⁻¹ = C.k) ∧
      (∃ d ∈ centralizer ({t} : Set X),
        d ∈ normalizer (L2E S.z w₂ t C.k : Set X) ∧ d * S.z * d⁻¹ = S.z * w₂ ∧
          d * w₂ * d⁻¹ = S.z ∧ d * (S.z * C.k) * d⁻¹ = S.z * C.k) ∧
      (∀ n ∈ normalizer (L2E S.z w₁ t C.k : Set X) ⊓ centralizer ({t} : Set X),
        n * C.k * n⁻¹ = C.k) ∧
      (∀ n ∈ normalizer (L2E S.z w₂ t C.k : Set X) ⊓ centralizer ({t} : Set X),
        n * (S.z * C.k) * n⁻¹ = S.z * C.k) ∧
      (∀ g ∈ centralizer ({t} : Set X),
        ¬ ∀ e ∈ L2E S.z w₂ t C.k, g * e * g⁻¹ ∈ L2E S.z w₁ t C.k) ∧
      ((∀ g ∈ centralizer ({t} : Set X), g * S.z * g⁻¹ ≠ t * S.z) →
        {b | ∃ g ∈ centralizer ({t} : Set X), g * S.z * g⁻¹ = b}.ncard ≡ 1 [MOD 4]) := by
  have hw₁R := Fr₁.V_le_R hw₁V
  have hw₂R := Fr₂.V_le_R hw₂V
  have hz2 := S.z_sq
  have hzinv : S.z⁻¹ = S.z := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hz2]
  have hzw₁ : S.z * w₁ = w₁ * S.z := S.z_comm_R hw₁R
  have hzw₂ : S.z * w₂ = w₂ * S.z := S.z_comm_R hw₂R
  have hkC := k_mem_C C
  have hzC := A.T_le_centralizer S.z_mem.1
  refine ⟨?_, ?_, fun n hn => Fr₁.conj_eq_of_mem_normalizer S C (Or.inl rfl) hw₁V hw₁2 hn,
    fun n hn => Fr₂.conj_eq_of_mem_normalizer S C (Or.inr rfl) hw₂V hw₂2 hn, ?_,
    card_conj_z_modEq C S Fr₁⟩
  ·
    obtain ⟨d, hdL, hdk, hdz, hdw⟩ := Fr₁.exists_cycle S hV₁ hw₁1 hw₁z hzw₁
    have hdC := L_le_C (A := A) hdL
    have hdk' : d * C.k * d⁻¹ = C.k := by rw [hdk, mul_inv_cancel_right]
    refine ⟨d, hdC, mem_normalizer_L2E ?_ ?_ ?_ ?_, hdz, hdw, hdk'⟩
    · rw [hdz]
      exact S.w_mem_L2E C w₁
    · rw [hdw]
      exact mul_mem (S.z_mem_L2E C w₁) (S.w_mem_L2E C w₁)
    · rw [commute_t_of_mem_C hdC, mul_inv_cancel_right]
      exact S.t_mem_L2E C w₁
    · rw [hdk']
      exact S.k_mem_L2E C w₁
  ·
    obtain ⟨d', hd'L, hd'κ, hd'z, hd'w⟩ := Fr₂.exists_cycle S hV₂ hw₂1 hw₂z hzw₂
    have hd'C := L_le_C (A := A) hd'L
    have h3 : d' * (S.z * w₂) * d'⁻¹ = S.z := by
      calc d' * (S.z * w₂) * d'⁻¹ = (d' * S.z * d'⁻¹) * (d' * w₂ * d'⁻¹) := by group
        _ = w₂ * (S.z * w₂) := by rw [hd'z, hd'w]
        _ = S.z := by rw [← mul_assoc, ← hzw₂, mul_assoc, ← pow_two, hw₂2, mul_one]
    have hz' : d'⁻¹ * S.z * d'⁻¹⁻¹ = S.z * w₂ := by
      calc d'⁻¹ * S.z * d'⁻¹⁻¹ = d'⁻¹ * (d' * (S.z * w₂) * d'⁻¹) * d' := by rw [h3]; group
        _ = S.z * w₂ := by group
    have hw' : d'⁻¹ * w₂ * d'⁻¹⁻¹ = S.z := by
      calc d'⁻¹ * w₂ * d'⁻¹⁻¹ = d'⁻¹ * (d' * S.z * d'⁻¹) * d' := by rw [hd'z]; group
        _ = S.z := by group
    have hzk' : d'⁻¹ * (S.z * C.k) * d'⁻¹⁻¹ = S.z * C.k := by
      calc d'⁻¹ * (S.z * C.k) * d'⁻¹⁻¹ = d'⁻¹ * ((S.z * C.k) * d') := by group
        _ = d'⁻¹ * (d' * (S.z * C.k)) := by rw [hd'κ]
        _ = S.z * C.k := by group
    have hk' : d'⁻¹ * C.k * d'⁻¹⁻¹ = (S.z * w₂)⁻¹ * (S.z * C.k) := by
      rw [← hz', ← hzk']
      group
    refine ⟨d'⁻¹, inv_mem hd'C, mem_normalizer_L2E ?_ ?_ ?_ ?_, hz', hw', hzk'⟩
    · rw [hz']
      exact mul_mem (S.z_mem_L2E C w₂) (S.w_mem_L2E C w₂)
    · rw [hw']
      exact S.z_mem_L2E C w₂
    · rw [commute_t_of_mem_C (inv_mem hd'C), mul_inv_cancel_right]
      exact S.t_mem_L2E C w₂
    · rw [hk']
      exact mul_mem (inv_mem (mul_mem (S.z_mem_L2E C w₂) (S.w_mem_L2E C w₂)))
        (mul_mem (S.z_mem_L2E C w₂) (S.k_mem_L2E C w₂))
  ·
    intro g hg hsub
    obtain ⟨c, hc, hgk⟩ : ∃ c : ℕ, c < 2 ∧ g * C.k * g⁻¹ = t ^ c * C.k := by
      rcases Fr₁.conj_eq_or_of_mem_L2E S C (Or.inl rfl) hw₁V hw₁2 hg (hsub _ (S.k_mem_L2E C w₂))
        with h | h
      · exact ⟨0, by norm_num, by rw [h, pow_zero, one_mul]⟩
      · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
    have hVmap : Fr₂.V.map (MulAut.conj g).toMonoidHom = Fr₁.V := by
      refine Subgroup.eq_of_le_of_card_ge ?_ (by
        rw [hc₁, card_map_of_injective (MulAut.conj g).injective, hc₂])
      rintro _ ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hvR := Fr₂.V_le_R hv
      have hvE : v ∈ L2E S.z w₂ t C.k := by
        rcases (hV₂ v).mp hv with h | h | h | h <;> rw [h]
        · exact one_mem _
        · exact S.z_mem_L2E C w₂
        · exact S.w_mem_L2E C w₂
        · exact mul_mem (S.z_mem_L2E C w₂) (S.w_mem_L2E C w₂)
      obtain ⟨a, b, -, -, hab⟩ := S.mem_L2E_of_mem_L C hw₁R hw₁2 (hsub v hvE)
        (conj_mem_L (A := A) hg hvR.2)
      rw [hab]
      exact mul_mem (pow_mem (Fr₁.z_mem_V S) a) (pow_mem hw₁V b)
    obtain ⟨d₁, hd₁L, hd₁k, hd₁V, hfpf⟩ := Fr₁.exists_three S
    have hd₁C := L_le_C (A := A) hd₁L
    set h := g⁻¹ * d₁ * g with hhdef
    have hhC : h ∈ centralizer ({t} : Set X) := mul_mem (mul_mem (inv_mem hg) hd₁C) hg
    have hhk : h * C.k * h⁻¹ = C.k := by
      have h1 : d₁ * (t ^ c * C.k) * d₁⁻¹ = t ^ c * C.k := by
        have ht' : d₁ * t ^ c = t ^ c * d₁ := (Commute.pow_right (commute_t_of_mem_C hd₁C) c)
        calc d₁ * (t ^ c * C.k) * d₁⁻¹ = t ^ c * (d₁ * C.k) * d₁⁻¹ := by
              rw [← mul_assoc, ht']; group
          _ = t ^ c * C.k := by rw [hd₁k]; group
      calc h * C.k * h⁻¹ = g⁻¹ * (d₁ * (g * C.k * g⁻¹) * d₁⁻¹) * g := by rw [hhdef]; group
        _ = g⁻¹ * (g * C.k * g⁻¹) * g := by rw [hgk, h1]
        _ = C.k := by group
    have hzV₁ : g * S.z * g⁻¹ ∈ Fr₁.V := by
      rw [← hVmap]
      exact ⟨S.z, Fr₂.z_mem_V S, rfl⟩
    have hu1 : g * S.z * g⁻¹ ≠ 1 := fun h' => S.z_ne_one (by
      calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group)
    have hu'V : d₁ * (g * S.z * g⁻¹) * d₁⁻¹ ∈ Fr₂.V.map (MulAut.conj g).toMonoidHom := by
      rw [hVmap]
      exact hd₁V _ hzV₁
    obtain ⟨v, hvV, hv⟩ := hu'V
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hv
    have hhz : h * S.z * h⁻¹ = v := by
      calc h * S.z * h⁻¹ = g⁻¹ * (d₁ * (g * S.z * g⁻¹) * d₁⁻¹) * g := by rw [hhdef]; group
        _ = v := by rw [← hv]; group
    have hvz : v ≠ S.z := by
      intro h'
      apply hfpf _ hzV₁ hu1
      rw [← hv, h']
    have hconj : h * (S.z * C.k) * h⁻¹ = (v * S.z) * t ^ 0 * (S.z * C.k) := by
      calc h * (S.z * C.k) * h⁻¹ = (h * S.z * h⁻¹) * (h * C.k * h⁻¹) := by group
        _ = v * C.k := by rw [hhz, hhk]
        _ = (v * S.z) * t ^ 0 * (S.z * C.k) := by
          rw [pow_zero, mul_one]
          calc v * C.k = v * (S.z * S.z) * C.k := by rw [← pow_two, hz2, mul_one]
            _ = v * S.z * (S.z * C.k) := by group
    have hvz1 := Fr₂.eq_one_of_conj C S hhC (mul_mem hvV (Fr₂.z_mem_V S)) 0 hconj
    apply hvz
    calc v = v * S.z * S.z⁻¹ := by group
      _ = S.z := by rw [hvz1, one_mul, hzinv]

end L2K

open L2K in
theorem fritzL2KFacts : FritzL2KFacts := by
  intro X _ _ t L F _ _ he A C
  obtain ⟨e₀⟩ := he
  obtain ⟨S⟩ := nonempty_gens (A := A)
  have hzk : S.z * C.k ∈ A.T := mul_mem S.z_mem.1 C.k_mem
  have hzk2 : (S.z * C.k) ^ 2 = 1 := by
    rw [(show Commute S.z C.k from S.z_comm_k C).mul_pow, S.z_sq, C.k_sq, one_mul]
  have hzkR : ∀ r ∈ A.R, S.z * C.k * r = r * (S.z * C.k) := by
    intro r hr
    rw [mul_assoc, commute_k C hr, ← mul_assoc, S.z_comm_R hr, mul_assoc]
  have hψzk : ψX A (S.z * C.k) ∉ R8 := by
    rw [ψX_mul S.z_mem.1 C.k_mem, S.ψ_z, ψX_k C]
    exact z8_mul_k8_not_mem_R8
  obtain ⟨Fr₁⟩ := nonempty_frame e₀ S C.k_mem C.k_sq (fun r hr => commute_k C hr)
    (ψX_k_not_mem_R8 C)
  obtain ⟨Fr₂⟩ := nonempty_frame e₀ S hzk hzk2 hzkR hψzk
  obtain ⟨w₁, hw₁, hw₁V, hc₁, hV₁⟩ := Fr₁.V_eq S
  obtain ⟨w₂, hw₂, hw₂V, hc₂, hV₂⟩ := Fr₂.V_eq S
  have hne : w₁ ≠ w₂ := by
    intro hw
    obtain ⟨d, hdL, hdk, hdV, hfpf⟩ := Fr₁.exists_three S
    have hdC := L_le_C (A := A) hdL
    have hzV := Fr₁.z_mem_V S
    set u := d * S.z * d⁻¹ with hu
    have huV : u ∈ Fr₁.V := hdV _ hzV
    have huz : u ≠ S.z := hfpf _ hzV S.z_ne_one
    have huV₂ : u * S.z ∈ Fr₂.V := by
      have hu' : u ∈ Fr₂.V := by
        rw [hV₂, ← hw]
        exact (hV₁ u).mp huV
      exact mul_mem hu' (Fr₂.z_mem_V S)
    have hconj : d * (S.z * C.k) * d⁻¹ = (u * S.z) * t ^ 0 * (S.z * C.k) := by
      calc d * (S.z * C.k) * d⁻¹ = u * (d * C.k * d⁻¹) := by rw [hu]; group
        _ = u * C.k := by rw [hdk, mul_inv_cancel_right]
        _ = (u * S.z) * t ^ 0 * (S.z * C.k) := by
          rw [pow_zero, mul_one]
          calc u * C.k = u * (S.z * S.z) * C.k := by rw [← pow_two, S.z_sq, mul_one]
            _ = u * S.z * (S.z * C.k) := by group
    have h1 := Fr₂.eq_one_of_conj C S hdC huV₂ 0 hconj
    apply huz
    calc u = u * S.z * S.z⁻¹ := by group
      _ = S.z := by
        rw [h1, one_mul, inv_eq_iff_mul_eq_one, ← pow_two, S.z_sq]
  have hy1 : S.y₀ ≠ 1 := fun h => by
    have := S.ψ_y₀
    rw [h, ψX_one] at this
    exact y8_ne_one this.symm
  have hyz : S.y₀ ≠ S.z := fun h => by
    have := S.ψ_y₀
    rw [h, S.ψ_z] at this
    exact y8_ne_z8 this.symm
  have hxy1 : S.x₀ * S.y₀ ≠ 1 := fun h => by
    have := S.ψ_xy
    rw [h, ψX_one] at this
    exact x8_mul_y8_ne_one this.symm
  have hxyz : S.x₀ * S.y₀ ≠ S.z := fun h => by
    have := S.ψ_xy
    rw [h, S.ψ_z] at this
    exact x8_mul_y8_ne_z8 this.symm
  rcases hw₁ with rfl | rfl <;> rcases hw₂ with rfl | rfl
  · exact absurd rfl hne
  ·
    have hxy : S.x₀⁻¹ * (S.x₀ * S.y₀) = S.y₀ := by group
    have hx2 : S.x₀⁻¹ ^ 2 = S.z := by
      rw [inv_pow, Gens.z, inv_eq_iff_mul_eq_one, ← pow_add, show 2 + 2 = 4 by rfl,
        S.x₀_pow_four]
    refine ⟨S.x₀⁻¹, S.x₀ * S.y₀, inv_mem S.x₀_mem, S.xy_mem, S.xy_sq, ?_, ?_, ?_⟩
    · have h := S.y₀_x₀_y₀
      calc S.x₀ * S.y₀ * S.x₀⁻¹ * (S.x₀ * S.y₀)⁻¹ = S.x₀ * (S.y₀ * S.x₀ * S.y₀⁻¹)⁻¹ * S.x₀⁻¹ := by
            group
        _ = S.x₀⁻¹⁻¹ := by rw [h]; group
    · rw [orderOf_inv, S.orderOf_x₀]
    · rw [hx2, hxy]
      exact facts_core C S Fr₁ Fr₂ hw₁V hw₂V S.y₀_sq S.xy_sq hy1 hyz hxy1 hxyz hc₁ hc₂ hV₁ hV₂
  ·
    refine ⟨S.x₀, S.y₀, S.x₀_mem, S.y₀_mem, S.y₀_sq, S.y₀_x₀_y₀, S.orderOf_x₀, ?_⟩
    exact facts_core C S Fr₁ Fr₂ hw₁V hw₂V S.xy_sq S.y₀_sq hxy1 hxyz hy1 hyz hc₁ hc₂ hV₁ hV₂
  · exact absurd rfl hne

end CFSG.ComponentClassification.HSFLit
