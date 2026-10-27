module

public import CFSG.CGT.M24S.NSOrbit4
public import CFSG.CGT.M24S.NSSecond

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} (c : NatCoord T H t)

theorem wset_of_mem_T {s : G} (hs : s = 1 ∨ s = t) : Wset c s := by
  rcases hs with rfl | rfl
  · exact wset_one c
  · exact wset_t c

theorem wset_mul (hF : Fixes c v₀) {e₁ e₂ : G} (h₁ : Wset c e₁) (h₂ : Wset c e₂) :
    Wset c (e₁ * e₂) := by
  have central : ∀ {x : G}, x ∈ c.E → x * t = t * x := fun hx => commute_t (c.E_le hx)
  have hTt : ∀ {e : G}, Wset c e → top (c.mat e) = 0 → e = 1 ∨ e = t := fun he h0 =>
    wset_T c (mem_T_of_top_eq_zero c he.1 h0) he
  by_cases hv₁ : top (c.mat e₁) = 0
  · rcases hTt h₁ hv₁ with rfl | rfl
    · rwa [one_mul]
    · rw [← central h₂.1]
      exact wset_mul_t c h₂
  by_cases hv₂ : top (c.mat e₂) = 0
  · rcases hTt h₂ hv₂ with rfl | rfl
    · rwa [mul_one]
    · exact wset_mul_t c h₁
  have he₁ : e₁ * e₁ = 1 := by rw [← pow_two]; exact h₁.2.1
  by_cases hv : top (c.mat e₂) = top (c.mat e₁)
  · rcases wset_unique c h₁ h₂ hv hv₁ with rfl | rfl
    · rw [he₁]
      exact wset_one c
    · rw [← mul_assoc, he₁, one_mul]
      exact wset_t c
  obtain ⟨e₃, h₃, hv₃⟩ := exists_wset c hF (top (c.mat e₁) + top (c.mat e₂))
  have hT : e₁ * e₂ * e₃ ∈ T := by
    apply mem_T_of_top_eq_zero c (c.E.mul_mem (c.E.mul_mem h₁.1 h₂.1) h₃.1)
    rw [top_mul_of_mem_E c (c.E.mul_mem h₁.1 h₂.1) h₃.1, top_mul_of_mem_E c h₁.1 h₂.1, hv₃,
      vec_add_self]
  have hf : tail (c.vec (e₁ * e₂ * e₃)) = 0 := by
    by_contra hne
    obtain ⟨u, hu⟩ := exists_dotProduct_eq_one _ hne
    obtain ⟨e₄, h₄, hv₄⟩ := exists_wset c hF u
    have hcomm : Commute e₄ (e₁ * e₂ * e₃) :=
      ((show Commute e₄ e₁ from wset_comm c hF h₄ h₁).mul_right
        (show Commute e₄ e₂ from wset_comm c hF h₄ h₂)).mul_right
        (show Commute e₄ e₃ from wset_comm c hF h₄ h₃)
    have h1 := conj_eq_of_dotProduct_eq_one c h₄.1 hT (by rw [hv₄]; exact hu)
    rw [← hcomm.eq, mul_inv_cancel_right] at h1
    exact c.z_ne_one (left_eq_mul.1 h1)
  have he₃ : e₃⁻¹ = e₃ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h₃.2.1)
  have e : e₁ * e₂ = (e₁ * e₂ * e₃) * e₃⁻¹ := by group
  rw [e, he₃]
  rcases eq_one_or_eq_t_of_tail_eq_zero c hT hf with h | h <;> rw [h]
  · rwa [one_mul]
  · rw [← central h₃.1]
    exact wset_mul_t c h₃

@[expose] def wsub (hF : Fixes c v₀) : Subgroup G where
  carrier := {e | Wset c e}
  one_mem' := wset_one c
  mul_mem' := fun h₁ h₂ => wset_mul c hF h₁ h₂
  inv_mem' := fun {e} he => by
    have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact he.2.1)
    change Wset c e⁻¹
    rw [he']
    exact he

theorem mem_wsub {hF : Fixes c v₀} {e : G} : e ∈ wsub c hF ↔ Wset c e := Iff.rfl

theorem wsub_inf_T (hF : Fixes c v₀) : wsub c hF ⊓ T = Subgroup.zpowers t := by
  ext s
  rw [Subgroup.mem_inf, mem_wsub]
  constructor
  · rintro ⟨hW, hs⟩
    rcases wset_T c hs hW with h | h <;> rw [h]
    · exact one_mem _
    · exact Subgroup.mem_zpowers t
  · intro hs
    have h := eq_one_or_eq_of_mem_zpowers c.z_sq hs
    refine ⟨wset_of_mem_T c h, ?_⟩
    rcases h with h | h <;> rw [h]
    · exact T.one_mem
    · exact c.mem

theorem card_wsub (hF : Fixes c v₀) : Nat.card (wsub c hF) = 16 := by
  have hWE : wsub c hF ≤ c.E := fun e he => he.1
  let f : wsub c hF →* Multiplicative (Fin 3 → ZMod 2) := c.τ.comp (Subgroup.inclusion hWE)
  have hf : ∀ w : wsub c hF, f w = Multiplicative.ofAdd (top (c.mat w)) := fun w =>
    c.τ_apply (Subgroup.inclusion hWE w)
  have hsurj : Function.Surjective f := fun a => by
    obtain ⟨e, he, hea⟩ := exists_wset c hF (Multiplicative.toAdd a)
    exact ⟨⟨e, he⟩, by rw [hf]; exact congrArg Multiplicative.ofAdd hea⟩
  have hker : f.ker = (Subgroup.zpowers t).subgroupOf (wsub c hF) := by
    ext w
    rw [MonoidHom.mem_ker, hf, Subgroup.mem_subgroupOf, ← wsub_inf_T c hF, ofAdd_eq_one]
    constructor
    · intro h
      exact ⟨w.2, mem_T_of_top_eq_zero c w.2.1 h⟩
    · intro h
      exact top_eq_zero_of_mem_T c h.2
  have hle : Subgroup.zpowers t ≤ wsub c hF := by
    rw [Subgroup.zpowers_le]
    exact wset_t c
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv,
    NatCoord.card_vec, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    card_zpowers_z c] at h1
  rw [h1]
  norm_num

theorem not_fixes_v₀ [Finite G] (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H) :
    ¬ Fixes c v₀ := fun hF =>
  hns (hasComplement_of_secondE16 c.le hN c.mem c.z_ne_one
    (fun e he => c.E_le (show Wset c e from he).1)
    (fun _ hk _ hw => wset_conj c hk hw) (fun _ ha _ hb => wset_comm c hF ha hb)
    (fun w hw => (show Wset c w from hw).2.1) (card_wsub c hF) (wsub_inf_T c hF)
    (fun w hw => centreTransvecting_of_mem_E c (show Wset c w from hw).1))

theorem moves_of_ne_zero [Finite G] (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H)
    {v : Fin 3 → ZMod 2} (hv : v ≠ 0) : Moves c v := by
  rcases moves_or_fixes c v with h | h
  · exact h
  obtain ⟨B, hB1, hBv⟩ := exists_vecMul_v₀_eq v hv
  obtain ⟨k, hk, hkB⟩ := c.exists_mem_cent B hB1
  exact absurd (fixes_of_conj c hk (by rw [hkB, hBv]) h) (not_fixes_v₀ c hN hns)

end CFSG.CGT.M24S.NSB
