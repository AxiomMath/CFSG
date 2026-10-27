
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillFacts
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowPBase

@[expose] public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

@[expose] def Pres (u : Bool) (σ : Equiv.Perm (Fin 64)) : Prop := presT u (tupleOf σ) = true

theorem nl_decomp : ∀ v, v < 64 → wpart v = 0 →
    v = (if (xpart v).testBit 0 then mkv 0 1 else 0) ^^^
      (if (xpart v).testBit 1 then mkv 0 2 else 0) ^^^
      (if (xpart v).testBit 2 then mkv 0 4 else 0) := by
  decide +kernel

theorem nr_decomp : ∀ v, v < 64 → wpart v = xpart v →
    v = (if (wpart v).testBit 0 then mkv 1 1 else 0) ^^^
      (if (wpart v).testBit 1 then mkv 2 2 else 0) ^^^
      (if (wpart v).testBit 2 then mkv 4 4 else 0) := by
  decide +kernel

theorem nl_nr_zero : ∀ v, v < 64 → wpart v = 0 → wpart v = xpart v → v = 0 := by decide +kernel

theorem presT_facts : presT false idT = true ∧ presT true idT = true ∧ presT false z0T = false ∧
    presT true z0T = false := by
  decide +kernel

theorem validT_omT : validT true omT = true := by decide +kernel

theorem om_facts : compT omT omT ≠ omT ∧ compT omT (compT omT omT) = idT := by decide +kernel

section Linear

variable {σ : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w))
include hσ

theorem maps_of_basis {p : ℕ → Prop} (hp0 : p 0)
    (hpx : ∀ v w, v < 64 → w < 64 → p v → p w → p (v ^^^ w)) {b₀ b₁ b₂ : ℕ}
    (hb₀ : b₀ < 64) (hb₁ : b₁ < 64) (hb₂ : b₂ < 64) (h₀ : p (fn σ b₀)) (h₁ : p (fn σ b₁))
    (h₂ : p (fn σ b₂)) {v : ℕ} {c₀ c₁ c₂ : Bool}
    (hdec : v = (if c₀ then b₀ else 0) ^^^ (if c₁ then b₁ else 0) ^^^ (if c₂ then b₂ else 0)) :
    p (fn σ v) := by
  have hz : fn σ 0 = 0 := by
    have := fn_val σ 0
    rw [map_zero_of_add hσ] at this
    exact this
  have key : ∀ (c : Bool) (b : ℕ), b < 64 → p (fn σ b) → (if c then b else 0) < 64 ∧
      p (fn σ (if c then b else 0)) := by
    intro c b hb hpb
    cases c
    · exact ⟨by norm_num, by simp only [Bool.false_eq_true, ite_false, hz]; exact hp0⟩
    · exact ⟨hb, hpb⟩
  obtain ⟨l₀, p₀⟩ := key c₀ b₀ hb₀ h₀
  obtain ⟨l₁, p₁⟩ := key c₁ b₁ hb₁ h₁
  obtain ⟨l₂, p₂⟩ := key c₂ b₂ hb₂ h₂
  rw [hdec, fn_xor hσ (Nat.xor_lt_two_pow (n := 6) l₀ l₁) l₂, fn_xor hσ l₀ l₁]
  exact hpx _ _ (Nat.xor_lt_two_pow (n := 6) (fn_lt _ _) (fn_lt _ _)) (fn_lt _ _)
    (hpx _ _ (fn_lt _ _) (fn_lt _ _) p₀ p₁) p₂

theorem maps_nl {p : ℕ → Prop} (hp0 : p 0)
    (hpx : ∀ v w, v < 64 → w < 64 → p v → p w → p (v ^^^ w))
    (h₀ : p (fn σ (mkv 0 1))) (h₁ : p (fn σ (mkv 0 2))) (h₂ : p (fn σ (mkv 0 4))) :
    ∀ v, v < 64 → wpart v = 0 → p (fn σ v) := fun v hv hw =>
  maps_of_basis hσ hp0 hpx (by decide) (by decide) (by decide) h₀ h₁ h₂ (nl_decomp v hv hw)

theorem maps_nr {p : ℕ → Prop} (hp0 : p 0)
    (hpx : ∀ v w, v < 64 → w < 64 → p v → p w → p (v ^^^ w))
    (h₀ : p (fn σ (mkv 1 1))) (h₁ : p (fn σ (mkv 2 2))) (h₂ : p (fn σ (mkv 4 4))) :
    ∀ v, v < 64 → wpart v = xpart v → p (fn σ v) := fun v hv hw =>
  maps_of_basis hσ hp0 hpx (by decide) (by decide) (by decide) h₀ h₁ h₂ (nr_decomp v hv hw)

end Linear

theorem imNl_tupleOf {σ : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w)) :
    imNl (tupleOf σ) = [fn σ (mkv 0 1), fn σ (mkv 0 2), fn σ (mkv 0 4)] := by
  simp only [imNl, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, pow_zero, pow_one]
  rw [evalV_tupleOf hσ (by decide), evalV_tupleOf hσ (by decide),
    evalV_tupleOf hσ (by decide)]
  rfl

theorem imNr_tupleOf {σ : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w)) :
    imNr (tupleOf σ) = [fn σ (mkv 1 1), fn σ (mkv 2 2), fn σ (mkv 4 4)] := by
  simp only [imNr, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, pow_zero, pow_one]
  rw [evalV_tupleOf hσ (by decide), evalV_tupleOf hσ (by decide),
    evalV_tupleOf hσ (by decide)]
  rfl

theorem wr_zero' : wpart 0 = xpart 0 := rfl

theorem wr_xor' : ∀ v w, v < 64 → w < 64 → wpart v = xpart v → wpart w = xpart w →
    wpart (v ^^^ w) = xpart (v ^^^ w) :=
  fun v w hv hw h1 h2 => by rw [wpart_xor v hv w hw, xpart_xor v hv w hw, h1, h2]

theorem wl_xor' : ∀ v w, v < 64 → w < 64 → wpart v = 0 → wpart w = 0 → wpart (v ^^^ w) = 0 :=
  fun v w hv hw h1 h2 => by rw [wpart_xor v hv w hw, h1, h2]; rfl

theorem sgnOK_false_iff {σ : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w)) :
    sgnOK false (tupleOf σ) = true ↔
      ((∀ v, v < 64 → wpart v = 0 → wpart (fn σ v) = 0) ∧
        (∀ v, v < 64 → wpart v = xpart v → wpart (fn σ v) = xpart (fn σ v))) ∨
      ((∀ v, v < 64 → wpart v = 0 → wpart (fn σ v) = xpart (fn σ v)) ∧
        (∀ v, v < 64 → wpart v = xpart v → wpart (fn σ v) = 0)) := by
  simp only [sgnOK, Bool.false_eq_true, ite_false, Bool.or_eq_true, Bool.and_eq_true,
    imNl_tupleOf hσ, imNr_tupleOf hσ, List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq]
  constructor
  · rintro (⟨hl, hr⟩ | ⟨hl, hr⟩)
    · exact Or.inl ⟨maps_nl hσ (p := fun v => wpart v = 0) rfl wl_xor' hl.1 hl.2.1 hl.2.2,
        maps_nr hσ (p := fun v => wpart v = xpart v) wr_zero' wr_xor' hr.1 hr.2.1 hr.2.2⟩
    · exact Or.inr ⟨maps_nl hσ (p := fun v => wpart v = xpart v) wr_zero' wr_xor' hl.1 hl.2.1
        hl.2.2, maps_nr hσ (p := fun v => wpart v = 0) rfl wl_xor' hr.1 hr.2.1 hr.2.2⟩
  · rintro (⟨hl, hr⟩ | ⟨hl, hr⟩)
    · exact Or.inl ⟨⟨hl _ (by decide) (by decide), hl _ (by decide) (by decide),
        hl _ (by decide) (by decide)⟩, ⟨hr _ (by decide) (by decide),
        hr _ (by decide) (by decide), hr _ (by decide) (by decide)⟩⟩
    · exact Or.inr ⟨⟨hl _ (by decide) (by decide), hl _ (by decide) (by decide),
        hl _ (by decide) (by decide)⟩, ⟨hr _ (by decide) (by decide),
        hr _ (by decide) (by decide), hr _ (by decide) (by decide)⟩⟩

theorem sgnOK_mul_false {σ τ : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w))
    (hτ : ∀ v w, τ (fx v w) = fx (τ v) (τ w)) (h1 : sgnOK false (tupleOf σ) = true)
    (h2 : sgnOK false (tupleOf τ) = true) : sgnOK false (tupleOf (σ * τ)) = true := by
  have hστ : ∀ v w, (σ * τ) (fx v w) = fx ((σ * τ) v) ((σ * τ) w) := fun v w => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hτ, hσ]
  rw [sgnOK_false_iff hσ] at h1
  rw [sgnOK_false_iff hτ] at h2
  rw [sgnOK_false_iff hστ]
  have hm : ∀ v, v < 64 → fn (σ * τ) v = fn σ (fn τ v) := fun v hv => fn_mul σ τ hv
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
  · exact Or.inl ⟨fun v hv h => by rw [hm v hv]; exact a1 _ (fn_lt _ _) (a2 v hv h),
      fun v hv h => by rw [hm v hv]; exact b1 _ (fn_lt _ _) (b2 v hv h)⟩
  · exact Or.inr ⟨fun v hv h => by rw [hm v hv]; exact b1 _ (fn_lt _ _) (a2 v hv h),
      fun v hv h => by rw [hm v hv]; exact a1 _ (fn_lt _ _) (b2 v hv h)⟩
  · exact Or.inr ⟨fun v hv h => by rw [hm v hv]; exact a1 _ (fn_lt _ _) (a2 v hv h),
      fun v hv h => by rw [hm v hv]; exact b1 _ (fn_lt _ _) (b2 v hv h)⟩
  · exact Or.inl ⟨fun v hv h => by rw [hm v hv]; exact b1 _ (fn_lt _ _) (a2 v hv h),
      fun v hv h => by rw [hm v hv]; exact a1 _ (fn_lt _ _) (b2 v hv h)⟩

theorem exists_omega : ∃ ω ∈ Gq true, tupleOf ω = omT := exists_of_validT validT_omT

section Unitary

variable {ω : Equiv.Perm (Fin 64)} (hω : ω ∈ Gq true) (hωt : tupleOf ω = omT)
include hω hωt

omit hω in
theorem omega_ne_one : ω ≠ 1 := fun h1 => by
  have := om_facts.2
  rw [h1, tupleOf_one] at hωt
  exact absurd hωt (by decide)

theorem omega_cube : ω * (ω * ω) = 1 :=
  tupleOf_injective (mul_mem hω (mul_mem hω hω)).1 (one_mem (Gq true)).1 (by
    rw [tupleOf_mul hω.1, tupleOf_mul hω.1, hωt, tupleOf_one]; exact om_facts.2)

theorem pres_true_iff {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq true) :
    Pres true σ ↔ σ * ω = ω * σ := by
  have e1 : compT (tupleOf σ) omT = tupleOf (σ * ω) := by rw [tupleOf_mul hσ.1, hωt]
  have e2 : compT omT (tupleOf σ) = tupleOf (ω * σ) := by rw [tupleOf_mul hω.1, hωt]
  simp only [Pres, presT, ite_true, beq_iff_eq, e1, e2]
  exact ⟨fun h => tupleOf_injective (mul_mem hσ hω).1 (mul_mem hω hσ).1 h,
    fun h => by rw [h]⟩

theorem sgn_true_iff {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq true) :
    sgnOK true (tupleOf σ) = true ↔ σ * ω = ω * σ ∨ σ * ω = ω * ω * σ := by
  have e1 : compT (tupleOf σ) omT = tupleOf (σ * ω) := by rw [tupleOf_mul hσ.1, hωt]
  have e2 : compT omT (tupleOf σ) = tupleOf (ω * σ) := by rw [tupleOf_mul hω.1, hωt]
  have e3 : compT (compT omT omT) (tupleOf σ) = tupleOf (ω * ω * σ) := by
    rw [tupleOf_mul (mul_mem hω hω).1, tupleOf_mul hω.1, hωt]
  simp only [sgnOK, ite_true, Bool.or_eq_true, beq_iff_eq]
  rw [e1, e2, e3]
  constructor
  · rintro (h | h)
    · exact Or.inl (tupleOf_injective (mul_mem hσ hω).1 (mul_mem hω hσ).1 h)
    · exact Or.inr (tupleOf_injective (mul_mem hσ hω).1 (mul_mem (mul_mem hω hω) hσ).1 h)
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

theorem sgnOK_mul_true {σ τ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq true) (hτ : τ ∈ Gq true)
    (h1 : sgnOK true (tupleOf σ) = true) (h2 : sgnOK true (tupleOf τ) = true) :
    sgnOK true (tupleOf (σ * τ)) = true := by
  rw [sgn_true_iff hω hωt hσ] at h1
  rw [sgn_true_iff hω hωt hτ] at h2
  rw [sgn_true_iff hω hωt (mul_mem hσ hτ)]
  have h3 := omega_cube hω hωt
  rcases h1 with hA | hA <;> rcases h2 with hB | hB
  · left
    calc σ * τ * ω = σ * (τ * ω) := by group
      _ = σ * (ω * τ) := by rw [hB]
      _ = (σ * ω) * τ := by group
      _ = ω * (σ * τ) := by rw [hA]; group
  · right
    calc σ * τ * ω = σ * (τ * ω) := by group
      _ = σ * (ω * ω * τ) := by rw [hB]
      _ = (σ * ω) * ω * τ := by group
      _ = (ω * σ) * ω * τ := by rw [hA]
      _ = ω * (σ * ω) * τ := by group
      _ = ω * (ω * σ) * τ := by rw [hA]
      _ = ω * ω * (σ * τ) := by group
  · right
    calc σ * τ * ω = σ * (τ * ω) := by group
      _ = σ * (ω * τ) := by rw [hB]
      _ = (σ * ω) * τ := by group
      _ = ω * ω * (σ * τ) := by rw [hA]; group
  · left
    calc σ * τ * ω = σ * (τ * ω) := by group
      _ = σ * (ω * ω * τ) := by rw [hB]
      _ = (σ * ω) * ω * τ := by group
      _ = (ω * ω * σ) * ω * τ := by rw [hA]
      _ = ω * ω * (σ * ω) * τ := by group
      _ = ω * ω * (ω * ω * σ) * τ := by rw [hA]
      _ = (ω * (ω * ω)) * ω * σ * τ := by group
      _ = ω * (σ * τ) := by rw [h3]; group

end Unitary

theorem sgnOK_mul {u : Bool} {σ τ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) (hτ : τ ∈ Gq u)
    (h1 : sgnOK u (tupleOf σ) = true) (h2 : sgnOK u (tupleOf τ) = true) :
    sgnOK u (tupleOf (σ * τ)) = true := by
  cases u
  · exact sgnOK_mul_false hσ.1 hτ.1 h1 h2
  · obtain ⟨ω, hω, hωt⟩ := exists_omega
    exact sgnOK_mul_true hω hωt hσ hτ h1 h2

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
