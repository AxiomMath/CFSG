module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qT3Lin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]

theorem sec5c3q_comm_apply {a b : Module.End (ZMod 3) V} (h : a * b = b * a) (x : V) :
    a (b x) = b (a x) := by
  simpa [Module.End.mul_apply] using congrArg (fun f => f x) h

theorem sec5c3q_anticomm_apply {a b : Module.End (ZMod 3) V} (h : a * b = -(b * a)) (x : V) :
    a (b x) = -b (a x) := by
  simpa [Module.End.mul_apply] using congrArg (fun f => f x) h

theorem sec5c3q_mem_ker_sub_one {t : Module.End (ZMod 3) V} {x : V} :
    x ∈ LinearMap.ker (t - 1) ↔ t x = x := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem sec5c3q_mem_ker_add_one {t : Module.End (ZMod 3) V} {x : V} :
    x ∈ LinearMap.ker (t + 1) ↔ t x = -x := by
  rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]

theorem sec5c3q_stable_of_comm {t T : Module.End (ZMod 3) V} (h : t * T = T * t) :
    ∀ x ∈ LinearMap.ker (t + 1), T x ∈ LinearMap.ker (t + 1) := by
  intro x hx
  rw [sec5c3q_mem_ker_add_one] at hx ⊢
  rw [sec5c3q_comm_apply h x, hx, map_neg]

theorem sec5c3q_not_comm_comm {t T₁ T₂ : Module.End (ZMod 3) V} (h₁ : T₁ * T₁ = 1)
    (h₂ : T₂ * T₂ = 1) (h12 : T₁ * T₂ = -(T₂ * T₁))
    (ht : finrank (ZMod 3) (LinearMap.ker (t + 1)) = 3)
    (c₁ : t * T₁ = T₁ * t) (c₂ : t * T₂ = T₂ * t) : False := by
  have s₁ := sec5c3q_stable_of_comm c₁
  have s₂ := sec5c3q_stable_of_comm c₂
  refine sec5c3q_no_anticomm ht (u := T₁.restrict s₁) (w := T₂.restrict s₂) ?_ ?_ ?_
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa [Module.End.mul_apply] using sec5c3q_apply_apply h₁ (x : V)
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa [Module.End.mul_apply] using sec5c3q_apply_apply h₂ (x : V)
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa [Module.End.mul_apply] using sec5c3q_anticomm_apply h12 (x : V)

theorem sec5c3q_not_anti_anti {t T₁ T₂ : Module.End (ZMod 3) V} (h₁ : T₁ * T₁ = 1)
    (h₂ : T₂ * T₂ = 1) (h12 : T₁ * T₂ = -(T₂ * T₁))
    (ht : finrank (ZMod 3) (LinearMap.ker (t + 1)) = 3)
    (a₁ : t * T₁ = -(T₁ * t)) (a₂ : t * T₂ = -(T₂ * t)) : False := by
  have hj : t * (T₁ * T₂) = (T₁ * T₂) * t := by
    calc t * (T₁ * T₂) = (t * T₁) * T₂ := (mul_assoc _ _ _).symm
      _ = (-(T₁ * t)) * T₂ := by rw [a₁]
      _ = -(T₁ * (t * T₂)) := by rw [neg_mul, mul_assoc]
      _ = -(T₁ * (-(T₂ * t))) := by rw [a₂]
      _ = (T₁ * T₂) * t := by rw [mul_neg, neg_neg, mul_assoc]
  have h21 : T₂ * T₁ = -(T₁ * T₂) := by rw [h12, neg_neg]
  have hjj : (T₁ * T₂) * (T₁ * T₂) = -1 := by
    calc (T₁ * T₂) * (T₁ * T₂) = T₁ * (T₂ * T₁) * T₂ := by simp only [mul_assoc]
      _ = T₁ * (-(T₁ * T₂)) * T₂ := by rw [h21]
      _ = -((T₁ * T₁) * (T₂ * T₂)) := by simp only [mul_neg, neg_mul, mul_assoc]
      _ = -1 := by rw [h₁, h₂, mul_one]
  have s := sec5c3q_stable_of_comm hj
  refine sec5c3q_no_sqrt_neg_one ht (u := (T₁ * T₂).restrict s) ?_
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simpa [Module.End.mul_apply] using congrArg (fun f => f (x : V)) hjj

theorem sec5c3q_branch_ncard_le {T₁ T₂ : Module.End (ZMod 3) V} (h₁ : T₁ * T₁ = 1)
    (h₂ : T₂ * T₂ = 1) (h12 : T₁ * T₂ = -(T₂ * T₁))
    (hU : finrank (ZMod 3) (LinearMap.ker (T₁ - 1)) = 3) (S : Set (Module.End (ZMod 3) V))
    (hsq : ∀ t ∈ S, t * t = 1) (hc₁ : ∀ t ∈ S, t * T₁ = T₁ * t)
    (ha₂ : ∀ t ∈ S, t * T₂ = -(T₂ * t))
    (hcomm : ∀ t ∈ S, ∀ t' ∈ S, t * t' = t' * t ∨ t * t' = -(t' * t)) : S.ncard ≤ 8 := by
  classical
  haveI := sec5c3q_finite_end (V := V)
  have hstab : ∀ t ∈ S, ∀ x ∈ LinearMap.ker (T₁ - 1), t x ∈ LinearMap.ker (T₁ - 1) := by
    intro t ht x hx
    rw [sec5c3q_mem_ker_sub_one] at hx ⊢
    rw [← sec5c3q_comm_apply (hc₁ t ht) x, hx]
  let ρ : S → Module.End (ZMod 3) (LinearMap.ker (T₁ - 1)) :=
    fun t => (t : Module.End (ZMod 3) V).restrict (hstab t t.2)
  have hρ : ∀ (t : S) (x : LinearMap.ker (T₁ - 1)),
      ((ρ t x : LinearMap.ker (T₁ - 1)) : V) = (t : Module.End (ZMod 3) V) x := fun t x => rfl
  have hρsq : ∀ t : S, ρ t * ρ t = 1 := by
    intro t
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa [hρ, Module.End.mul_apply] using sec5c3q_apply_apply (hsq t t.2) (x : V)
  have hρcomm : ∀ t t' : S, Commute (ρ t) (ρ t') := by
    intro t t'
    rcases hcomm t t.2 t' t'.2 with h | h
    · show ρ t * ρ t' = ρ t' * ρ t
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simpa [hρ, Module.End.mul_apply] using sec5c3q_comm_apply h (x : V)
    · exfalso
      refine sec5c3q_no_anticomm hU (hρsq t) (hρsq t') ?_
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simpa [hρ, Module.End.mul_apply] using sec5c3q_anticomm_apply h (x : V)
  have hρinj : Function.Injective ρ := by
    intro t t' htt
    have hagree : ∀ x ∈ LinearMap.ker (T₁ - 1),
        (t : Module.End (ZMod 3) V) x = (t' : Module.End (ZMod 3) V) x := by
      intro x hx
      have := congrArg (fun f => ((f ⟨x, hx⟩ : LinearMap.ker (T₁ - 1)) : V)) htt
      simpa [hρ] using this
    have hfix : ∀ x ∈ LinearMap.ker (T₁ - 1),
        (t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V) x) = x := by
      intro x hx
      rw [hagree _ (hstab t' t'.2 x hx)]
      exact sec5c3q_apply_apply (hsq t' t'.2) x
    have hT₂ : ∀ y, (t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V) (T₂ y)) =
        T₂ ((t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V) y)) := by
      intro y
      rw [sec5c3q_anticomm_apply (ha₂ t' t'.2) y, map_neg,
        sec5c3q_anticomm_apply (ha₂ t t.2), neg_neg]
    have hv : ∀ v, (t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V) v) = v := by
      intro v
      have h22 : (2 : ZMod 3) * 2 = 1 := by decide
      set a : V := (2 : ZMod 3) • (v + T₁ v) with ha
      set b : V := (2 : ZMod 3) • (v - T₁ v) with hb
      have hsm : a + b = (2 : ZMod 3) • ((v + T₁ v) + (v - T₁ v)) := (smul_add _ _ _).symm
      have hab : a + b = v := by
        calc a + b = (2 : ZMod 3) • ((v + T₁ v) + (v - T₁ v)) := hsm
          _ = (2 : ZMod 3) • ((2 : ZMod 3) • v) := by
            congr 1
            rw [two_smul]
            abel
          _ = ((2 : ZMod 3) * 2) • v := smul_smul _ _ _
          _ = v := by rw [h22, one_smul]
      have haU : a ∈ LinearMap.ker (T₁ - 1) := by
        rw [sec5c3q_mem_ker_sub_one, ha, map_smul, map_add, sec5c3q_apply_apply h₁, add_comm]
      have hT₁b : T₁ b = -b := by
        rw [hb, map_smul, map_sub, sec5c3q_apply_apply h₁, ← smul_neg, neg_sub]
      have hbU : T₂ b ∈ LinearMap.ker (T₁ - 1) := by
        rw [sec5c3q_mem_ker_sub_one, sec5c3q_anticomm_apply h12, hT₁b, map_neg, neg_neg]
      have hbb : (t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V) b) = b := by
        calc (t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V) b)
            = (t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V) (T₂ (T₂ b))) := by
              rw [sec5c3q_apply_apply h₂ b]
          _ = T₂ ((t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V) (T₂ b))) := hT₂ _
          _ = T₂ (T₂ b) := by rw [hfix _ hbU]
          _ = b := sec5c3q_apply_apply h₂ b
      calc (t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V) v)
          = (t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V) (a + b)) := by rw [hab]
        _ = a + b := by rw [map_add, map_add, hfix a haU, hbb]
        _ = v := hab
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    calc (t : Module.End (ZMod 3) V) v
        = (t : Module.End (ZMod 3) V) ((t' : Module.End (ZMod 3) V)
            ((t' : Module.End (ZMod 3) V) v)) := by rw [sec5c3q_apply_apply (hsq t' t'.2)]
      _ = (t' : Module.End (ZMod 3) V) v := hv _
  calc S.ncard = Nat.card S := (Nat.card_coe_set_eq S).symm
    _ ≤ 2 ^ finrank (ZMod 3) (LinearMap.ker (T₁ - 1)) :=
        sec5c3q_card_le_two_pow ρ hρcomm hρsq hρinj
    _ = 8 := by rw [hU]; norm_num

theorem sec5c3q_caseB_ncard_le {T₁ T₂ : Module.End (ZMod 3) V} (S : Set (Module.End (ZMod 3) V))
    (hV : finrank (ZMod 3) V = 6) (hsq : ∀ t ∈ S, t * t = 1)
    (hdim : ∀ t ∈ S, finrank (ZMod 3) (LinearMap.range (t - 1)) = 3)
    (hcomm : ∀ t ∈ S, ∀ t' ∈ S, t * t' = t' * t ∨ t * t' = -(t' * t))
    (hT₁ : T₁ ∈ S) (hT₂ : T₂ ∈ S) (h12 : T₁ * T₂ = -(T₂ * T₁)) : S.ncard ≤ 16 := by
  classical
  haveI := sec5c3q_finite_end (V := V)
  have hker : ∀ t ∈ S, finrank (ZMod 3) (LinearMap.ker (t + 1)) = 3 := fun t ht => by
    rw [← sec5c3q_range_sub_one (hsq t ht)]
    exact hdim t ht
  have hfix : ∀ t ∈ S, finrank (ZMod 3) (LinearMap.ker (t - 1)) = 3 := fun t ht => by
    have h := LinearMap.finrank_range_add_finrank_ker (t - 1)
    rw [hdim t ht, hV] at h
    omega
  have h21 : T₂ * T₁ = -(T₁ * T₂) := by rw [h12, neg_neg]
  set S₁ : Set (Module.End (ZMod 3) V) :=
    {t | t ∈ S ∧ t * T₁ = T₁ * t ∧ t * T₂ = -(T₂ * t)} with hS₁
  set S₂ : Set (Module.End (ZMod 3) V) :=
    {t | t ∈ S ∧ t * T₂ = T₂ * t ∧ t * T₁ = -(T₁ * t)} with hS₂
  have hcov : S ⊆ S₁ ∪ S₂ := by
    intro t ht
    rcases hcomm t ht T₁ hT₁ with c₁ | a₁ <;> rcases hcomm t ht T₂ hT₂ with c₂ | a₂
    · exact (sec5c3q_not_comm_comm (hsq T₁ hT₁) (hsq T₂ hT₂) h12 (hker t ht) c₁ c₂).elim
    · exact Or.inl ⟨ht, c₁, a₂⟩
    · exact Or.inr ⟨ht, c₂, a₁⟩
    · exact (sec5c3q_not_anti_anti (hsq T₁ hT₁) (hsq T₂ hT₂) h12 (hker t ht) a₁ a₂).elim
  have hb₁ : S₁.ncard ≤ 8 :=
    sec5c3q_branch_ncard_le (hsq T₁ hT₁) (hsq T₂ hT₂) h12 (hfix T₁ hT₁) S₁
      (fun t ht => hsq t ht.1) (fun t ht => ht.2.1) (fun t ht => ht.2.2)
      (fun t ht t' ht' => hcomm t ht.1 t' ht'.1)
  have hb₂ : S₂.ncard ≤ 8 :=
    sec5c3q_branch_ncard_le (hsq T₂ hT₂) (hsq T₁ hT₁) h21 (hfix T₂ hT₂) S₂
      (fun t ht => hsq t ht.1) (fun t ht => ht.2.1) (fun t ht => ht.2.2)
      (fun t ht t' ht' => hcomm t ht.1 t' ht'.1)
  calc S.ncard ≤ (S₁ ∪ S₂).ncard := Set.ncard_le_ncard hcov
    _ ≤ S₁.ncard + S₂.ncard := Set.ncard_union_le _ _
    _ ≤ 16 := by omega

end CFSG.OddStandard.SmallF3.Omega
