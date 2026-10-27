module

public import CFSG.GH74.Uniqueness.SU.SU5Q8D8
public import CFSG.GH74.Uniqueness.SU.SU5Models

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

namespace J2Syl

@[expose] def q1 : J2Syl := ⟨⟨1, 1, F4c.w⟩, 1⟩

@[expose] def q2 : J2Syl := ⟨⟨F4c.w, F4c.w2, F4c.w⟩, 1⟩

@[expose] def qf : QuaternionGroup 2 → J2Syl
  | .a i => q1 ^ i.val
  | .xa i => q2 * q1 ^ i.val

@[expose] def qhom : QuaternionGroup 2 →* J2Syl where
  toFun := qf
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

@[expose] def rho : J2Syl := ⟨⟨0, 0, F4c.w⟩, Multiplicative.ofAdd 1⟩

@[expose] def df : DihedralGroup 4 → J2Syl
  | .r i => rho ^ i.val
  | .sr i => x0 * rho ^ i.val

@[expose] def dhom : DihedralGroup 4 →* J2Syl where
  toFun := df
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem qhom_injective : Function.Injective qhom := by
  have h : ∀ x y : QuaternionGroup 2, qf x = qf y → x = y := by decide +kernel
  exact fun x y hxy => h x y hxy

theorem dhom_injective : Function.Injective dhom := by
  have h : ∀ x y : DihedralGroup 4, df x = df y → x = y := by decide +kernel
  exact fun x y hxy => h x y hxy

@[expose] def Qs : Subgroup J2Syl := qhom.range

@[expose] def Ds : Subgroup J2Syl := dhom.range

theorem Qs_equiv : Nonempty (Qs ≃* QuaternionGroup 2) :=
  ⟨(MonoidHom.ofInjective qhom_injective).symm⟩

theorem Ds_equiv : Nonempty (Ds ≃* DihedralGroup 4) :=
  ⟨(MonoidHom.ofInjective dhom_injective).symm⟩

theorem mem_Qs {s : J2Syl} : s ∈ Qs ↔ s.right = 1 ∧ s * x0 = x0 * s := by
  have h1 : ∀ x : QuaternionGroup 2, (qf x).right = 1 ∧ qf x * x0 = x0 * qf x := by
    decide +kernel
  have h2 : ∀ s : J2Syl, s.right = 1 ∧ s * x0 = x0 * s → ∃ x : QuaternionGroup 2, qf x = s := by
    decide +kernel
  constructor
  · rintro ⟨x, rfl⟩
    exact h1 x
  · intro h
    obtain ⟨x, hx⟩ := h2 s h
    exact ⟨x, hx⟩

theorem mem_Ds {s : J2Syl} : s ∈ Ds ↔ s.left.a = 0 ∧ s.left.b = 0 := by
  have h1 : ∀ x : DihedralGroup 4, (df x).left.a = 0 ∧ (df x).left.b = 0 := by decide +kernel
  have h2 : ∀ s : J2Syl, s.left.a = 0 ∧ s.left.b = 0 → ∃ x : DihedralGroup 4, df x = s := by
    decide +kernel
  constructor
  · rintro ⟨x, rfl⟩
    exact h1 x
  · intro h
    obtain ⟨x, hx⟩ := h2 s h
    exact ⟨x, hx⟩

instance instDecMemQs (s : J2Syl) : Decidable (s ∈ Qs) :=
  decidable_of_iff _ mem_Qs.symm

instance instDecMemDs (s : J2Syl) : Decidable (s ∈ Ds) :=
  decidable_of_iff _ mem_Ds.symm

@[expose] def R : Subgroup J2Syl := subOfPred (fun s => s.left.b = F4c.sg s.left.a)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def V : Subgroup J2Syl :=
  subOfPred (fun s => s.right = 1 ∧ s.left.a = 0 ∧ s.left.c = 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

instance instDecMemR (s : J2Syl) : Decidable (s ∈ R) :=
  inferInstanceAs (Decidable (s.left.b = F4c.sg s.left.a))

instance instDecMemV (s : J2Syl) : Decidable (s ∈ V) :=
  inferInstanceAs (Decidable (s.right = 1 ∧ s.left.a = 0 ∧ s.left.c = 0))

theorem mem_R {s : J2Syl} : s ∈ R ↔ s.left.b = F4c.sg s.left.a := Iff.rfl

theorem mem_V {s : J2Syl} : s ∈ V ↔ s.right = 1 ∧ s.left.a = 0 ∧ s.left.c = 0 := Iff.rfl

theorem card_R : Nat.card R = 32 := by
  unfold R; rw [card_subOfPred]; decide +kernel

theorem card_V : Nat.card V = 4 := by
  unfold V; rw [card_subOfPred]; decide +kernel

theorem R_normal : ∀ g r : J2Syl, r ∈ R → g * r * g⁻¹ ∈ R := by decide +kernel

theorem isE_V : IsE 2 V := by
  have h1 : ∀ s t : J2Syl, s ∈ V → t ∈ V → s * t = t * s := by decide +kernel
  have h2 : ∀ s : J2Syl, s ∈ V → s * s = 1 := by decide +kernel
  exact ⟨isElemAbelian_iff.2 ⟨fun a ha b hb => h1 a b ha hb,
    fun a ha => by rw [pow_two]; exact h2 a ha⟩, card_V⟩

theorem R_inf_V : R ⊓ V = ⊥ := by
  have h : ∀ s : J2Syl, s ∈ R → s ∈ V → s = 1 := by decide +kernel
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  exact h s hs.1 hs.2

theorem R_sup_V : R ⊔ V = ⊤ := by
  have h : ∀ s : J2Syl, ∃ r v : J2Syl, r ∈ R ∧ v ∈ V ∧ r * v = s := by
    intro s
    refine ⟨s * ⟨⟨0, s.left.b + F4c.sg s.left.a, 0⟩, 1⟩, ⟨⟨0, s.left.b + F4c.sg s.left.a, 0⟩, 1⟩,
      ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
    · revert s; decide +kernel
    · revert s; decide +kernel
  rw [eq_top_iff]
  intro s _
  obtain ⟨r, v, hr, hv, rfl⟩ := h s
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hv)

theorem Qs_le_R : Qs ≤ R := by
  have h : ∀ s : J2Syl, (s.right = 1 ∧ s * x0 = x0 * s) → s.left.b = F4c.sg s.left.a := by
    decide +kernel
  intro s hs
  exact h s (mem_Qs.1 hs)

theorem Ds_le_R : Ds ≤ R := by
  have h : ∀ s : J2Syl, (s.left.a = 0 ∧ s.left.b = 0) → s.left.b = F4c.sg s.left.a := by
    decide +kernel
  intro s hs
  exact h s (mem_Ds.1 hs)

theorem Qs_Ds_comm : ∀ q ∈ Qs, ∀ d ∈ Ds, q * d = d * q := by
  have h : ∀ q d : J2Syl, (q.right = 1 ∧ q * x0 = x0 * q) → (d.left.a = 0 ∧ d.left.b = 0) →
      q * d = d * q := by decide +kernel
  intro q hq d hd
  exact h q d (mem_Qs.1 hq) (mem_Ds.1 hd)

@[expose] def qa (a : F4c) : J2Syl := ⟨⟨a, F4c.sg a, if a = 0 then 0 else F4c.w⟩, 1⟩

theorem R_factor : ∀ r : J2Syl, r ∈ R →
    ((qa r.left.a).right = 1 ∧ qa r.left.a * x0 = x0 * qa r.left.a) ∧
      ((qa r.left.a)⁻¹ * r).left.a = 0 ∧ ((qa r.left.a)⁻¹ * r).left.b = 0 := by
  decide +kernel

theorem Qs_sup_Ds : Qs ⊔ Ds = R := by
  apply le_antisymm
  · exact sup_le Qs_le_R Ds_le_R
  · intro r hr
    obtain ⟨h1, h2, h3⟩ := R_factor r hr
    have hq : qa r.left.a ∈ Qs := mem_Qs.2 h1
    have hd : (qa r.left.a)⁻¹ * r ∈ Ds := mem_Ds.2 ⟨h2, h3⟩
    have := Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hd)
    simpa using this

theorem Qs_inf_Ds : ∀ s : J2Syl, s ∈ Qs ⊓ Ds ↔ (s = 1 ∨ s = z0) := by
  have h : ∀ s : J2Syl, ((s.right = 1 ∧ s * x0 = x0 * s) ∧ (s.left.a = 0 ∧ s.left.b = 0)) ↔
      (s = 1 ∨ s = z0) := by decide +kernel
  intro s
  rw [Subgroup.mem_inf, mem_Qs, mem_Ds]
  exact h s

theorem card_Qs_inf_Ds : Nat.card ↥(Qs ⊓ Ds) = 2 := by
  have h : (Qs ⊓ Ds : Subgroup J2Syl) =
      subOfPred (fun s : J2Syl => s = 1 ∨ s = z0) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) := by
    ext s
    rw [Qs_inf_Ds s]; exact Iff.rfl
  rw [h, card_subOfPred]
  decide +kernel

theorem isQ8D8_R : IsQ8D8 R :=
  ⟨Qs, Ds, Qs_equiv, Ds_equiv, Qs_Ds_comm, Qs_sup_Ds, card_Qs_inf_Ds⟩

end J2Syl

end CFSG.GH74.Uniqueness.SU.SU5
