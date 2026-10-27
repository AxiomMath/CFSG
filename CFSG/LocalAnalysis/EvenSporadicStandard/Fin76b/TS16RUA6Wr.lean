module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrHom

public section

namespace CFSG.EvenSporadicStandard.Fin76b.A6X

abbrev A6 : Type := alternatingGroup (Fin 6)

abbrev Yaut : Type := MulAut (A6 × A6)

@[expose] def Yone : Subgroup Yaut where
  carrier := {τ | ∃ f₁ f₂ : MulAut A6, ∀ a b : A6, τ (a, b) = (f₁ a, f₂ b)}
  mul_mem' := by
    rintro τ σ ⟨f₁, f₂, hf⟩ ⟨g₁, g₂, hg⟩
    show ∃ f₁ f₂ : MulAut A6, ∀ a b : A6, (τ * σ) (a, b) = (f₁ a, f₂ b)
    refine ⟨f₁ * g₁, f₂ * g₂, fun a b => ?_⟩
    simp only [MulAut.mul_apply, hg, hf]
  one_mem' := by
    show ∃ f₁ f₂ : MulAut A6, ∀ a b : A6, (1 : Yaut) (a, b) = (f₁ a, f₂ b)
    exact ⟨1, 1, fun a b => rfl⟩
  inv_mem' := by
    rintro τ ⟨f₁, f₂, hf⟩
    show ∃ f₁ f₂ : MulAut A6, ∀ a b : A6, τ⁻¹ (a, b) = (f₁ a, f₂ b)
    refine ⟨f₁⁻¹, f₂⁻¹, fun a b => ?_⟩
    have h : τ (f₁⁻¹ a, f₂⁻¹ b) = (a, b) := by
      simp only [hf, MulAut.apply_inv_self]
    rw [← h, MulAut.inv_apply_self]

theorem mem_Yone {τ : Yaut} :
    τ ∈ Yone ↔ ∃ f₁ f₂ : MulAut A6, ∀ a b : A6, τ (a, b) = (f₁ a, f₂ b) :=
  Iff.rfl

theorem exists_swap_of_not_mem_Yone {τ : Yaut} (h : τ ∉ Yone) :
    ∃ g₁ g₂ : MulAut A6, ∀ a b : A6, τ (a, b) = (g₁ b, g₂ a) := by
  obtain ⟨d, hd⟩ := TS8Wr.exists_dec τ
  obtain ⟨ε, f₁, f₂⟩ := d
  cases ε
  · exact absurd (mem_Yone.2 ⟨f₁, f₂, (TS8Wr.dec_false_iff τ f₁ f₂).1 hd⟩) h
  · exact ⟨f₁, f₂, (TS8Wr.dec_true_iff τ f₁ f₂).1 hd⟩

theorem sq_mem_Yone (τ : Yaut) : τ * τ ∈ Yone := by
  obtain ⟨d, hd⟩ := TS8Wr.exists_dec τ
  obtain ⟨ε, f₁, f₂⟩ := d
  have h := TS8Wr.dec_mul hd hd
  cases ε
  · have h' : TS8Wr.Dec (τ * τ) (false, f₁ * f₁, f₂ * f₂) := h
    exact mem_Yone.2 ⟨f₁ * f₁, f₂ * f₂, (TS8Wr.dec_false_iff _ _ _).1 h'⟩
  · have h' : TS8Wr.Dec (τ * τ) (false, f₁ * f₂, f₂ * f₁) := h
    exact mem_Yone.2 ⟨f₁ * f₂, f₂ * f₁, (TS8Wr.dec_false_iff _ _ _).1 h'⟩

theorem decOf_fst_eq_false_iff (τ : Yaut) : (TS8Wr.decOf τ).1 = false ↔ τ ∈ Yone := by
  have hd : TS8Wr.Dec τ (TS8Wr.decOf τ) := TS8Wr.decOf_spec τ
  constructor
  · intro h
    rcases hdec : TS8Wr.decOf τ with ⟨ε, f₁, f₂⟩
    rw [hdec] at hd h
    cases ε
    · exact mem_Yone.2 ⟨f₁, f₂, (TS8Wr.dec_false_iff τ f₁ f₂).1 hd⟩
    · simp at h
  · intro h
    obtain ⟨f₁, f₂, hf⟩ := mem_Yone.1 h
    have h' : TS8Wr.Dec τ (false, f₁, f₂) := (TS8Wr.dec_false_iff τ f₁ f₂).2 hf
    rw [TS8Wr.dec_unique hd h']

theorem decOf_one : TS8Wr.decOf (1 : Yaut) = (false, 1, 1) := by
  refine TS8Wr.dec_unique (TS8Wr.decOf_spec 1) ?_
  rw [TS8Wr.dec_false_iff]
  intro a b
  simp

theorem pres_decOf {τ : Yaut} (h : τ ∈ Yone) :
    TS8Wr.Pres τ (TS8Wr.decOf τ).2.1 (TS8Wr.decOf τ).2.2 := by
  obtain ⟨f₁, f₂, hf⟩ := mem_Yone.1 h
  have h' : TS8Wr.Dec τ (false, f₁, f₂) := (TS8Wr.dec_false_iff τ f₁ f₂).2 hf
  rw [TS8Wr.dec_unique (TS8Wr.decOf_spec τ) h']
  exact hf

theorem decOf_mul_of_mem {τ σ : Yaut} (hτ : τ ∈ Yone) (hσ : σ ∈ Yone) :
    TS8Wr.decOf (τ * σ) = (false, (TS8Wr.decOf τ).2.1 * (TS8Wr.decOf σ).2.1,
      (TS8Wr.decOf τ).2.2 * (TS8Wr.decOf σ).2.2) := by
  have h1 : (TS8Wr.decOf τ).1 = false := (decOf_fst_eq_false_iff τ).2 hτ
  have h2 : (TS8Wr.decOf σ).1 = false := (decOf_fst_eq_false_iff σ).2 hσ
  refine TS8Wr.dec_unique (TS8Wr.decOf_spec (τ * σ)) ?_
  have h := TS8Wr.dec_mul (TS8Wr.decOf_spec τ) (TS8Wr.decOf_spec σ)
  rw [h1, h2] at h
  exact h

theorem zmod_two_xor (a b : Bool) :
    (if xor a b then (1 : ZMod 2) else 0) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

@[expose] noncomputable def sgnY : Yaut →* Multiplicative (ZMod 2) where
  toFun τ := Multiplicative.ofAdd (if (TS8Wr.decOf τ).1 then (1 : ZMod 2) else 0)
  map_one' := by
    simp [decOf_one]
  map_mul' τ σ := by
    have h : (TS8Wr.decOf (τ * σ)).1 = xor (TS8Wr.decOf τ).1 (TS8Wr.decOf σ).1 :=
      congrArg Prod.fst (TS8Wr.dec_unique (TS8Wr.decOf_spec (τ * σ))
        (TS8Wr.dec_mul (TS8Wr.decOf_spec τ) (TS8Wr.decOf_spec σ)))
    show Multiplicative.ofAdd (if (TS8Wr.decOf (τ * σ)).1 then (1 : ZMod 2) else 0) =
      Multiplicative.ofAdd (if (TS8Wr.decOf τ).1 then (1 : ZMod 2) else 0) *
        Multiplicative.ofAdd (if (TS8Wr.decOf σ).1 then (1 : ZMod 2) else 0)
    rw [h, zmod_two_xor, ofAdd_add]

theorem sgnY_eq_one_iff (τ : Yaut) : sgnY τ = 1 ↔ τ ∈ Yone := by
  rw [← decOf_fst_eq_false_iff]
  show Multiplicative.ofAdd (if (TS8Wr.decOf τ).1 then (1 : ZMod 2) else 0) = 1 ↔
    (TS8Wr.decOf τ).1 = false
  cases hb : (TS8Wr.decOf τ).1
  · simp
  · simp

theorem le_Yone_of_simple {H : Subgroup Yaut} (e : ↥H ≃* A6) : H ≤ Yone := by
  haveI : IsSimpleGroup A6 := CFSG.EvenSporadicStandard.M24Std.DRes.alt6_simple
  haveI : IsSimpleGroup ↥H := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (sgnY.comp H.subtype).ker with h | h
  · exfalso
    have hinj : Function.Injective (sgnY.comp H.subtype) :=
      (MonoidHom.ker_eq_bot_iff _).1 h
    have h1 := Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card ↥H = 360 := by
      rw [Nat.card_congr e.toEquiv, CFSG.EvenSporadicStandard.M24Std.DRes.card_alt6]
    have h3 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [← Nat.card_congr (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2)),
        Nat.card_zmod]
    omega
  · intro τ hτ
    have hmem : (⟨τ, hτ⟩ : ↥H) ∈ (sgnY.comp H.subtype).ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    exact (sgnY_eq_one_iff τ).1 hmem

@[expose] noncomputable def coord₁ : ↥Yone →* MulAut A6 where
  toFun τ := (TS8Wr.decOf (τ : Yaut)).2.1
  map_one' := by
    show (TS8Wr.decOf ((1 : ↥Yone) : Yaut)).2.1 = 1
    rw [Subgroup.coe_one, decOf_one]
  map_mul' τ σ := by
    show (TS8Wr.decOf ((τ * σ : ↥Yone) : Yaut)).2.1 =
      (TS8Wr.decOf (τ : Yaut)).2.1 * (TS8Wr.decOf (σ : Yaut)).2.1
    rw [Subgroup.coe_mul, decOf_mul_of_mem τ.2 σ.2]

@[expose] noncomputable def coord₂ : ↥Yone →* MulAut A6 where
  toFun τ := (TS8Wr.decOf (τ : Yaut)).2.2
  map_one' := by
    show (TS8Wr.decOf ((1 : ↥Yone) : Yaut)).2.2 = 1
    rw [Subgroup.coe_one, decOf_one]
  map_mul' τ σ := by
    show (TS8Wr.decOf ((τ * σ : ↥Yone) : Yaut)).2.2 =
      (TS8Wr.decOf (τ : Yaut)).2.2 * (TS8Wr.decOf (σ : Yaut)).2.2
    rw [Subgroup.coe_mul, decOf_mul_of_mem τ.2 σ.2]

theorem coord_apply (τ : ↥Yone) (a b : A6) :
    (τ : Yaut) (a, b) = (coord₁ τ a, coord₂ τ b) :=
  pres_decOf τ.2 a b

end CFSG.EvenSporadicStandard.Fin76b.A6X
