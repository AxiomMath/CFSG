module

public import CFSG.LieType.Universal.Unitary.Roots
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

variable (F : Type) [Field F] [Finite F] (p f : ℕ) [Fact p.Prime] [CharP F p]

@[expose] noncomputable def fixedSubfield : Subfield F :=
  (unitaryInvolution F p f).toRingHom.eqLocusField (RingHom.id F)

variable {F p f}

theorem mem_fixedSubfield {c : F} :
    c ∈ fixedSubfield F p f ↔ unitaryInvolution F p f c = c :=
  Iff.rfl

@[expose] noncomputable def unitaryTrace : F →+ F where
  toFun c := c + unitaryInvolution F p f c
  map_zero' := by simp
  map_add' a b := by rw [map_add]; ring

theorem ker_unitaryTrace : (unitaryTrace (F := F) (p := p) (f := f)).ker =
    traceZero (unitaryInvolution F p f) := by
  ext c
  rfl

variable (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem range_unitaryTrace : (unitaryTrace (F := F) (p := p) (f := f)).range =
    (fixedSubfield F p f).toAddSubgroup := by
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  ext a
  constructor
  · rintro ⟨c, rfl⟩
    change unitaryInvolution F p f (c + unitaryInvolution F p f c) =
      c + unitaryInvolution F p f c
    rw [map_add, hσ.invol, add_comm]
  · intro ha
    obtain ⟨c, hc⟩ := hσ.trace_surj a ha
    exact ⟨c, hc⟩

theorem card_traceZero_eq_card_fixedSubfield :
    Nat.card (traceZero (unitaryInvolution F p f)) = Nat.card (fixedSubfield F p f) := by
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hσζ : unitaryInvolution F p f (ζ : F) = -ζ := by
    have := ζ.2
    rw [mem_traceZero] at this
    linear_combination this
  refine Nat.card_congr
    { toFun := fun c => ⟨(c : F) / ζ, ?_⟩
      invFun := fun c => ⟨(c : F) * ζ, ?_⟩
      left_inv := fun c => Subtype.ext (div_mul_cancel₀ _ hζ)
      right_inv := fun c => Subtype.ext (mul_div_cancel_right₀ _ hζ) }
  · change unitaryInvolution F p f ((c : F) / ζ) = (c : F) / ζ
    have hc := c.2
    rw [mem_traceZero] at hc
    rw [map_div₀, hσζ, show unitaryInvolution F p f (c : F) = -c by linear_combination hc,
      neg_div_neg_eq]
  · rw [mem_traceZero, map_mul, hσζ, show unitaryInvolution F p f (c : F) = c from c.2]
    ring

theorem card_fixedSubfield : Nat.card (fixedSubfield F p f) = p ^ f := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (unitaryTrace (F := F) (p := p) (f := f)).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange _).toEquiv,
    range_unitaryTrace hF, ker_unitaryTrace, card_traceZero_eq_card_fixedSubfield hF, hF] at h1
  have h2 : Nat.card (fixedSubfield F p f).toAddSubgroup = Nat.card (fixedSubfield F p f) := rfl
  rw [h2, ← pow_two] at h1
  exact (Nat.pow_left_injective two_ne_zero h1).symm

theorem card_traceZero : Nat.card (traceZero (unitaryInvolution F p f)) = p ^ f := by
  rw [card_traceZero_eq_card_fixedSubfield hF, card_fixedSubfield hF]

theorem exists_norm_one_orderOf_eq :
    ∃ l : Fˣ, unitaryInvolution F p f (l : F) * l = 1 ∧ orderOf l = p ^ f + 1 := by
  have hq := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hF
  have hcard : Nat.card Fˣ = (p ^ f) ^ 2 - 1 :=
    CFSG.ClassicalGroups.Unitary.card_units_of_card hF
  have hfac : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    rw [CFSG.ClassicalGroups.Unitary.sq_sub_one_eq _ hq.le, mul_comm]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgo : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  refine ⟨g ^ (p ^ f - 1), ?_, ?_⟩
  · have key : (g ^ (p ^ f - 1)) ^ p ^ f * g ^ (p ^ f - 1) = 1 := by
      rw [← pow_mul, ← pow_add]
      have : (p ^ f - 1) * p ^ f + (p ^ f - 1) = (p ^ f) ^ 2 - 1 := by
        rw [hfac]
        ring
      rw [this, ← hgo, pow_orderOf_eq_one]
    have := congrArg (fun u : Fˣ => (u : F)) key
    rw [unitaryInvolution_apply]
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] using this
  · rw [orderOf_pow' g (by omega), hgo, hfac, Nat.gcd_mul_right_left]
    exact Nat.mul_div_cancel_left _ (by omega)

end CFSG.LieType.Steinberg
