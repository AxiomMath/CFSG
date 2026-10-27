module

public import CFSG.FeitThompson.Foundations.FrobeniusNormPrimeDegree
public import CFSG.FeitThompson.Foundations.FiniteFieldUnitsCyclic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset

variable {p q : ℕ} {F : Type*} [Field F]

omit [Field F] in
theorem sub_one_mul_geomSum (hp : 1 ≤ p) (q : ℕ) :
    (p - 1) * ∑ i ∈ range q, p ^ i = p ^ q - 1 := by
  have h1 : 1 ≤ p ^ q := Nat.one_le_pow _ _ hp
  have h2 := mul_geom_sum (p : ℤ) q
  have : ((p - 1 : ℕ) : ℤ) * ((∑ i ∈ range q, p ^ i : ℕ) : ℤ) = ((p ^ q - 1 : ℕ) : ℤ) := by
    push_cast [hp, h1]; exact h2
  exact_mod_cast this

theorem exponent_ne_zero_of_natCard_eq_prime_pow (h : Nat.card F = p ^ q) : q ≠ 0 := by
  rintro rfl
  have h1 : Nat.card F ≠ 1 := fun hh => by
    have : Subsingleton F := (Nat.card_eq_one_iff_unique.mp hh).1
    exact one_ne_zero (α := F) (Subsingleton.elim _ _)
  exact h1 (by simpa using h)

theorem geomSum_pos_of_natCard_eq_prime_pow (hp : p.Prime) (h : Nat.card F = p ^ q) :
    0 < ∑ i ∈ range q, p ^ i :=
  Finset.sum_pos (fun i _ => pow_pos hp.pos i)
    (by simpa [Finset.nonempty_range_iff] using exponent_ne_zero_of_natCard_eq_prime_pow (F := F) h)

theorem natCard_units_eq_sub_one_mul_geomSum (hp : p.Prime) (h : Nat.card F = p ^ q) :
    Nat.card Fˣ = (p - 1) * ∑ i ∈ range q, p ^ i := by
  rw [Nat.card_units, h, sub_one_mul_geomSum hp.one_lt.le]

noncomputable def normOneUnits (F : Type*) [Field F] : Subgroup Fˣ :=
  (Units.map (Algebra.norm (⊥ : Subfield F) (S := F))).ker

theorem normOneUnits_eq_ker :
    normOneUnits F = (Units.map (Algebra.norm (⊥ : Subfield F) (S := F))).ker := (rfl)

theorem mem_normOneUnits {u : Fˣ} :
    u ∈ normOneUnits F ↔ Algebra.norm (⊥ : Subfield F) (u : F) = 1 := by
  simp [normOneUnits, MonoidHom.mem_ker, Units.ext_iff]

theorem normOneUnits_eq_rootsOfUnity (hp : p.Prime) (h : Nat.card F = p ^ q) :
    normOneUnits F = rootsOfUnity (∑ i ∈ range q, p ^ i) F := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  have : CharP F p := charP_of_natCard_eq_prime_pow hp h
  ext u
  rw [mem_normOneUnits, mem_rootsOfUnity', Subtype.ext_iff,
    coe_norm_bot_eq_pow_sum p F h, OneMemClass.coe_one]

theorem mem_normOneUnits_iff_pow_eq_one (hp : p.Prime) (h : Nat.card F = p ^ q) (u : Fˣ) :
    u ∈ normOneUnits F ↔ (u : F) ^ ((p ^ q - 1) / (p - 1)) = 1 := by
  rw [normOneUnits_eq_rootsOfUnity hp h, mem_rootsOfUnity', Nat.geomSum_eq hp.two_le]

theorem natCard_normOneUnits (hp : p.Prime) (h : Nat.card F = p ^ q) :
    Nat.card (normOneUnits F) = ∑ i ∈ range q, p ^ i := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  have hdvd : (∑ i ∈ range q, p ^ i) ∣ Nat.card Fˣ :=
    ⟨p - 1, by rw [natCard_units_eq_sub_one_mul_geomSum hp h, Nat.mul_comm]⟩
  rw [normOneUnits_eq_rootsOfUnity hp h, rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker,
    Nat.gcd_eq_right hdvd]

theorem natCard_normOneUnits_eq_div (hp : p.Prime) (h : Nat.card F = p ^ q) :
    Nat.card (normOneUnits F) = (p ^ q - 1) / (p - 1) := by
  rw [natCard_normOneUnits hp h, Nat.geomSum_eq hp.two_le]

theorem isCyclic_normOneUnits (F : Type*) [Field F] [Finite F] : IsCyclic (normOneUnits F) :=
  have : IsCyclic Fˣ := isCyclic_units_of_finite_field F
  Subgroup.isCyclic _

theorem exists_generator_normOneUnits (hp : p.Prime) (h : Nat.card F = p ^ q) :
    ∃ u : Fˣ, u ∈ normOneUnits F ∧ orderOf u = ∑ i ∈ range q, p ^ i ∧
      ∀ v : Fˣ, v ∈ normOneUnits F → v ∈ Subgroup.zpowers u := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  obtain ⟨g, hg⟩ := (isCyclic_normOneUnits F).exists_generator
  refine ⟨(g : Fˣ), g.2, ?_, fun v hv => ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg,
      natCard_normOneUnits hp h]
  · obtain ⟨n, hn⟩ := hg ⟨v, hv⟩
    exact ⟨n, by simpa using congrArg (Subtype.val : normOneUnits F → Fˣ) hn⟩

theorem surjective_unitsMap_norm_bot (F : Type*) [Field F] [Finite F] :
    Function.Surjective (Units.map (Algebra.norm (⊥ : Subfield F) (S := F))) :=
  FiniteField.unitsMap_norm_surjective _ _

theorem exists_pow_geomSum_eq (hp : p.Prime) (h : Nat.card F = p ^ q) {y : F}
    (hy : y ∈ (⊥ : Subfield F)) (hy0 : y ≠ 0) :
    ∃ z : F, z ≠ 0 ∧ z ^ (∑ i ∈ range q, p ^ i) = y := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  have : CharP F p := charP_of_natCard_eq_prime_pow hp h
  obtain ⟨z, hz⟩ := FiniteField.norm_surjective (⊥ : Subfield F) F ⟨y, hy⟩
  have hz' : z ^ (∑ i ∈ range q, p ^ i) = y := by
    rw [← coe_norm_bot_eq_pow_sum p F h, hz]
  refine ⟨z, ?_, hz'⟩
  rintro rfl
  exact hy0 (by rw [← hz', zero_pow (geomSum_pos_of_natCard_eq_prime_pow hp h (F := F)).ne'])

theorem normOneUnits_isCyclic_natCard_and_norm_surjective (hp : p.Prime)
    (h : Nat.card F = p ^ q) :
    IsCyclic (normOneUnits F) ∧ Nat.card (normOneUnits F) = (p ^ q - 1) / (p - 1) ∧
      Function.Surjective (Units.map (Algebra.norm (⊥ : Subfield F) (S := F))) :=
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  ⟨isCyclic_normOneUnits F, natCard_normOneUnits_eq_div hp h, surjective_unitsMap_norm_bot F⟩

end

end CFSG.FeitThompson
