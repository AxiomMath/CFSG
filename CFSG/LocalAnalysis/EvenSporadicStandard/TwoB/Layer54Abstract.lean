module

public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB.Layer54

open CFSG.ComponentClassification CFSG.ComponentClassification.LayerMultiplication
open CFSG.ComponentClassification.SemisimpleComponentStructure
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

theorem sq_mul_comm_of_commutator {q h c : H} (hc : c = q * h * q⁻¹ * h⁻¹)
    (hcen : ∀ y : H, c * y = y * c) (hcc : c * c = 1) : q ^ 2 * h = h * q ^ 2 := by
  have e1 : q * h = c * h * q := by rw [hc]; group
  calc q ^ 2 * h = q * (q * h) := by rw [pow_two, mul_assoc]
    _ = q * (c * h * q) := by rw [e1]
    _ = (q * c) * h * q := by group
    _ = (c * q) * h * q := by rw [← hcen q]
    _ = c * (q * h) * q := by group
    _ = c * (c * h * q) * q := by rw [e1]
    _ = (c * c) * h * (q * q) := by group
    _ = h * q ^ 2 := by rw [hcc, one_mul, pow_two]

theorem exists_two_pow_eq_one_of_layer (S : Subgroup H)
    (hS : ∀ c ∈ S, (∀ y : H, c * y = y * c) ∧ c * c = 1)
    (hZ : ∀ (i : ComponentIndex H) (c : ↥i.val), c ∈ Subgroup.center ↥i.val → (c : H) ∈ S)
    {t : H} (ht : t ∈ Layer.subgroup H)
    (hd : ∀ (i : ComponentIndex H) (a : H), a ∈ i.val → a * t = t * a →
      ∃ k : ℕ, a ^ 2 ^ k = 1)
    {x : H} (hx : x ∈ Layer.subgroup H) (hxt : x * t = t * x) :
    ∃ m : ℕ, x ^ 2 ^ m = 1 := by
  classical
  obtain ⟨g, hg⟩ := surjective H ⟨t, ht⟩
  obtain ⟨f, hf⟩ := surjective H ⟨x, hx⟩
  have hgt : ambient H g = t := congrArg Subtype.val hg
  have hfx : ambient H f = x := congrArg Subtype.val hf
  have hcomm : ambient H ⁅f, g⁆ = 1 := by
    rw [map_commutatorElement, hgt, hfx, commutatorElement_def, hxt]
    group
  have hcen := kernel_coordinate_central ⁅f, g⁆ hcomm
  have key : ∀ i : ComponentIndex H, ∃ k : ℕ, ((f i : ↥i.val) : H) ^ 2 ^ k = 1 := by
    intro i
    have hc : (((⁅f, g⁆ i : ↥i.val)) : H) ∈ S := hZ i _ (hcen i)
    have hcdef : (((⁅f, g⁆ i : ↥i.val)) : H) =
        ((f i : ↥i.val) : H) * ((g i : ↥i.val) : H) * ((f i : ↥i.val) : H)⁻¹ *
          ((g i : ↥i.val) : H)⁻¹ := by
      simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply]
      rfl
    have hsq := sq_mul_comm_of_commutator hcdef (hS _ hc).1 (hS _ hc).2
    have hmem : ((f i : ↥i.val) : H) ^ 2 ∈ i.val := pow_mem (f i).2 2
    have hcommt : ((f i : ↥i.val) : H) ^ 2 * t = t * ((f i : ↥i.val) : H) ^ 2 := by
      set u : (j : ComponentIndex H) → ↥j.val := Pi.mulSingle i ((f i) ^ 2) with hu
      have hu1 : ambient H u = ((f i : ↥i.val) : H) ^ 2 := by
        rw [hu]
        exact Subgroup.noncommPiCoprod_mulSingle
          (H := fun j : ComponentIndex H => j.val) (hcomm := coordinate_commute H) i _
      have hug : u * g = g * u := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [hu, Pi.mul_apply, Pi.mulSingle_eq_same]
          exact Subtype.ext (by simpa using hsq)
        · simp only [hu, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul, mul_one]
      have := congrArg (ambient H) hug
      rwa [map_mul, map_mul, hu1, hgt] at this
    obtain ⟨k, hk⟩ := hd i _ hmem hcommt
    refine ⟨k + 1, ?_⟩
    rw [pow_succ', pow_mul]
    exact hk
  choose k hk using key
  refine ⟨Finset.univ.sup k, ?_⟩
  have hf1 : f ^ 2 ^ Finset.univ.sup k = 1 := by
    funext i
    apply Subtype.ext
    have hle : k i ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ i)
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
    simp only [Pi.pow_apply, Pi.one_apply]
    show (((f i) ^ 2 ^ Finset.univ.sup k : ↥i.val) : H) = 1
    rw [Subgroup.coe_pow, hr, pow_add, pow_mul, hk i, one_pow]
  have hxpow : (⟨x, hx⟩ : ↥(Layer.subgroup H)) ^ 2 ^ Finset.univ.sup k = 1 := by
    rw [← hf, ← map_pow, hf1, map_one]
  simpa using congrArg Subtype.val hxpow

theorem normal_center_layer (H : Type*) [Group H] :
    ((Subgroup.center (Layer.subgroup H)).map (Layer.subgroup H).subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨l, hl, rfl⟩ := hn
  have hmem : g * (l : H) * g⁻¹ ∈ Layer.subgroup H := (Layer.normal H).conj_mem l l.2 g
  refine ⟨⟨g * (l : H) * g⁻¹, hmem⟩, ?_, rfl⟩
  show _ ∈ Subgroup.center _
  rw [Subgroup.mem_center_iff]
  intro m
  have hm : g⁻¹ * (m : H) * g ∈ Layer.subgroup H := by
    have := (Layer.normal H).conj_mem m m.2 g⁻¹
    rwa [inv_inv] at this
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hl ⟨g⁻¹ * (m : H) * g, hm⟩)
  apply Subtype.ext
  show (m : H) * (g * (l : H) * g⁻¹) = g * (l : H) * g⁻¹ * (m : H)
  have h2 : (g⁻¹ * (m : H) * g) * (l : H) = (l : H) * (g⁻¹ * (m : H) * g) := h1
  calc (m : H) * (g * (l : H) * g⁻¹) = g * ((g⁻¹ * (m : H) * g) * (l : H)) * g⁻¹ := by group
    _ = g * ((l : H) * (g⁻¹ * (m : H) * g)) * g⁻¹ := by rw [h2]
    _ = g * (l : H) * g⁻¹ * (m : H) := by group

theorem center_layer_le_pCore (hodd : CFSG.pPrimeCore 2 H = ⊥) :
    (Subgroup.center (Layer.subgroup H)).map (Layer.subgroup H).subtype ≤ CFSG.pCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← CFSG.Fitting_eq_pcore H 2 hodd]
  refine le_sSup ⟨normal_center_layer H, ?_⟩
  have : IsMulCommutative ↥(Subgroup.center (Layer.subgroup H)) := inferInstance
  have : Group.IsNilpotent ↥(Subgroup.center (Layer.subgroup H)) := CommGroup.isNilpotent
  exact Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _
    (Layer.subgroup H).subtype_injective)

theorem center_component_le (i : ComponentIndex H) (c : ↥i.val)
    (hc : c ∈ Subgroup.center ↥i.val) :
    (c : H) ∈ (Subgroup.center (Layer.subgroup H)).map (Layer.subgroup H).subtype := by
  have h1 : (c : H) ∈ (Subgroup.center ↥i.val).map i.val.subtype := ⟨c, hc, rfl⟩
  rw [← component_center_intersection i.val i.property] at h1
  exact h1.2

end CFSG.EvenSporadicStandard.TwoB.Layer54
