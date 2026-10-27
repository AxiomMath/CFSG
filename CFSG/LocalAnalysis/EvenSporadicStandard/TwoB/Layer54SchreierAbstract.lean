module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54Abstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB.Layer54

open CFSG.ComponentClassification CFSG.ComponentClassification.LayerMultiplication
open CFSG.ComponentClassification.SemisimpleComponentStructure
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

def actHom {A : Type*} [Group A] (ρ : A →* H) (Q : Subgroup H)
    (hn : ∀ (a : A), ∀ m ∈ Q, ρ a * m * (ρ a)⁻¹ ∈ Q) : A →* MulAut ↥Q where
  toFun a :=
    { toFun := fun m => ⟨ρ a * m * (ρ a)⁻¹, hn a m m.2⟩
      invFun := fun m => ⟨ρ a⁻¹ * m * (ρ a⁻¹)⁻¹, hn a⁻¹ m m.2⟩
      left_inv := fun m => by
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := fun m => by
        apply Subtype.ext
        simp [mul_assoc]
      map_mul' := fun x y => by
        apply Subtype.ext
        simp [mul_assoc] }
  map_one' := by
    apply MulEquiv.ext
    intro m
    apply Subtype.ext
    simp
  map_mul' := fun a b => by
    apply MulEquiv.ext
    intro m
    apply Subtype.ext
    simp [mul_assoc]

theorem exists_coordinates {A : Type*} [Group A] [Group.IsPerfect A] (ρ : A →* H)
    (hn : ∀ (i : ComponentIndex H) (a : A), ∀ m ∈ i.val, ρ a * m * (ρ a)⁻¹ ∈ i.val)
    (hOut : ∀ i : ComponentIndex H, Group.IsSolvable (Outer ↥i.val)) (a : A) :
    ∃ f : (i : ComponentIndex H) → ↥i.val,
      ∀ (i : ComponentIndex H), ∀ m ∈ i.val, ρ a * m * (ρ a)⁻¹ = f i * m * (f i : H)⁻¹ := by
  have key : ∀ i : ComponentIndex H, ∃ q : ↥i.val,
      ∀ m : ↥i.val, ρ a * (m : H) * (ρ a)⁻¹ = q * m * (q : H)⁻¹ := by
    intro i
    have := hOut i
    obtain ⟨q, hq⟩ := perfect_action_inner (actHom ρ i.val (hn i)) a
    refine ⟨q, fun m => ?_⟩
    have := congrArg (fun φ => ((φ m : ↥i.val) : H)) hq
    simpa [actHom] using this
  choose f hf using key
  exact ⟨f, fun i m hm => hf i ⟨m, hm⟩⟩

theorem ambient_conj_coordinate (f : (i : ComponentIndex H) → ↥i.val) (i : ComponentIndex H)
    (m : ↥i.val) :
    ambient H f * (m : H) * (ambient H f)⁻¹ = (f i : H) * m * (f i : H)⁻¹ := by
  classical
  have hmul : ∀ (j : ComponentIndex H) (x : ↥j.val), ambient H (Pi.mulSingle j x) = (x : H) :=
    fun j x => Subgroup.noncommPiCoprod_mulSingle
      (H := fun j : ComponentIndex H => j.val) (hcomm := coordinate_commute H) j x
  have hconj : f * Pi.mulSingle i m * f⁻¹ = Pi.mulSingle i (f i * m * (f i)⁻¹) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  have := congrArg (ambient H) hconj
  rw [map_mul, map_mul, map_inv, hmul, hmul] at this
  simpa using this

theorem commute_layer_of_coordinates (g : H) (f : (i : ComponentIndex H) → ↥i.val)
    (hf : ∀ (i : ComponentIndex H), ∀ m ∈ i.val, g * m * g⁻¹ = f i * m * (f i : H)⁻¹) :
    ∀ x ∈ Layer.subgroup H, (ambient H f)⁻¹ * g * x = x * ((ambient H f)⁻¹ * g) := by
  have hle : Layer.subgroup H ≤ Subgroup.centralizer {(ambient H f)⁻¹ * g} := by
    apply sSup_le
    intro Q hQ m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hf ⟨Q, hQ⟩ m hm
    rw [← ambient_conj_coordinate f ⟨Q, hQ⟩ ⟨m, hm⟩] at h1
    calc m * ((ambient H f)⁻¹ * g)
        = (ambient H f)⁻¹ * (ambient H f * m * (ambient H f)⁻¹) * g := by group
      _ = (ambient H f)⁻¹ * (g * m * g⁻¹) * g := by rw [h1]
      _ = (ambient H f)⁻¹ * g * m := by group
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

theorem exists_centralizing_layer_element {A : Type*} [Group A] [Group.IsPerfect A] (ρ : A →* H)
    (hn : ∀ (i : ComponentIndex H) (a : A), ∀ m ∈ i.val, ρ a * m * (ρ a)⁻¹ ∈ i.val)
    (hOut : ∀ i : ComponentIndex H, Group.IsSolvable (Outer ↥i.val)) (a : A) :
    ∃ e ∈ Layer.subgroup H, ∀ x ∈ Layer.subgroup H, e⁻¹ * ρ a * x = x * (e⁻¹ * ρ a) := by
  obtain ⟨f, hf⟩ := exists_coordinates ρ hn hOut a
  refine ⟨ambient H f, ?_, commute_layer_of_coordinates (ρ a) f hf⟩
  rw [← range_eq_layer H]
  exact ⟨f, rfl⟩

theorem mem_pCore_of_centralizes_layer (hodd : CFSG.pPrimeCore 2 H = ⊥)
    (hcen : ∀ c ∈ CFSG.pCore 2 H, ∀ y : H, c * y = y * c)
    {c : H} (hc : ∀ x ∈ Layer.subgroup H, c * x = x * c) : c ∈ CFSG.pCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CFSG.generalizedFitting H = CFSG.pCore 2 H ⊔ Layer.subgroup H := by
    rw [CFSG.generalizedFitting, CFSG.Fitting_eq_pcore H 2 hodd,
      CFSG.layer_eq_componentClassification]
  have hcent : CFSG.pCore 2 H ⊔ Layer.subgroup H ≤ Subgroup.centralizer {c} := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hcen x hx c)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hc x hx).symm
  have hcF : c ∈ CFSG.generalizedFitting H := by
    refine CFSG.centralizer_generalizedFitting_le H ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [hF] at hx
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hcent hx))
  rw [hF] at hcF
  have hle : Layer.subgroup H ≤ Subgroup.centralizer (CFSG.pCore 2 H : Set H) := fun x _ => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hcen h hh x
  obtain ⟨f, hf, e, he, rfl⟩ :=
    CFSG.EvenSporadicStandard.exists_mul_of_mem_sup_of_le_centralizer hle hcF
  have hecen : (⟨e, he⟩ : ↥(Layer.subgroup H)) ∈ Subgroup.center ↥(Layer.subgroup H) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 : f * (y : H) = (y : H) * f := hcen f hf y
    have h2 : f * e * (y : H) = (y : H) * (f * e) := hc y y.2
    have h3 : f * (e * (y : H)) = f * ((y : H) * e) := by
      calc f * (e * (y : H)) = f * e * (y : H) := by rw [mul_assoc]
        _ = (y : H) * (f * e) := h2
        _ = ((y : H) * f) * e := by rw [mul_assoc]
        _ = (f * (y : H)) * e := by rw [h1]
        _ = f * ((y : H) * e) := by rw [mul_assoc]
    exact (mul_left_cancel h3).symm
  have hep : e ∈ CFSG.pCore 2 H := center_layer_le_pCore hodd ⟨⟨e, he⟩, hecen, rfl⟩
  exact mul_mem hf hep

theorem commutator_mul_central {a b c d : H} (hc : ∀ y : H, c * y = y * c)
    (hd : ∀ y : H, d * y = y * d) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hcb : c * (b * d) = (b * d) * c := hc (b * d)
  have hda : d * a⁻¹ = a⁻¹ * d := hd a⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * (b * d)) * c⁻¹ * a⁻¹ * (b * d)⁻¹ := by group
    _ = a * ((b * d) * c) * c⁻¹ * a⁻¹ * (b * d)⁻¹ := by rw [hcb]
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [hda]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem le_layer_of_perfect_normalizes {K : Subgroup H} (hperf : ⁅K, K⁆ = K)
    (hodd : CFSG.pPrimeCore 2 H = ⊥) (hcen : ∀ c ∈ CFSG.pCore 2 H, ∀ y : H, c * y = y * c)
    (hOut : ∀ i : ComponentIndex H, Group.IsSolvable (Outer ↥i.val))
    (hn : ∀ (i : ComponentIndex H), ∀ k ∈ K, ∀ m ∈ i.val, k * m * k⁻¹ ∈ i.val) :
    K ≤ Layer.subgroup H := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hperf
  have hdec : ∀ k ∈ K, ∃ e ∈ Layer.subgroup H, ∃ c ∈ CFSG.pCore 2 H, k = e * c := by
    intro k hk
    obtain ⟨e, he, hec⟩ := exists_centralizing_layer_element K.subtype
      (fun i a m hm => hn i a a.2 m hm) hOut ⟨k, hk⟩
    exact ⟨e, he, e⁻¹ * k, mem_pCore_of_centralizes_layer hodd hcen (fun x hx => hec x hx),
      by group⟩
  have hcomm : ⁅K, K⁆ ≤ Layer.subgroup H := by
    rw [Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨e₁, he₁, c₁, hc₁, rfl⟩ := hdec k₁ hk₁
    obtain ⟨e₂, he₂, c₂, hc₂, rfl⟩ := hdec k₂ hk₂
    rw [commutator_mul_central (hcen c₁ hc₁) (hcen c₂ hc₂), commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem he₁ he₂) (inv_mem he₁)) (inv_mem he₂)
  rw [← hperf]
  exact hcomm

end CFSG.EvenSporadicStandard.TwoB.Layer54
