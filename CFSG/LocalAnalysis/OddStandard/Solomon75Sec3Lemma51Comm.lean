module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Tools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Comm

theorem comm_comm_eq_one_of_commute_forall {P : Type*} [Group P] (H : Subgroup P) {a b t : P}
    (ha : a ∈ H) (hb : b ∈ H) (ht : t ∈ H)
    (hat : ∀ g ∈ H, g * ⁅a, t⁆ = ⁅a, t⁆ * g)
    (hbt : ∀ g ∈ H, g * ⁅b, t⁆ = ⁅b, t⁆ * g) : ⁅⁅a, b⁆, t⁆ = 1 := by
  have h := comm_comm_eq_one_of_central_comm (X := H) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (t := ⟨t, ht⟩) (Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hat g g.2))
    (Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hbt g g.2))
  have h' := congrArg H.subtype h
  simpa only [map_commutatorElement, map_one, Subgroup.subtype_apply] using h'

theorem exists_mul_eq_of_mem_sup_of_mul_comm {P : Type*} [Group P] {A B : Subgroup P}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : P} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hle : B ≤ Subgroup.normalizer (A : Set P) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have h1 : b * n * b⁻¹ = n := by
        rw [← h n hn b hb]
        group
      rw [h1]
      exact hn
    · intro hn
      have h2 := h _ hn b hb
      have h3 : n = b * n * b⁻¹ := by
        have h4 : b * n = b * (b * n * b⁻¹) := by
          calc b * n = b * n * b⁻¹ * b := by group
            _ = b * (b * n * b⁻¹) := h2
        exact mul_left_cancel h4
      rw [h3]
      exact hn
  have hmem : x ∈ ((A ⊔ B : Subgroup P) : Set P) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hle] at hmem
  exact hmem

theorem commute_factors_of_commute_prod {P : Type*} [Group P] {A B : Subgroup P}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {c₁ c₂ : P} (hc₁ : c₁ ∈ A) (hc₂ : c₂ ∈ B)
    (h : ∀ g ∈ A ⊔ B, g * (c₁ * c₂) = (c₁ * c₂) * g) :
    (∀ g ∈ A, g * c₁ = c₁ * g) ∧ (∀ g ∈ B, g * c₂ = c₂ * g) := by
  constructor
  · intro g hg
    have h1 := h g (Subgroup.mem_sup_left hg)
    have h2 : g * c₂ = c₂ * g := hAB g hg c₂ hc₂
    apply mul_right_cancel (b := c₂)
    calc g * c₁ * c₂ = g * (c₁ * c₂) := mul_assoc _ _ _
      _ = c₁ * c₂ * g := h1
      _ = c₁ * (c₂ * g) := mul_assoc _ _ _
      _ = c₁ * (g * c₂) := by rw [h2]
      _ = c₁ * g * c₂ := (mul_assoc _ _ _).symm
  · intro g hg
    have h1 := h g (Subgroup.mem_sup_right hg)
    have h2 : c₁ * g = g * c₁ := hAB c₁ hc₁ g hg
    apply mul_left_cancel (a := c₁)
    calc c₁ * (g * c₂) = c₁ * g * c₂ := (mul_assoc _ _ _).symm
      _ = g * c₁ * c₂ := by rw [h2]
      _ = g * (c₁ * c₂) := mul_assoc _ _ _
      _ = c₁ * c₂ * g := h1
      _ = c₁ * (c₂ * g) := mul_assoc _ _ _

theorem mul_comm_sup_of_forall_mul_comm {P : Type*} [Group P] (A : Subgroup P)
    (S : Finset (Subgroup P)) (h : ∀ B ∈ S, ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ a ∈ A, ∀ b ∈ S.sup id, a * b = b * a := by
  intro a ha
  have hle : S.sup id ≤ centralizer ({a} : Set P) := by
    refine Finset.sup_le fun B hB => ?_
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h B hB a ha b hb).symm
  intro b hb
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hb)).symm

theorem comm_mem_sup_inf_centralizer {P : Type*} [Group P] (S : Finset (Subgroup P))
    (hcomm : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ {u : P}, u ∈ S.sup id → ∀ {x y : P}, x ∈ S.sup id → y ∈ S.sup id →
      (∀ g ∈ S.sup id, g * ⁅x, u⁆ = ⁅x, u⁆ * g) → (∀ g ∈ S.sup id, g * ⁅y, u⁆ = ⁅y, u⁆ * g) →
      ⁅x, y⁆ ∈ S.sup (fun A => A ⊓ centralizer ({u} : Set P)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro u hu x y hx hy _ _
    have hx1 : x = 1 := by simpa using hx
    subst hx1
    simp
  | insert A S' hA ih =>
    intro u hu x y hx hy hxu hyu
    have hne : ∀ A' ∈ S', A ≠ A' := fun A' hA' h => hA (by rw [h]; exact hA')
    have hcomm' : ∀ A' ∈ S', ∀ B ∈ S', A' ≠ B → ∀ a ∈ A', ∀ b ∈ B, a * b = b * a :=
      fun A' hA' B hB => hcomm A' (Finset.mem_insert_of_mem hA') B (Finset.mem_insert_of_mem hB)
    have hAA : ∀ A' ∈ S', ∀ a ∈ A, ∀ b ∈ A', a * b = b * a := fun A' hA' =>
      hcomm A (Finset.mem_insert_self A S') A' (Finset.mem_insert_of_mem hA') (hne A' hA')
    have hAB : ∀ a ∈ A, ∀ b ∈ S'.sup id, a * b = b * a :=
      mul_comm_sup_of_forall_mul_comm A S' hAA
    have hsup : (insert A S').sup id = A ⊔ S'.sup id := Finset.sup_insert
    rw [hsup] at hu hx hy hxu hyu
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_mul_comm hAB hx
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_eq_of_mem_sup_of_mul_comm hAB hy
    obtain ⟨au, hau, bu, hbu, rfl⟩ := exists_mul_eq_of_mem_sup_of_mul_comm hAB hu
    have hxu' : ⁅a * b, au * bu⁆ = ⁅a, au⁆ * ⁅b, bu⁆ :=
      comm_mul_mul_eq_of_commute_pair (hAB a ha bu hbu) (hAB au hau b hb) (hAB a ha b hb)
        (hAB au hau bu hbu)
    have hyu' : ⁅a' * b', au * bu⁆ = ⁅a', au⁆ * ⁅b', bu⁆ :=
      comm_mul_mul_eq_of_commute_pair (hAB a' ha' bu hbu) (hAB au hau b' hb') (hAB a' ha' b' hb')
        (hAB au hau bu hbu)
    have hxy' : ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ * ⁅b, b'⁆ :=
      comm_mul_mul_eq_of_commute_pair (hAB a ha b' hb') (hAB a' ha' b hb) (hAB a ha b hb)
        (hAB a' ha' b' hb')
    have hmem : ∀ (H : Subgroup P) {p q : P}, p ∈ H → q ∈ H → ⁅p, q⁆ ∈ H :=
      fun H p q hp hq => by
        rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem hp hq) (H.inv_mem hp)) (H.inv_mem hq)
    rw [hxu'] at hxu
    rw [hyu'] at hyu
    obtain ⟨hxA, hxB⟩ := commute_factors_of_commute_prod hAB (hmem A ha hau) (hmem _ hb hbu) hxu
    obtain ⟨hyA, hyB⟩ := commute_factors_of_commute_prod hAB (hmem A ha' hau) (hmem _ hb' hbu) hyu
    rw [hxy', Finset.sup_insert]
    refine Subgroup.mul_mem_sup ?_ ?_
    · refine Subgroup.mem_inf.mpr ⟨hmem A ha ha', ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : ⁅⁅a, a'⁆, au⁆ = 1 := comm_comm_eq_one_of_commute_forall A ha ha' hau hxA hyA
      have h1' := commutatorElement_eq_one_iff_mul_comm.mp h1
      have h2 := hAB _ (hmem A ha ha') bu hbu
      calc ⁅a, a'⁆ * (au * bu) = (⁅a, a'⁆ * au) * bu := (mul_assoc _ _ _).symm
        _ = (au * ⁅a, a'⁆) * bu := by rw [h1']
        _ = au * (⁅a, a'⁆ * bu) := mul_assoc _ _ _
        _ = au * (bu * ⁅a, a'⁆) := by rw [h2]
        _ = au * bu * ⁅a, a'⁆ := (mul_assoc _ _ _).symm
    · have hih := ih hcomm' hbu hb hb' hxB hyB
      have hle : S'.sup (fun A' => A' ⊓ centralizer ({bu} : Set P)) ≤
          S'.sup (fun A' => A' ⊓ centralizer ({au * bu} : Set P)) := by
        refine Finset.sup_mono_fun fun A' hA' z hz => ?_
        refine Subgroup.mem_inf.mpr ⟨hz.1, ?_⟩
        have hz2 := Subgroup.mem_centralizer_singleton_iff.mp hz.2
        have hz3 : au * z = z * au := hAA A' hA' au hau z hz.1
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc z * (au * bu) = (z * au) * bu := (mul_assoc _ _ _).symm
          _ = (au * z) * bu := by rw [hz3]
          _ = au * (z * bu) := mul_assoc _ _ _
          _ = au * (bu * z) := by rw [hz2]
          _ = au * bu * z := (mul_assoc _ _ _).symm
      exact hle hih

end Comm

end CFSG.OddStandard.Solomon75
