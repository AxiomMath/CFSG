module

public import CFSG.GroupTheory.ThreeTranspositions.CyclicSylow
public import CFSG.GroupTheory.ThreeTranspositions.NormalCores
public import CFSG.Fischer.Classification.Basic.Center

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
open scoped commutatorElement

variable {X : Type} [Group X] {E : Set X}

private abbrev noncommutingProducts (E : Set X) : Set X :=
  {x : X | ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a ∧ x = a * b}

private lemma conj_mem_noncommutingProducts (hP : Pair X E) (g : X) {x : X}
    (hx : x ∈ noncommutingProducts E) : g * x * g⁻¹ ∈ noncommutingProducts E := by
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := hx
  refine ⟨g * a * g⁻¹, Pair.conj_mem hP ha g, g * b * g⁻¹, Pair.conj_mem hP hb g, ?_, ?_⟩
  · intro h
    exact hab ((conj_commute_iff g a b).mp h)
  · exact (conj_mul_conj g a b).symm

private lemma closure_noncommutingProducts_normal (hP : Pair X E) :
    (Subgroup.closure (noncommutingProducts E)).Normal :=
  ⟨fun n hn g => by
    induction hn using Subgroup.closure_induction with
    | mem y hy => exact Subgroup.subset_closure (conj_mem_noncommutingProducts hP g hy)
    | one => simpa using Subgroup.one_mem _
    | mul y z _ _ ihy ihz =>
        have h : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
        rw [h]
        exact Subgroup.mul_mem _ ihy ihz
    | inv y _ ihy =>
        have h : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
        rw [h]
        exact Subgroup.inv_mem _ ihy⟩

theorem mul_mem_closure_noncommuting (hP : Pair X E) {d e : X} (hd : d ∈ E) (he : e ∈ E) :
    d * e ∈ Subgroup.closure {x : X | ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a ∧ x = a * b} := by
  change d * e ∈ Subgroup.closure (noncommutingProducts E)
  let R : Set X := {x : X | x ∈ E ∧ d * x ∈ Subgroup.closure (noncommutingProducts E)}
  have hdR : d ∈ R := ⟨hd, by rw [Pair.mul_self hP hd]; exact Subgroup.one_mem _⟩
  have hconj : ∀ g ∈ Subgroup.closure E,
      (∀ x ∈ R, g * x * g⁻¹ ∈ R) ∧ (∀ x ∈ R, g⁻¹ * x * g ∈ R) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem f hf =>
        have key : ∀ x ∈ R, f * x * f ∈ R := by
          intro x hx
          have hxE : x ∈ E := hx.1
          have hdx : d * x ∈ Subgroup.closure (noncommutingProducts E) := hx.2
          have hfxE : f * x * f ∈ E := Pair.mul_mul_mem hP hf hxE
          have hmem : d * (f * x * f) ∈ Subgroup.closure (noncommutingProducts E) := by
            by_cases h : f * x = x * f
            · have hfix : f * x * f = x := by
                calc f * x * f = (f * x) * f := rfl
                  _ = (x * f) * f := by rw [h]
                  _ = x * (f * f) := by rw [mul_assoc]
                  _ = x * 1 := by rw [Pair.mul_self hP hf]
                  _ = x := mul_one x
              rw [hfix]
              exact hdx
            · have hxf : x * f ≠ f * x := fun hc => h hc.symm
              have hbraid : f * x * f = x * f * x := (Pair.mul_mul_eq hP hxE hf hxf).symm
              have hfxG : f * x ∈ noncommutingProducts E := ⟨f, hf, x, hxE, h, rfl⟩
              have hfxN : f * x ∈ Subgroup.closure (noncommutingProducts E) :=
                Subgroup.subset_closure hfxG
              have hdfx : d * (f * x * f) = (d * x) * (f * x) := by
                rw [hbraid]
                simp only [mul_assoc]
              rw [hdfx]
              exact Subgroup.mul_mem _ hdx hfxN
          exact ⟨hfxE, hmem⟩
        refine ⟨?_, ?_⟩
        · intro x hx
          rw [Pair.inv_eq hP hf]
          exact key x hx
        · intro x hx
          rw [Pair.inv_eq hP hf]
          exact key x hx
    | one =>
        exact ⟨fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
    | mul g₁ g₂ _ _ ih₁ ih₂ =>
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · have h1 : g₂ * x * g₂⁻¹ ∈ R := ih₂.1 x hx
          have h2 : g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ ∈ R := ih₁.1 _ h1
          rw [show (g₁ * g₂) * x * (g₁ * g₂)⁻¹ =
                g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ by group]
          exact h2
        · have h1 : g₁⁻¹ * x * g₁ ∈ R := ih₁.2 x hx
          have h2 : g₂⁻¹ * (g₁⁻¹ * x * g₁) * g₂ ∈ R := ih₂.2 _ h1
          rw [show (g₁ * g₂)⁻¹ * x * (g₁ * g₂) =
                g₂⁻¹ * (g₁⁻¹ * x * g₁) * g₂ by group]
          exact h2
    | inv g₁ _ ih =>
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · simpa only [inv_inv] using ih.2 x hx
        · simpa only [inv_inv] using ih.1 x hx
  have hER : E ⊆ R := by
    intro f hf
    obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP hd hf)
    have hgE : g ∈ Subgroup.closure E := by
      rw [Pair.closure_eq hP]
      exact Subgroup.mem_top g
    have hgd : g * d * g⁻¹ ∈ R := (hconj g hgE).1 d hdR
    rw [hg] at hgd
    exact hgd
  exact (hER he).2

theorem commutator_eq_closure_noncommuting (hP : Pair X E) :
    commutator X = Subgroup.closure {x : X | ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a ∧ x = a * b} := by
  change commutator X = Subgroup.closure (noncommutingProducts E)
  refine le_antisymm ?_ ?_
  · haveI : (Subgroup.closure (noncommutingProducts E)).Normal :=
      closure_noncommutingProducts_normal hP
    refine Pair.commutator_le_of_forall hP ?_
    intro e he f hf
    rw [Pair.inv_eq hP he]
    exact mul_mem_closure_noncommuting hP hf he
  · rw [Subgroup.closure_le]
    rintro x ⟨a, ha, b, hb, hab, rfl⟩
    have hba : b * a ≠ a * b := fun h => hab h.symm
    have h3 : (b * a) ^ 3 = 1 := by
      rw [← Pair.orderOf_mul_eq_three hP hb ha hba, pow_orderOf_eq_one]
    have hsq : (b * a) * (b * a) = a * b := by
      have h3'' : (b * a) ^ 2 * (b * a) = 1 := by
        rw [← pow_succ]
        simpa using h3
      rw [mul_eq_one_iff_eq_inv, pow_two] at h3''
      rw [h3'', mul_inv_rev, Pair.inv_eq hP hb, Pair.inv_eq hP ha]
    have hcomm : ⁅a, a * b⁆ = a * b := by
      rw [commutatorElement_def, mul_inv_rev, Pair.inv_eq hP ha, Pair.inv_eq hP hb]
      calc a * (a * b) * a * (b * a)
          = (a * a) * ((b * a) * (b * a)) := by simp only [mul_assoc]
        _ = (b * a) * (b * a) := by rw [Pair.mul_self hP ha, one_mul]
        _ = a * b := hsq
    rw [← hcomm, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top (a * b))

theorem isSimpleGroup_commutator_of_pair (hP : Pair X E) (hX : ¬ HasE9 X)
    (hO : CFSG.pPrimeCore 3 X = ⊥) (hnc : ∃ d ∈ E, ∃ e ∈ E, d * e ≠ e * d) :
    IsSimpleGroup ↥(commutator X) := by
  haveI : Finite X := Pair.finite hP
  have hX' : ¬ HasE9 ↥(commutator X) := fun h =>
    hX (HasE9.map_injective (commutator X).subtype (commutator X).subtype_injective h)
  have hO' : CFSG.pPrimeCore 3 ↥(commutator X) = ⊥ :=
    pPrimeCore_eq_bot_of_normal Nat.prime_three hO (commutator X)
  haveI : Nontrivial ↥(commutator X) := by
    obtain ⟨d, hd, e, he, hde⟩ := hnc
    refine nontrivial_of_ne (⟨⁅d, e⁆, ?_⟩ : ↥(commutator X)) 1 ?_
    · rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top d) (Subgroup.mem_top e)
    · intro h
      exact hde (commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp h))
  let S : Set ↥(commutator X) := {s | s = 1 ∨ orderOf s = 3}
  have hImage : (commutator X).subtype '' S =
      {y : X | y ∈ commutator X ∧ (y = 1 ∨ orderOf y = 3)} := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s.2, ?_⟩
      rcases hs with hs | hs
      · left
        rw [hs]
        rfl
      · right
        change orderOf (s : X) = 3
        rwa [Subgroup.orderOf_coe]
    · rintro ⟨hy, h | h⟩
      · exact ⟨1, Or.inl rfl, by rw [map_one]; exact h.symm⟩
      · exact ⟨⟨y, hy⟩, Or.inr (by rw [Subgroup.orderOf_mk, h]), rfl⟩
  have hS : Subgroup.closure S = ⊤ := by
    rw [eq_top_iff, ← Subgroup.map_subtype_le_map_subtype (G' := commutator X)]
    rw [Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_closure, hImage]
    conv_lhs => rw [commutator_eq_closure_noncommuting hP]
    refine Subgroup.closure_mono ?_
    rintro y ⟨a, ha, b, hb, hab, rfl⟩
    exact ⟨by
        rw [commutator_eq_closure_noncommuting hP]
        exact Subgroup.subset_closure ⟨a, ha, b, hb, hab, rfl⟩,
      Or.inr (Pair.orderOf_mul_eq_three hP ha hb hab)⟩
  exact isSimpleGroup_of_generated_by_order_three hX' hO' hS (fun s hs => hs)

end CFSG.GroupTheory.ThreeTranspositions
