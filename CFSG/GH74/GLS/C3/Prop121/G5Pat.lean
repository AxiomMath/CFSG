module

public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Layer3

theorem pattern_map {G : Type} [Group G] [Finite G]
    (hP : SameCentralizerOfInvolutionPattern G (alternatingGroup (Fin 9)))
    {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) :
    ∃ φ : ↥S →* alternatingGroup (Fin 9), Function.Injective φ ∧ IsSylowOf 2 φ.range ⊤ ∧
      (∀ u v : ↥S, orderOf u = 2 → orderOf v = 2 →
        (IsConj (u : G) (v : G) ↔ IsConj (φ u) (φ v))) ∧
      (∀ u : ↥S, orderOf u = 2 → Nat.card ↥(centralizer ({(u : G)} : Set G)) =
        Nat.card ↥(centralizer ({φ u} : Set (alternatingGroup (Fin 9))))) := by
  obtain ⟨S₁, S', φ₁, hcls, hcent⟩ := hP
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSylow : ∀ {X : Type} [Group X] [Finite X] (T : Sylow 2 X),
      IsSylowOf 2 (T : Subgroup X) ⊤ := by
    intro X _ _ T
    rw [isSylowOf_iff]
    refine ⟨le_top, T.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact T.not_dvd_index
  obtain ⟨k, -, hk⟩ := IsSylowOf.exists_mem_conj (hSylow S₁) hS
  let c : ↥S →* ↥(S₁ : Subgroup G) :=
    { toFun := fun s => ⟨k⁻¹ * s * k, (hk s).1 s.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
  have hcinj : Function.Injective c := by
    intro a b h
    apply Subtype.ext
    have h2 : k⁻¹ * (a : G) * k = k⁻¹ * (b : G) * k :=
      congrArg (fun z : ↥(S₁ : Subgroup G) => (z : G)) h
    simpa using h2
  let φ : ↥S →* alternatingGroup (Fin 9) :=
    ((S' : Subgroup (alternatingGroup (Fin 9))).subtype).comp
      ((φ₁ : ↥(S₁ : Subgroup G) →* ↥(S' : Subgroup (alternatingGroup (Fin 9)))).comp c)
  have hφinj : Function.Injective φ :=
    Subtype.val_injective.comp (φ₁.injective.comp hcinj)
  have hrange : φ.range = (S' : Subgroup (alternatingGroup (Fin 9))) := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact SetLike.coe_mem _
    · intro hy
      obtain ⟨z, hz⟩ := φ₁.surjective ⟨y, hy⟩
      have hzS : k * (z : G) * k⁻¹ ∈ S := by
        rw [hk]
        have : k⁻¹ * (k * (z : G) * k⁻¹) * k = z := by group
        rw [this]
        exact z.2
      refine ⟨⟨k * z * k⁻¹, hzS⟩, ?_⟩
      have hcz : c ⟨k * z * k⁻¹, hzS⟩ = z := by
        apply Subtype.ext
        show k⁻¹ * (k * (z : G) * k⁻¹) * k = z
        group
      show ((φ₁ (c ⟨k * z * k⁻¹, hzS⟩) : ↥(S' : Subgroup (alternatingGroup (Fin 9)))) :
        alternatingGroup (Fin 9)) = y
      rw [hcz, hz]
  have hconj : ∀ a b : G, IsConj a b → IsConj (k⁻¹ * a * k) (k⁻¹ * b * k) := by
    intro a b h
    have := (isConj_map_iff (MulAut.conj k⁻¹) (a := a) (b := b)).2 h
    simpa [MulAut.conj_apply] using this
  have hconj' : ∀ a b : G, IsConj (k⁻¹ * a * k) (k⁻¹ * b * k) → IsConj a b := by
    intro a b h
    have := (isConj_map_iff (MulAut.conj k⁻¹) (a := a) (b := b)).1
    apply this
    simpa [MulAut.conj_apply] using h
  refine ⟨φ, hφinj, ?_, ?_, ?_⟩
  · rw [hrange]
    exact hSylow S'
  · intro u v hu hv
    have hu' : orderOf (c u) = 2 := by rw [orderOf_injective c hcinj u]; exact hu
    have hv' : orderOf (c v) = 2 := by rw [orderOf_injective c hcinj v]; exact hv
    have h1 := hcls (c u) (c v) hu' hv'
    constructor
    · intro h
      exact h1.1 (hconj _ _ h)
    · intro h
      exact hconj' _ _ (h1.2 h)
  · intro u hu
    have hu' : orderOf (c u) = 2 := by rw [orderOf_injective c hcinj u]; exact hu
    have hc : IsConj (u : G) ((c u : ↥(S₁ : Subgroup G)) : G) := isConj_iff.2 ⟨k⁻¹, by simp [c]⟩
    rw [card_centralizer_eq_of_isConj hc]
    exact Nat.card_congr (hcent (c u) hu').some.toEquiv

end CFSG.GH74.GLS.C3.Prop121
