module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Sylow

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
theorem centralizer_conj_eq (u k : G) :
    Subgroup.centralizer ({k⁻¹ * u * k} : Set G) =
      rightConjugate (Subgroup.centralizer ({u} : Set G)) k := by
  ext x
  rw [mem_rightConjugate_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc k * x * k⁻¹ * u = k * (x * (k⁻¹ * u * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * u * k) * x) * k⁻¹ := by rw [hx]
      _ = u * (k * x * k⁻¹) := by group
  · intro hx
    calc x * (k⁻¹ * u * k) = k⁻¹ * ((k * x * k⁻¹) * u) * k := by group
      _ = k⁻¹ * (u * (k * x * k⁻¹)) * k := by rw [hx]
      _ = k⁻¹ * u * k * x := by group

theorem Hyp.exists_conj_sylow_inf (h : Hyp S A₁ A₂)
    (hSH : (S : Subgroup G) ≤ overlapClosure A₁ A₂) {u : G} {X : Subgroup G}
    (hXS : X ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G))
    (hX : FixesOnly (overlapClosure A₁ A₂) X) :
    ∃ k ∈ overlapClosure A₁ A₂,
      (∃ P : Sylow 2 (Subgroup.centralizer ({k⁻¹ * u * k} : Set G)),
        (P : Subgroup _) =
          (S : Subgroup G).subgroupOf (Subgroup.centralizer ({k⁻¹ * u * k} : Set G))) ∧
      ∀ x ∈ (A₁ : Set G) ∪ A₂, x ∈ Subgroup.centralizer ({u} : Set G) →
        k⁻¹ * x * k ∈ (A₁ : Set G) ∪ A₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := Subgroup.centralizer ({u} : Set G)
  have hSC : IsPGroup 2 (((S : Subgroup G) ⊓ C).subgroupOf C) :=
    (S.isPGroup'.to_le inf_le_left).comap_of_injective C.subtype C.subtype_injective
  obtain ⟨T, hT⟩ := hSC.exists_le_sylow
  let T' : Subgroup G := (T : Subgroup C).map C.subtype
  have hT'p : IsPGroup 2 T' := T.isPGroup'.map C.subtype
  have hST' : (S : Subgroup G) ⊓ C ≤ T' := by
    intro x hx
    exact ⟨⟨x, hx.2⟩, hT hx, rfl⟩
  have hT'H : T' ≤ overlapClosure A₁ A₂ :=
    le_of_fixesOnly (odd_index_of_sylow_le hSH) hT'p (hXS.trans hST') hX
  obtain ⟨k, hk, hkS⟩ := exists_conj_le_sylow hSH hT'H hT'p
  refine ⟨k, hk, ?_, fun x hx hxC => ?_⟩
  · let C' := Subgroup.centralizer ({k⁻¹ * u * k} : Set G)
    have hC' : C' = rightConjugate C k := centralizer_conj_eq u k
    have hcardC : Nat.card C' = Nat.card C := by rw [hC', rightConjugate_card]
    have hTk : rightConjugate T' k ≤ (S : Subgroup G) ⊓ C' := by
      intro y hy
      rw [mem_rightConjugate_iff] at hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := hkS _ hy
        simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using this
      · rw [hC', mem_rightConjugate_iff]
        obtain ⟨c, -, hc⟩ := hy
        rw [← hc]
        exact c.property
    have hcard_ge : 2 ^ (Nat.card C').factorization 2 ≤
        Nat.card ((S : Subgroup G).subgroupOf C') := by
      rw [hcardC, ← Sylow.card_eq_multiplicity T,
        ← Subgroup.card_map_of_injective C.subtype_injective,
        ← rightConjugate_card T' k]
      refine (Subgroup.card_le_of_le hTk).trans (le_of_eq ?_)
      rw [← Subgroup.card_map_of_injective C'.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
    have hcard_le : Nat.card ((S : Subgroup G).subgroupOf C') ≤
        2 ^ (Nat.card C').factorization 2 := by
      have hp : IsPGroup 2 ((S : Subgroup G).subgroupOf C') :=
        S.isPGroup'.comap_of_injective C'.subtype C'.subtype_injective
      obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
      rw [← Sylow.card_eq_multiplicity Q]
      exact Subgroup.card_le_of_le hQ
    exact ⟨Sylow.ofCard _ (le_antisymm hcard_le hcard_ge), rfl⟩
  · have hxT' : x ∈ T' := hST' ⟨by
      rcases hx with hx | hx
      · exact h.le_one hx
      · exact h.le_two hx, hxC⟩
    exact h.conj_mem_of_mem_overlapClosure hx hk (hkS x hxT')

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
