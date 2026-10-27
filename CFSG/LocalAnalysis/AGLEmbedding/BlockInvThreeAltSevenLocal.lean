module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeAltSeven
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeAltSevenSylow
import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeAltSevenFour

public section

namespace CFSG.AGLEmbedding.AltSevenInv

open Equiv Equiv.Perm

variable {T : Subgroup (alternatingGroup (Fin 7))}

theorem wit_E1 (hE : ∀ σ, inT T σ ↔ σ ∈ [1, r * r]) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) :=
  invThree_of_witCheck hE (swap 0 6 * swap 0 5) (swap 2 4 * swap 5 6) (by decide +kernel)

theorem wit_E2 (hE : ∀ σ, inT T σ ↔ σ ∈ [1, s]) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) :=
  invThree_of_witCheck hE (swap 0 4 * swap 0 2) (swap 2 4 * swap 5 6) (by decide +kernel)

theorem wit_E3 (hE : ∀ σ, inT T σ ↔ σ ∈ [1, s * r * r]) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) :=
  invThree_of_witCheck hE (swap 0 3 * swap 0 1) (swap 1 3 * swap 5 6) (by decide +kernel)

theorem wit_E4 (hE : ∀ σ, inT T σ ↔ σ ∈ [1, s * r]) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) :=
  invThree_of_witCheck hE (swap 0 6 * swap 0 5) (swap 3 4 * swap 5 6) (by decide +kernel)

theorem wit_E5 (hE : ∀ σ, inT T σ ↔ σ ∈ [1, s * r * r * r]) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) :=
  invThree_of_witCheck hE (swap 0 6 * swap 0 5) (swap 2 3 * swap 5 6) (by decide +kernel)

theorem wit_E6 (hE : ∀ σ, inT T σ ↔ σ ∈ [1, r * r, s, s * r * r]) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) :=
  invThree_of_witCheck hE (swap 1 5 * swap 1 2 * (swap 3 6 * swap 3 4)) (swap 2 5 * swap 4 6)
    (by decide +kernel)

theorem wit_E7 (hE : ∀ σ, inT T σ ↔ σ ∈ [1, r * r, s * r, s * r * r * r]) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) :=
  invThree_of_witCheck hE (swap 2 4 * swap 2 3) (swap 3 4 * swap 5 6) (by decide +kernel)

theorem eq_of_inT_of_le_P0 (hTP : T ≤ P0) {σ : Perm (Fin 7)} (h : inT T σ) :
    σ = 1 ∨ σ = r ∨ σ = r * r ∨ σ = r * r * r ∨ σ = s ∨ σ = s * r ∨ σ = s * r * r ∨
      σ = s * r * r * r := by
  have := mem_p0_of_inT hTP h
  simpa [p0List] using this

theorem invThree_of_le_P0_of_s (hTP : T ≤ P0) (hr : ¬ inT T r) (hr3 : ¬ inT T (r * r * r))
    (hs : inT T s) : InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := p0_rels
  have hsr : ¬ inT T (s * r) := fun h => hr (h1 ▸ inT_mul hs h)
  have hsr3 : ¬ inT T (s * r * r * r) := fun h => hr3 (h2 ▸ inT_mul hs h)
  by_cases hr2 : inT T (r * r)
  · have hsr2 : inT T (s * r * r) := h3 ▸ inT_mul hs hr2
    refine wit_E6 fun σ => ⟨fun h => ?_, fun h => ?_⟩
    · rcases eq_of_inT_of_le_P0 hTP h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact absurd h hr
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact absurd h hr3
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact absurd h hsr
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))
      · exact absurd h hsr3
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact inT_one
      · exact hr2
      · exact hs
      · exact hsr2
  · have hsr2 : ¬ inT T (s * r * r) := fun h => hr2 (h4 ▸ inT_mul hs h)
    refine wit_E2 fun σ => ⟨fun h => ?_, fun h => ?_⟩
    · rcases eq_of_inT_of_le_P0 hTP h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact absurd h hr
      · exact absurd h hr2
      · exact absurd h hr3
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact absurd h hsr
      · exact absurd h hsr2
      · exact absurd h hsr3
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact inT_one
      · exact hs

theorem invThree_of_le_P0_of_sr2 (hTP : T ≤ P0) (hr : ¬ inT T r) (hr3 : ¬ inT T (r * r * r))
    (hs : ¬ inT T s) (hsr2 : inT T (s * r * r)) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) := by
  obtain ⟨-, -, -, -, h5, h6, h7, -⟩ := p0_rels
  have hsr : ¬ inT T (s * r) := fun h => hr3 (h5 ▸ inT_mul hsr2 h)
  have hsr3 : ¬ inT T (s * r * r * r) := fun h => hr (h6 ▸ inT_mul hsr2 h)
  have hr2 : ¬ inT T (r * r) := fun h => hs (h7 ▸ inT_mul hsr2 h)
  refine wit_E3 fun σ => ⟨fun h => ?_, fun h => ?_⟩
  · rcases eq_of_inT_of_le_P0 hTP h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact absurd h hr
    · exact absurd h hr2
    · exact absurd h hr3
    · exact absurd h hs
    · exact absurd h hsr
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact absurd h hsr3
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact inT_one
    · exact hsr2

theorem invThree_of_le_P0_of_sr (hTP : T ≤ P0) (hr : ¬ inT T r) (hr3 : ¬ inT T (r * r * r))
    (hs : ¬ inT T s) (hsr2 : ¬ inT T (s * r * r)) (hsr : inT T (s * r)) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) := by
  obtain ⟨-, -, -, -, -, -, -, h8, h9, -⟩ := p0_rels
  by_cases hr2 : inT T (r * r)
  · have hsr3 : inT T (s * r * r * r) := h8 ▸ inT_mul hsr hr2
    refine wit_E7 fun σ => ⟨fun h => ?_, fun h => ?_⟩
    · rcases eq_of_inT_of_le_P0 hTP h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact absurd h hr
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact absurd h hr3
      · exact absurd h hs
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact absurd h hsr2
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact inT_one
      · exact hr2
      · exact hsr
      · exact hsr3
  · have hsr3 : ¬ inT T (s * r * r * r) := fun h => hr2 (h9 ▸ inT_mul hsr h)
    refine wit_E4 fun σ => ⟨fun h => ?_, fun h => ?_⟩
    · rcases eq_of_inT_of_le_P0 hTP h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact absurd h hr
      · exact absurd h hr2
      · exact absurd h hr3
      · exact absurd h hs
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact absurd h hsr2
      · exact absurd h hsr3
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact inT_one
      · exact hsr

theorem invThree_of_le_P0_of_not_sr (hTP : T ≤ P0) (hT1 : T ≠ ⊥) (hr : ¬ inT T r)
    (hr3 : ¬ inT T (r * r * r)) (hs : ¬ inT T s) (hsr2 : ¬ inT T (s * r * r))
    (hsr : ¬ inT T (s * r)) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10⟩ := p0_rels
  by_cases hsr3 : inT T (s * r * r * r)
  · have hr2 : ¬ inT T (r * r) := fun h => hsr (h10 ▸ inT_mul hsr3 h)
    refine wit_E5 fun σ => ⟨fun h => ?_, fun h => ?_⟩
    · rcases eq_of_inT_of_le_P0 hTP h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact absurd h hr
      · exact absurd h hr2
      · exact absurd h hr3
      · exact absurd h hs
      · exact absurd h hsr
      · exact absurd h hsr2
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact inT_one
      · exact hsr3
  · have hr2 : inT T (r * r) := by
      by_contra hr2
      apply hT1
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have hx' := inT_coe.mpr hx
      rcases eq_of_inT_of_le_P0 hTP hx' with h | h | h | h | h | h | h | h
      · exact Subtype.ext h
      · exact absurd (h ▸ hx') hr
      · exact absurd (h ▸ hx') hr2
      · exact absurd (h ▸ hx') hr3
      · exact absurd (h ▸ hx') hs
      · exact absurd (h ▸ hx') hsr
      · exact absurd (h ▸ hx') hsr2
      · exact absurd (h ▸ hx') hsr3
    refine wit_E1 fun σ => ⟨fun h => ?_, fun h => ?_⟩
    · rcases eq_of_inT_of_le_P0 hTP h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact absurd h hr
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact absurd h hr3
      · exact absurd h hs
      · exact absurd h hsr
      · exact absurd h hsr2
      · exact absurd h hsr3
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact inT_one
      · exact hr2

theorem invThree_of_le_P0 (hTP : T ≤ P0) (hT1 : T ≠ ⊥) (hr : ¬ inT T r)
    (hr3 : ¬ inT T (r * r * r)) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) := by
  by_cases hs : inT T s
  · exact invThree_of_le_P0_of_s hTP hr hr3 hs
  by_cases hsr2 : inT T (s * r * r)
  · exact invThree_of_le_P0_of_sr2 hTP hr hr3 hs hsr2
  by_cases hsr : inT T (s * r)
  · exact invThree_of_le_P0_of_sr hTP hr hr3 hs hsr2 hsr
  exact invThree_of_le_P0_of_not_sr hTP hT1 hr hr3 hs hsr2 hsr

end CFSG.AGLEmbedding.AltSevenInv

namespace CFSG.AGLEmbedding

open AltSevenInv

theorem kFactAltSevenTwoLocalInv_holds : KFactAltSevenTwoLocalInv := by
  intro T hT2 hT1 hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hTP⟩ := hT2.exists_le_sylow
  set P0S : Sylow 2 (alternatingGroup (Fin 7)) := isPGroup_P0.toSylow not_two_dvd_index_P0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) P P0S
  set φ : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) := MulAut.conj g
  set T' := T.map φ.toMonoidHom
  have hT'P : T' ≤ P0 := by
    have h1 : T' ≤ (P : Subgroup (alternatingGroup (Fin 7))).map φ.toMonoidHom :=
      Subgroup.map_mono hTP
    have h2 : (P : Subgroup (alternatingGroup (Fin 7))).map φ.toMonoidHom = P0 := by
      have := congrArg (fun Q : Sylow 2 (alternatingGroup (Fin 7)) =>
        (Q : Subgroup (alternatingGroup (Fin 7)))) hg
      simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at this
      exact this
    exact h1.trans h2.le
  have hT'2 : IsPGroup 2 T' := hT2.map _
  have hT'1 : T' ≠ ⊥ := fun h =>
    hT1 ((Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h)
  have hNT' : Subgroup.normalizer (T' : Set (alternatingGroup (Fin 7))) =
      (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))).map φ.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq T φ).symm
  have hN' : ¬ IsPGroup 2 (Subgroup.normalizer (T' : Set (alternatingGroup (Fin 7)))) := by
    rw [hNT']
    intro h
    exact hN (h.of_equiv (Subgroup.equivMapOfInjective _ _ φ.injective).symm)
  have hInv' : InvThree (Subgroup.normalizer (T' : Set (alternatingGroup (Fin 7)))) := by
    by_cases hr : inT T' r ∨ inT T' (r * r * r)
    · exact absurd (isPGroup_normalizer_of_r hT'P hT'2 hT'1 hr) hN'
    · simp only [not_or] at hr
      exact invThree_of_le_P0 hT'P hT'1 hr.1 hr.2
  rw [hNT'] at hInv'
  have := hInv'.map_injective φ.symm.toMonoidHom φ.symm.injective
  rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ by
    ext x; simp, Subgroup.map_id] at this

end CFSG.AGLEmbedding
