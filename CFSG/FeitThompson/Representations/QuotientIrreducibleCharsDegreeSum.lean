module

import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module
open scoped ComplexConjugate

variable {G : Type*} [Group G]

section Surjection

variable {k : Type*} [Field k] {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V] [Module k V]

def Representation.subrepresentationComp (ρ : Representation k Q V) {f : G →* Q}
    (hf : Function.Surjective f) :
    Subrepresentation (ρ.comp f : Representation k G V) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun q v hv => by
    obtain ⟨g, rfl⟩ := hf q; exact U.apply_mem_toSubmodule g hv⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem Representation.isIrreducible_comp_iff (ρ : Representation k Q V) {f : G →* Q}
    (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f : Representation k G V) ↔ ρ.IsIrreducible := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h
    exact (Representation.subrepresentationComp ρ hf).symm.isSimpleOrder
  · have := h
    exact (Representation.subrepresentationComp ρ hf).isSimpleOrder

end Surjection

def irrTrivialOn (N : Subgroup G) : Set (G → ℂ) :=
  {χ ∈ Irr G | (N : Set G) ⊆ charValueKernel χ}

variable {N : Subgroup G}

theorem mem_irrTrivialOn {χ : G → ℂ} :
    χ ∈ irrTrivialOn N ↔ χ ∈ Irr G ∧ ∀ n ∈ N, χ n = χ 1 := by
  simp [irrTrivialOn, Set.subset_def]

theorem irrTrivialOn_subset_Irr : irrTrivialOn N ⊆ Irr G := fun _ h => h.1

theorem finite_irrTrivialOn [Finite G] : (irrTrivialOn N).Finite :=
  finite_Irr.subset irrTrivialOn_subset_Irr

noncomputable def irrTrivialOnFinset (N : Subgroup G) [Finite G] : Finset (G → ℂ) :=
  (finite_irrTrivialOn (N := N)).toFinset

@[simp]
theorem mem_irrTrivialOnFinset [Finite G] {χ : G → ℂ} :
    χ ∈ irrTrivialOnFinset N ↔ χ ∈ irrTrivialOn N :=
  Set.Finite.mem_toFinset _

variable [N.Normal]

theorem comp_mk_one (ψ : G ⧸ N → ℂ) : (ψ ∘ (QuotientGroup.mk : G → G ⧸ N)) 1 = ψ 1 := (rfl)

omit [N.Normal] in
theorem comp_mk_injective :
    Function.Injective (fun ψ : G ⧸ N → ℂ => ψ ∘ (QuotientGroup.mk : G → G ⧸ N)) := by
  intro ψ₁ ψ₂ h
  funext q
  induction q using QuotientGroup.induction_on with
  | _ g => exact congrFun h g

theorem mem_irrTrivialOn_comp_mk {χ : G ⧸ N → ℂ} (hχ : χ ∈ Irr (G ⧸ N)) :
    χ ∘ (QuotientGroup.mk : G → G ⧸ N) ∈ irrTrivialOn N := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hχ
  have hσ : Representation.IsIrreducible
      (W.ρ.comp (QuotientGroup.mk' N) : Representation ℂ G W.V) :=
    (Representation.isIrreducible_comp_iff W.ρ (QuotientGroup.mk'_surjective N)).2 hW
  have hchar : Representation.character (W.ρ.comp (QuotientGroup.mk' N) :
      Representation ℂ G W.V) = W.character ∘ (QuotientGroup.mk : G → G ⧸ N) := by
    funext g
    rw [fdRepCharacter_eq]
    rfl
  refine mem_irrTrivialOn.2 ⟨?_, ?_⟩
  · rw [← hchar]
    exact character_mem_Irr_of_isIrreducible _ hσ
  · intro n hn
    have h1 : (QuotientGroup.mk n : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).2 hn
    change W.character (QuotientGroup.mk n) = W.character (QuotientGroup.mk 1)
    simp [h1]

theorem exists_comp_mk_eq_of_mem_irrTrivialOn [Finite G] {χ : G → ℂ} (hχ : χ ∈ irrTrivialOn N) :
    ∃ ψ ∈ Irr (G ⧸ N), ψ ∘ (QuotientGroup.mk : G → G ⧸ N) = χ := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hχ.1
  have hker : ∀ n : N, W.ρ ((n : G)) = 1 := by
    intro n
    have h := (mem_irrTrivialOn.1 hχ).2 (n : G) n.2
    rw [fdRepCharacter_eq, Representation.char_one W.ρ] at h
    exact (Representation.character_eq_finrank_iff_of_finite W.ρ).1 h
  have htriv : Representation.IsTrivial (W.ρ.comp N.subtype) := ⟨fun n => hker n⟩
  set σ : Representation ℂ (G ⧸ N) W.V := Representation.ofQuotient W.ρ N with hσdef
  have hg : ∀ g : G, σ (QuotientGroup.mk g) = W.ρ g := fun g =>
    LinearMap.ext fun v => Representation.ofQuotient_coe_apply W.ρ N g v
  have hcomp : (σ.comp (QuotientGroup.mk' N) : Representation ℂ G W.V) = W.ρ := MonoidHom.ext hg
  have hσirr : σ.IsIrreducible := by
    rw [← Representation.isIrreducible_comp_iff σ (QuotientGroup.mk'_surjective N), hcomp]
    exact hW
  refine ⟨σ.character, character_mem_Irr_of_isIrreducible σ hσirr, ?_⟩
  funext g
  rw [fdRepCharacter_eq]
  change LinearMap.trace ℂ W.V (σ (QuotientGroup.mk g)) = LinearMap.trace ℂ W.V (W.ρ g)
  rw [hg g]

noncomputable def inflationEquiv (N : Subgroup G) [N.Normal] [Finite G] :
    Irr (G ⧸ N) ≃ irrTrivialOn N :=
  Equiv.ofBijective
    (fun ψ => ⟨(ψ : G ⧸ N → ℂ) ∘ (QuotientGroup.mk : G → G ⧸ N),
      mem_irrTrivialOn_comp_mk ψ.2⟩)
    ⟨fun ψ₁ ψ₂ h => Subtype.ext (comp_mk_injective (Subtype.ext_iff.1 h)), fun χ => by
      obtain ⟨ψ, hψ, hcomp⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn χ.2
      exact ⟨⟨ψ, hψ⟩, Subtype.ext hcomp⟩⟩

@[simp]
theorem inflationEquiv_apply_coe [Finite G] (ψ : Irr (G ⧸ N)) :
    ((inflationEquiv N ψ : G → ℂ)) = (ψ : G ⧸ N → ℂ) ∘ (QuotientGroup.mk : G → G ⧸ N) := (rfl)

omit [N.Normal] in
theorem sum_comp_mk [Fintype G] [Fintype (G ⧸ N)] (F : G ⧸ N → ℂ) :
    ∑ g : G, F (g : G ⧸ N) = (Nat.card N : ℂ) * ∑ q : G ⧸ N, F q := by
  classical
  rw [← Fintype.sum_fiberwise' (QuotientGroup.mk : G → G ⧸ N) F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have h1 : Nat.card (QuotientGroup.mk ⁻¹' ({q} : Set (G ⧸ N))) = Nat.card N := by
    simpa using QuotientGroup.card_preimage_mk N ({q} : Set (G ⧸ N))
  have h2 : Fintype.card {x : G // (x : G ⧸ N) = q} = Nat.card N := by
    rw [← Nat.card_eq_fintype_card, ← h1]
    exact Nat.card_congr (Equiv.refl _)
  simp [h2]

theorem cfInner_comp_mk [Fintype G] [Fintype (G ⧸ N)] (f h : G ⧸ N → ℂ) :
    cfInner (f ∘ (QuotientGroup.mk : G → G ⧸ N)) (h ∘ (QuotientGroup.mk : G → G ⧸ N))
      = cfInner f h := by
  rw [cfInner_def, cfInner_def]
  have hsum := sum_comp_mk (N := N) (fun q => f q * conj (h q))
  rw [show ∑ g : G, (f ∘ (QuotientGroup.mk : G → G ⧸ N)) g *
      conj ((h ∘ (QuotientGroup.mk : G → G ⧸ N)) g)
      = ∑ g : G, (fun q => f q * conj (h q)) (g : G ⧸ N) from rfl, hsum]
  have hN : (Nat.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hQ : (Nat.card (G ⧸ N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
  push_cast
  field_simp

theorem sum_sq_degree_irrTrivialOn [Finite G] :
    ∑ χ ∈ irrTrivialOnFinset N, χ 1 ^ 2 = (Nat.card (G ⧸ N) : ℂ) := by
  rw [← sum_character_one_sq' (G := G ⧸ N)]
  refine (Finset.sum_bij (fun ψ _ => ψ ∘ (QuotientGroup.mk : G → G ⧸ N)) ?_ ?_ ?_ ?_).symm
  · intro ψ hψ
    exact mem_irrTrivialOnFinset.2 (mem_irrTrivialOn_comp_mk (mem_irrFinset.1 hψ))
  · intro ψ₁ _ ψ₂ _ h
    exact comp_mk_injective h
  · intro χ hχ
    obtain ⟨ψ, hψ, hcomp⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn (mem_irrTrivialOnFinset.1 hχ)
    exact ⟨ψ, mem_irrFinset.2 hψ, hcomp⟩
  · intro ψ _
    rfl

theorem sum_sq_degree_irrTrivialOn_eq_index [Finite G] :
    ∑ χ ∈ irrTrivialOnFinset N, χ 1 ^ 2 = (N.index : ℂ) := by
  rw [sum_sq_degree_irrTrivialOn, Subgroup.index_eq_card]

end CFSG.FeitThompson
