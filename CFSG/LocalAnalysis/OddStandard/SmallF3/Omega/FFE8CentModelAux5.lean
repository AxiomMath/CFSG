module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentModelAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ε : ZMod 3}

private theorem card_even_subsets (hε : ε = 1 ∨ ε = -1) :
    Nat.card {K : Finset FFE8Idx //
      Even K.card ∧ Even (K.filter fun i => ffE8Norm ε i = -1).card} = 16 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rcases hε with rfl | rfl <;> decide

theorem ffOutFFE8CentModel_card_inf (hQ : Q.Nondegenerate) (hε : ε = 1 ∨ ε = -1)
    (fr : PFrame Q FFE8Idx (ffE8Norm ε)) :
    Nat.card ↥(ffOutFFE8CentModel_grp fr ⊓ omegaGroup hQ) = 16 := by
  have hc : ∀ i, ffE8Norm ε i = 1 ∨ ffE8Norm ε i = -1 := by
    rintro (i | i)
    · fin_cases i <;> simp [ffE8Norm]
    · simpa [ffE8Norm] using hε
  let F : {K : Finset FFE8Idx //
      Even K.card ∧ Even (K.filter fun i => ffE8Norm ε i = -1).card} →
      ↥(ffOutFFE8CentModel_grp fr ⊓ omegaGroup hQ) :=
    fun K => ⟨fr.signChange K.1, ⟨K.1, rfl⟩, (ffE8Sign_mem_omega_iff hQ fr hc K.1).mpr K.2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun J K h => Subtype.ext (fr.signChange_injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨g, ⟨K, rfl⟩, hg⟩
    exact ⟨⟨K, (ffE8Sign_mem_omega_iff hQ fr hc K).mp hg⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), card_even_subsets hε]

private def idx (p : Fin 2) : Option (Fin 5) → FFE8Idx
  | none => Sum.inl p
  | some i => Fin.cases (motive := fun _ => FFE8Idx) (Sum.inl (1 - p)) (fun j => Sum.inr j) i

private theorem idx_bijective (p : Fin 2) : Function.Bijective (idx p) := by
  revert p
  decide

theorem ffOutFFE8CentModel_exists_conj (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hε : ε = 1 ∨ ε = -1)
    (fr : PFrame Q FFE8Idx (ffE8Norm ε)) :
    ∃ (γ : simGroup Q) (frP : PFrame Q (Option (Fin 5)) ffC),
      ffOutFFE8CentModel_grp fr ⊓ omegaGroup hQ = (ffB0p frP).map (simAct Q γ).toMonoidHom := by
  obtain ⟨p, hp1, hp2⟩ : ∃ p : Fin 2, ffE8Norm ε (Sum.inl p) = -ε ∧
      ffE8Norm ε (Sum.inl (1 - p)) = ε := by
    rcases hε with rfl | rfl
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨0, rfl, rfl⟩
  have hεne : ε ≠ 0 := by
    rcases hε with rfl | rfl <;> decide
  let e : Option (Fin 5) ≃ FFE8Idx := Equiv.ofBijective (idx p) (idx_bijective p)
  let b : Module.Basis (Option (Fin 5)) (ZMod 3) V := fr.b.reindex e.symm
  have hb : ∀ o, b o = fr.b (e o) := fun o => by
    simp [b, Module.Basis.reindex_apply]
  refine fg_conj_E16 hQ hdim _ inf_le_right (ffOutFFE8CentModel_card_inf hQ hε fr) b hεne
    (fun i j hij => ?_) ?_ (fun i => ?_) ?_
  · rw [hb, hb]
    exact fr.orth _ _ (e.injective.ne hij)
  · rw [hb, fr.norm]
    exact hp1
  · rw [hb, fr.norm]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hp2
    · rfl
  · rintro g ⟨⟨K, rfl⟩, -⟩ o
    rw [hb o, fr.signChange_basis]
    by_cases ho : e o ∈ K
    · exact ⟨-1, by decide, by simp [ho]⟩
    · exact ⟨1, by decide, by simp [ho]⟩

end CFSG.OddStandard.SmallF3.Omega
