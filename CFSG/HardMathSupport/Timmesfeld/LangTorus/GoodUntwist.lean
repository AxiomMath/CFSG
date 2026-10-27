module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement Matrix

set_option linter.unusedSectionVars false


section PairChar

variable {τ : Tag}

@[expose] noncomputable def pairChar (β : Fin τ.rank → ℤ) :
    Multiplicative (Fin τ.rank → ℤ) →*
      Multiplicative ((Fin τ.rank → ℤ) ⧸ AddSubgroup.zmultiples β) :=
  AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' (AddSubgroup.zmultiples β))

theorem pairChar_eq_one_iff (β α : Fin τ.rank → ℤ) :
    pairChar β (Multiplicative.ofAdd α) = 1 ↔ α ∈ AddSubgroup.zmultiples β := by
  unfold pairChar
  constructor
  · intro h
    have h' : QuotientAddGroup.mk' (AddSubgroup.zmultiples β) α = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    exact (QuotientAddGroup.eq_zero_iff _).1 h'
  · intro h
    have h' : QuotientAddGroup.mk' (AddSubgroup.zmultiples β) α = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 h
    apply Multiplicative.toAdd.injective
    simpa using h'

theorem kernelRoots_pairChar {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hlen : ∀ α, IsRoot τ α → iform α α = iform β β) :
    kernelRoots (pairChar β) = {β, -β} := by
  ext α
  constructor
  · rintro ⟨hα, hk⟩
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 ((pairChar_eq_one_iff β α).1 hk)
    have h1 := hlen α hα
    rw [← hk, iform_smul_left, iform_smul_right] at h1
    have hpos := iform_self_pos_of_isRoot hβ
    have h2 : k * k = 1 := by
      have : (k * k - 1) * iform β β = 0 := by linear_combination h1
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · omega
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with rfl | rfl
    · left
      simpa using hk.symm
    · right
      simpa using hk.symm
  · rintro (rfl | rfl)
    · exact ⟨hβ, (pairChar_eq_one_iff α α).2 (AddSubgroup.mem_zmultiples _)⟩
    · refine ⟨IsRoot.neg hβ, (pairChar_eq_one_iff β (-β)).2 ?_⟩
      exact AddSubgroup.neg_mem _ (AddSubgroup.mem_zmultiples _)

theorem componentRoots_pairChar {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hlen : ∀ α, IsRoot τ α → iform α α = iform β β)
    (hβk : β ∈ kernelRoots (pairChar β)) :
    componentRoots (pairChar β) (⟦⟨β, hβk⟩⟧ : KernelComponent (pairChar β)) = {β, -β} := by
  have hker := kernelRoots_pairChar hβ hlen
  have hnk : -β ∈ kernelRoots (pairChar β) := by rw [hker]; exact Or.inr rfl
  ext α
  constructor
  · rintro ⟨hα, -⟩
    rw [hker] at hα
    exact hα
  · rintro (rfl | rfl)
    · exact ⟨hβk, rfl⟩
    · refine ⟨hnk, Quotient.sound (Relation.EqvGen.rel _ _ ?_)⟩
      show (-β : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) ≠ 0
      rw [dotProduct_mulVec_eq_iform, iform_neg_left]
      have := iform_self_pos_of_isRoot hβ
      omega

end PairChar

section Untwist

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem rootReflection_smul_self {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootReflection β • β = -β := by
  have h := ((exceptional_Lang_root_rank_one_torus_transport τ ℚ hβ).2.2.2.1 β).1
  rw [h, Int.mul_ediv_cancel 2 (iform_self_pos_of_isRoot hβ).ne']
  simp [two_smul]

theorem exists_untwist_pair {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hlen : ∀ α, IsRoot τ α → iform α α = iform β β) {m : ℕ} (hm : 0 < m)
    (hρ : (S.ρ : (Fin τ.rank → ℤ) → _)^[m] β = β ∨ (S.ρ : (Fin τ.rank → ℤ) → _)^[m] β = -β) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ m)) ∧
      z ∈ torusGroup τ L ⊔ rootSpan τ L {β, -β} ∧
      ∀ g ∈ rootSpan τ L {β, -β},
        iterHom S.D.step m (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  set φ : ModGL τ L →* ModGL τ L := iterHom S.D.step m with hφdef
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * m)
  have hσc : ∀ c, σ c = c ^ (S.D.q ^ m) := by
    intro c
    have h1 : σ c = iterateFrobenius L r (e * m) c := by
      rw [← hσ]
      rfl
    rw [h1, iterateFrobenius_def, hq, ← pow_mul]
  set χ := pairChar β with hχ
  have hker : kernelRoots χ = {β, -β} := kernelRoots_pairChar hβ hlen
  have hβk : β ∈ kernelRoots χ := by rw [hker]; exact Or.inl rfl
  set i : KernelComponent χ := ⟦⟨β, hβk⟩⟧ with hi
  have hcomp : componentRoots χ i = {β, -β} := componentRoots_pairChar hβ hlen hβk
  obtain ⟨w, hw, hwβ, hwnβ⟩ : ∃ w : WeylGroup τ,
      w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots χ i, s = rootReflection γ} ∧
      (S.ρ : (Fin τ.rank → ℤ) → _)^[m] β = w • β ∧
      (S.ρ : (Fin τ.rank → ℤ) → _)^[m] (-β) = w • (-β) := by
    rcases hρ with h | h
    · exact ⟨1, one_mem _, by rw [one_smul]; exact h, by rw [one_smul, rho_iterate_neg, h]⟩
    · refine ⟨rootReflection β, Subgroup.subset_closure ⟨β, by rw [hcomp]; exact Or.inl rfl, rfl⟩,
        ?_, ?_⟩
      · rw [h, rootReflection_smul_self hβ]
      · rw [rho_iterate_neg, h, smul_neg, rootReflection_smul_self hβ]
  have hφpin : ∀ γ ∈ componentRoots χ i, ∃ m' : L, m' ≠ 0 ∧
      ∀ c : L, φ (pinnedX τ L γ c) = pinnedX τ L (w • γ) (m' * σ c) := by
    intro γ hγ
    rw [hcomp] at hγ
    have hγr : IsRoot τ γ := by
      rcases hγ with rfl | hγ
      · exact hβ
      · rw [Set.mem_singleton_iff.1 hγ]; exact IsRoot.neg hβ
    have hργ : (S.ρ : (Fin τ.rank → ℤ) → _)^[m] γ = w • γ := by
      rcases hγ with rfl | hγ
      · exact hwβ
      · rw [Set.mem_singleton_iff.1 hγ]; exact hwnβ
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S m hγr
    refine ⟨μ, hμ0, fun c => ?_⟩
    rw [hφdef, iterHom_eq_iterate, hμ, hργ, hσc]
  obtain ⟨y, hy, hpin⟩ := exists_pin i σ φ hw hφpin
  rw [hcomp] at hy hpin
  have hρker : ∀ γ ∈ kernelRoots χ, (S.ρ : (Fin τ.rank → ℤ) → _)^[m] γ ∈ kernelRoots χ := by
    intro γ hγ
    rw [hker] at hγ ⊢
    rcases hγ with rfl | hγ
    · rcases hρ with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rw [Set.mem_singleton_iff.1 hγ, rho_iterate_neg]
      rcases hρ with h | h
      · rw [h]; exact Or.inr rfl
      · rw [h, neg_neg]; exact Or.inl rfl
  obtain ⟨z, hzZ, hφz⟩ := exists_lang_torus_sup_kernelRoots S hm hρker (by rw [hker]; exact hy)
  replace hφz : φ z = z * y := hφz
  refine ⟨σ, z, hσc, by rw [hker] at hzZ; exact hzZ, fun g hg => ?_⟩
  rw [map_mul, map_mul, map_inv, hφz]
  have := hpin g hg
  calc z * y * φ g * (z * y)⁻¹ = z * (y * φ g * y⁻¹) * z⁻¹ := by group
    _ = z * frobGL σ g * z⁻¹ := by rw [this]

end Untwist

end CFSG.HardMathSupport.Timmesfeld.LangTorus
