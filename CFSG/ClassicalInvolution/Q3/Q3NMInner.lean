module

public import CFSG.ClassicalInvolution.Q3.Q3NMAut
public import CFSG.ClassicalInvolution.Q3.Q3TJD4

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank

theorem center_quotient_center_eq_bot_of_isQuasisimple {X : Type} [Group X]
    (hX : CFSG.Open.IsQuasisimple X) : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
  have hs : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (X ⧸ Subgroup.center X)) with h1 | h1
  · exact h1
  · exfalso
    have hcomm : ∀ a b : X ⧸ Subgroup.center X, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top a) b).symm
    have hle : commutator X ≤ Subgroup.center X := by
      rw [commutator, Subgroup.commutator_le]
      intro x _ y _
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    have htop : (⊤ : Subgroup X) ≤ Subgroup.center X := hX.1 ▸ hle
    obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : X ⧸ Subgroup.center X)).mp hs.toNontrivial
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    exact ha ((QuotientGroup.eq_one_iff x).mpr (htop (Subgroup.mem_top x)))

section Rows


@[expose] def AutOddFreeInnerTag (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (hp : Nat.Prime 3), IsFundTag t → StatedLieAdmissible t n 3 1 →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n 3 1 hp).K →* X),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center _ → AutOddFreeInner X

@[expose] def AutOddFreeTag (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (hp : Nat.Prime 3), IsFundTag t → StatedLieAdmissible t n 3 1 →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n 3 1 hp).K →* X),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center _ → AutOddFree X

theorem centralQuotientData {t : StatedLieTag} {n : ℕ} (hp : Nat.Prime 3) (hFT : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (X : Type) [Group X]
    (ψ : (modelUniv t n 3 1 hp).K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center _) :
    CFSG.Open.IsQuasisimple X ∧
      Function.Surjective ((QuotientGroup.mk' (Subgroup.center X)).comp ψ) ∧
      ((QuotientGroup.mk' (Subgroup.center X)).comp ψ).ker ≤
        Subgroup.center (modelUniv t n 3 1 hp).K ∧
      CFSG.Open.IsQuasisimple (X ⧸ Subgroup.center X) ∧
        Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
  have hKq : CFSG.Open.IsQuasisimple (modelUniv t n 3 1 hp).K :=
    (ModelFacts.modelClauseZero t n 3 1 hp hFT hadm).1
  have hXq : CFSG.Open.IsQuasisimple X := isQuasisimple_of_centralQuotient hKq ψ hψ hker
  have : Group.IsPerfect (modelUniv t n 3 1 hp).K := ⟨hKq.1⟩
  set π := QuotientGroup.mk' (Subgroup.center X) with hπ
  set ψ' := π.comp ψ with hψ'def
  have hψ' : Function.Surjective ψ' := (QuotientGroup.mk'_surjective _).comp hψ
  have hker' : ψ'.ker ≤ Subgroup.center (modelUniv t n 3 1 hp).K := by
    intro k hk
    have hcen := center_le_map_center_of_perfect ψ hψ hker
    have h1 : ψ k ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).mp hk
    obtain ⟨c, hc, hck⟩ := hcen h1
    have h2 : c⁻¹ * k ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hck, inv_mul_cancel]
    have h3 : k = c * (c⁻¹ * k) := by group
    rw [h3]
    exact mul_mem hc (hker h2)
  exact ⟨hXq, hψ', hker', isQuasisimple_of_centralQuotient hKq ψ' hψ' hker',
    center_quotient_center_eq_bot_of_isQuasisimple hXq⟩

theorem autOddFreeInnerTag_of_oddAut {t : StatedLieTag} {n : ℕ}
    (hodd : ∀ (hp : Nat.Prime 3), IsFundTag t → StatedLieAdmissible t n 3 1 →
      ∀ (S : Type) [Group S] [Finite S], CFSG.Open.IsQuasisimple S → Subgroup.center S = ⊥ →
        ∀ f : (modelUniv t n 3 1 hp).K →* S, Function.Surjective f →
          f.ker ≤ Subgroup.center _ → ∀ s : S, orderOf s = 2 → ∀ α : MulAut S,
            Odd (orderOf α) → (∀ x ∈ Subgroup.centralizer ({s} : Set S), α x = x) →
              α ∈ innSubgroup S) :
    AutOddFreeInnerTag t n := by
  intro hp hFT hadm X _ _ ψ hψ hker
  obtain ⟨hXq, hψ', hker', hSq, hZS⟩ := centralQuotientData hp hFT hadm X ψ hψ hker
  have : Group.IsPerfect X := ⟨hXq.1⟩
  have hKq : CFSG.Open.IsQuasisimple (modelUniv t n 3 1 hp).K :=
    (ModelFacts.modelClauseZero t n 3 1 hp hFT hadm).1
  have : Group.IsPerfect (modelUniv t n 3 1 hp).K := ⟨hKq.1⟩
  refine autOddFreeInner_of_centralQuotient ?_
  exact autOddFreeInner_of_centralizing_inner hZS
    (fun x hx => modelOddCentralizerFree3_proved t n hp hFT hadm _ _ hψ' hker' x hx)
    (hodd hp hFT hadm _ hSq hZS _ hψ' hker')

theorem oddAut_inner_centralQuotient {t : StatedLieTag} {n : ℕ}
    (hD4 : ¬ (t = .POmegaPlus ∧ n = 4)) (hT : t ≠ .trialityD4) (hp : Nat.Prime 3)
    (hFT : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (X : Type) [Group X] [Finite X]
    (ψ : (modelUniv t n 3 1 hp).K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center _) :
    ∀ α : MulAut (X ⧸ Subgroup.center X), Odd (orderOf α) →
      α ∈ innSubgroup (X ⧸ Subgroup.center X) := by
  obtain ⟨_, hψ', hker', hSq, hZS⟩ := centralQuotientData hp hFT hadm X ψ hψ hker
  intro α hα
  rcases Q3T.steinbergOddAut3_of_PSU Q3T.steinbergOddAut3PSU_proved t n hFT hadm
    (X ⧸ Subgroup.center X) hSq hZS _ hψ' hker' α hα with ⟨g, hg⟩ | h | h
  · exact ⟨g, hg.symm⟩
  · exact absurd h hD4
  · exact absurd h hT

theorem autOddFreeInnerTag_of_not_D4 {t : StatedLieTag} {n : ℕ}
    (hD4 : ¬ (t = .POmegaPlus ∧ n = 4)) (hT : t ≠ .trialityD4) : AutOddFreeInnerTag t n :=
  autOddFreeInnerTag_of_oddAut fun hp hFT hadm S _ _ hSq hZ f hf hker _ _ α hα _ => by
    rcases Q3T.steinbergOddAut3_of_PSU Q3T.steinbergOddAut3PSU_proved t n hFT hadm S hSq hZ f hf
      hker α hα with ⟨g, hg⟩ | h | h
    · exact ⟨g, hg.symm⟩
    · exact absurd h hD4
    · exact absurd h hT

theorem autOddFreeInnerTag_trialityD4 : AutOddFreeInnerTag .trialityD4 0 :=
  autOddFreeInnerTag_of_oddAut fun hp _ _ S _ _ _ _ f hf hker s hs α _ hcent => by
    have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [exc3_center_trialityD4 0 hp] at hker
      exact le_bot_iff.mp hker
    obtain ⟨g, hg⟩ := Q3T.eq_conj_of_centralizes_td4 (MulEquiv.ofBijective f ⟨hinj, hf⟩) hs α hcent
    exact ⟨g, hg.symm⟩

theorem autOddFreeInnerOn_D4 {S : Type} [Group S] [Finite S] (hSq : CFSG.Open.IsQuasisimple S)
    (hZ : Subgroup.center S = ⊥) (f : (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →* S)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center _) :
    AutOddFreeInnerOn S (fun s => ∃ K : Subgroup S, IsClassicalMember3 K s) := by
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  refine autOddFreeInnerOn_of_centralizing_inner _ hZ
    (fun x _ hx => modelOddCentralizerFree3_proved .POmegaPlus 4 Nat.prime_three trivial hadm S
      f hf hker x hx) ?_
  rintro s ⟨K, hK⟩ _ α hα hcent
  obtain ⟨g, hg⟩ := Q3T.d4OddAutInner3_proved S hSq hZ f hf hker s K hK α hα fun c hc => by
    rw [hcent c hc, inv_mul_cancel]
    exact one_mem _
  exact ⟨g, hg.symm⟩

end Rows

end CFSG.ClassicalInvolution.Q3.Q3NM
