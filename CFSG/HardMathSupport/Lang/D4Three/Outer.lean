module

public import CFSG.HardMathSupport.Lang.E27Lie.TrialityAll

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)



variable {K : Type} [Field K] [Finite K]

theorem sigma_ne_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ≠ 1 := by
  intro h
  have hc := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hp hf hK σ hσ
  have htop : fixSubfield σ = ⊤ := by
    ext c
    simp [h]
  rw [htop] at hc
  have hc' : Nat.card K = p ^ f := by
    rw [← hc]
    exact (Nat.card_congr Subfield.topEquiv.toEquiv).symm
  have hp1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  rw [hK] at hc'
  nlinarith [hp1, pow_pos (lt_trans Nat.zero_lt_one hp1) 2]

theorem sigma_cube {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ^ 3 = 1 := by
  ext c
  exact ringEquiv_cube_apply_eq hK hσ c

theorem fieldActor_cube {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) :
    fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
  have h1 : fieldActor (t := TwistTag.D4) σ (σ ^ 3) = fieldActor σ σ ^ 3 :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
  rw [← h1, hσ3, fieldActor_one]

theorem exists_theta {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    (∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) ∧
    Nonempty (DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ.toRingHom) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -, -, -, -, he⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact ⟨⟨Θ, hΘ, hker⟩, he⟩
  · obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -, -, -, -, he⟩ :=
      odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
    exact ⟨⟨Θ, hΘ, hker⟩, he⟩

theorem fieldActor_not_inner {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    fieldActor (t := TwistTag.D4) σ σ ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨⟨Θ, hΘ, hker⟩, -⟩ := exists_theta hp hf hK σ hσ
  intro hin
  have h1 : Θ (fieldActor (t := TwistTag.D4) σ σ) = σ :=
    hΘ _ 1 σ (by rw [map_one, one_mul])
  have h2 : fieldActor (t := TwistTag.D4) σ σ ∈ Θ.ker := by rw [hker]; exact hin
  rw [MonoidHom.mem_ker] at h2
  exact sigma_ne_one hp hf hK σ hσ (h1.symm.trans h2)

theorem model_graphFixedRootGroup {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    TwistedChevalleyModel (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) .D4 (p ^ f) := by
  obtain ⟨-, ⟨e⟩⟩ := exists_theta hp hf hK σ hσ
  exact ⟨K, inferInstance, inferInstance, hK, σ.toRingHom, hσ, ⟨e.symm⟩⟩

theorem twentySeven_dvd_fixedSubgroup_graphFixed {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    27 ∣ Nat.card (fixedSubgroup α) :=
  CFSG.HardMathSupport.Lang.E27Lie.twentySeven_dvd_fixedSubgroup_trialityD4_model hp hf _
    (model_graphFixedRootGroup hp hf hK σ hσ) α hα3 hαin

end CFSG.HardMathSupport.Lang.D4Three
