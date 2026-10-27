module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KGD CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def D4MinusFrame (p f : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharP L p]
    (g₀ : ModGL TwistTag.D4.tag L) : Prop :=
  g₀ ∈ adjointGroup TwistTag.D4.tag L ∧
    diagramMap TwistTag.D4 L * g₀ = g₀ * diagramMap TwistTag.D4 L ∧
    twistHom TwistTag.D4 L (iterateFrobenius L p f) g₀ = g₀ * trialityOpposition L

@[expose] def D4MinusToral (p f : ℕ) (hp : p.Prime) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Prop :=
  haveI : Fact p.Prime := ⟨hp⟩
  ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : IsAlgClosure K L) (_ : CharP L p)
    (g₀ : ModGL TwistTag.D4.tag L) (b : Lˣ), D4MinusFrame p f L g₀ ∧ b ^ 3 = 1 ∧ b ≠ 1 ∧
      triEmb K σ L s = g₀ * rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] * g₀⁻¹

@[expose] def D4MinusElliptic (p f : ℕ) (hp : p.Prime) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Prop :=
  haveI : Fact p.Prime := ⟨hp⟩
  ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : IsAlgClosure K L) (_ : CharP L p)
    (g₀ : ModGL TwistTag.D4.tag L), D4MinusFrame p f L g₀ ∧
      g₀⁻¹ * triEmb K σ L n * g₀ ∈ monomialSubgroup TwistTag.D4.tag L ∧
      g₀⁻¹ * triEmb K σ L n * g₀ ∉ torusGroup TwistTag.D4.tag L

@[expose] def D4MinusNF : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime), p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1 →
      (∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj y)⁻¹ = fieldActor (t := TwistTag.D4) σ σ) ∨
      (∃ y s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        D4MinusToral p f hp K σ s ∧
        MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj y)⁻¹ = MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) ∨
      (∃ y n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        D4MinusElliptic p f hp K σ n ∧
        MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj y)⁻¹ = MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ)

@[expose] def D4OuterThreeA2Minus : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime), p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      D4MinusToral p f hp K σ s →
        D4Out (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)

@[expose] def D4OuterThreeEllMinus : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime), p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      D4MinusElliptic p f hp K σ n →
      normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1 →
        D4Out (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ)

theorem d4Minus_cocycle (hnf : D4MinusNF) (hA2 : D4OuterThreeA2Minus)
    (hEll : D4OuterThreeEllMinus) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1)
    (hnot : ¬ ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj y)⁻¹ = fieldActor (t := TwistTag.D4) σ σ ∨
        MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj y)⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹) :
    D4Out (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) := by
  classical
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  rcases hnf p f hp hp2 hp3 hf hq K hK σ hσ g hg with ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ |
      ⟨y, n, hn, hyn⟩
  · exact absurd ⟨y, Or.inl hy⟩ hnot
  · exact (hA2 p f hp hp2 hp3 hf hq K hK σ hσ s hs).of_conj_eq _ hys
  · have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
      rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
      exact mul_inv_cancel _
    have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
    exact (hEll p f hp hp2 hp3 hf hq K hK σ hσ n hn hN).of_conj_eq _ hyn

theorem d4Minus_of_stages (hnf : D4MinusNF) (hA2 : D4OuterThreeA2Minus)
    (hEll : D4OuterThreeEllMinus) : D4OuterThreeMinus := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ φ hφord hφout hconj
  obtain ⟨g, hg, hφ | hφ⟩ := d4_outer_three_normal_form hp hp2 hf K hK σ hσ φ hφord hφout
  · rw [hφ]
    refine d4Minus_cocycle hnf hA2 hEll hp hp2 hp3 hf hq K hK σ hσ g hg ?_
    rintro ⟨y, hy⟩
    refine hconj ⟨y, ?_⟩
    rw [hφ]
    exact hy
  · have h1 : D4Out (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) := by
      refine d4Minus_cocycle hnf hA2 hEll hp hp2 hp3 hf hq K hK σ hσ g hg ?_
      rintro ⟨y, hy⟩
      rw [← hφ] at hy
      refine hconj ⟨y, ?_⟩
      rcases hy with h | h
      · right
        calc MulAut.conj y * φ * (MulAut.conj y)⁻¹
            = (MulAut.conj y * φ⁻¹ * (MulAut.conj y)⁻¹)⁻¹ := by group
          _ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹ := by rw [h]
      · left
        calc MulAut.conj y * φ * (MulAut.conj y)⁻¹
            = (MulAut.conj y * φ⁻¹ * (MulAut.conj y)⁻¹)⁻¹ := by group
          _ = fieldActor (t := TwistTag.D4) σ σ := by rw [h, inv_inv]
    rw [← hφ] at h1
    have h2 := h1.inv
    rwa [inv_inv] at h2

end CFSG.GH74.GLS.Stage2.Bender.Thm1
