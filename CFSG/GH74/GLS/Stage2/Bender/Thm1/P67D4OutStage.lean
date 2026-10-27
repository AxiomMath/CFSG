module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Toral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MonoNF

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def D4OuterThreeA2Toral : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 1 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ d : Kˣ, Units.map σ.toRingHom.toMonoidHom d = d → d ^ 3 = 1 → d ≠ 1 →
    ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] →
        D4Out (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)

@[expose] def D4OuterThreeEll : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 1 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom →
      (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom →
      normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1 →
        D4Out (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ)

@[expose] def D4OuterThreeMinus : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), orderOf φ = 3 →
      φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
      (¬ ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ = fieldActor (t := TwistTag.D4) σ σ ∨
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹) →
      D4Out φ

theorem d4_fieldActor_pow_three {p f : ℕ} (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
  rw [hσ3, map_one] at h
  exact h.symm

theorem d4_stage_cocycle (hA2 : D4OuterThreeA2Toral)
    (hEll : D4OuterThreeEll)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1)
    (hnot : ¬ ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj y)⁻¹ =
        fieldActor (t := TwistTag.D4) σ σ) :
    D4Out (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) := by
  have hmono := CFSG.GH74.GLS.Stage2.Bender.Thm1.d4MonoNF
  classical
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  obtain ⟨y₀, n₀, hn₀, hy₀⟩ := hmono p f hp hp2 hp3 hf hq K hK σ hσ g hg
  have hcube : (MulAut.conj n₀ * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hy₀, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  have hN₀ := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
  by_cases htor : (n₀ : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · obtain ⟨t, s, hs, hs3, hts, d, hd, hd3, hsd⟩ := d4_toral_conj hp hp2 hf K hK σ hσ n₀ htor hN₀
    have hconj : MulAut.conj (t * y₀) * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
        (MulAut.conj (t * y₀))⁻¹ = MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ := by
      rw [← hts, ← hy₀, map_mul]
      group
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [map_one, one_mul] at hconj
      exact hnot ⟨t * y₀, hconj⟩
    have hd1 : d ≠ 1 := by
      rintro rfl
      apply hs1
      apply Subtype.ext
      have h1 : (![1, 1, 1, 1] : Fin TwistTag.D4.tag.rank → Kˣ) =
          (1 : Fin TwistTag.D4.tag.rank → Kˣ) := funext fun i => by fin_cases i <;> rfl
      rw [hsd, h1, rootDiagUnit_one]
      rfl
    exact (hA2 p f hp hp2 hp3 hf hq K hK σ hσ d hd hd3 hd1 s hsd).of_conj_eq _ hconj
  · exact (hEll p f hp hp2 hp3 hf hq K hK σ hσ n₀ hn₀ htor hN₀).of_conj_eq _ hy₀

theorem d4Rest_of_stages (hA2 : D4OuterThreeA2Toral)
    (hEll : D4OuterThreeEll) (hMinus : D4OuterThreeMinus) : D4OuterThreeRest := by
  intro p f hp hp2 hp3 hf K _ _ hK σ hσ φ hφord hφout hconj
  have hq3 : ¬ 3 ∣ p ^ f := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq12 : (p ^ f) % 3 = 1 ∨ (p ^ f) % 3 = 2 := by omega
  rcases hq12 with hq | hq
  · obtain ⟨g, hg, hφ | hφ⟩ := d4_outer_three_normal_form hp hp2 hf K hK σ hσ φ hφord hφout
    · rw [hφ]
      refine d4_stage_cocycle hA2 hEll hp hp2 hp3 hf hq K hK σ hσ g hg ?_
      rintro ⟨y, hy⟩
      refine hconj ⟨y, Or.inl ?_⟩
      rw [hφ]
      exact hy
    · have h1 : D4Out (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) := by
        refine d4_stage_cocycle hA2 hEll hp hp2 hp3 hf hq K hK σ hσ g hg ?_
        rintro ⟨y, hy⟩
        rw [← hφ] at hy
        refine hconj ⟨y, Or.inr ?_⟩
        calc MulAut.conj y * φ * (MulAut.conj y)⁻¹
            = (MulAut.conj y * φ⁻¹ * (MulAut.conj y)⁻¹)⁻¹ := by group
          _ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹ := by rw [hy]
      rw [← hφ] at h1
      have h2 := h1.inv
      rwa [inv_inv] at h2
  · exact hMinus p f hp hp2 hp3 hf hq K hK σ hσ φ hφord hφout hconj

theorem d4OuterThree_of_stages (hG2 : D4OuterThreeG2)
    (hA2 : D4OuterThreeA2Toral) (hEll : D4OuterThreeEll) (hMinus : D4OuterThreeMinus) :
    D4OuterThree :=
  d4OuterThree_of_G2_rest hG2 (d4Rest_of_stages hA2 hEll hMinus)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
