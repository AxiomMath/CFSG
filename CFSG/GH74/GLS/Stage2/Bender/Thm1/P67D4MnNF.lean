module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSub

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section NF

theorem d4Minus_hcomm {p f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    {L : Type} [Field L] [Algebra K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (p ^ f)) :
    (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
  RingHom.ext fun c => by simp [hσ, hFr, map_pow]

theorem d4Minus_nf_aux {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L p]
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1) :
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
        (MulAut.conj y)⁻¹ = MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨g₀, hg₀C, hg₀P, hg₀F⟩ := d4Minus_exists_frame (L := L) p hp2 hf
  have hg₀ : D4MinusFrame p f L g₀ := ⟨hg₀C, hg₀P, hg₀F⟩
  obtain ⟨N, hidx, hstab, hprop⟩ := d4Minus_exists_N hf hq hK hσ hg₀
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm := d4Minus_hcomm hσ Fr hFr
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hα : ∀ y, fieldActor (t := TwistTag.D4) σ σ
      (fieldActor (t := TwistTag.D4) σ σ (fieldActor (t := TwistTag.D4) σ σ y)) = y :=
    fun y => by
      have := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) => φ y) hψ3
      simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at this
      exact this
  have hnorm3 : ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      normSeq (fieldActor (t := TwistTag.D4) σ σ) x 3 = x * fieldActor (t := TwistTag.D4) σ σ x *
        fieldActor (t := TwistTag.D4) σ σ (fieldActor (t := TwistTag.D4) σ σ x) := fun x => by
    simp only [normSeq, pow_two, MulAut.mul_apply, MulAut.one_apply, pow_zero, pow_one, one_mul]
  have hg' : g * fieldActor (t := TwistTag.D4) σ σ g *
      fieldActor (t := TwistTag.D4) σ σ (fieldActor (t := TwistTag.D4) σ σ g) = 1 := by
    rw [← hnorm3]
    exact hg
  obtain ⟨y, n, hnN, hyn⟩ := exists_conj_mem_of_index_not_dvd
    (fieldActor (t := TwistTag.D4) σ σ) hα N hstab hidx g hg'
  have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  have hn3 := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
  have hn3' : n * fieldActor (t := TwistTag.D4) σ σ n *
      fieldActor (t := TwistTag.D4) σ σ (fieldActor (t := TwistTag.D4) σ σ n) = 1 := by
    rw [← hnorm3]
    exact hn3
  obtain ⟨hnM, hnT⟩ := hprop n hnN
  by_cases htor : d4MinusPsi σ L g₀ n ∈ torusGroup TwistTag.D4.tag L
  · have hT0 := hnT htor
    have hcoc : d4MinusPsi σ L g₀ n *
        ((diagramMap TwistTag.D4 L)⁻¹ * d4MinusPsi σ L g₀ n * diagramMap TwistTag.D4 L) *
        ((diagramMap TwistTag.D4 L)⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * d4MinusPsi σ L g₀ n *
          diagramMap TwistTag.D4 L) * diagramMap TwistTag.D4 L) = 1 := by
      have := congrArg (d4MinusPsi σ L g₀) hn3'
      simpa only [map_mul, d4MinusPsi_fieldActor Fr hcomm hg₀P, map_one] using this
    obtain ⟨e, he, b, hb3, -, hrel⟩ := d4Minus_torus_h1 (dvd_pow_self p (by omega) : p ∣ p ^ f) Fr
      hFr hT0 hcoc
    obtain ⟨y₁, hy₁⟩ := (d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F e).2
      ⟨twistedTorusOf_le_adjointGroup _ _ he, (mem_twistedTorusOf.1 he).2⟩
    set δ := fieldActor (t := TwistTag.D4) σ σ with hδ
    have hψs : d4MinusPsi σ L g₀ (y₁ * n * (δ y₁)⁻¹) =
        rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] := by
      rw [map_mul, map_mul, map_inv, hy₁, hδ, d4MinusPsi_fieldActor Fr hcomm hg₀P, hy₁]
      exact hrel
    have hconj : MulAut.conj (y₁ * y) * (MulAut.conj g * δ) * (MulAut.conj (y₁ * y))⁻¹ =
        MulAut.conj (y₁ * n * (δ y₁)⁻¹) * δ := by
      have e1 : MulAut.conj (y₁ * y) * (MulAut.conj g * δ) * (MulAut.conj (y₁ * y))⁻¹ =
          MulAut.conj y₁ * (MulAut.conj y * (MulAut.conj g * δ) * (MulAut.conj y)⁻¹) *
            (MulAut.conj y₁)⁻¹ := by
        rw [map_mul]
        group
      rw [e1, hyn, conj_twist_eq]
    by_cases hb1 : b = 1
    · left
      refine ⟨y₁ * y, ?_⟩
      have hs1 : y₁ * n * (δ y₁)⁻¹ = 1 := by
        apply d4MinusPsi_injective g₀
        have h1 : (![1, 1, b, 1] : Fin TwistTag.D4.tag.rank → Lˣ) = 1 := by
          rw [hb1]
          funext i
          fin_cases i <;> rfl
        rw [hψs, h1]
        exact (rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)).trans (map_one _).symm
      rw [hconj, hs1, map_one, one_mul]
    · right
      left
      refine ⟨y₁ * y, y₁ * n * (δ y₁)⁻¹, ⟨L, inferInstance, inferInstance, inferInstance,
        inferInstance, g₀, b, hg₀, hb3, hb1, ?_⟩, hconj⟩
      have h := hψs
      rw [d4MinusPsi_apply] at h
      calc triEmb K σ L (y₁ * n * (δ y₁)⁻¹) =
          g₀ * (g₀⁻¹ * triEmb K σ L (y₁ * n * (δ y₁)⁻¹) * g₀) * g₀⁻¹ := by group
        _ = _ := by rw [h]
  · right
    right
    refine ⟨y, n, ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, g₀, hg₀, ?_, ?_⟩,
      hyn⟩
    · rwa [d4MinusPsi_apply] at hnM
    · rwa [d4MinusPsi_apply] at htor

end NF

theorem d4MinusNF : D4MinusNF := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ g hg
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := by
    have : Fintype K := Fintype.ofFinite K
    have h : Fintype.card K = p ^ (f * 3) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]
    exact charP_of_card_eq_prime_pow h
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  exact d4Minus_nf_aux hp hp2 hf hq K hK σ hσ (AlgebraicClosure K) g hg

theorem d4OuterThreeMinus_of_leaves (hA2 : D4OuterThreeA2Minus) (hEll : D4OuterThreeEllMinus) :
    D4OuterThreeMinus :=
  d4Minus_of_stages d4MinusNF hA2 hEll

end CFSG.GH74.GLS.Stage2.Bender.Thm1
