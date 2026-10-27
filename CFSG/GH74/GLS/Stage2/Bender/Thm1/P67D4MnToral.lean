module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MinusStmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFrame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnH90
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutG2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem d4Minus_out_of_toral (hA2m : D4OuterThreeA2Minus) {p f : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L p] {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    (t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (ht : d4MinusPsi σ L g₀ t ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L p f)))
    (hcoc : t * fieldActor (t := TwistTag.D4) σ σ t *
      fieldActor (t := TwistTag.D4) σ σ (fieldActor (t := TwistTag.D4) σ σ t) = 1) :
    D4Out (MulAut.conj t * fieldActor (t := TwistTag.D4) σ σ) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := id hg₀
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  have hcoc' : d4MinusPsi σ L g₀ t *
      ((diagramMap TwistTag.D4 L)⁻¹ * d4MinusPsi σ L g₀ t * diagramMap TwistTag.D4 L) *
      ((diagramMap TwistTag.D4 L)⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * d4MinusPsi σ L g₀ t *
        diagramMap TwistTag.D4 L) * diagramMap TwistTag.D4 L) = 1 := by
    have := congrArg (d4MinusPsi σ L g₀) hcoc
    simpa only [map_mul, d4MinusPsi_fieldActor Fr hcomm hg₀P, map_one] using this
  obtain ⟨e, he, b, hb3, -, hrel⟩ :=
    d4Minus_torus_h1 (dvd_pow_self p (by omega) : p ∣ p ^ f) Fr hFr ht hcoc'
  obtain ⟨y₁, hy₁⟩ := (d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F e).2
    ⟨twistedTorusOf_le_adjointGroup _ _ he, (mem_twistedTorusOf.1 he).2⟩
  set δ := fieldActor (t := TwistTag.D4) σ σ with hδ
  have hψs : d4MinusPsi σ L g₀ (y₁ * t * (δ y₁)⁻¹) =
      rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] := by
    rw [map_mul, map_mul, map_inv, hy₁, hδ, d4MinusPsi_fieldActor Fr hcomm hg₀P, hy₁]
    exact hrel
  have hconj := conj_twist_eq δ y₁ t
  by_cases hb1 : b = 1
  ·
    have hs1 : y₁ * t * (δ y₁)⁻¹ = 1 := by
      apply d4MinusPsi_injective g₀
      have h1 : (![1, 1, b, 1] : Fin TwistTag.D4.tag.rank → Lˣ) = 1 := by
        rw [hb1]
        funext i
        fin_cases i <;> rfl
      rw [hψs, h1]
      exact (rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)).trans (map_one _).symm
    rw [hs1, map_one, one_mul] at hconj
    exact (d4OuterThreeG2_thm p f hp hp2 hp3 hf K hK σ hσ).of_conj_eq _ hconj
  ·
    have hs : D4MinusToral p f hp K σ (y₁ * t * (δ y₁)⁻¹) := by
      have h := hψs
      rw [d4MinusPsi_apply] at h
      refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, g₀, b, hg₀, hb3,
        hb1, ?_⟩
      calc triEmb K σ L (y₁ * t * (δ y₁)⁻¹) =
          g₀ * (g₀⁻¹ * triEmb K σ L (y₁ * t * (δ y₁)⁻¹) * g₀) * g₀⁻¹ := by group
        _ = _ := by rw [h]
    exact (hA2m p f hp hp2 hp3 hf hq K hK σ hσ _ hs).of_conj_eq _ hconj

end CFSG.GH74.GLS.Stage2.Bender.Thm1
