module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1Comp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Conj
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4OddCore
public import CFSG.LieType.HighestRoot.CentTrialityThree
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Galois

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E1

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.Foote5.OddLieCore (oddFixed)

open scoped MatrixGroups


theorem triality_slB_component {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx : orderOf x = 2) :
    ∃ (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (ψ : SL(2, K) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Function.Injective ψ ∧
      (∀ C : SL(2, K), (ψ C : ModGL TwistTag.D4.tag K) =
        (c : ModGL TwistTag.D4.tag K)⁻¹ * twistedIncl σ.toRingHom (slB σ.toRingHom hσ3 C) *
          (c : ModGL TwistTag.D4.tag K)) ∧
      GorensteinWalter.IsComponentOf ψ.range (oddFixed (MulAut.conj x)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hD : D4Data K σ.toRingHom (p ^ f) := ⟨hodd, hK, hσ⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  let ι : twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (MonoidHom.ofInjective (twistedIncl_injective σ.toRingHom)).trans
      (MulEquiv.subgroupCongr hD.range)
  have hι : ∀ y, (ι y : ModGL TwistTag.D4.tag K) = twistedIncl σ.toRingHom y := fun _ => rfl
  obtain ⟨c, hc⟩ := exists_conj_eq_aLong hp hp2 hf hK σ hσ x hx
  have htι : ι (τL hσ3) = c * x * c⁻¹ :=
    Subtype.ext (by rw [hι, twistedIncl_slLong_neg_one hσ3, hc])
  set φ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* twistedGroup σ.toRingHom :=
    ι.symm.toMonoidHom.comp (MulAut.conj c).toMonoidHom with hφ
  have hφi : Function.Injective φ := ι.symm.injective.comp (MulAut.conj c).injective
  have key : ∀ s, φ s * τL hσ3 = τL hσ3 * φ s ↔ s * x = x * s := by
    intro s
    have hτ : τL hσ3 = ι.symm (c * x * c⁻¹) := by rw [← htι, MulEquiv.symm_apply_apply]
    rw [hτ]
    simp only [hφ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [← map_mul, ← map_mul, ι.symm.injective.eq_iff]
    have e1 : c * s * c⁻¹ * (c * x * c⁻¹) = c * (s * x) * c⁻¹ := by group
    have e2 : c * x * c⁻¹ * (c * s * c⁻¹) = c * (x * s) * c⁻¹ := by group
    rw [e1, e2]
    constructor
    · intro h
      exact mul_left_cancel (mul_right_cancel h)
    · intro h
      rw [h]
  have hmap : (fixedSubgroup (MulAut.conj x)).map φ =
      centralizer ({τL hσ3} : Set (twistedGroup σ.toRingHom)) := by
    ext y
    rw [mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have h1 : x * s * x⁻¹ = s := hs
      refine (key s).2 ?_
      calc s * x = x * s * x⁻¹ * x := by rw [h1]
        _ = x * s := by group
    · intro hy
      obtain ⟨s, rfl⟩ : ∃ s, φ s = y := by
        refine ⟨(MulAut.conj c).symm (ι y), ?_⟩
        show ι.symm ((MulAut.conj c) ((MulAut.conj c).symm (ι y))) = y
        rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
      refine ⟨s, ?_, rfl⟩
      have h2 := (key s).1 hy
      show x * s * x⁻¹ = s
      rw [← h2]
      group
  set B := (slB σ.toRingHom hσ3).range with hB
  have hBle : B ≤ centralizer ({τL hσ3} : Set (twistedGroup σ.toRingHom)) := by
    rintro _ ⟨C, rfl⟩
    exact slB_mem_cent hσ3 C
  have hBn : (B.subgroupOf (centralizer ({τL hσ3} : Set (twistedGroup σ.toRingHom)))).Normal := by
    refine ⟨fun n hn y => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨C, hC⟩ := hn
    have hy : (y : twistedGroup σ.toRingHom) * slLong σ.toRingHom hσ3 (-1) =
        slLong σ.toRingHom hσ3 (-1) * y := mem_centralizer_singleton_iff.1 y.2
    have hyS := mem_SProd_of_centralizes hσ3 hD.neg_one hD.hC₀ hD.hgF hy
    obtain ⟨C', hC'⟩ := SProd_conj_slB hσ3 hyS C
    refine ⟨C', ?_⟩
    simp only [coe_mul, coe_inv, ← hC, hC']
  have h4 : 4 ≤ Nat.card K := by
    have h3 : 3 ≤ p ^ f := by
      have := hp.two_le
      have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      omega
    rw [hK]
    calc 4 ≤ 3 ^ 3 := by norm_num
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left h3 3
  have hBq : GorensteinWalter.IsQuasisimple B :=
    gw_isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (slB_injective hσ3))
      (gw_isQuasisimple_of_isQuasisimple (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4))
  obtain ⟨hcomp, -⟩ := isComponentOf_oddFixed_of_map (MulAut.conj x) φ hφi hmap hBle
    hBn.isSubnormal hBq
  set ψ : SL(2, K) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    ((MulAut.conj c).symm.toMonoidHom.comp ι.toMonoidHom).comp (slB σ.toRingHom hσ3) with hψ
  have hφψ : ∀ C, φ (ψ C) = slB σ.toRingHom hσ3 C := fun C => by
    show ι.symm ((MulAut.conj c) ((MulAut.conj c).symm (ι (slB σ.toRingHom hσ3 C)))) = _
    rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  have hrange : ψ.range = B.comap φ := by
    ext s
    constructor
    · rintro ⟨C, rfl⟩
      exact ⟨C, (hφψ C).symm⟩
    · rintro ⟨C, hC⟩
      exact ⟨C, hφi (by rw [hφψ, hC])⟩
  refine ⟨c, ψ, ?_, fun C => ?_, hrange ▸ hcomp⟩
  · exact ((MulAut.conj c).symm.injective.comp ι.injective).comp (slB_injective hσ3)
  · show (((MulAut.conj c).symm (ι (slB σ.toRingHom hσ3 C)) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) = _
    rw [MulAut.conj_symm_apply, coe_mul, coe_mul, coe_inv, hι]

end CFSG.ComponentClassification.HarrisLit.L33.SR.E1
