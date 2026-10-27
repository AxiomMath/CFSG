module

public import CFSG.GH74.GLS.IVK.Lifted32.HypSetting
public import CFSG.GH74.GLS.IVK.Lifted.SLSign
import all CFSG.GH74.GLS.Stage1.Thm4.L97b
import all CFSG.GH74.GLS.Stage1.Thm4.L98b

public section

namespace CFSG.GH74.GLS.IVK.Lifted32

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm4 CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage2.Local (Cen toBar barOf)
open CFSG.GH74.GLS.Stage1.Thm2.Recip (II4_44 innOf Hat phi hatMk phi_mk phi_mul_self)
open scoped commutatorElement

namespace Hyp

section Dict

theorem stableAut_one {F : Type} [Field F] (g : IVK.SL2 F) :
    stableAut (StatedSL 2 F) (fieldStable_statedSL 2) 1 g = g :=
  Subtype.ext (Units.ext (by ext i j; rfl))

theorem stableAut_eq_slFieldAut' {F : Type} [Field F] [Finite F] (σ : F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    stableAut (StatedSL 2 F) (fieldStable_statedSL 2) σ (specialLinearGroupEquivStatedSL 2 F g) =
      specialLinearGroupEquivStatedSL 2 F (IVK.Lifted.slFieldAut σ g) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem dict_indFAut (h2A7 : IVK.Lifted.II4_2A7) {Q : Type} [Group Q] [Finite Q]
    (hO : IVK.Lifted.HatOK Q) (φ : MulAut Q) (hφ2 : φ * φ = 1) (hφ : IsFAutomorphism Q φ) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (e : Q ≃* IVK.SL2 F) (σ : F ≃+* F),
        ∀ x : Q, e (φ x) = stableAut (StatedSL 2 F) (fieldStable_statedSL 2) σ (e x)) ∨
      (IsDoubleCoverOfAlt Q 7 ∧ (φ = 1 ∨ φ ∉ innOf Q)) := by
  rcases IVK.Lifted.sl_or_a7 hO.sl2 with ⟨F, hFf, hFin, hodd, h3, ⟨eH⟩⟩ | h7
  · left
    have hfc : IVK.Lifted.FixedCond Q φ := hφ.2.2.2.2
    by_cases hφ1 : φ = 1
    · refine ⟨F, hFf, hFin, eH.trans (specialLinearGroupEquivStatedSL 2 F), 1, fun x => ?_⟩
      rw [hφ1, stableAut_one]
      rfl
    · by_cases hσ : (IVK.Lifted.gammaOf hodd h3 (MulAut.congr eH φ)).right = 1
      · exact absurd hfc (IVK.Lifted.not_fixedCond_of_right_eq_one hodd h3 eH φ hφ1 hσ)
      · have hα2 : MulAut.congr eH φ * MulAut.congr eH φ = 1 := by
          rw [← map_mul, hφ2, map_one]
        obtain ⟨β, hβ⟩ := IVK.Lifted.exists_conj_slFieldAut hodd h3 (MulAut.congr eH φ) hα2 hσ
        refine ⟨F, hFf, hFin, (eH.trans β⁻¹).trans (specialLinearGroupEquivStatedSL 2 F),
          (IVK.Lifted.gammaOf hodd h3 (MulAut.congr eH φ)).right, fun x => ?_⟩
        have h1 : (eH.trans β⁻¹) (φ x) =
            IVK.Lifted.slFieldAut (IVK.Lifted.gammaOf hodd h3 (MulAut.congr eH φ)).right
              ((eH.trans β⁻¹) x) := by
          have := congrArg (fun γ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => γ (β⁻¹ (eH x))) hβ
          simp only [MulAut.mul_apply, MulAut.congr_apply] at this
          simpa using this
        show specialLinearGroupEquivStatedSL 2 F ((eH.trans β⁻¹) (φ x)) = _
        rw [h1, ← stableAut_eq_slFieldAut']
        rfl
  · right
    refine ⟨h7, ?_⟩
    by_cases hin : φ ∈ innOf Q
    · left
      obtain ⟨c, hc⟩ := hin
      have hcz : c ∈ Subgroup.center Q :=
        IVK.Lifted.dict_inner h2A7 hO.sl2 c (by rw [hc]; exact hφ)
      rw [← hc]
      exact IVK.Lifted.conj_eq_one_of_mem_center hcz
    · right
      exact hin

end Dict
end Hyp

section FAut

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

open Hyp

theorem inducesFAut_bar (_hII : II4_4_4_center) (h44 : II4_44) (h2A7 : IVK.Lifted.II4_2A7)
    (hC : Cfg5 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) {b : G} (hbC : b ∈ Cen z)
    (hb2 : orderOf b = 2) (hf : CFSG.GH74.GLS.InducesFAut b K) :
    IVK.Prod3.IndFAut (barOf z K) (toBar z ⟨b, hbC⟩) := by
  obtain ⟨hbN, hF⟩ := hf
  have hKC := K_le_Cz hC hK
  have hKmem : K ∈ ({K₁, K₂} : Set (Subgroup G)) := by rcases hK with rfl | rfl <;> simp
  have hOK := IVK.Lifted.std4_hatOK h44 hC.std hKmem
  have hbb : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb2, sq] at this
  have hφ2 : phi K b hbN * phi K b hbN = 1 := phi_mul_self K hbN hbb
  let Φ := L97.hatBar (rigid_of_comp hC hK)
  let b' : CentralizerBar z := toBar z ⟨b, hbC⟩
  have hnorm : b' ∈ normalizer ((barOf z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) :=
    (mem_normalizer_iff_bar hKC (pcomp_of hC hK)).1 hbN
  refine ⟨fun x hx => (Subgroup.mem_normalizer_iff.1 hnorm x).1 hx, ?_⟩
  have hR : ∀ y : Hat K, ((Φ (phi K b hbN y) : ↥(barOf z K)) : CentralizerBar z) =
      b' * (Φ y : CentralizerBar z) * b'⁻¹ := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    show ((Φ (phi K b hbN (hatMk K k)) : ↥(barOf z K)) : CentralizerBar z) = _
    rw [phi_mk]
    show toBar z ⟨b * (k : G) * b⁻¹, _⟩ = _
    rw [show (⟨b * (k : G) * b⁻¹, _⟩ : ↥(Cz z)) = ⟨b, hbC⟩ * ⟨(k : G), hKC k.2⟩ * ⟨b, hbC⟩⁻¹ from rfl,
      map_mul, map_mul, map_inv]
    rfl
  have hy : ∀ x : ↥(barOf z K), (Φ.symm x) ∈ (Set.univ : Set (Hat K)) := fun _ => trivial
  have hconj : ∀ (x : ↥(barOf z K)) (hx : b' * (x : CentralizerBar z) * b'⁻¹ ∈ barOf z K),
      Φ.symm ⟨b' * x * b'⁻¹, hx⟩ = phi K b hbN (Φ.symm x) := by
    intro x hx
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hR, MulEquiv.apply_symm_apply]
  rcases dict_indFAut h2A7 hOK (phi K b hbN) hφ2 hF with
    ⟨F, hFf, hFin, e, σ, he⟩ | ⟨h7, hdisj⟩
  · left
    refine ⟨F, hFf, hFin, Φ.symm.trans e, σ, fun x hx => ?_⟩
    show e (Φ.symm ⟨b' * x * b'⁻¹, hx⟩) = stableAut (StatedSL 2 F) (fieldStable_statedSL 2) σ (e (Φ.symm x))
    rw [hconj x hx, he]
  · right
    refine ⟨isDoubleCoverOfAlt_of_equiv Φ h7, ?_⟩
    rcases hdisj with h1 | h1
    · left
      intro x hx
      have := hR (Φ.symm ⟨x, hx⟩)
      rw [h1] at this
      simpa using this.symm
    · right
      rintro ⟨k, hk, hkk⟩
      apply h1
      refine ⟨Φ.symm ⟨k, hk⟩, ?_⟩
      ext y
      apply Φ.injective
      apply Subtype.ext
      rw [MulAut.conj_apply, hR, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact (hkk (Φ y) (Φ y).2).symm

end FAut

end CFSG.GH74.GLS.IVK.Lifted32
