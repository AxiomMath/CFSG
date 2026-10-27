module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLCore
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KOdd2Fin

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Matrix

namespace EvenSL

theorem charP_two_of_natCard_even {K : Type} [Field K] [Finite K] (h : Nat.card K % 2 = 0) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  have hd : 2 ∣ p ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card]; exact Nat.dvd_of_mod_eq_zero h
  have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1
    (Nat.prime_two.dvd_of_dvd_pow hd)).symm
  subst this
  exact hp

theorem mem_statedScalars_of_repHom_scalar {K : Type} [Field K] (G : Subgroup (GL (Fin 3) K))
    (g : G) (c : K) (h : repHom G g = c • (1 : Module.End K (Fin 3 → K))) :
    (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
  have hmat : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
    apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin 3)).injective
    rw [map_smul, map_one]
    exact h
  have hc : c ≠ 0 := by
    intro hc0
    have h1 : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((g : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hmat, hc0, zero_smul, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨Units.mk0 c hc, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, hmat]
  simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end EvenSL

open EvenSL

theorem inputPSL3EvenNoSL_holds : InputPSL3EvenNoSL := by
  intro Y _ _ hY H N _ hSL
  obtain ⟨K, hF, hfin, h3, h2, ⟨e⟩⟩ := hY
  have hchar : CharP K 2 := charP_two_of_natCard_even h2
  classical
  let Sc := (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)
  let φ : ↥(StatedSL 3 K) →* Y := e.symm.toMonoidHom.comp (QuotientGroup.mk' Sc)
  have hφ : Function.Surjective φ := e.symm.surjective.comp (QuotientGroup.mk'_surjective Sc)
  let G0 : Subgroup ↥(StatedSL 3 K) := H.comap φ
  let G : Subgroup (GL (Fin 3) K) := G0.map (StatedSL 3 K).subtype
  let e0 : ↥G0 ≃* ↥G :=
    Subgroup.equivMapOfInjective G0 (StatedSL 3 K).subtype Subtype.val_injective
  let ψ : ↥G →* ↥H := (φ.subgroupComap H).comp e0.symm.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro h
    obtain ⟨x, hx⟩ := hφ h.1
    have hxG : x ∈ G0 := by
      show φ x ∈ H
      rw [hx]; exact h.2
    refine ⟨e0 ⟨x, hxG⟩, ?_⟩
    have : ψ (e0 ⟨x, hxG⟩) = (φ.subgroupComap H) ⟨x, hxG⟩ := by simp [ψ]
    rw [this]
    exact Subtype.ext hx
  let ψ' : ↥G →* ↥H ⧸ N := (QuotientGroup.mk' N).comp ψ
  let M : Subgroup ↥G := ψ'.ker
  have hM : M.Normal := MonoidHom.normal_ker ψ'
  let eqv : ↥G ⧸ M ≃* ↥H ⧸ N :=
    QuotientGroup.quotientKerEquivOfSurjective ψ' ((QuotientGroup.mk'_surjective N).comp hψ)
  have hSL' : IsSLThreeFour (↥G ⧸ M) := isSLThreeFour_of_mulEquiv eqv hSL
  have hscal : ∀ g : ↥G, (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K → g ∈ M := by
    intro g hg
    obtain ⟨x, rfl⟩ := e0.surjective g
    have hx : (x : ↥(StatedSL 3 K)) ∈ Sc := Subgroup.mem_subgroupOf.2 hg
    have h1 : φ x.1 = 1 := by
      have : (QuotientGroup.mk' Sc) x.1 = 1 := (QuotientGroup.eq_one_iff _).2 hx
      simp [φ]
      exact hx
    show ψ' (e0 x) = 1
    have : ψ (e0 x) = 1 := by
      have h' : ψ (e0 x) = (φ.subgroupComap H) x := by simp [ψ]
      rw [h']
      exact Subtype.ext h1
    simp [ψ', this]
  refine sl34_not_quotient hSL' (repHom G) (repHom_injective G) (QuotientGroup.mk' M)
    (QuotientGroup.mk'_surjective M) ?_
  rintro g ⟨c, hc⟩
  exact (QuotientGroup.eq_one_iff g).2 (hscal g (mem_statedScalars_of_repHom_scalar G g c hc))

theorem inputNoSLSection_holds : InputNoSLSection :=
  inputNoSLSection_of_odd_even inputL3U3OddNoSec16_holds inputPSL3EvenNoSL_holds

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
