module

public import CFSG.ClassicalInvolution.AschTight.S1911FusA
public import CFSG.ClassicalInvolution.Asc77.AscT7TFAut
public import CFSG.ClassicalInvolution.Asc77.AscT7TTrace
public import CFSG.ClassicalInvolution.Asc77.AscT7TZStar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open scoped MatrixGroups

namespace T7T

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem ringEquiv_pow_eq_one (hf : f ≠ 0)
    (σ : GaloisField p f ≃+* GaloisField p f) : σ ^ f = 1 := by
  let σ' : GaloisField p f ≃ₐ[ZMod p] GaloisField p f :=
    AlgEquiv.ofRingEquiv (f := σ) fun x => by
      simp only [Algebra.algebraMap_eq_smul_one]
      rw [← ZMod.natCast_zmod_val x, Nat.cast_smul_eq_nsmul, map_nsmul, map_one]
  have hcard : Nat.card (GaloisField p f ≃ₐ[ZMod p] GaloisField p f) = f := by
    rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank p hf]
  have h1 : σ' ^ f = 1 := by
    have := pow_card_eq_one (G := GaloisField p f ≃ₐ[ZMod p] GaloisField p f) (x := σ')
    rwa [← Nat.card_eq_fintype_card, hcard] at this
  have key : ∀ n : ℕ, ∀ x, (σ ^ n) x = (σ' ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      calc (σ ^ (n + 1)) x = (σ ^ n) (σ x) := by rw [pow_succ]; rfl
        _ = (σ' ^ n) (σ x) := ih _
        _ = (σ' ^ (n + 1)) x := by rw [pow_succ]; rfl
  ext x
  rw [key f x, h1]
  rfl


theorem fieldPart_ne_one_of_isFAut {K R : Subgroup G} {z a : G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)))
    (h3 : 3 < Nat.card (GaloisField p f)) (hp2 : p ≠ 2)
    (hRK : R ≤ K) (hR : IsQuatSub R) (hz : IsUniqueInvolution R z)
    (hFa : IsFAut R a) (ha2 : IsPGroup 2 (Subgroup.zpowers a))
    (haN : a ∈ Subgroup.normalizer (K : Set G)) :
    (normalizerToPGammaL2Mod e hFcard hF h3 ⟨a, haN⟩).right ≠ 1 := by
  intro hσ
  obtain ⟨x, hxR, hcardx, hxmem, hxne, hxinv⟩ := exists_cyclic_of_isFAut hR hz hFa ha2
  obtain ⟨g, hg⟩ := exists_semilinHom_of_mem e hFcard hF h3 ⟨a, haN⟩
  rw [hσ] at hg
  obtain ⟨k, hRk⟩ := hR.natCard_eq
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := k + 2) hRk.2
  let xK : ↥K := ⟨x, hRK hxR⟩
  let xbar : SL(2, GaloisField p f) := e (QuotientGroup.mk xK)
  have haR : conjSub a R = R := mem_normalizer_iff_conjSub_eq.mp hFa.1
  have haxR : a * x * a⁻¹ ∈ R := by
    have := conj_mem_conjSub (n := a) hxR
    rwa [haR] at this
  let axK : ↥K := ⟨a * x * a⁻¹, hRK haxR⟩
  have hslx : slAut K e ⟨a, haN⟩ xbar = e (QuotientGroup.mk axK) := by
    simp [slAut, xbar, oddCoreQuotientAut_mk]
    exact congrArg _ (Subtype.ext (normalizerConj_apply_coe K ⟨a, haN⟩ xK))
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have haxK : axK = xK ^ j := Subtype.ext (by simpa [xK, axK] using hj.symm)
  have hy : e (QuotientGroup.mk axK) ∈ Subgroup.zpowers xbar :=
    ⟨j, by rw [haxK]; simp [xbar, map_zpow]⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hR2) ⟨x, hxR⟩
  have hxm : xbar ^ (2 ^ m) = 1 := by
    have h1 : xK ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      have : x ^ (2 ^ m) = 1 := by
        rw [← hm]
        have := pow_orderOf_eq_one (⟨x, hxR⟩ : ↥R)
        exact congrArg Subtype.val this
      simpa [xK] using this
    simp only [xbar, ← map_pow, ← QuotientGroup.mk_pow, h1]
    simp
  have hmat : (g : Matrix (Fin 2) (Fin 2) (GaloisField p f)) *
      (xbar : Matrix (Fin 2) (Fin 2) (GaloisField p f)) *
        ((g⁻¹ : GL (Fin 2) (GaloisField p f)) : Matrix (Fin 2) (Fin 2) (GaloisField p f)) =
      ((e (QuotientGroup.mk axK) : SL(2, GaloisField p f)) :
        Matrix (Fin 2) (Fin 2) (GaloisField p f)) := by
    rw [← hslx, hg, AscL62.coe_semilinHom]
    simp
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p f) p]; exact hp2)
  rcases eq_or_eq_inv_of_conj_mem_zpowers h2 hxm hy g hmat with h | h
  · apply hxne
    have h1 : (QuotientGroup.mk axK : K ⧸ classicalInvolutionOddCore K) = QuotientGroup.mk xK :=
      e.injective h
    have h3 := QuotientGroup.eq.mp h1
    have h4 : axK⁻¹ * xK = 1 := by
      refine eq_one_of_mem_oddCore (H := K) (T := R) hR2 h3 ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, xK, axK]
      exact R.mul_mem (R.inv_mem haxR) hxR
    have h5 : axK = xK := inv_mul_eq_one.mp h4
    simpa [xK, axK] using congrArg Subtype.val h5
  · apply hxinv
    have h1 : (QuotientGroup.mk axK : K ⧸ classicalInvolutionOddCore K) =
        QuotientGroup.mk xK⁻¹ := e.injective (by rw [h]; simp [xbar])
    have h3 := QuotientGroup.eq.mp h1
    have h4 : axK⁻¹ * xK⁻¹ = 1 := by
      refine eq_one_of_mem_oddCore (H := K) (T := R) hR2 h3 ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, xK, axK]
      exact R.mul_mem (R.inv_mem haxR) (R.inv_mem hxR)
    have h5 : axK = xK⁻¹ := inv_mul_eq_one.mp h4
    simpa [xK, axK] using congrArg Subtype.val h5

end T7T

end CFSG.ClassicalInvolution.Asc77
