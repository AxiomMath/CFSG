module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigTI
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
public import Certificates.Certificate41721
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.AGLEmbedding.MaxD2 CFSG.AGLEmbeddingD2 CFSG.RankThree.Native CFSG.Sporadic.Schreier
open Certificates.MaxD2Heis

noncomputable def autModelEquiv {M : Type*} [Group M] {P R : Subgroup M}
    (h : CFSG.Sporadic.SmallOddCore.AutModel P R) : MulAut P ≃* R :=
  MulEquiv.ofBijective (h.hom.codRestrict R h.elt_mem)
    ⟨fun a b hab => h.hom_injective (congrArg Subtype.val hab), fun x => by
      let α : MulAut P :=
        { toFun := fun p => ⟨(x : M) * p * (x : M)⁻¹, h.conj_mem x x.2 p p.2⟩
          invFun := fun p => ⟨(x : M)⁻¹ * p * x, by
            simpa using h.conj_mem (x : M)⁻¹ (R.inv_mem x.2) p p.2⟩
          left_inv := fun p => Subtype.ext (by simp [mul_assoc])
          right_inv := fun p => Subtype.ext (by simp [mul_assoc])
          map_mul' := fun p q => Subtype.ext (by simp [mul_assoc]) }
      exact ⟨α, Subtype.ext (h.elt_eq x.2 fun p => rfl)⟩⟩

theorem exists_sylow_weakTI_mcl
    {K : Type} [Group K] [Finite K] (θ : K ≃* mcl275P) :
    ∃ R₀ : Sylow 5 (MulAut K), WeakTI (R₀ : Subgroup (MulAut K)) := by
  have hp : Nat.Prime 5 := by norm_num
  have hmodel := CFSG.RankThree.PartOne.mcl_autModel
  let Φ : MulAut K ≃* mcl275R := (MulAut.congr θ).trans (autModelEquiv hmodel)
  have hcardX : Nat.card (MulAut K) = 1796256000 :=
    (Nat.card_congr Φ.toEquiv).trans card_mcl275R
  obtain ⟨R, hRG, hcardR, hTI⟩ := tiHeis_of_check
    (S := [mcl275A, mcl275B, mcl275U]) (D := mclFiveDataR) rfl hp mclFiveDataR_hS
    (by
      have h1 : [mcl275A, mcl275B, mcl275U].length = 3 := rfl
      have h2 : mclFiveDataR.gT.size = 3 := rfl
      rw [h1, h2])
    (by rw [mclR_closure_eq]; exact card_mcl275R) mcl_five_check_R
    Certificates.certificate41721
  rw [mclR_closure_eq] at hRG hTI
  refine exists_sylow_weakTI_of_equiv hp Φ hRG ?_ hTI
  rw [hcardR, hcardX, factorization_eq_of_pow_dvd Nat.prime_five (k := 3) (by norm_num)
    (by norm_num) (by norm_num)]
  rfl

theorem signalizerAutAt_mcl
    {p : ℕ} (hp : p = 5) :
    SignalizerAutAt p (.sporadic .McL) := by
  subst hp
  intro K _ _ ⟨e⟩ B Y hB hBc hY hBY _
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  let θ : K ≃* mcl275P := (e.trans eC.symm).trans mcl275Equiv
  obtain ⟨R₀, hR₀⟩ := exists_sylow_weakTI_mcl θ
  exact centralizes_of_sylow_weakTI (by norm_num) R₀ hR₀ hB hBc
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).1 hY) hBY

end CFSG.LocalAnalysis.RankFourTheoremC
