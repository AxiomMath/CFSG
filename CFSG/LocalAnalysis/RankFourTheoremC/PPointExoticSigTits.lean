module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigTI
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal
public import Certificates.Certificate41722
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.Sporadic.Schreier.TitsAutD
import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.Schreier.Tits CFSG.AGLEmbedding.MaxD2 CFSG.AGLEmbeddingD2
open Certificates.MaxD2Perm


theorem exists_sylow_weakTI_tits {K : Type} [Group K] [Finite K] (eS : K ≃* titsD) :
    ∃ R₀ : Sylow 5 (MulAut K), WeakTI (R₀ : Subgroup (MulAut K)) := by
  have hp : Nat.Prime 5 := by norm_num
  let Φ : MulAut K ≃* titsA := (MulAut.congr eS).trans titsConjEquiv.symm
  have hcardX : Nat.card (MulAut K) = Nat.card titsA := Nat.card_congr Φ.toEquiv
  obtain ⟨R, hRG, hcardR, hTI⟩ := tiTorus_of_check
    (S := [titsDGen 0, titsDGen 1, titsGen 0, titsGen 1, titsGen 2, titsGen 3]) (D := titsAData)
    rfl hp titsA_hS
    (by
      have h1 : [titsDGen 0, titsDGen 1, titsGen 0, titsGen 1, titsGen 2, titsGen 3].length = 6 :=
        rfl
      have h2 : titsAData.gT.size = 6 := rfl
      rw [h1, h2])
    (by rw [← titsA_eq_closure_list]; exact card_titsA) tits_five_local_check_a
    Certificates.certificate41722
  rw [← titsA_eq_closure_list] at hRG hTI
  refine exists_sylow_weakTI_of_equiv hp Φ hRG ?_ hTI
  rw [hcardR, hcardX, card_titsA,
    factorization_five_eq_two (by norm_num) (by norm_num) (by norm_num)]
  rfl

theorem signalizerAutAt_tits {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hp : p = 5)
    (hd : d.1 = .tits) : SignalizerAutAt p (.lie d) := by
  subst hp
  intro K _ _ ⟨e⟩ B Y hB hBc hY hBY _
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  obtain ⟨eS⟩ := titsModelEquiv K 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  obtain ⟨R₀, hR₀⟩ := exists_sylow_weakTI_tits eS
  exact centralizes_of_sylow_weakTI (by norm_num) R₀ hR₀ hB hBc
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).1 hY) hBY

end CFSG.LocalAnalysis.RankFourTheoremC
