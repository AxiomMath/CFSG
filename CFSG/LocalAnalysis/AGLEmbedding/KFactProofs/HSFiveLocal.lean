
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocalBase

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocalEq
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisCaseFor
public import CFSG.RankThree.PartOne.KS.HSMcL
public import CFSG.Sporadic.Bridge.HSSurj
public import Certificates.Certificate19831
public import Certificates.Certificate19832

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.MaxD2
open CFSG.RankThree.Native Certificates.MaxD2Heis
open CFSG.ComponentClassification.OuterAutomorphisms

theorem hs_heisData_P :
    ∃ R₀ : Subgroup (Equiv.Perm (Fin 100)), HeisDataEq 5 2 3 12 hs100P R₀ :=
  ⟨_, Certificates.certificate19831.1⟩

theorem hs_heisData_R :
    ∃ R₀ : Subgroup (Equiv.Perm (Fin 100)), HeisDataEq 5 2 3 12 hs100R R₀ :=
  ⟨_, Certificates.certificate19832.1⟩

theorem heisLocalEq_hsP
    {X : Type*} [Group X] [Finite X] (e : X ≃* hs100P)
    (R : Sylow 5 X) : HeisLocalEq 5 (R : Subgroup X) := by
  obtain ⟨R₀, hR₀⟩ := hs_heisData_P
  have hT := heisLocalEq_of_heisDataEq hR₀ (le_refl 2) orderOf_three_zmod_five_hs (by norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine heisLocalEq_sylow e hT ?_ R
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀.1).toEquiv, hR₀.2.1,
    factorization_card_hs100P_five]

theorem heisLocalEq_hsR
    {X : Type*} [Group X] [Finite X] (e : X ≃* hs100R)
    (R : Sylow 5 X) : HeisLocalEq 5 (R : Subgroup X) := by
  obtain ⟨R₀, hR₀⟩ := hs_heisData_R
  have hT := heisLocalEq_of_heisDataEq hR₀ (le_refl 2) orderOf_three_zmod_five_hs (by norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine heisLocalEq_sylow e hT ?_ R
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀.1).toEquiv, hR₀.2.1, card_hs100R,
    factorization_eq_of_pow_dvd Nat.prime_five (k := 3) (by norm_num) (by norm_num)
      (by norm_num)]

theorem d2HeisLocalEqAt_hs :
    D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5 := by
  intro X _ _ K hKn hC ⟨e⟩ p hp R
  have hp5 : p = 5 := hp
  subst hp5
  have : K.Normal := hKn
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  let θ : K ≃* hs100P := (e.trans eC.symm).trans hs100Equiv
  refine ⟨?_, ?_⟩
  ·
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence θ).toEquiv]
    have h2 := outer_card_hs100P
    have hpos : 0 < Nat.card (Outer hs100P) := Nat.card_pos
    intro hdvd
    have := Nat.le_of_dvd hpos hdvd
    omega
  ·
    have hcardR := card_hs100R
    have hmodel := CFSG.RankThree.PartOne.hs_autModel
    have hinj := hmodel.embed_injective K θ hC
    set ι := hmodel.embed K θ with hι
    have hPB : hs100P ≤ ι.range := fun y hy =>
      ⟨(θ.symm ⟨y, hy⟩ : K), by rw [hι, hmodel.embed_coe, MulEquiv.apply_symm_apply]⟩
    have hBR : ι.range ≤ hs100R := by
      rintro _ ⟨x, rfl⟩
      exact hmodel.embed_mem K θ x
    have hcard2 : Nat.card hs100R = 2 * Nat.card hs100P := by
      rw [hcardR, card_hs100P]
    let eX : X ≃* ι.range := MonoidHom.ofInjective hinj
    rcases eq_or_eq_of_index_two hPB hBR hcard2 with hB | hB
    · exact heisLocalEq_hsP (eX.trans (MulEquiv.subgroupCongr hB)) R
    · exact heisLocalEq_hsR (eX.trans (MulEquiv.subgroupCongr hB)) R

end CFSG.AGLEmbeddingD2
