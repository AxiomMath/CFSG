module

public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightLinGen
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightBT

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.RankThree.PartOne CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Campbell CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem alt_three_block_gen {G T V M : Subgroup Γ}
    (hG : CharTwo G) (hT : IsSylowTwoOf T G) (hMG : M ≤ G) (hne : M ≠ G)
    (hN : G ⊓ Subgroup.normalizer (T : Set Γ) ≤ M)
    (hchN : ∀ C : Subgroup Γ, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      G ⊓ Subgroup.normalizer (C : Set Γ) ≤ M)
    (hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ M)
    (hZ : G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ) ≤ M)
    (hVn : G ≤ Subgroup.normalizer (V : Set Γ))
    (hVQ : V ≤ omegaOneCenterOf (pCoreOf 2 G)) (hnat : IsNatSL G V 1) :
    ∃ E : Subgroup Γ, IsBTBlock G T E ∧ IsNaturalAltModule ↥E 1 ∧ pCoreOf 2 E ≤ V ∧
      G ≤ baum T ⊔ E ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) ∧
      ⁅E, omegaOneCenterOf (baum T)⁆ ≤ V := by
  classical
  obtain ⟨α, β, hαs, hαk, hβs, hβk, hβe⟩ := hnat
  rw [Subgroup.inf_subgroupOf_left] at hαk
  rw [Subgroup.inf_subgroupOf_left] at hβk
  have hβe' : ∀ (g : ↥G) (v v' : ↥V), (v' : Γ) = g * v * g⁻¹ →
      Multiplicative.toAdd (β v') =
        (α g : Matrix (Fin 2) (Fin 2) (GaloisField 2 1)).mulVec (Multiplicative.toAdd (β v)) := by
    intro g v v' hv'
    have hw : (g : Γ) * v * (g : Γ)⁻¹ ∈ V := hv' ▸ v'.2
    have h1 : v' = ⟨(g : Γ) * v * (g : Γ)⁻¹, hw⟩ := Subtype.ext hv'
    rw [h1, hβe g v hw]
    rfl
  obtain ⟨E, P', hP'G, hBP', hVP', hSyl, hmin, hcharP, hαP', hnc, hTSC, hJS, hEeq, hchi, hnex,
    hcomm2, hEY, hnotC, hGfin⟩ :=
    three_eight_linear_gen hG hT hMG hne hN hchN hC hZ hVn hVQ α hαs hαk β hβs hβe' hβk
  obtain ⟨n', hn', hcard, -, halt⟩ := hnex
  have hn1 : n' = 1 := by
    have h1 : (2 : ℕ) ^ n' = 2 ^ 1 := by
      rw [← hcard]
      exact GaloisField.card 2 1 (by omega)
    exact Nat.pow_right_injective (le_refl 2) h1
  have hshort : IsShort2 E := hchi.1.1
  obtain ⟨hblk, hnatA⟩ := isBTBlock_of_alt_three hP'G hmin hEeq hshort (halt hn1) hnotC
  have hEP' : E ≤ P' := hEeq ▸ twoResidual_le P'
  have hEn : P' ≤ Subgroup.normalizer (E : Set Γ) := hEeq ▸ le_normalizer_twoResidual P'
  have hQE : pCoreOf 2 E ≤ pCoreOf 2 P' :=
    le_pCoreOf_of_normalizes (p := 2)
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E).trans hEP')
      (hEn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E)
  have hQV : pCoreOf 2 E ≤ V := by
    rw [← hblk.perfect]
    exact (Subgroup.commutator_mono hQE le_rfl).trans hcomm2
  exact ⟨E, hblk, hnatA, hQV, hGfin, hEY⟩

end CFSG.CGT.PushingUpLit.BHS6
