module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4Graph
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecAssembly
public import CFSG.RankThree.CentralLift.LinearScalarCover
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks

variable {H : Type} [Group H] [Finite H]

theorem card_factor {k : Type} [Field k] {A : Subgroup (projectiveSL 4 k)}
    (hA : A = factorL k ∨ A = factorR k) :
    Nat.card A = Nat.card (SpecialLinearGroup (Fin 2) k) := by
  rcases hA with rfl | rfl
  · exact (Nat.card_congr (MonoidHom.ofInjective proj_bdL_injective).toEquiv).symm
  · exact (Nat.card_congr (MonoidHom.ofInjective proj_bdR_injective).toEquiv).symm

theorem card_projectiveSL_two_mul_two {E : Type} [Field E] [Finite E] :
    Nat.card E * (Nat.card E ^ 2 - 1) ≤ Nat.card (projectiveSL 2 E) * 2 := by
  have h1 := (scalars 2 E).card_eq_card_quotient_mul_card_subgroup
  rw [card_SL_eq (by norm_num : 1 ≤ 2)] at h1
  simp only [show 2 * (2 - 1) / 2 = 1 from rfl, pow_one, show Finset.Icc 2 2 = {2} from rfl,
    Finset.prod_singleton] at h1
  have h2 : Nat.card (scalars 2 E) ≤ 2 :=
    Nat.le_of_dvd two_pos (CFSG.RankThree.CentralLift.card_scalars_dvd (k := E) (n := 2) 0)
  calc Nat.card E * (Nat.card E ^ 2 - 1)
      = Nat.card (projectiveSL 2 E) * Nat.card (scalars 2 E) := h1
    _ ≤ Nat.card (projectiveSL 2 E) * 2 := Nat.mul_le_mul_left _ h2

theorem false_of_large_J (c : Sp4Rec.Config H) {k : Type} [Field k]
    [Finite k] (htwo : (2 : k) ≠ 0) (hK : Nat.card c.K = Nat.card (SpecialLinearGroup (Fin 2) k))
    (hq : IsQuasisimple c.J) {E : Type} [Field E] [Finite E] (hE : Nat.card E = Nat.card k ^ 2)
    (eJ : c.J ≃* projectiveSL 2 E) : False := by
  classical
  have hk3 : 3 ≤ Nat.card k := by
    have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
    have hne2 : Nat.card k ≠ 2 := by
      intro h
      have := Fintype.ofFinite k
      have h0 := FiniteField.cast_card_eq_zero k
      rw [← Nat.card_eq_fintype_card, h] at h0
      exact htwo (by exact_mod_cast h0)
    omega
  have hE4 : 4 ≤ Nat.card E := by rw [hE]; nlinarith
  obtain ⟨hs, hnab⟩ := Sp4Rec.isSimpleGroup_of_isSmallAltOrL2 c.type_J
  have hZ := Sp4Rec.center_eq_pPrimeCore hq hs hnab
  have hZ1 : Nat.card (center c.J) = 1 := by
    rw [Nat.card_congr (Subgroup.centerCongr eJ).toEquiv,
      OddSelector.center_projectiveSL_two_eq_bot hE4, Subgroup.card_bot]
  have hO : Nat.card (pPrimeCore 2 c.J) = 1 := by rw [← hZ]; exact hZ1
  have hJO : Nat.card (c.J ⧸ pPrimeCore 2 c.J) = Nat.card c.J := by
    have h := (pPrimeCore 2 c.J).card_eq_card_quotient_mul_card_subgroup
    rw [hO, mul_one] at h
    exact h.symm
  obtain ⟨e⟩ := c.quotient_J_K
  have hle : Nat.card c.J ≤ Nat.card c.K := by
    rw [← hJO, Nat.card_congr e.toEquiv]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hPJ := card_projectiveSL_two_mul_two (E := E)
  rw [← Nat.card_congr eJ.toEquiv, hE] at hPJ
  have hSL := card_SL_eq (K := k) (by norm_num : 1 ≤ 2)
  simp only [show 2 * (2 - 1) / 2 = 1 from rfl, pow_one, show Finset.Icc 2 2 = {2} from rfl,
    Finset.prod_singleton] at hSL
  rw [hK, hSL] at hle
  set q := Nat.card k with hqd
  have hq1 : 1 ≤ q ^ 2 - 1 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  have e4 : (q ^ 2) ^ 2 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    have h1 : 1 ≤ q ^ 2 := by omega
    zify [h1, Nat.one_le_pow 2 (q ^ 2) (by omega)]
    ring
  rw [e4] at hPJ
  have h3 : q ^ 2 * ((q ^ 2 - 1) * (q ^ 2 + 1)) ≤ q * (q ^ 2 - 1) * 2 :=
    hPJ.trans (Nat.mul_le_mul_right 2 hle)
  have h4 : q * (q ^ 2 - 1) * (q * (q ^ 2 + 1)) ≤ q * (q ^ 2 - 1) * 2 := by
    calc q * (q ^ 2 - 1) * (q * (q ^ 2 + 1)) = q ^ 2 * ((q ^ 2 - 1) * (q ^ 2 + 1)) := by ring
      _ ≤ q * (q ^ 2 - 1) * 2 := h3
  have hpos : 0 < q * (q ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  have h5 := Nat.le_of_mul_le_mul_left h4 hpos
  nlinarith

theorem linearFourExclusion : Sp4Rec.LinearFourExclusion := by
  intro H _ _ c p f hp hp2 hG
  classical
  have hGn : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨⟨-, hf, -⟩, k, _, _, hk, ⟨φ₀⟩⟩ := hG
  have : CharP k p := finite_field_prime_power_characteristic hp hf hk
  have hodd : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hodd
  set φ' : ↥(generalizedFitting H) ≃* projectiveSL 4 k :=
    φ₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 k).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 k)) with hφ'
  obtain ⟨g, hg⟩ := proj_surjective 4 k (φ' ⟨c.b, c.b_mem_G⟩)
  have hpc := c.pairConfig φ'
  rw [← hg] at hpc
  obtain ⟨β, P, hβ4, hgP⟩ := exists_frame_of_pairConfig htwo hpc
  set φ : ↥(generalizedFitting H) ≃* projectiveSL 4 k := φ'.trans (conjAut 4 k P⁻¹) with hφ
  set g₀ := CatalogueBHigherLinearAction.slConjugation 4 k P⁻¹ g with hg₀def
  have hg₀ : (g₀ : Matrix (Fin 4) (Fin 4) k) = X1 (β : k) := by
    rw [hg₀def, coe_slConjugation, inv_inv, Matrix.mul_assoc, hgP, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hφb : φ ⟨c.b, c.b_mem_G⟩ = proj 4 k g₀ := by
    rw [hφ, MulEquiv.trans_apply, ← hg, conjAut_proj]
  have hβ0 : (β : k) ≠ 0 := β.ne_zero
  have hβ4' : (β : k) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hβ4, Units.val_one]
  have hpc₀ := c.pairConfig φ
  rw [hφb] at hpc₀
  have hfac := pairConfig_factors htwo hβ0 hg₀ hpc₀
  have hKcard : Nat.card c.K = Nat.card (SpecialLinearGroup (Fin 2) k) := by
    have h1 : Nat.card ((c.K.subgroupOf (generalizedFitting H)).map φ.toMonoidHom) =
        Nat.card c.K := by
      rw [Subgroup.card_map_of_injective φ.injective]
      exact Nat.card_congr (subgroupOfEquivOfLe c.K_le_G).toEquiv
    rw [← h1]
    exact card_factor (hfac.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  have hq := c.isQuasisimple_J_of_fixed φ fun α hα2 hα1 L hL =>
    CatalogueBLinearHigherB.odd_higher_linear_involution_fixed_p_components 4 k hodd
      (by norm_num) α hα1 hα2 2 Nat.prime_two L hL
  obtain ⟨p', f', hp'2, hsrc, hZodd⟩ := c.exists_src_J hq
  have hsrc' : StatedClassicalModel (c.J ⧸ center c.J) .PSL 2 p' f' ∨
      Nonempty (c.J ⧸ center c.J ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (c.J ⧸ center c.J) .PSL 3 2 2 :=
    hsrc.elim Or.inl fun h => Or.inr (Or.inl h)
  have hLc := c.isComponentOf_J hq
  have hZ := OddSelector.center_projectiveSL_eq_bot (k := k) (by norm_num : 3 ≤ 4)
  obtain ⟨ρ, hinj, hρW, -, hρg⟩ := OutcomeLocal.socle_extension c.centralizer_eq_bot φ hZ
  obtain ⟨-, hCA, hCW', hL₁⟩ := OddSelector.socle_images φ hinj hρW c.J_le_G hLc
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) (by norm_num : 3 ≤ 4)
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ c.a)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      obtain ⟨μ, hμ, hsq, -⟩ := OddSelector.inner_case_reduction c.orderOf_a le_rfl hp hp2 hf hk
        hinj hL₁ hρa hp'2 hsrc' (fun _ => Or.inr hZodd)
      obtain ⟨-, E, _, _, hE, ⟨eJ⟩⟩ :=
        OddSelector.selectorRowS_of_inner htwo hinj hCA hCW' hL₁ hρa hμ hsq
      exact false_of_large_J c htwo hKcard hq hE eJ
    · exact OddSelector.field_case_false c.orderOf_a (by norm_num) hp hp2 hf hk hinj hL₁ hτ hρa
        hp'2 hsrc'
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut 4 k B * dualAut 4 k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← c.orderOf_a, pow_orderOf_eq_one, map_one]
      have hB := OddSelector.transpose_eq_or_eq_neg_of_pureGraph (by norm_num) B hα2
      exact false_of_graph c φ hinj hρW hρg hβ0 hβ4' hg₀ hφb hfac hρa hB
    · exact OddSelector.graph_field_case_false c.orderOf_a le_rfl hp hp2 hf hk hinj hL₁ hτ hρa
        hp'2 hsrc'

end Catalog7L4

end CFSG.ComponentClassification.GSThmB
