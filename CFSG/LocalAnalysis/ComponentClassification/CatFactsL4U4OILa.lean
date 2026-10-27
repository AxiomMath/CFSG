module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ESplit
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowO
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraphField
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIL

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.OddSelector OutInv

variable {k : Type} [Field k] [Finite k]

theorem map_conj_fixSub (φ : MulAut (projectiveSL 4 k)) :
    (fixSub φ).map (MulAut.conj : projectiveSL 4 k →* MulAut (projectiveSL 4 k)) =
      OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {φ} := by
  ext α
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨⟨x, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := CSL.mul_conj_mul_inv φ x
    rw [show φ x = x from hx] at h1
    calc MulAut.conj x * φ = φ * MulAut.conj x * φ⁻¹ * φ := by rw [h1]
      _ = φ * MulAut.conj x := by group
  · intro hα
    obtain ⟨⟨x, rfl⟩, hc⟩ := mem_inf.1 hα
    refine ⟨x, ?_, rfl⟩
    rw [mem_centralizer_singleton_iff] at hc
    have h1 : MulAut.conj (φ x) = MulAut.conj x := by
      rw [← CSL.mul_conj_mul_inv, ← hc]
      group
    exact CSL.conj_injective h1

theorem selectorRowO_of_component {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hk : Nat.card k = p ^ f) {φ : MulAut (projectiveSL 4 k)} (hφ2 : φ ^ 2 = 1)
    (hφ : φ ∉ (conjAut 4 k).range) {J' : Subgroup (projectiveSL 4 k)} (hJφ : J' ≤ fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (fixSub φ)))
    (hJm : Blueprint.LieModel (↥J' ⧸ center ↥J') .PSL 2 p (2 * f)) :
    SelectorRowO 4 k (MonoidHom.id (MulAut (projectiveSL 4 k)))
      (OuterAutomorphisms.inner (projectiveSL 4 k)) φ
      (J'.map (MulAut.conj : projectiveSL 4 k →* MulAut (projectiveSL 4 k))) := by
  classical
  set ρ := MonoidHom.id (MulAut (projectiveSL 4 k)) with hρ
  have hinj : Function.Injective ρ := Function.injective_id
  set L := J'.map (MulAut.conj : projectiveSL 4 k →* MulAut (projectiveSL 4 k)) with hL
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [map_one, h]⟩
  have ha : orderOf φ = 2 := orderOf_eq_prime hφ2 hφ1
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hp.odd_of_ne_two hp2).pow
  have hJc : CFSG.Assembly.IsComponentOf J' (fixSub φ) :=
    (isComponentOf_iff_isComponent_subgroupOf hJφ).2 hJ
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ φ}) := by
    have h1 := isComponentOf_map_of_injective hJc MulAut.conj CSL.conj_injective
    rw [map_conj_fixSub] at h1
    rw [hρ, Subgroup.map_id]
    exact h1
  have eJL : ↥J' ≃* ↥L := J'.equivMapOfInjective _ CSL.conj_injective
  have hLm : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 2 p (2 * f) :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr (center ↥J') (center ↥L) eJL (Subgroup.map_center_eq eJL)) hJm
  have hsrc : StatedClassicalModel (↥L ⧸ center ↥L) .PSL 2 p (2 * f) ∨
      Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (↥L ⧸ center ↥L) .PSL 3 2 2 :=
    Or.inl (GSThmB.statedClassicalModel_of_lieModel_ne_zero (by norm_num) hLm)
  have hCA : (centralizer {φ}).map ρ = ρ.range ⊓ centralizer {ρ φ} := by
    rw [hρ, Subgroup.map_id, MonoidHom.range_eq_top.2 Function.surjective_id, top_inf_eq]
    rfl
  have hCW : (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {φ}).map ρ =
      OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ φ} := by
    rw [hρ, Subgroup.map_id]
    rfl
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) (by norm_num : 3 ≤ 4)
  obtain ⟨B, τ, ε, hε, hφB⟩ := hform φ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hφB
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hφB
      exact absurd ⟨B, hφB.symm⟩ hφ
    · exact (field_case_false ha (by norm_num) hp hp2 hf hk hinj hL₁ hτ hφB hp2 hsrc).elim
  · rw [pow_one] at hφB
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hφB
      have hα2 : (conjAut 4 k B * dualAut 4 k) ^ 2 = 1 := by rw [← hφB]; exact hφ2
      rcases transpose_eq_or_eq_neg_of_pureGraph (by norm_num) B hα2 with hB | hB
      · by_cases hsplit : ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
            ∀ v ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ v = 0
        · exfalso
          obtain ⟨-, ⟨eL⟩⟩ := Catalog7L4E.split_component_iso hp hp2 hf hk hinj hL₁ hφB hB hsplit
          have hqodd : GorensteinWalter.IsOddPrimePower (Nat.card k) :=
            ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hk⟩
          have h1 : Nat.card ↥L = Nat.card k * (Nat.card k ^ 2 - 1) / 2 := by
            rw [Nat.card_congr eL.toEquiv]
            exact GorensteinWalter.psl2_card_formula k hqodd
          have h2 := AZ.two_mul_card_of_isSec8JType hp hp2 (Or.inl hLm : GSThmB.IsSec8JType _ p f)
          have h3 := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (center ↥L))
          have hq3 : 3 ≤ p ^ f := by
            have : 3 ≤ p := by have := hp.two_le; omega
            exact this.trans (Nat.le_self_pow (by omega) p)
          rw [hk] at h1
          set q := p ^ f with hq
          have h4 : q * (q ^ 2 - 1) % 2 = 0 := by
            have : Even (q * (q ^ 2 - 1)) := by
              rcases Nat.even_or_odd q with he | ho
              · exact he.mul_right _
              · exact (Nat.Odd.sub_odd (ho.pow) odd_one).mul_left _
            exact Nat.even_iff.mp this
          have h5 : q ^ 2 * (q ^ 4 - 1) ≤ q * (q ^ 2 - 1) := by omega
          have h6 : q * (q ^ 2 - 1) < q ^ 2 * (q ^ 4 - 1) := by
            have a1 : q < q ^ 2 := by nlinarith
            have a2 : 1 ≤ q ^ 2 - 1 := by
              have : 9 ≤ q ^ 2 := by nlinarith
              omega
            have a3 : q ^ 2 - 1 ≤ q ^ 4 - 1 :=
              Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) (by norm_num)) 1
            calc q * (q ^ 2 - 1) < q ^ 2 * (q ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right a1 a2
              _ ≤ q ^ 2 * (q ^ 4 - 1) := Nat.mul_le_mul_left _ a3
          omega
        · exact (selectorRowO_of_nonsplit hodd hinj hCA hCW hL₁ hφB hB hsplit).1
      · exact (symplectic_case_false (by norm_num) hp hp2 hf hk hinj hL₁ hφB hB hp2 hsrc).elim
    · exact (graph_field_case_false ha (by norm_num) hp hp2 hf hk hinj hL₁ hτ hφB hp2
        hsrc).elim

end OIL

end CFSG.ComponentClassification.CatFactsL4U4
