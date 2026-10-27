module

public import CFSG.ClassicalInvolution.Uniform.UIH8
public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.ClassicalInvolution.Q3.OddCentralizerModels

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups commutatorElement

section Thm2

theorem commutator_mem_center_of_commutes {C G : Type*} [Group C] [Group G] (φ : C →* G)
    (hker : φ.ker ≤ Subgroup.center C) {N : Subgroup G} (hcomm : Commutes φ.range N) {r : C}
    {z : G} (hrz : φ r = z) (hzN : z ∈ N) (y : C) : r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center C := by
  apply hker
  rw [MonoidHom.mem_ker]
  have h := hcomm (φ y) ⟨y, rfl⟩ z hzN
  simp only [map_mul, map_inv, hrz]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  exact h.symm

variable {p f : ℕ} [Fact p.Prime]

theorem thm2BelowU_of_citBelowT {n : ℕ} (hn : CITBelowT (.sl2 p f) n) : Thm2BelowU p f n := by
  intro _ _ G _ _ hG Ω hΩ hO hgen K hK _ z hz hN
  obtain ⟨N, hNn, hN2, hzN⟩ := hN
  have : N.Normal := hNn
  obtain ⟨D⟩ := exists_omegaLieU hn hΩ ⟨K, hK⟩ hO hG
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hK
  have hgen' : omegaGen Ω = ⊤ := hgen
  have hQ : (D.hom i).range.Normal :=
    ⟨fun x hx g => D.mem_comp_conj (hgen' ▸ Subgroup.mem_top g) hx⟩
  rcases D.valid i with ⟨t, m, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  ·
    have hker := castHom_ker_le_center hc (D.hom i) (D.ker_le_center i)
    have hQ' : (castHom hc (D.hom i)).range.Normal := by
      rw [range_castHom]
      exact hQ
    have hquasi : CFSG.Open.IsQuasisimple (compModel p e t m).G :=
      isQuasisimple_modelUniv t m p e Fact.out (isFundTag_modelFacts ht) hadm
    have hcomm := commutes_range_of_normal_pGroup hquasi (castHom hc (D.hom i)) hker hQ' hN2
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom i) hR
    have hKR' : K = R'.map (castHom hc (D.hom i)) := hKR.trans hRR.symm
    obtain ⟨r, hrR, hrz⟩ := Subgroup.mem_map.mp (hKR' ▸ hz.mem)
    have hzc := commutator_mem_center_of_commutes (castHom hc (D.hom i)) hker hcomm hrz hzN
    by_cases hne : t = .PSL ∧ m = 2
    · have hR'top : R' = ⊤ :=
        (fundamentalIsWhole_modelUniv t m p e Fact.out (isFundTag_modelFacts ht) hadm).1 hne R' hR'
      have hK' : K = (castHom hc (D.hom i)).range := by rw [hKR', hR'top, Subgroup.map_top]
      rw [hK']
      exact hQ'
    · exfalso
      have hr1 := fundNoncentral_generic p t m e ht hadm hne R' hR' r hrR hzc
      apply hz.ne_one
      rw [← hrz, hr1, map_one]
  ·
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom i) hR
    have hR'top : R' = ⊤ := Set.mem_singleton_iff.mp hR'
    have hK' : K = (castHom hc (D.hom i)).range := by
      rw [hKR, ← hRR, hR'top, Subgroup.map_top]
    rw [hK', range_castHom]
    exact hQ
  ·
    have hM := Q3.m11Facts
    have hker := castHom_ker_le_center hc (D.hom i) (D.ker_le_center i)
    have hQ' : (castHom hc (D.hom i)).range.Normal := by
      rw [range_castHom]
      exact hQ
    have hquasi : CFSG.Open.IsQuasisimple (Q3.CompData.m11).G := Q3.isQuasisimple_m11 hM
    have hcomm := commutes_range_of_normal_pGroup hquasi (castHom hc (D.hom i)) hker hQ' hN2
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom i) hR
    have hKR' : K = R'.map (castHom hc (D.hom i)) := hKR.trans hRR.symm
    obtain ⟨r, hrR, hrz⟩ := Subgroup.mem_map.mp (hKR' ▸ hz.mem)
    have hzc := commutator_mem_center_of_commutes (castHom hc (D.hom i)) hker hcomm hrz hzN
    have hbot := Q3.center_m11_eq_bot hM
    have hrc : r ∈ Subgroup.center (Q3.CompData.m11).G := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := hzc y
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    exfalso
    apply hz.ne_one
    have hr1 : r = 1 := Subgroup.mem_bot.mp (hbot ▸ hrc)
    rw [← hrz, hr1, map_one]

theorem ihInterfaceU_of_thm4 (h4 : ∀ n : ℕ, CITBelowT (.sl2 p f) n → Thm4BelowU p f n) :
    IHInterfaceU p f :=
  fun n hn => ⟨h4 n hn, thm2BelowU_of_citBelowT hn⟩

end Thm2

end CFSG.ClassicalInvolution.Uniform
