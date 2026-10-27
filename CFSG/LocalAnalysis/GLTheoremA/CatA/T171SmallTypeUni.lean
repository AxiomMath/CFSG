module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeUniTorus
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
public import CFSG.RankThree.PartOne.FOC.PSUModel
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBadCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Dickson.Sec6.I1431

theorem wit5_of_cover {Y : Type} [Group Y] {S : Type} [Group S]
    (ρ : S →* Y) {E₀ U₀ : Subgroup S} (hE : IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 5)
    (hρZ : ∀ g ∈ E₀, ρ g ∈ Subgroup.center Y → g = 1)
    (hU2 : IsPGroup 2 U₀) (hU : ∃ u ∈ U₀, ρ u ∉ Subgroup.center Y)
    (hnorm : ∀ e ∈ E₀, ∀ u ∈ U₀, e * u * e⁻¹ ∈ U₀) : Wit5 Y := by
  have hρ1 : ∀ g ∈ E₀, ρ g = 1 → g = 1 := fun g hg h =>
    hρZ g hg (by rw [h]; exact Subgroup.one_mem _)
  have hcardE : Nat.card (E₀.map ρ) = Nat.card E₀ := by
    refine (Nat.card_congr
      (Equiv.ofBijective (fun x : E₀ => (⟨ρ x, x, x.2, rfl⟩ : E₀.map ρ)) ⟨?_, ?_⟩)).symm
    · intro x y hxy
      have h : ρ (x : S) = ρ (y : S) := congrArg Subtype.val hxy
      have hxy' : (x : S)⁻¹ * y = 1 :=
        hρ1 _ (E₀.mul_mem (E₀.inv_mem x.2) y.2) (by rw [map_mul, map_inv, h, inv_mul_cancel])
      exact Subtype.ext (inv_mul_eq_one.1 hxy')
    · rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hEZ : E₀.map ρ ⊓ Subgroup.center Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro y ⟨⟨x, hx, rfl⟩, hyZ⟩
    rw [hρZ x hx hyZ, map_one]
  have hUne : U₀.map ρ ≠ ⊥ := by
    obtain ⟨u, hu, hπu⟩ := hU
    intro hbot
    have hmem : ρ u ∈ U₀.map ρ := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hπu (by rw [hmem]; exact Subgroup.one_mem _)
  have hnorm' : E₀.map ρ ≤ Subgroup.normalizer ((U₀.map ρ : Subgroup Y) : Set Y) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨e * u * e⁻¹, hnorm e he u hu, by simp only [map_mul, map_inv]⟩
    · rintro ⟨u, hu, hu'⟩
      refine ⟨e⁻¹ * u * e, by simpa using hnorm e⁻¹ (E₀.inv_mem he) u hu, ?_⟩
      rw [map_mul, map_mul, map_inv, hu']
      group
  exact ⟨E₀.map ρ, hE.map ρ, hcardE.trans hcard, hEZ, U₀.map ρ, hU2.map ρ, hUne, hnorm'⟩

theorem uniHighWit_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : UniHighWit := by
  intro n q hv hq hn Y hGY hFinY hY he
  letI := hGY
  letI := hFinY
  obtain ⟨e⟩ := he
  obtain ⟨hp, hf⟩ := CFSG.LocalAnalysis.GLTheoremA.I1431C2.cl_primePower_card_two hq
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv e
  rw [hp, hf] at hC
  obtain ⟨K, _, _, h, -, -, ⟨e0⟩⟩ := CFSG.RankThree.PartOne.FOC.exists_psu_model hC
  haveI : CharP K 2 := h.charP
  have hdvd : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have h2 : ¬(n + 1 = 6 ∧ 2 = 2 ∧ 1 = 1) := fun ⟨ha, _, _⟩ => by omega
  have hKcard : Nat.card K = 4 := by
    rw [h.card]
    norm_num
  have h3K : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hKcard]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 := exists_prime_orderOf_dvd_card' 3 h3K
  have hroots : Nat.card (rootsOfUnity 3 K) = 3 := by
    have hdvdc : Nat.card (rootsOfUnity 3 K) ∣ Nat.card Kˣ :=
      Subgroup.card_subgroup_dvd_card (rootsOfUnity 3 K)
    have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hKcard]
    rw [h3] at hdvdc
    exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvdc) (three_le_card_roots (K := K) hζ)
  obtain ⟨ρ, hρ⟩ := exists_suHom_to_cover hGA h hC e0 (by omega) h2
    (QuotientGroup.mk' (Subgroup.center Y)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le
  have hn7 : 7 ≤ n + 1 := by omega
  have hE : IsElemAbelian 3 (suTorus5 h hdvd hn7).range :=
    isElemAbelian_range (suTorus5 h hdvd hn7) (fun w => pow_three_eq_one_five w)
  have hcard : Nat.card (suTorus5 h hdvd hn7).range = 3 ^ 5 :=
    suTorus5_card h hdvd hn7 hroots
  have hρZ : ∀ g ∈ (suTorus5 h hdvd hn7).range, ρ g ∈ Subgroup.center Y → g = 1 := by
    rintro _ ⟨w, rfl⟩ hg
    have h1 : e0.symm ((QuotientGroup.mk' (normOneScalars h
        (gramSU h (idGram K (n + 1))) (n + 1))) (suTorus5 h hdvd hn7 w)) = 1 := by
      rw [← hρ]
      exact (QuotientGroup.eq_one_iff _).2 hg
    have h3 : (QuotientGroup.mk' (normOneScalars h
        (gramSU h (idGram K (n + 1))) (n + 1))) (suTorus5 h hdvd hn7 w) = 1 := by
      have h4 := congrArg e0 h1
      simpa using h4
    rw [suTorus5_normOne h hdvd hn7 ((QuotientGroup.eq_one_iff _).1 h3), map_one]
  have hU : ∃ u ∈ Subgroup.zpowers (swapSU h hn7), ρ u ∉ Subgroup.center Y := by
    refine ⟨swapSU h hn7, Subgroup.mem_zpowers _, ?_⟩
    intro hg
    have h1 : e0.symm ((QuotientGroup.mk' (normOneScalars h
        (gramSU h (idGram K (n + 1))) (n + 1))) (swapSU h hn7)) = 1 := by
      rw [← hρ]
      exact (QuotientGroup.eq_one_iff _).2 hg
    have h3 : (QuotientGroup.mk' (normOneScalars h
        (gramSU h (idGram K (n + 1))) (n + 1))) (swapSU h hn7) = 1 := by
      have h4 := congrArg e0 h1
      simpa using h4
    obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq_one_iff _).1 h3
    exact swapGL_not_scalar (by simp [Fin.ext_iff]) c hc
  exact wit5_of_cover ρ hE hcard hρZ
    (isElemAbelian_zpowers (swapSU_sq h hn7)).isPGroup hU
    (by
      rintro _ ⟨w, rfl⟩ _ ⟨k, rfl⟩
      have hc := suTorus5_commute_swapSU h hdvd hn7 w
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k)

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
