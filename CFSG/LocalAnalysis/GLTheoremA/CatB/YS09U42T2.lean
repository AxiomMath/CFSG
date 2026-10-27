module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.TwoCentral

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.YS09U42T2

open CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43 CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

@[expose] def E0gens : List (List (Fin 45)) := [[4, 3, 1, 0], [15, 25]]

@[expose] def E0elems : List Tab :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 9, 10, 14, 12, 13, 35, 44, 42, 43, 38, 36, 37, 41, 39, 40, 15, 24, 22, 23, 18, 16, 17, 21, 19, 20, 25, 34, 32, 33, 28, 26, 27, 31, 29, 30],
   [0, 1, 2, 4, 5, 3, 7, 8, 6, 11, 9, 10, 14, 12, 13, 25, 34, 32, 33, 28, 26, 27, 31, 29, 30, 35, 44, 42, 43, 38, 36, 37, 41, 39, 40, 15, 24, 22, 23, 18, 16, 17, 21, 19, 20],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 9, 13, 14, 12, 25, 30, 31, 29, 33, 34, 32, 27, 28, 26, 35, 40, 41, 39, 43, 44, 42, 37, 38, 36, 15, 20, 21, 19, 23, 24, 22, 17, 18, 16],
   [0, 1, 2, 4, 5, 3, 7, 8, 6, 10, 11, 9, 13, 14, 12, 15, 20, 21, 19, 23, 24, 22, 17, 18, 16, 25, 30, 31, 29, 33, 34, 32, 27, 28, 26, 35, 40, 41, 39, 43, 44, 42, 37, 38, 36],
   [0, 1, 2, 5, 3, 4, 8, 6, 7, 10, 11, 9, 13, 14, 12, 35, 40, 41, 39, 43, 44, 42, 37, 38, 36, 15, 20, 21, 19, 23, 24, 22, 17, 18, 16, 25, 30, 31, 29, 33, 34, 32, 27, 28, 26],
   [0, 1, 2, 4, 5, 3, 7, 8, 6, 9, 10, 11, 12, 13, 14, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
   [0, 1, 2, 5, 3, 4, 8, 6, 7, 9, 10, 11, 12, 13, 14, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24],
   [0, 1, 2, 5, 3, 4, 8, 6, 7, 11, 9, 10, 14, 12, 13, 15, 24, 22, 23, 18, 16, 17, 21, 19, 20, 25, 34, 32, 33, 28, 26, 27, 31, 29, 30, 35, 44, 42, 43, 38, 36, 37, 41, 39, 40]]

@[expose] def E0par : List (ℕ × ℕ) := [(0, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (4, 1), (6, 1)]

@[expose] def E0act : List (List ℕ) := [[1, 3, 4, 0, 6, 7, 2, 8, 5], [2, 4, 5, 6, 7, 0, 8, 1, 3]]

theorem E0_enumOK : enumOK (E0gens.map wtab) E0elems E0par E0act = true := by
  decide +kernel

abbrev E0 : Subgroup (Equiv.Perm (Fin 45)) := gen (E0gens.map wperm)

theorem card_E0 : Nat.card E0 = 9 := (card_gen_words E0_enumOK).trans (by decide)

theorem E0_le_H0 : E0 ≤ H0 := le_H0_of_fix E0_enumOK (by decide +kernel)

theorem c_mem_E0 : wperm [4, 3, 1, 0] ∈ E0 := wperm_mem_gen (by simp [E0gens])

theorem e_mem_E : wperm [16, 15] ∈ E := wperm_mem_gen (ws := Egens) (by simp [Egens])

theorem c_noncomm : wperm [4, 3, 1, 0] * wperm [16, 15] ≠ wperm [16, 15] * wperm [4, 3, 1, 0] := by
  intro h
  have hA : Rep (wperm [4, 3, 1, 0] * wperm [16, 15])
      (tmul (wtab [4, 3, 1, 0]) (wtab [16, 15])) := rep_mul (rep_wperm _) (rep_wperm _)
  have hB : Rep (wperm [4, 3, 1, 0] * wperm [16, 15])
      (tmul (wtab [16, 15]) (wtab [4, 3, 1, 0])) := by
    rw [h]; exact rep_mul (rep_wperm _) (rep_wperm _)
  exact (by decide +kernel : ¬ (tmul (wtab [4, 3, 1, 0]) (wtab [16, 15]) =
    tmul (wtab [16, 15]) (wtab [4, 3, 1, 0]))) (rep_eq_tab hA hB)

theorem factorization_three_576 : (576 : ℕ).factorization 3 = 2 := by
  rw [show (576 : ℕ) = 3 ^ 2 * 64 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem exists_conj_E0 {F : Subgroup (Equiv.Perm (Fin 45))} (hF : F ≤ H0) (hFc : Nat.card F = 9) :
    ∃ h ∈ H0, F = E0.map (MulAut.conj h).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_conj_eq_of_card E0_le_H0 hF
    (by rw [card_E0, card_H0, factorization_three_576]; norm_num)
    (by rw [hFc, card_H0, factorization_three_576]; norm_num)

theorem exists_noncomm_conj_E0 {h : Equiv.Perm (Fin 45)} (hh : h ∈ H0) :
    ∃ x ∈ E, ∃ y ∈ E0.map (MulAut.conj h).toMonoidHom, x * y ≠ y * x := by
  have hN : ∀ x ∈ E, h * x * h⁻¹ ∈ E := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (H0_le_normalizer_E hh) x).1 hx
  refine ⟨h * wperm [16, 15] * h⁻¹, hN _ e_mem_E, h * wperm [4, 3, 1, 0] * h⁻¹,
    ⟨wperm [4, 3, 1, 0], c_mem_E0, rfl⟩, ?_⟩
  intro hc
  have hab : wperm [16, 15] * wperm [4, 3, 1, 0] = wperm [4, 3, 1, 0] * wperm [16, 15] := by
    calc wperm [16, 15] * wperm [4, 3, 1, 0]
        = h⁻¹ * ((h * wperm [16, 15] * h⁻¹) * (h * wperm [4, 3, 1, 0] * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * wperm [4, 3, 1, 0] * h⁻¹) * (h * wperm [16, 15] * h⁻¹)) * h := by rw [hc]
      _ = wperm [4, 3, 1, 0] * wperm [16, 15] := by group
  exact c_noncomm hab.symm

theorem exists_conj_of_sylow {z : Equiv.Perm (Fin 45)} (hz1 : z ≠ 1)
    {S : Subgroup (Equiv.Perm (Fin 45))} (hSP : S ≤ P) (hScard : Nat.card S = 64) (hzS : z ∈ S)
    (hSc : ∀ s ∈ S, z * s = s * z) : ∃ g ∈ P, z = g * tauPerm 0 * g⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgP, hSg⟩ := exists_conj_eq_of_card S0_le_P hSP card_S0_eq_P
    (by rw [hScard, card_P, factorization_two_25920]; norm_num)
  refine ⟨g, hgP, ?_⟩
  have hw : g⁻¹ * z * g ∈ S0 := by
    rw [hSg] at hzS
    obtain ⟨s, hs, hsz⟩ := hzS
    have hgs : g⁻¹ * z * g = s := by
      rw [← hsz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hgs]; exact hs
  have hcomm : ∀ t ∈ S0, (g⁻¹ * z * g) * t = t * (g⁻¹ * z * g) := by
    intro t ht
    have htS : g * t * g⁻¹ ∈ S := by
      rw [hSg]; exact ⟨t, ht, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hct := hSc _ htS
    calc (g⁻¹ * z * g) * t = g⁻¹ * (z * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * z) * g := by rw [hct]
      _ = t * (g⁻¹ * z * g) := by group
  rcases eq_of_mem_center_S0 hw hcomm with h | h
  · exact absurd (by
      have : z = 1 := by
        calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
      exact this) hz1
  · rw [← h]; group

theorem finite_P_part {z : Equiv.Perm (Fin 45)} (hzP : z ∈ P) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    {S : Subgroup (Equiv.Perm (Fin 45))} (hSP : S ≤ P) (hS2 : IsPGroup 2 S)
    (hScard : Nat.card S = 64) (hzS : z ∈ S) (hSc : ∀ s ∈ S, z * s = s * z)
    {F : Subgroup (Equiv.Perm (Fin 45))} (hFP : F ≤ P) (hFc : ∀ f ∈ F, z * f = f * z)
    (hFcard : Nat.card F = 9) :
    ∃ T : Subgroup (Equiv.Perm (Fin 45)), T ≤ P ∧ IsPGroup 2 T ∧ Nat.card T = 32 ∧
      (∀ f ∈ F, ∀ t ∈ T, f * t * f⁻¹ ∈ T) ∧ ∃ x ∈ T, ∃ y ∈ F, x * y ≠ y * x := by
  obtain ⟨g, hgP, rfl⟩ := exists_conj_of_sylow hz1 hSP hScard hzS hSc
  have hFH : ∀ f ∈ F, g⁻¹ * f * g ∈ H0 := by
    intro f hf
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hgP) (hFP hf)) hgP, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := hFc f hf
    calc g⁻¹ * f * g * tauPerm 0 = g⁻¹ * (f * (g * tauPerm 0 * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * tauPerm 0 * g⁻¹) * f) * g := by rw [hc]
      _ = tauPerm 0 * (g⁻¹ * f * g) := by group
  set F' : Subgroup (Equiv.Perm (Fin 45)) := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'
  have hF'H : F' ≤ H0 := by
    rintro _ ⟨f, hf, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hFH f hf
  have hF'c : Nat.card F' = 9 := by
    rw [hF', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hFcard]
  obtain ⟨h, hh, hFeq⟩ := exists_conj_E0 hF'H hF'c
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := exists_noncomm_conj_E0 hh
  have hy₀F' : y₀ ∈ F' := by rw [hFeq]; exact hy₀
  obtain ⟨f₀, hf₀, hf₀y⟩ := hy₀F'
  have hT_le : E.map (MulAut.conj g).toMonoidHom ≤ P := by
    rintro _ ⟨e, he, rfl⟩
    have heP : e ∈ P := (Subgroup.mem_inf.1 (E_le_H0 he)).1
    show g * e * g⁻¹ ∈ P
    exact mul_mem (mul_mem hgP heP) (inv_mem hgP)
  have hTc : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 32 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_E]
  have hT2 : IsPGroup 2 (E.map (MulAut.conj g).toMonoidHom) :=
    IsPGroup.of_card (n := 5) (by rw [hTc]; norm_num)
  have hTn : ∀ f ∈ F, ∀ t ∈ E.map (MulAut.conj g).toMonoidHom,
      f * t * f⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom := by
    intro f hf t ht
    obtain ⟨e, he, rfl⟩ := ht
    have hk := hFH f hf
    refine ⟨(g⁻¹ * f * g) * e * (g⁻¹ * f * g)⁻¹, ?_, ?_⟩
    · exact ((Subgroup.mem_normalizer_iff.1 (H0_le_normalizer_E hk) e).1 he)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hf₀eq : f₀ = g * y₀ * g⁻¹ := by
    rw [← hf₀y]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  refine ⟨E.map (MulAut.conj g).toMonoidHom, hT_le, hT2, hTc, hTn,
    (MulAut.conj g).toMonoidHom x₀, Subgroup.mem_map_of_mem _ hx₀, f₀, hf₀, ?_⟩
  intro hc
  apply hxy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc
  rw [hf₀eq] at hc
  have hc' : g * (x₀ * y₀) * g⁻¹ = g * (y₀ * x₀) * g⁻¹ := by
    calc g * (x₀ * y₀) * g⁻¹ = g * x₀ * g⁻¹ * (g * y₀ * g⁻¹) := by group
      _ = g * y₀ * g⁻¹ * (g * x₀ * g⁻¹) := hc
      _ = g * (y₀ * x₀) * g⁻¹ := by group
  calc x₀ * y₀ = g⁻¹ * (g * (x₀ * y₀) * g⁻¹) * g := by group
    _ = g⁻¹ * (g * (y₀ * x₀) * g⁻¹) * g := by rw [hc']
    _ = y₀ * x₀ := by group

theorem finite_psp43_part {z : CFSG.GH74.Exceptional.PSp43} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    {S : Subgroup CFSG.GH74.Exceptional.PSp43} (hS2 : IsPGroup 2 S)
    (hScard : Nat.card S = 64) (hzS : z ∈ S) (hSc : ∀ s ∈ S, z * s = s * z)
    {F : Subgroup CFSG.GH74.Exceptional.PSp43} (hFc : ∀ f ∈ F, z * f = f * z)
    (hFcard : Nat.card F = 9) :
    ∃ T : Subgroup CFSG.GH74.Exceptional.PSp43, IsPGroup 2 T ∧ Nat.card T = 32 ∧
      (∀ f ∈ F, ∀ t ∈ T, f * t * f⁻¹ ∈ T) ∧ ∃ x ∈ T, ∃ y ∈ F, x * y ≠ y * x := by
  have hinj : Function.Injective CFSG.ComponentClassification.CatFactsSmall.PSp43.psi :=
    psi_injective'
  have hPr := range_psi_eq
  set ψ := CFSG.ComponentClassification.CatFactsSmall.PSp43.psi with hψ
  have hSP : S.map ψ ≤ P := by
    rw [← hPr]; exact Subgroup.map_le_range ψ S
  have hS'card : Nat.card (S.map ψ) = 64 := by
    rw [Subgroup.card_map_of_injective hinj, hScard]
  have hS'2 : IsPGroup 2 (S.map ψ) := IsPGroup.of_card (n := 6) (by rw [hS'card]; norm_num)
  have hFP : F.map ψ ≤ P := by
    rw [← hPr]; exact Subgroup.map_le_range ψ F
  have hF'card : Nat.card (F.map ψ) = 9 := by
    rw [Subgroup.card_map_of_injective hinj, hFcard]
  have hz2' : ψ z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have hz1' : ψ z ≠ 1 := fun h => hz1 (hinj (h.trans (map_one ψ).symm))
  have hzP : ψ z ∈ P := by rw [← hPr]; exact ⟨z, rfl⟩
  have hSc' : ∀ s ∈ S.map ψ, ψ z * s = s * ψ z := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hSc s hs]
  have hFc' : ∀ f ∈ F.map ψ, ψ z * f = f * ψ z := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul, hFc f hf]
  obtain ⟨TP, hTPP, hTP2, hTPc, hTPn, x, hx, y, hy, hxy⟩ :=
    finite_P_part hzP hz2' hz1' hSP hS'2 hS'card (Subgroup.mem_map_of_mem ψ hzS) hSc' hFP hFc'
      hF'card
  have hTPr : TP ≤ ψ.range := by rw [hPr]; exact hTPP
  have hmap : (TP.comap ψ).map ψ = TP := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hTPr]
  have hcardT : Nat.card (TP.comap ψ) = 32 := by
    have h1 := Subgroup.card_map_of_injective (f := ψ) hinj (K := TP.comap ψ)
    rw [hmap, hTPc] at h1
    exact h1.symm
  refine ⟨TP.comap ψ, IsPGroup.of_card (n := 5) (by rw [hcardT]; norm_num), hcardT, ?_, ?_⟩
  · intro f hf t ht
    rw [Subgroup.mem_comap] at ht ⊢
    have := hTPn (ψ f) (Subgroup.mem_map_of_mem ψ hf) (ψ t) ht
    simpa [map_mul, map_inv] using this
  · obtain ⟨xb, hxb⟩ := hTPr hx
    obtain ⟨yb, hybF, hyb⟩ := hy
    refine ⟨xb, Subgroup.mem_comap.2 (hxb ▸ hx), yb, hybF, ?_⟩
    intro hc
    apply hxy
    rw [← hxb, ← hyb, ← map_mul, ← map_mul, hc]

end CFSG.LocalAnalysis.GLTheoremA.CatB.YS09U42T2
