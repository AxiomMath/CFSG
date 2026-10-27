module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.AdjDispTorus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.TwE6Rep27

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))


theorem chi_eq_one_of_hatH {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (hχ : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hK σ hσ a w) = 1) :
    ∀ h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ), χ h = 1 := by
  intro h hh
  obtain ⟨s, z, hz, rfl⟩ := exists_hatH_prod hf hK σ hσ hh
  obtain ⟨w, rfl⟩ := ker_eq_hatH hf hK σ hσ hz
  have hP : ∀ x ∈ (List.finRange TwistTag.E6.foldedTag.rank).map
      (fun a => hatH hf hK σ hσ a (s a)), x ∈ (twistedE6Datum hf hK σ hσ).H.comap
        (coverHom hf hK σ hσ) := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact hatH_mem_H hf hK σ hσ a (s a)
  have hone : ∀ x ∈ ((List.finRange TwistTag.E6.foldedTag.rank).map
      (fun a => hatH hf hK σ hσ a (s a))).map χ, x = 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hb
    exact hχ a (s a)
  have hQ : hatH hf hK σ hσ twN0 (mkOrbitUnit hK σ hσ twN0 orbit_card_twN0 w) *
      hatH hf hK σ hσ twN1 (mkOrbitUnit hK σ hσ twN1 orbit_card_twN1 (w ^ 2)) ∈
      (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ) :=
    mul_mem (hatH_mem_H hf hK σ hσ _ _) (hatH_mem_H hf hK σ hσ _ _)
  rw [chi_mul_cover hf hK σ hσ ht (Subgroup.list_prod_mem _ hP) hQ,
    chi_list_prod_cover hf hK σ hσ ht _ hP, List.prod_eq_one hone,
    chi_mul_cover hf hK σ hσ ht (hatH_mem_H hf hK σ hσ _ _) (hatH_mem_H hf hK σ hσ _ _)]
  simp only [hχ, mul_one, one_mul]

theorem sum_units_orbitField_eq_one (k : Type*) [Field k] [CharP k 2]
    (a : Fin TwistTag.E6.foldedTag.rank) [Fintype (orbitField TwistTag.E6 K σ a)ˣ] :
    ∑ _u : (orbitField TwistTag.E6 K σ a)ˣ, (1 : k) = 1 := by
  haveI : Fintype (orbitField TwistTag.E6 K σ a) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card (orbitField TwistTag.E6 K σ a) 2
  have h22 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  have hpow : ((2 ^ (n : ℕ) : ℕ) : k) = 0 := by
    rw [CharP.cast_eq_zero_iff k 2]
    exact dvd_pow_self 2 n.ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card,
    Nat.card_units, Nat.card_eq_fintype_card, hn, Nat.cast_sub Nat.one_le_two_pow, hpow,
    Nat.cast_one]
  linear_combination -h22

theorem coinvScalar_residual {k V : Type*} [Field k] [Algebra K k] [CharP k 2] [AddCommGroup V]
    [Module k V] {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ (Finset.univ.erase twN0))
    (hχ : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hK σ hσ a w) = 1)
    {μ : Fin TwistTag.E6.foldedTag.rank → k}
    (hμ : (twistedE6CoverData hf hK σ hσ).datum.IsCurtisType ρ y χ μ)
    (ω : List (Fin TwistTag.E6.foldedTag.rank)) :
    (twistedE6CoverData hf hK σ hσ).datum.coinvScalar χ μ ω = if twN0 ∈ ω then 0 else 1 := by
  have hfac : ∀ s : Fin TwistTag.E6.foldedTag.rank,
      μ s - (twistedE6CoverData hf hK σ hσ).datum.dScalar χ s = if s = twN0 then 0 else 1 := by
    intro s
    haveI : Fintype (orbitField TwistTag.E6 K σ s)ˣ := Fintype.ofFinite _
    have hd : (twistedE6CoverData hf hK σ hσ).datum.dScalar χ s =
        ∑ u : (orbitField TwistTag.E6 K σ s)ˣ, χ (hatH hf hK σ hσ s u) :=
      (twistedE6CoverRankOne hf hK σ hσ).dScalar_datum (twistedCover_hodd hf hK σ hσ) s χ
    by_cases hs : s = twN0
    · subst hs
      have hnot : twN0 ∉ Finset.univ.erase twN0 := fun h => (Finset.mem_erase.1 h).1 rfl
      rw [IsCoverType.mu_eq_dScalar (twistedCover_hodd hf hK σ hσ) ht hμ hnot, sub_self, if_pos rfl]
    · have hmem : s ∈ Finset.univ.erase twN0 := Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩
      have hμ0 : μ s = 0 := by
        rw [twisted_mu_eq hf hK σ hσ ht hμ s, if_neg]
        exact fun h => h.2 hmem
      rw [hμ0, zero_sub, hd, if_neg hs]
      simp only [hχ]
      rw [sum_units_orbitField_eq_one σ k s]
      exact neg_one_eq_one_iff.2 (ringChar.eq k 2)
  simp only [CurtisDatum.coinvScalar, hfac]
  induction ω with
  | nil => simp
  | cons s ω ih =>
    by_cases hs : s = twN0
    · subst hs
      simp
    · have hs' : twN0 ≠ s := fun h => hs h.symm
      simp [hs, hs', ih]

theorem coinvScalar_twRep27 {μ : Fin TwistTag.E6.foldedTag.rank → K}
    (hμ : (twistedE6CoverData hf hK σ hσ).datum.IsCurtisType (twRep27 σ)
      (e6Y27 : Fin e6Data.d →₀ K) (twChi27 σ) μ)
    (ω : List (Fin TwistTag.E6.foldedTag.rank)) :
    (twistedE6CoverData hf hK σ hσ).datum.coinvScalar (twChi27 σ) μ ω = 0 ↔ twN0 ∈ ω := by
  have ht := twRep27_isCoverType hf hK σ hσ
  have hfac : ∀ s : Fin TwistTag.E6.foldedTag.rank,
      μ s - (twistedE6CoverData hf hK σ hσ).datum.dScalar (twChi27 σ) s = 0 ↔ s = twN0 := by
    intro s
    haveI : Fintype (orbitField TwistTag.E6 K σ s)ˣ := Fintype.ofFinite _
    have hd : (twistedE6CoverData hf hK σ hσ).datum.dScalar (twChi27 σ) s =
        ∑ u : (orbitField TwistTag.E6 K σ s)ˣ, twChi27 σ (hatH hf hK σ hσ s u) :=
      (twistedE6CoverRankOne hf hK σ hσ).dScalar_datum (twistedCover_hodd hf hK σ hσ) s
        (twChi27 σ)
    by_cases hs : s = twN0
    · subst hs
      have hnot : twN0 ∉ Finset.univ.erase twA0 := fun h => (Finset.mem_erase.1 h).1 rfl
      rw [IsCoverType.mu_eq_dScalar (twistedCover_hodd hf hK σ hσ) ht hμ hnot, sub_self]
      simp
    · have hmem : s ∈ Finset.univ.erase twA0 := Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩
      have hall : ∀ u : (orbitField TwistTag.E6 K σ s)ˣ, twChi27 σ (hatH hf hK σ hσ s u) = 1 :=
        ((ht.2.2.2 s).1 hmem).1
      have hμ0 : μ s = 0 := by
        rw [twisted_mu_eq hf hK σ hσ ht hμ s, if_neg]
        exact fun h => h.2 hmem
      rw [hμ0, hd]
      simp only [hall]
      rw [sum_units_orbitField_eq_one σ K s]
      simp [hs]
  unfold CurtisDatum.coinvScalar
  rw [List.prod_eq_zero_iff, List.mem_map]
  constructor
  · rintro ⟨s, hs, h0⟩
    have h1 := (hfac s).1 h0
    rw [← h1]
    exact hs
  · intro h
    exact ⟨twN0, h, (hfac twN0).2 rfl⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
