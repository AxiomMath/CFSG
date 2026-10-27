module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimpleLocal
public import CFSG.LargeExtraspecial.AS35WL4
public import CFSG.LargeExtraspecial.AS35WU4
public import CFSG.LargeExtraspecial.AS35WSp4Gen
public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Cls

public section

open Subgroup CFSG.Blueprint

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

theorem not_sq_dvd_nine_sixty {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    ¬ (p ^ f) ^ 2 ∣ 960 := by
  intro h
  have h1 : p ^ 2 ∣ 960 := (pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 2).trans h
  have h2 : p ^ 2 ≤ 960 := Nat.le_of_dvd (by norm_num) h1
  have h3 : p ≤ 30 := by nlinarith
  interval_cases p <;> revert hp hp2 h1 <;> decide

theorem not_cube_dvd_nine_sixty {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    ¬ (p ^ f) ^ 3 ∣ 960 := fun h =>
  CFSG.LargeExtraspecial.AS35W.not_cube_dvd hp hp2 hf (h.trans (by norm_num))

theorem eq_three_or_five_of_pow_dvd_nine_sixty {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h : p ^ f ∣ 960) : p ^ f = 3 ∨ p ^ f = 5 := by
  have h1 : p ∣ 960 := (dvd_pow_self p (by omega)).trans h
  have h15 : p ∣ 15 := by
    have h' : p ∣ 2 ^ 6 * 15 := by norm_num; exact h1
    rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)) hp2
    · exact h2
  have hp15 : p ≤ 15 := Nat.le_of_dvd (by norm_num) h15
  have hsq : ¬ p ^ 2 ∣ 960 := by
    intro h2
    exact not_sq_dvd_nine_sixty hp hp2 (le_refl 1) (by simpa using h2)
  have hf1 : f = 1 := by
    by_contra hne
    have hf2 : 2 ≤ f := by omega
    exact hsq ((pow_dvd_pow p hf2).trans h)
  subst hf1
  rw [pow_one] at h ⊢
  interval_cases p <;> revert hp hp2 h15 <;> decide

open CFSG.LocalAnalysis.ComponentInitial in
theorem AlmostSimpleLocal.false_of_lieModel_psl_four {T : Type} [Group T] {u : T}
    (h : AlmostSimpleLocal T u) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hM : LieModel T .PSL 4 p f) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hM
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h' := h.map e
  have hdvd := (CFSG.LargeExtraspecial.AS35W.sq_dvd_card_centralizer_L4 hodd h'.orderOf_eq).trans
    h'.card_dvd
  rw [hK] at hdvd
  exact not_sq_dvd_nine_sixty hp hp2 hf hdvd

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
theorem AlmostSimpleLocal.false_of_lieModel_psu_four {T : Type} [Group T] {u : T}
    (h : AlmostSimpleLocal T u) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : p ^ f % 4 = 1) (hM : LieModel T .PSU 4 p f) : False := by
  obtain ⟨K, _, _, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (T ≃* StatedProj (StatedSU 4 (p ^ f) K)) := by
    rcases hM with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hdata : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) hdata
  have e : T ≃* hypPSU hdata 2 0 := e₀.trans (hypPSUEquivStatedProj hdata hR₀ (by omega)).symm
  have h' := h.map e
  have hdvd := (CFSG.LargeExtraspecial.AS35W.sq_dvd_card_centralizer_U4 hdata hp2 hq
    h'.orderOf_eq).trans h'.card_dvd
  exact not_sq_dvd_nine_sixty hp hp2 hf hdvd

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer in
theorem AlmostSimpleLocal.false_of_lieModel_psl_five {T : Type} [Group T] {u : T}
    (h : AlmostSimpleLocal T u) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f % 4 = 3)
    (hM : LieModel T .PSL 5 p f) : False := by
  have hp2 : p ≠ 2 := CFSG.LargeExtraspecial.AS35W.ne_two_of_mod_four hf (Or.inl hq)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hM
  have hz' := h.map e
  obtain ⟨g, hg⟩ := proj_surjective 5 K (e u)
  rw [← hg] at hz'
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hK]
    have : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨k, hk⟩ := this
    omega
  have hz2 : proj 5 K g ^ 2 = 1 := by rw [← hz'.orderOf_eq, pow_orderOf_eq_one]
  have hB : conjAut (3 + 2) K (Matrix.SpecialLinearGroup.toGL g) ^ 2 = 1 := by
    change conjAut 5 K (Matrix.SpecialLinearGroup.toGL g) ^ 2 = 1
    rw [conjAut_toGL, ← map_pow, hz2, map_one]
  obtain ⟨ρ, hρ, hfix⟩ := Odd87.exists_fixed_sl3_block hchar _ hB
  have hle : ρ.range ≤ centralizer ({proj 5 K g} : Set (projectiveSL 5 K)) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hfix s
    change conjAut 5 K (Matrix.SpecialLinearGroup.toGL g) (ρ s) = ρ s at h1
    rw [conjAut_toGL, MulAut.conj_apply] at h1
    calc ρ s * proj 5 K g = proj 5 K g * ρ s * (proj 5 K g)⁻¹ * proj 5 K g := by rw [h1]
      _ = proj 5 K g * ρ s := by group
  have hdvd := hz'.card_dvd_of_le hle
  rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv] at hdvd
  have h3 : (p ^ f) ^ 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [card_SL_eq (by norm_num), hK]
    exact Dvd.intro _ rfl
  exact not_cube_dvd_nine_sixty hp hp2 hf (h3.trans hdvd)

open CFSG.GH74.GLS.Stage2.Signalizer CFSG.ClassicalGroups.UnitaryFlag in
theorem AlmostSimpleLocal.false_of_lieModel_psu_five {T : Type} [Group T] {u : T}
    (h : AlmostSimpleLocal T u) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f % 4 = 1)
    (hM : LieModel T .PSU 5 p f) : False := by
  have hp2 : p ≠ 2 := CFSG.LargeExtraspecial.AS35W.ne_two_of_mod_four hf (Or.inr hq)
  obtain ⟨K, _, _, hdat, -, ⟨e⟩⟩ := Odd87.exists_unitaryData_equiv hp hf hM
  have hz' := h.map e
  have hz2 : e u ^ 2 = 1 := by
    have := pow_orderOf_eq_one (e u)
    rwa [hz'.orderOf_eq] at this
  have hα : (MulAut.conj (e u)) ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  rcases Odd87.unitary5_involution_cases hdat hp2 _ hα with ⟨ψ, hψ, hfix⟩ | ⟨hni, -⟩
  · have hle : ((hypProj hdat 2 1).comp ψ).range ≤ centralizer ({e u} : Set _) := by
      intro s hs
      rw [mem_centralizer_singleton_iff]
      have h1 := hfix s hs
      rw [MulAut.conj_apply] at h1
      calc s * e u = e u * s * (e u)⁻¹ * e u := by rw [h1]
        _ = e u * s := by group
    have hdvd := hz'.card_dvd_of_le hle
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv] at hdvd
    have h3 : (p ^ f) ^ 3 ∣ Nat.card ↥(unitarySU p f K 3) := by
      rw [Odd87.card_unitarySU_three hdat, mul_assoc]
      exact Dvd.intro _ rfl
    exact not_cube_dvd_nine_sixty hp hp2 hf (h3.trans hdvd)
  · exact hni (e u) rfl

open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank in
theorem AlmostSimpleLocal.false_of_lieModel_psp_two {T : Type} [Group T] [Finite T] {u : T}
    (h : AlmostSimpleLocal T u) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hM : LieModel T .PSp 2 p f) (hq : p ^ f ≠ 5) : False := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hM
  have : Finite (StatedProj (StatedSp 2 K)) := Finite.of_equiv T e.toEquiv
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hz' := h.map e
  obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd (u := e u) hz'.orderOf_eq
  have hz'' := hz'.map (MulAut.conj g⁻¹)
  have hgz : MulAut.conj g⁻¹ (e u) = g⁻¹ * e u * g := by rw [MulAut.conj_apply, inv_inv]
  rw [hgz] at hz''
  rcases hg with hg | hg <;> rw [hg] at hz''
  · have hdvd := (CFSG.LargeExtraspecial.AS35W.sq_dvd_card_X0 hodd).trans
      (hz''.card_dvd_of_le X0_le_centralizer)
    rw [hK] at hdvd
    exact not_sq_dvd_nine_sixty hp hp2 hf hdvd
  · have hLdvd : Nat.card (Lsub K) ∣ 960 := hz''.card_dvd_of_le Lsub_le_centralizer
    rw [CFSG.GH74.GLS.Stage2.Local.P34.card_Lsub hodd] at hLdvd
    have hqL : Nat.card K ∣ Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
      obtain ⟨k, hk⟩ := hodd
      rw [hk]
      refine ⟨2 * k * (k + 1), ?_⟩
      have h1 : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by
        have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
        omega
      rw [h1, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    have hq960 : p ^ f ∣ 960 := by
      rw [← hK]
      exact hqL.trans hLdvd
    rcases eq_three_or_five_of_pow_dvd_nine_sixty hp hp2 hf hq960 with h3 | h5
    · obtain ⟨M, hM1, hMperf, hMcard⟩ := hz''.exists_perfect
      have hML := perfect_le_L (two_ne_zero_of_odd_card hodd) hM1 hMperf
      have hle : Nat.card ↥M ≤ Nat.card ↥(Lsub K) :=
        Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hML)
      rw [CFSG.GH74.GLS.Stage2.Local.P34.card_Lsub hodd, hMcard, hK, h3] at hle
      norm_num at hle
    · exact hq h5

end CFSG.EvenSporadicStandard.TwoHS.GH312
