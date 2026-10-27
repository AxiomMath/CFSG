module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnA
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnField
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Un

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87


theorem un_primeForm_model {Y : Type} [Group Y] {n p f : ℕ} (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) (hLie : LieModel Y .PSU n p f) :
    p.Prime ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData p f K),
      Nonempty (Y ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨hp, hf, F, _, _, hF, ⟨e₀⟩⟩ := Generic.lieModel_psu_data hLie
  have h : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_one (n := n)) hn hq
  exact ⟨hp, F, inferInstance, inferInstance, h,
    ⟨(e₀.trans (unitaryPSUEquiv h (by omega)).symm).trans eT.symm⟩⟩

theorem un_hyp_model {Y : Type} [Group Y] {n p f : ℕ} (r ε : ℕ) (hrε : 2 * r + ε = n)
    (hn : 1 ≤ n) (hLie : LieModel Y .PSU n p f) :
    p.Prime ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData p f K),
      Nonempty (Y ≃* hypPSU h r ε) := by
  subst hrε
  obtain ⟨hp, hf, F, _, _, hF, ⟨e₀⟩⟩ := Generic.lieModel_psu_data hLie
  have h : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  exact ⟨hp, F, inferInstance, inferInstance, h, ⟨e₀.trans (hypPSUEquivStatedProj h hR hn).symm⟩⟩

theorem un_caseA_of_lieModel {Y : Type} [Group Y] {n p f : ℕ} (hn : n = 4 ∨ n = 5) (hp2 : p ≠ 2)
    (hLie : LieModel Y .PSU n p f) (hcen : Subgroup.center Y = ⊥) {V Z : Subgroup (MulAut Y)}
    (h2 : N2Cfg Y p V Z) (h3 : N3Full Y V Z) : False := by
  obtain ⟨-, K, _, _, h, ⟨e⟩⟩ := un_hyp_model 2 (n - 4) (by omega) (by omega) hLie
  have hcen' : Subgroup.center (hypPSU h 2 (n - 4)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    have : y ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      apply e.injective
      simpa using hx (e g)
    rw [hcen, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  exact un_caseA h (by norm_num) (by omega) (by omega) hp2 hcen'
    (h2.map_mulEquiv (MulAut.congr e)) (h3.map_mulEquiv e)

@[expose] def UnLeafPlus (n : ℕ) : Prop :=
  ∀ {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K), (n = 4 ∨ n = 5) → p ≠ 2 →
    ∀ {r : ℕ}, r ≠ p → r ∣ p ^ f + 1 →
    ∀ {V Z : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))},
      V ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      N2Cfg (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) r V Z →
      N3Deriv (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) V Z → False

@[expose] def UnLeafMinus (n : ℕ) : Prop :=
  ∀ {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K), (n = 4 ∨ n = 5) →
    ∀ {r : ℕ}, r ≠ p → ¬ r ∣ p ^ f + 1 →
    ∀ {V Z : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))},
      V ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      N2Cfg (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) r V Z →
      N3Full (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) V Z → False

theorem cf67CoreFull_Un {n : ℕ} (hn : n = 4 ∨ n = 5) (hplus : UnLeafPlus n)
    (hminus : UnLeafMinus n) {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hLie : LieModel Y .PSU n p f) : CF67CoreFull Y := by
  intro hs hnab r V Z h2 h3
  have hcen : Subgroup.center Y = ⊥ := un_center_eq_bot_of_simple hs hnab
  by_cases hrp : r = p
  · subst hrp
    exact un_caseA_of_lieModel hn hp2 hLie hcen h2 h3
  · have hq : ¬(n = 3 ∧ p ^ f = 2) := by omega
    obtain ⟨-, K, _, _, h, ⟨eT⟩⟩ := un_primeForm_model (by omega) hq hLie
    have h2' := h2.map_mulEquiv (MulAut.congr eT)
    have h3' := h3.map_mulEquiv eT
    by_cases hVD : V.map (MulAut.congr eT).toMonoidHom ≤
        primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    · by_cases hrq : r ∣ p ^ f + 1
      · exact hplus h hn hp2 hrp hrq hVD h2' h3'.deriv
      · exact hminus h hn hrp hrq hVD h2' h3'
    · exact false_of_u_noninner h (by omega) hq hp2 hrp h2' h3'.deriv hVD

theorem cf67CoreDeriv_U5_five (hplus : UnLeafPlus 5) {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hp2 : p ≠ 2) (h5 : 5 ∣ p ^ f + 1) (hLie : LieModel Y .PSU 5 p f) : CF67CoreDeriv Y 5 := by
  have hq : ¬(5 = 3 ∧ p ^ f = 2) := by omega
  obtain ⟨hp, K, _, _, h, ⟨eT⟩⟩ := un_primeForm_model (by norm_num) hq hLie
  refine CF67CoreDeriv.of_mulEquiv eT ?_
  intro hs hn V Z h2 h3
  have hrp : (5 : ℕ) ≠ p := by
    rintro rfl
    have h1 : 5 ∣ 5 ^ f := dvd_pow_self 5 (by
      rintro rfl
      simp at h5)
    have := (Nat.dvd_add_right h1).mp h5
    omega
  by_cases hVD : V ≤ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  · exact hplus h (Or.inr rfl) hp2 hrp h5 hVD h2 h3
  · exact false_of_u_noninner h (by norm_num) hq hp2 hrp h2 h3 hVD

theorem U5_cover_odd (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) {p f : ℕ}
    (hLie : LieModel (J ⧸ center J) .PSU 5 p f) {r : ℕ} (hr : r.Prime)
    (hd : r ∣ Nat.card (center J)) : r = 5 ∧ 5 ∣ p ^ f + 1 := by
  have hM : Models.LieModel (J ⧸ center J) .PSU 5 p f :=
    CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hLie
  have hgen : genericOrders .PSU 5 p f = (Nat.gcd 5 (p ^ f + 1), 1) := by
    unfold genericOrders; rfl
  have hex : exceptionalOrders .PSU 5 p f = (1, 1) := by
    unfold exceptionalOrders; split <;> simp_all
  have hpos : 0 < Nat.gcd 5 (p ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hne : (genericOrders .PSU 5 p f).1 * (genericOrders .PSU 5 p f).2 *
      ((exceptionalOrders .PSU 5 p f).1 * (exceptionalOrders .PSU 5 p f).2) ≠ 0 := by
    rw [hex, hgen]; simp
  have h := hd.trans (card_center_dvd_table hGA hJ hM hne)
  rw [hex, hgen] at h
  have h1 : r ∣ Nat.gcd 5 (p ^ f + 1) := by simpa using h
  have hr5 : r = 5 :=
    (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp (h1.trans (Nat.gcd_dvd_left _ _))
  exact ⟨hr5, by rw [← hr5]; exact h1.trans (Nat.gcd_dvd_right _ _)⟩

theorem exceptional_PSU4_of_ne {p f : ℕ} (hp2 : p ≠ 2) (h31 : ¬(p = 3 ∧ f = 1)) :
    exceptionalOrders .PSU 4 p f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem U4_cover_odd (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) {p f : ℕ} (hp2 : p ≠ 2)
    (hLie : LieModel (J ⧸ center J) .PSU 4 p f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd : r ∣ Nat.card (center J)) : r = 3 ∧ p = 3 ∧ f = 1 := by
  have hM : Models.LieModel (J ⧸ center J) .PSU 4 p f :=
    CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hLie
  have hgen : genericOrders .PSU 4 p f = (Nat.gcd 4 (p ^ f + 1), 1) := by
    unfold genericOrders; rfl
  by_cases h31 : p = 3 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h31
    have hex : exceptionalOrders .PSU 4 3 1 = (3, 3) := by
      unfold exceptionalOrders; rfl
    have hne : (genericOrders .PSU 4 3 1).1 * (genericOrders .PSU 4 3 1).2 *
        ((exceptionalOrders .PSU 4 3 1).1 * (exceptionalOrders .PSU 4 3 1).2) ≠ 0 := by
      rw [hex, hgen]; norm_num
    have h := hd.trans (card_center_dvd_table hGA hJ hM hne)
    rw [hex, hgen] at h
    have h36 : r ∣ 36 := by norm_num at h; exact h
    have hr36 : r ∣ 2 ^ 2 * 3 ^ 2 := by norm_num; exact h36
    rcases (Nat.Prime.dvd_mul hr).mp hr36 with h4 | h9
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h4)) hr2
    · exact ⟨(Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h9), rfl, rfl⟩
  · exfalso
    have hex := exceptional_PSU4_of_ne hp2 h31
    have hpos : 0 < Nat.gcd 4 (p ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hne : (genericOrders .PSU 4 p f).1 * (genericOrders .PSU 4 p f).2 *
        ((exceptionalOrders .PSU 4 p f).1 * (exceptionalOrders .PSU 4 p f).2) ≠ 0 := by
      rw [hex, hgen]; simp
    have h := hd.trans (card_center_dvd_table hGA hJ hM hne)
    rw [hex, hgen] at h
    have h1 : r ∣ Nat.gcd 4 (p ^ f + 1) := by simpa using h
    have h4 : r ∣ 4 := h1.trans (Nat.gcd_dvd_left _ _)
    have h22 : r ∣ 2 ^ 2 := by norm_num; exact h4
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h22))

theorem FU5_data {Y : Type} [Group Y] (hY : FU5 Y) :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ LieModel Y .PSU 5 p f := by
  obtain ⟨p, f, hp, hf, hq4, hLie⟩ := hY
  refine ⟨p, f, hp, hf, ?_, hLie⟩
  rintro rfl
  have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  omega

theorem cf67CoreFull_U5 (hplus : UnLeafPlus 5) (hminus : UnLeafMinus 5) (Y : Type) [Group Y]
    [Finite Y] (hY : FU5 Y) : CF67CoreFull Y := by
  obtain ⟨p, f, -, -, hp2, hLie⟩ := FU5_data hY
  exact cf67CoreFull_Un (Or.inr rfl) hplus hminus hp2 hLie

theorem cf67CoreFull_U4 (hplus : UnLeafPlus 4) (hminus : UnLeafMinus 4) (Y : Type) [Group Y]
    [Finite Y] (hY : FU4 Y) : CF67CoreFull Y := by
  obtain ⟨p, f, -, -, hp2, -, hLie⟩ := hY
  exact cf67CoreFull_Un (Or.inl rfl) hplus hminus hp2 hLie

theorem cf67CoreDeriv_U5_cover (hplus : UnLeafPlus 5)
    (hGA : CFSG.Open.GriessAllModelsStatement) {J : Type}
    [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FU5 (J ⧸ center J)) {r : ℕ}
    (hr : r.Prime) (hd : r ∣ Nat.card (center J)) : CF67CoreDeriv (J ⧸ center J) r := by
  obtain ⟨p, f, -, -, hp2, hLie⟩ := FU5_data hY
  obtain ⟨rfl, h5⟩ := U5_cover_odd hGA hJ hLie hr hd
  exact cf67CoreDeriv_U5_five hplus hp2 h5 hLie

theorem cf67CoreDeriv_U4_cover
    (hUD : ∀ {Y : Type} [Group Y] [Finite Y], LieModel Y .PSU 4 3 1 → CF67CoreDeriv Y 3)
    (hGA : CFSG.Open.GriessAllModelsStatement) {J : Type}
    [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FU4 (J ⧸ center J)) {r : ℕ}
    (hr : r.Prime) (hr2 : Odd r) (hd : r ∣ Nat.card (center J)) :
    CF67CoreDeriv (J ⧸ center J) r := by
  obtain ⟨p, f, -, -, hp2, -, hLie⟩ := hY
  have hr2' : r ≠ 2 := by
    rintro rfl
    exact absurd hr2 (by decide)
  obtain ⟨rfl, rfl, rfl⟩ := U4_cover_odd hGA hJ hp2 hLie hr hr2' hd
  exact hUD hLie

theorem cf67U5_thm_of_leaves (hplus : UnLeafPlus 5) (hminus : UnLeafMinus 5)
    (hGA : CFSG.Open.GriessAllModelsStatement) : CF67U5 :=
  cf67Fam_of_core (fun Y _ _ hY => cf67CoreFull_U5 hplus hminus Y hY)
    (fun _ _ _ hJ hY _ hr _ hd => cf67CoreDeriv_U5_cover hplus hGA hJ hY hr hd)

theorem cf67U4_thm_of_leaves (hplus : UnLeafPlus 4) (hminus : UnLeafMinus 4)
    (hUD : ∀ {Y : Type} [Group Y] [Finite Y], LieModel Y .PSU 4 3 1 → CF67CoreDeriv Y 3)
    (hGA : CFSG.Open.GriessAllModelsStatement) : CF67U4 :=
  cf67Fam_of_core (fun Y _ _ hY => cf67CoreFull_U4 hplus hminus Y hY)
    (fun _ _ _ hJ hY _ hr hr2 hd => cf67CoreDeriv_U4_cover hUD hGA hJ hY hr hr2 hd)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Un
