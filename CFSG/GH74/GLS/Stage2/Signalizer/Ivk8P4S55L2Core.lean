module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Step
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Even
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Tr3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ComponentClassification L2Ord L2Dick

section Core

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
  {K : Subgroup Γ} {a : Γ}


theorem stepL2_core (hE1 : CrossE1) (hf : Hyp89 p ρ K a) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrp : r ≠ p) (hL : FL2d r (↥K ⧸ center ↥K)) :
    p = 3 ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀)
      (_ : (↥K ⧸ center ↥K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀),
        Nat.card F₀ = 5 ∧ 2 ∣ Nat.card (center ↥K) := by
  classical
  have hrf : Fact r.Prime := ⟨hr⟩
  have hpf : Fact p.Prime := ⟨hf.prime⟩
  obtain ⟨f, hf1, hmod⟩ := hL
  obtain ⟨-, -, -, hq3, F₀, hF₀field, hF₀fin, hcard, ⟨e0⟩⟩ := AutL2Facts.lieModel_psl2_data hmod
  have : CharP F₀ r := charP_of_card_eq_pow hr hf1 hcard
  obtain ⟨y, hy⟩ := hf.l2_inner hE1 hr hr2 hrp ⟨f, hf1, hmod⟩
  have hno := hf.no_invariant_of_E1 hE1 hr hr2 hrp ⟨hr, hr2, Or.inl ⟨f, hf1, hmod⟩⟩
  have hcen := center_quot_trivial hf e0
  have hinj := conj_inj_of_centerless hcen
  have hy1' : y ≠ 1 := by
    rintro rfl
    exact hf.bAutN_ne_one (by rw [hy, map_one])
  have hy1 : e0 y ≠ 1 := fun h => hy1' (e0.injective (by rw [h, map_one]))
  have hypow : y ^ p = 1 := by
    apply hinj
    rw [map_pow, ← hy, map_one]
    exact hf.bAutN_pow
  have hyp : (e0 y) ^ p = 1 := by rw [← map_pow, hypow, map_one]
  have hp35 : p = 3 ∨ p = 5 := by
    obtain ⟨k₀, hk₀, hJ₀⟩ := exists_nonPGroup_pair hf
    obtain ⟨-, -, -, -, -, -, -, hord, -⟩ := pair_orders hf hr2 hrp hcard e0 hy hno hk₀ hJ₀
    have hmem : e0 y ∈ Subgroup.closure ({e0 y, e0 (QuotientGroup.mk ⟨k₀, hk₀⟩) * e0 y *
        (e0 (QuotientGroup.mk ⟨k₀, hk₀⟩))⁻¹} :
          Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    rcases hord _ hmem with h | h | h
    · exact absurd (eq_one_of_pow_odd_sq (hf.prime.odd_of_ne_two hf.odd) hyp h) hy1
    · by_contra hne
      have h1 : (e0 y) ^ Nat.gcd p 3 = 1 := (pow_gcd_eq_one (a := e0 y)).mpr ⟨hyp, h⟩
      have hc : Nat.Coprime p 3 := (Nat.coprime_primes hf.prime Nat.prime_three).mpr
        (fun h3 => hne (Or.inl h3))
      rw [hc.gcd_eq_one, pow_one] at h1
      exact hy1 h1
    · by_contra hne
      have h1 : (e0 y) ^ Nat.gcd p 5 = 1 := (pow_gcd_eq_one (a := e0 y)).mpr ⟨hyp, h⟩
      have hc : Nat.Coprime p 5 := (Nat.coprime_primes hf.prime Nat.prime_five).mpr
        (fun h5 => hne (Or.inr h5))
      rw [hc.gcd_eq_one, pow_one] at h1
      exact hy1 h1
  have h5 : Nat.card F₀ = 5 := by
    by_contra hne
    have h3 : Nat.card F₀ ≠ 3 := by rw [hcard]; exact hq3
    by_cases h9 : Nat.card F₀ = 9
    · have hr3 : r = 3 := by
        have h' : r ^ f = 3 ^ 2 := by rw [← hcard, h9]; norm_num
        have hdvd : r ∣ 3 ^ 2 := h' ▸ dvd_pow_self r (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow hdvd)
      have hp5 : p = 5 := by
        rcases hp35 with h | h
        · exact absurd (hr3.trans h.symm) hrp
        · exact h
      have : CharP F₀ 3 := by rw [← hr3]; infer_instance
      refine l2_trace_contra hf hr2 hrp hcard e0 hy hno hp35 hy1 hyp 1 (fun Mh hMh => Or.inr ?_)
      have hq := quartic_of_psl_pow_five (M := Mh) (by rw [hMh]; exact hy1)
        (by rw [hMh, ← hp5]; exact hyp)
      exact bad_t9 hq
    · obtain ⟨t, ht⟩ := exists_good_t hr hr2 hcard hf1 h3 hne h9
      exact l2_trace_contra hf hr2 hrp hcard e0 hy hno hp35 hy1 hyp t (fun _ _ => Or.inl ht)
  have hr5 : r = 5 := by
    have h' : r ^ f = 5 := by rw [← hcard, h5]
    have hdvd : r ∣ 5 := h' ▸ dvd_pow_self r (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp hdvd
  have hp3 : p = 3 := by
    rcases hp35 with h | h
    · exact h
    · exact absurd (hr5.trans h.symm) hrp
  refine ⟨hp3, F₀, hF₀field, hF₀fin, e0, h5, ?_⟩
  have : CharP F₀ 5 := by rw [← hr5]; infer_instance
  have hY : Nat.card (↥K ⧸ center ↥K) = 60 := by
    rw [Nat.card_congr e0.toEquiv, CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hcard hr2,
      ← hcard, h5]
    norm_num
  obtain ⟨G, Mh, hMh, htr1, htr2⟩ := exists_conj_traces (e0 y) hy1 1
  have hMhne : (QuotientGroup.mk Mh : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) ≠ 1 := by
    rw [hMh]; exact hy1
  have hMh3 : (QuotientGroup.mk Mh : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) ^ 3 = 1 := by
    rw [hMh, ← hp3]; exact hyp
  have hα : (Mh : Matrix (Fin 2) (Fin 2) F₀).trace ^ 2 = 1 := by
    have := sq_of_psl_pow_three hMhne hMh3
    linear_combination this
  have htr3 : ((Mh⁻¹ * (G * Mh * G⁻¹) : Matrix.SpecialLinearGroup (Fin 2) F₀) :
      Matrix (Fin 2) (Fin 2) F₀).trace = 3 := by
    rw [htr1]; norm_num
  have h23 : (2 : F₀) ≠ 3 := by
    intro h
    have h' : (3 : F₀) - 2 = 0 := sub_eq_zero.mpr h.symm
    norm_num at h'
  have hz5 := psl_pow_five_of_trace htr3
  have hz1ne := ne_one_of_conj_trace hα htr3 h23
  obtain ⟨k₁, hk₁⟩ := QuotientGroup.mk_surjective (e0.symm (QuotientGroup.mk G))
  have hk : (k₁ : Γ) ∈ K := k₁.2
  have hg : e0 (QuotientGroup.mk (⟨(k₁ : Γ), hk⟩ : ↥K)) = QuotientGroup.mk G := by
    show e0 (QuotientGroup.mk k₁) = _
    rw [hk₁, MulEquiv.apply_symm_apply]
  have hz1 : (QuotientGroup.mk (Mh⁻¹ * (G * Mh * G⁻¹)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) =
      (e0 y)⁻¹ * (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹) := by
    rw [← hMh]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  by_cases hJ : IsPGroup p ↥(Subgroup.closure ({a, (k₁ : Γ) * a * (k₁ : Γ)⁻¹} : Set Γ))
  · exfalso
    have hc := pair_comm_of_pgroup hf hr2 hrp hcard e0 hy hk hJ
    rw [hg] at hc
    have hcomm : Commute (e0 y) (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹) := hc
    have hw : (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹ :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) ^ p = 1 := by
      rw [conj_pow, hyp, mul_one, mul_inv_cancel]
    have hz : ((e0 y)⁻¹ * (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹)) ^ 3 = 1 := by
      rw [hcomm.inv_left.mul_pow, inv_pow, ← hp3, hyp, inv_one, hw, mul_one]
    rw [← hz1] at hz
    have h1 := (pow_gcd_eq_one (a := (QuotientGroup.mk (Mh⁻¹ * (G * Mh * G⁻¹)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀))).mpr ⟨hz, hz5⟩
    rw [show Nat.gcd 3 5 = 1 by norm_num, pow_one] at h1
    exact hz1ne h1
  · obtain ⟨N, hN, F', hFf, hFfin, e', hcardF', -, h5'⟩ :=
      pair_orders hf hr2 hrp hcard e0 hy hno hk hJ
    rw [hg] at h5'
    have hmem1 : (e0 y)⁻¹ * (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹) ∈
        Subgroup.closure ({e0 y, QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹} :
          Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hF'5 : Nat.card F' = 5 := by
      refine h5' ⟨_, hmem1, ?_, ?_⟩
      · rw [← hz1]; exact hz5
      · rw [← hz1]; exact hz1ne
    obtain ⟨yh, c, hyc, hcC, hac⟩ := hf.exists_inner_decomp hy
    subst hac
    exact even_center_of_pair yh.2 hcC hk rfl N e' hF'5 hY

end Core

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
