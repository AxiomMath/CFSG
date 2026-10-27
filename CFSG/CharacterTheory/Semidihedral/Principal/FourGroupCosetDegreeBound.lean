module

public import CFSG.CharacterTheory.Semidihedral.Principal.CosetConstantHalfDegree
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public section

namespace CFSG.Semidihedral.Principal

open EigenCalculus

namespace CosetConstantEigenspaces

open Polynomial in
theorem coeff_eq_of_sum_pow_rat {ℓ : ℕ} (hℓ : ℓ.Prime) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ ℓ)
    (c : Fin ℓ → ℤ) {q : ℚ} (hq : ∑ j : Fin ℓ, (c j : ℂ) * ζ ^ (j : ℕ) = q) (j k : Fin ℓ)
    (hj : (j : ℕ) ≠ 0) (hk : (k : ℕ) ≠ 0) : c j = c k := by
  have := Fact.mk hℓ
  set F : ℚ[X] := ∑ i : Fin ℓ, C (c i : ℚ) * X ^ (i : ℕ) - C q with hFdef
  have hF : aeval ζ F = 0 := by
    rw [hFdef, map_sub, map_sum, aeval_C, sub_eq_zero]
    simp only [map_mul, aeval_C, aeval_X_pow, eq_ratCast, Rat.cast_intCast]
    exact hq
  have hdvd : minpoly ℚ ζ ∣ F := minpoly.dvd ℚ ζ hF
  rw [← cyclotomic_eq_minpoly_rat hζ hℓ.pos] at hdvd
  obtain ⟨G, hG⟩ := hdvd
  have hΦdeg : (cyclotomic ℓ ℚ).natDegree = ℓ - 1 := by
    rw [natDegree_cyclotomic, Nat.totient_prime hℓ]
  have hFdeg : F.natDegree ≤ ℓ - 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    have := i.2
    omega
  have hGc : G = C (G.coeff 0) := by
    by_cases hG0 : G = 0
    · simp [hG0]
    · apply eq_C_of_natDegree_eq_zero
      have hΦ0 : cyclotomic ℓ ℚ ≠ 0 := (cyclotomic.monic ℓ ℚ).ne_zero
      have h := natDegree_mul hΦ0 hG0
      rw [← hG, hΦdeg] at h
      omega
  have hcoeff : ∀ i : Fin ℓ, (i : ℕ) ≠ 0 → (c i : ℚ) = G.coeff 0 := by
    intro i hi
    have h : F.coeff (i : ℕ) = (cyclotomic ℓ ℚ * G).coeff (i : ℕ) := by rw [hG]
    have hFi : F.coeff (i : ℕ) = c i := by
      rw [hFdef, coeff_sub, finsetSum_coeff, coeff_C, ite_eq_right hi, sub_zero]
      simp only [coeff_C_mul, coeff_X_pow]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        rw [ite_eq_right, mul_zero]
        intro h'
        exact hb (Fin.ext h'.symm)
      · simp
    rw [hFi, hGc, coeff_mul_C, cyclotomic_prime, finsetSum_coeff] at h
    simp only [coeff_X_pow] at h
    rw [Finset.sum_eq_single (i : ℕ)] at h
    · simpa using h
    · intro b _ hb
      rw [ite_eq_right (Ne.symm hb)]
    · intro h'
      exact absurd (Finset.mem_range.mpr i.2) h'
  exact_mod_cast (hcoeff j hj).trans (hcoeff k hk).symm

variable {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem trace_restrict_of_coset_constant (ρ : Representation ℂ G W) {z h : G} {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (hz : z ^ ℓ = 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ ℓ)
    (hcomm : Commute (ρ z) (ρ h)) (hconst : ∀ i : ℕ, ρ.character (h * z ^ i) = ρ.character h)
    (j : Fin ℓ) :
    LinearMap.trace ℂ (Module.End.eigenspace (ρ z) (ζ ^ (j : ℕ)))
        ((ρ h).restrict (mapsTo_eigenspace hcomm (ζ ^ (j : ℕ)))) =
      if (j : ℕ) = 0 then ρ.character h else 0 := by
  have hf : ρ z ^ ℓ = 1 := by rw [← map_pow, hz, map_one]
  have : NeZero ℓ := ⟨hℓ⟩
  rw [trace_restrict_eq_fourier hcomm hℓ hf hζ j]
  have hterm : ∀ i ∈ Finset.range ℓ, ((ζ ^ (j : ℕ))⁻¹) ^ i * LinearMap.trace ℂ W (ρ h * ρ z ^ i) =
      ρ.character h * ((ζ ^ ((0 : Fin ℓ) : ℕ) * (ζ ^ (j : ℕ))⁻¹) ^ i) := by
    intro i _
    rw [← map_pow, ← map_mul]
    change _ * ρ.character (h * z ^ i) = _
    rw [hconst i, Fin.val_zero, pow_zero, one_mul, mul_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_pow_root hζ 0 j]
  by_cases hj : (j : ℕ) = 0
  · have hj' : (0 : Fin ℓ) = j := Fin.ext hj.symm
    rw [ite_eq_left hj', ite_eq_left hj]
    have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
    field_simp
  · have hj' : (0 : Fin ℓ) ≠ j := fun h' => hj (by rw [← h']; rfl)
    rw [ite_eq_right hj', ite_eq_right hj, mul_zero, mul_zero]

theorem card_dvd_finrank_of_trace_eq_zero [Finite G] (ρ : Representation ℂ G W)
    (H : Subgroup G) (E : Submodule ℂ W) (hE : ∀ h ∈ H, ∀ v ∈ E, ρ h v ∈ E)
    (htr : ∀ h (hh : h ∈ H), h ≠ 1 → LinearMap.trace ℂ E ((ρ h).restrict (hE h hh)) = 0) :
    ∃ m : ℕ, Module.finrank ℂ E = Nat.card H * m := by
  classical
  let σ := Representation.subrepresentation (ρ.comp H.subtype) E fun h v hv => hE h h.2 v hv
  have : Fintype H := Fintype.ofFinite H
  have hcard : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  let : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hcard
  have h := Representation.card_inv_mul_sum_char_eq_finrank σ
  have hsum : ∑ h : H, σ.character h = Module.finrank ℂ E := by
    rw [Finset.sum_eq_single 1]
    · rw [Representation.char_one]
    · intro h _ hh
      exact htr h h.2 (fun h' => hh (Subtype.ext h'))
    · simp
  rw [hsum] at h
  refine ⟨Module.finrank ℂ σ.invariants, ?_⟩
  have h' : (Module.finrank ℂ E : ℂ) = Nat.card H * Module.finrank ℂ σ.invariants := by
    rw [← h, mul_inv_cancel_left₀ hcard]
  exact_mod_cast h'

theorem generator_eigenspaces [Finite G] (ρ : Representation ℂ G W) (H P : Subgroup G)
    (hHP : ∀ h ∈ H, ∀ u ∈ P, h * u = u * h) {ℓ : ℕ} (hℓ : ℓ.Prime) (hPcard : Nat.card P = ℓ)
    (hconst : ∀ h ∈ H, h ≠ 1 → ∀ u ∈ P, ρ.character (h * u) = ρ.character h)
    {z : G} (hz : z ∈ P) (hratz : ∃ q : ℚ, ρ.character z = q)
    (hρz : ρ z ≠ 1) :
    (∀ μ : ℂ, μ ^ ℓ = 1 → μ ≠ 1 → ∃ m : ℕ, 0 < m ∧
      Module.finrank ℂ (Module.End.eigenspace (ρ z) μ) = Nat.card H * m) ∧
    (∀ h ∈ H, h ≠ 1 → ‖ρ.character h‖ ≤ Module.finrank ℂ (Module.End.eigenspace (ρ z) 1)) ∧
    (∀ h ∈ H, h ≠ 1 →
      ((Nat.card H * (ℓ - 1) : ℕ) : ℝ) + ‖ρ.character h‖ ≤ Module.finrank ℂ W) := by
  classical
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have : NeZero ℓ := ⟨hℓ0⟩
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ℓ) with hζdef
  have hζ : IsPrimitiveRoot ζ ℓ := Complex.isPrimitiveRoot_exp ℓ hℓ0
  have hzℓ : z ^ ℓ = 1 := by
    have h := P.orderOf_dvd_natCard hz
    rw [hPcard] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hf : ρ z ^ ℓ = 1 := by rw [← map_pow, hzℓ, map_one]
  let E : Fin ℓ → Submodule ℂ W := fun j => Module.End.eigenspace (ρ z) (ζ ^ (j : ℕ))
  let j₀ : Fin ℓ := ⟨0, hℓ.pos⟩
  have hE₀ : E j₀ = Module.End.eigenspace (ρ z) 1 := by
    change Module.End.eigenspace (ρ z) (ζ ^ 0) = _
    rw [pow_zero]
  have hcommH : ∀ h ∈ H, Commute (ρ z) (ρ h) := fun h hh => by
    change ρ z * ρ h = ρ h * ρ z
    rw [← map_mul, ← map_mul, hHP h hh z hz]
  have htrace : ∀ h (hh : h ∈ H), h ≠ 1 → ∀ j : Fin ℓ,
      LinearMap.trace ℂ (E j) ((ρ h).restrict (mapsTo_eigenspace (hcommH h hh) (ζ ^ (j : ℕ)))) =
        if (j : ℕ) = 0 then ρ.character h else 0 :=
    fun h hh h1 j => trace_restrict_of_coset_constant ρ hℓ0 hzℓ hζ (hcommH h hh)
      (fun i => hconst h hh h1 (z ^ i) (P.pow_mem hz i)) j
  have hdvd : ∀ j : Fin ℓ, (j : ℕ) ≠ 0 → ∃ m : ℕ, Module.finrank ℂ (E j) = Nat.card H * m := by
    intro j hj
    refine card_dvd_finrank_of_trace_eq_zero ρ H (E j)
      (fun h hh v hv => mapsTo_eigenspace (hcommH h hh) _ v hv) fun h hh h1 => ?_
    rw [htrace h hh h1 j, ite_eq_right hj]
  have hsumz : ρ.character z =
      ∑ j : Fin ℓ, ((Module.finrank ℂ (E j) : ℤ) : ℂ) * ζ ^ (j : ℕ) := by
    have h := trace_mul_pow_eq_sum (Commute.one_right (ρ z)) hℓ0 hf hζ 1
    rw [one_mul, pow_one] at h
    change LinearMap.trace ℂ W (ρ z) = _
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_one, show (1 : Module.End ℂ W).restrict (mapsTo_eigenspace (Commute.one_right (ρ z))
      (ζ ^ (j : ℕ))) = 1 from by ext; rfl, LinearMap.trace_one, mul_comm]
    push_cast
    rfl
  obtain ⟨q, hq⟩ := hratz
  have hequal : ∀ j k : Fin ℓ, (j : ℕ) ≠ 0 → (k : ℕ) ≠ 0 →
      Module.finrank ℂ (E j) = Module.finrank ℂ (E k) := by
    intro j k hj hk
    have h := coeff_eq_of_sum_pow_rat hℓ hζ (fun j => (Module.finrank ℂ (E j) : ℤ)) (q := q)
      (by rw [← hq, hsumz]) j k hj hk
    exact_mod_cast h
  have hfin := finrank_eq_sum hℓ0 hf hζ
  have hpos : ∃ j : Fin ℓ, (j : ℕ) ≠ 0 ∧ 0 < Module.finrank ℂ (E j) := by
    by_contra hcon
    push Not at hcon
    apply hρz
    have hsum0 : Module.finrank ℂ W = Module.finrank ℂ (E j₀) := by
      rw [hfin, Finset.sum_eq_single j₀]
      · intro j _ hj
        exact Nat.eq_zero_of_le_zero (hcon j fun h => hj (Fin.ext h))
      · simp
    have htop : E j₀ = ⊤ := Submodule.eq_top_of_finrank_eq hsum0.symm
    ext v
    have hv : v ∈ E j₀ := htop ▸ Submodule.mem_top
    rw [hE₀, Module.End.mem_eigenspace_iff, one_smul] at hv
    rw [hv, Module.End.one_apply]
  obtain ⟨j₁, hj₁, hj₁pos⟩ := hpos
  have hmult : ∀ j : Fin ℓ, (j : ℕ) ≠ 0 → ∃ m : ℕ, 0 < m ∧
      Module.finrank ℂ (E j) = Nat.card H * m := by
    intro j hj
    obtain ⟨m, hm⟩ := hdvd j hj
    refine ⟨m, Nat.pos_of_ne_zero fun h0 => ?_, hm⟩
    have := hequal j j₁ hj hj₁
    rw [hm, h0, mul_zero] at this
    omega
  have hprin : ∀ h ∈ H, h ≠ 1 → ‖ρ.character h‖ ≤ Module.finrank ℂ (E j₀) := by
    intro h hh h1
    have htr := htrace h hh h1 j₀
    rw [ite_eq_left rfl] at htr
    rw [← htr]
    refine norm_trace_le_finrank (orderOf_pos h).ne' ?_
    rw [Module.End.pow_restrict]
    ext v
    change (ρ h ^ orderOf h) (v : W) = v
    rw [← map_pow, pow_orderOf_eq_one, map_one, Module.End.one_apply]
  refine ⟨fun μ hμ hμ1 => ?_, fun h hh h1 => hE₀ ▸ hprin h hh h1, fun h hh h1 => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
    have hi0 : i ≠ 0 := fun h0 => hμ1 (by rw [h0, pow_zero])
    exact hmult ⟨i, hi⟩ hi0
  · have hsplit : Module.finrank ℂ W = Module.finrank ℂ (E j₀) +
        ∑ j ∈ Finset.univ.erase j₀, Module.finrank ℂ (E j) := by
      rw [hfin]
      exact (Finset.add_sum_erase _ (fun j => Module.finrank ℂ (E j)) (Finset.mem_univ j₀)).symm
    have hlow : Nat.card H * (ℓ - 1) ≤ ∑ j ∈ Finset.univ.erase j₀, Module.finrank ℂ (E j) := by
      have hcardE : (Finset.univ.erase j₀).card = ℓ - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
      calc Nat.card H * (ℓ - 1) = ∑ _j ∈ Finset.univ.erase j₀, Nat.card H := by
            rw [Finset.sum_const, hcardE, smul_eq_mul, mul_comm]
        _ ≤ ∑ j ∈ Finset.univ.erase j₀, Module.finrank ℂ (E j) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj0 : (j : ℕ) ≠ 0 := fun h0 => (Finset.mem_erase.mp hj).1 (Fin.ext h0)
            obtain ⟨m, hm, hmeq⟩ := hmult j hj0
            rw [hmeq]
            exact Nat.le_mul_of_pos_right _ hm
    have hp := hprin h hh h1
    rw [hsplit]
    push_cast
    have hlow' : ((Nat.card H * (ℓ - 1) : ℕ) : ℝ) ≤
        ((∑ j ∈ Finset.univ.erase j₀, Module.finrank ℂ (E j) : ℕ) : ℝ) := by
      exact_mod_cast hlow
    push_cast at hlow'
    linarith

theorem cyclic_prime_coset_constant_eigenspaces [Finite G] (ρ : Representation ℂ G W)
    (H P : Subgroup G) (hHP : ∀ h ∈ H, ∀ u ∈ P, h * u = u * h)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hPcard : Nat.card P = ℓ)
    (hrat : ∀ u ∈ P, ∃ q : ℚ, ρ.character u = q) (hker : ¬ P ≤ MonoidHom.ker ρ)
    (hconst : ∀ h ∈ H, h ≠ 1 → ∀ u ∈ P, ρ.character (h * u) = ρ.character h) :
    (∀ z ∈ P, z ≠ 1 → ∀ μ : ℂ, μ ^ ℓ = 1 → μ ≠ 1 →
      ∃ m : ℕ, 0 < m ∧ Module.finrank ℂ (Module.End.eigenspace (ρ z) μ) = Nat.card H * m) ∧
    (∀ z ∈ P, z ≠ 1 → ∀ h ∈ H, h ≠ 1 →
      ‖ρ.character h‖ ≤ Module.finrank ℂ (Module.End.eigenspace (ρ z) 1)) ∧
    (∀ h ∈ H, h ≠ 1 →
      ((Nat.card H * (ℓ - 1) : ℕ) : ℝ) + ‖ρ.character h‖ ≤ Module.finrank ℂ W) := by
  have hgen : ∀ z ∈ P, z ≠ 1 → ρ z ≠ 1 := by
    intro z hz hz1 hρ1
    apply hker
    have hord : orderOf z = ℓ := by
      rcases hℓ.eq_one_or_self_of_dvd _ (hPcard ▸ P.orderOf_dvd_natCard hz) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
    have hPz : Subgroup.zpowers z = P := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr hz) (by rw [hPcard, Nat.card_zpowers, hord])
    rw [← hPz, Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.mpr hρ1
  have hfacts : ∀ z ∈ P, z ≠ 1 → _ := fun z hz hz1 =>
    generator_eigenspaces ρ H P hHP hℓ hPcard hconst hz (hrat z hz) (hgen z hz hz1)
  refine ⟨fun z hz hz1 => (hfacts z hz hz1).1, fun z hz hz1 => (hfacts z hz hz1).2.1,
    fun h hh h1 => ?_⟩
  have hPne : P ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hPcard]
    exact hℓ.one_lt
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  exact (hfacts z z.2 (fun h' => hz1 (Subtype.ext h'))).2.2 h hh h1

end CosetConstantEigenspaces

open CosetConstantEigenspaces

theorem four_group_central_prime_coset_constant_degree_bound {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ G W)
    (V : Subgroup G) [IsKleinFour V] (P : Subgroup G) (hPV : P ≤ Subgroup.centralizer V)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (_hℓodd : Odd ℓ) (hPcard : Nat.card P = ℓ)
    (hrat : ∀ u ∈ P, ∃ q : ℚ, ρ.character u = q) (hker : ¬ P ≤ MonoidHom.ker ρ)
    (hconst : ∀ v ∈ V, v ≠ 1 → ∀ u ∈ P, ρ.character (v * u) = ρ.character v) :
    (∀ z ∈ P, z ≠ 1 → ∀ μ : ℂ, μ ^ ℓ = 1 → μ ≠ 1 →
      ∃ m : ℕ, 0 < m ∧ Module.finrank ℂ (Module.End.eigenspace (ρ z) μ) = 4 * m) ∧
    (∀ v ∈ V, v ≠ 1 →
      ((4 * (ℓ - 1) : ℕ) : ℝ) + ‖ρ.character v‖ ≤ Module.finrank ℂ W) := by
  have hcard : Nat.card V = 4 := IsKleinFour.card_four
  have hVP : ∀ v ∈ V, ∀ u ∈ P, v * u = u * v :=
    fun v hv u hu => Subgroup.mem_centralizer_iff.mp (hPV hu) v hv
  obtain ⟨h1, -, h3⟩ := cyclic_prime_coset_constant_eigenspaces ρ V P hVP hℓ hPcard hrat hker
    hconst
  rw [hcard] at h1 h3
  exact ⟨h1, h3⟩

end CFSG.Semidihedral.Principal
