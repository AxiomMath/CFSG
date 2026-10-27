module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphField
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNormal

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Timmesfeld (IsPrimitivePrimeDivisor exists_isPrimitivePrimeDivisor)
open CFSG.Quasithin (perfectCore)

section Inner

variable {F : Type} [Field F] [Finite F]

theorem half_sq_add_two_le {k m : ℕ} (hn : 3 ≤ 2 * k + m) (hn4 : 2 * k + m ≠ 4) :
    ((2 * k + m) / 2) ^ 2 + 2 ≤ k * (k - 1) / 2 + m * (m - 1) / 2 + (k * k + m * k + k * m) := by
  have ha := LinearPilot.two_mul_choose_two_eq k
  have hb := LinearPilot.two_mul_choose_two_eq m
  have hk : k * (k - 1) + k = k * k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rfl
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
  have hm : m * (m - 1) + m = m * m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rfl
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
  generalize k * (k - 1) / 2 = A at ha ⊢
  generalize m * (m - 1) / 2 = B at hb ⊢
  generalize k * (k - 1) = X at ha hk
  generalize m * (m - 1) = Y at hb hm
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [show (2 * k + 2 * s) / 2 = k + s by omega]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rcases (show s ≥ 3 by omega) with hs
      nlinarith
    · rcases Nat.eq_zero_or_pos s with rfl | hs1
      · have : 3 ≤ k := by omega
        nlinarith
      · nlinarith
  · rw [show (2 * k + (2 * s + 1)) / 2 = k + s by omega]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have : 1 ≤ s := by omega
      nlinarith
    · nlinarith

theorem le_factorization_card_centralizer_GL_two_pow [CharP F 2] {n e : ℕ} (he : 1 ≤ e)
    (hF : Nat.card F = 2 ^ e) (hn : 3 ≤ n) (hn4 : n ≠ 4) {B : GL (Fin n) F} (hB : B * B = 1) :
    e * ((n / 2) ^ 2 + 2) ≤
      (Nat.card (centralizer ({B} : Set (GL (Fin n) F)))).factorization 2 := by
  set V := Fin n → F
  set Ψ : GL (Fin n) F ≃* (V ≃ₗ[F] V) := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V) with hΨ
  set g := Ψ B with hg
  have hgg : g * g = 1 := by rw [hg, ← map_mul, hB, map_one]
  have hcardC : Nat.card (centralizer ({B} : Set (GL (Fin n) F))) =
      Nat.card (centralizer ({g} : Set (V ≃ₗ[F] V))) := by
    refine Nat.card_congr (Equiv.subtypeEquiv Ψ.toEquiv fun x => ?_)
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    change x * B = B * x ↔ Ψ x * Ψ B = Ψ B * Ψ x
    rw [← map_mul, ← map_mul, Ψ.injective.eq_iff]
  set k := Module.finrank F (LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)) with hk
  have hk2 : 2 * k ≤ n := by
    have h := CFSG.LargeExtraspecial.GLR.two_mul_finrank_range_sub_id_le hgg
    rwa [Module.finrank_fin_fun] at h
  set m := n - 2 * k with hm
  have hdim : Module.finrank F V = 2 * k + m := by
    rw [Module.finrank_fin_fun]
    omega
  have hcard := CFSG.LargeExtraspecial.GLR.card_centralizer_of_mul_self_eq_one hgg hk.symm hdim
  rw [hcardC, hcard]
  have hGk := LinearPilot.factorization_card_GL_two_pow he hF k
  have hGm := LinearPilot.factorization_card_GL_two_pow he hF m
  rw [Nat.factorization_mul (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
      (pow_ne_zero _ (by rw [hF]; positivity)), Finsupp.add_apply,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hGk, hGm,
    hF, ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have harith := half_sq_add_two_le (k := k) (m := m) (by omega) (by omega)
  rw [show 2 * k + m = n by omega] at harith
  have := Nat.mul_le_mul_left e harith
  nlinarith

theorem le_factorization_card_centralizer_projectiveSL_two_pow [CharP F 2] {n e : ℕ}
    (he : 1 ≤ e) (hF : Nat.card F = 2 ^ e) (hn : 3 ≤ n) (hn4 : n ≠ 4) {y : projectiveSL n F}
    (hyy : y * y = 1) :
    e * ((n / 2) ^ 2 + 2) ≤
      (Nat.card (centralizer ({y} : Set (projectiveSL n F)))).factorization 2 := by
  obtain ⟨A, hAA, rfl⟩ := LinearPilot.exists_proj_eq_of_mul_self hyy
  rw [LinearPilot.InvPlacement.centralizer_proj_eq_map hAA]
  set C := centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin n) F)) with hC
  set φ := (proj n F).comp C.subtype with hφ
  have hrange : φ.range = C.map (proj n F) := by rw [hφ, MonoidHom.range_comp, range_subtype]
  have hfac := card_ker_mul_card_range φ
  rw [hrange] at hfac
  have hkerdvd : Nat.card φ.ker ∣ Nat.card F - 1 := by
    have hle : φ.ker.map C.subtype ≤ scalars n F := by
      rintro _ ⟨x, hx, rfl⟩
      exact proj_eq_one_iff.mp hx
    have h1 := Subgroup.card_dvd_of_le hle
    rw [card_map_of_injective C.subtype_injective] at h1
    exact h1.trans (card_scalars_dvd (by omega))
  have hodd := LinearPilot.odd_card_sub_one_of_two_pow he hF
  have hker2 : (Nat.card φ.ker).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h2 =>
      (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hkerdvd))
  have hv : (Nat.card (C.map (proj n F))).factorization 2 = (Nat.card C).factorization 2 := by
    rw [← hfac, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      hker2, zero_add]
  rw [hv, ← LinearPilot.factorization_card_centralizer_toGL he hF (by omega) A]
  exact le_factorization_card_centralizer_GL_two_pow he hF hn hn4 (by rw [← map_mul, hAA, map_one])

end Inner

section Arith

variable {K : Type} [Field K] [Finite K]

theorem factorization_two_mul_card_statedSp_mul {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f)
    (hKc : Nat.card K = 2 ^ f) :
    (2 * (Nat.card (StatedSp n K) * f)).factorization 2 = 1 + f * n ^ 2 + f.factorization 2 := by
  rw [Nat.factorization_mul two_ne_zero (mul_ne_zero Nat.card_pos.ne' (by omega)),
    Finsupp.add_apply, Nat.factorization_mul Nat.card_pos.ne' (by omega), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, factorization_card_statedSp hn hKc hf]
  ring

theorem dvd_of_dvd_two_pow_mul_of_odd {j a i : ℕ} (hj : Odd j) (h : j ∣ 2 ^ a * i) : j ∣ i :=
  (Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hj)).dvd_of_dvd_mul_left h

theorem exists_odd_index {n m : ℕ} (hn : 3 ≤ n) (hm : m = 2 * n ∨ m = 2 * n + 1) :
    ∃ j, Odd j ∧ 5 ≤ j ∧ j ≤ m ∧ n < j := by
  rcases hm with rfl | rfl
  · exact ⟨2 * n - 1, ⟨n - 1, by omega⟩, by omega, by omega, by omega⟩
  · exact ⟨2 * n + 1, ⟨n, rfl⟩, by omega, le_rfl, by omega⟩

theorem not_dvd_two_mul_mul_of_odd {n f a j c : ℕ} (ha : 0 < a) (hj : Odd j) (hnj : n < j)
    (hfa : 2 * f = 2 ^ c * a) : ∀ i, 1 ≤ i → i ≤ n → ¬ a * j ∣ 2 * f * i := by
  intro i hi hin hdvd
  rw [hfa, show 2 ^ c * a * i = a * (2 ^ c * i) by ring] at hdvd
  have h1 := dvd_of_dvd_two_pow_mul_of_odd hj (Nat.dvd_of_mul_dvd_mul_left ha hdvd)
  have := Nat.le_of_dvd (by omega) h1
  omega

end Arith

section Classes

variable {F K : Type} [Field F] [Finite F] [Field K] [Finite K]

theorem not_card_centralizer_dvd_of_linear [CharP F 2] {n f m : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (hKc : Nat.card K = 2 ^ f) (hm : m = 2 * n ∨ m = 2 * n + 1)
    {y : projectiveSL m F} (hyy : y * y = 1) :
    ¬ Nat.card (centralizer ({y} : Set (projectiveSL m F))) ∣
      2 * (Nat.card (StatedSp n K) * f) := by
  intro hdvd
  have h1 := le_factorization_card_centralizer_projectiveSL_two_pow hf hF (by omega) (by omega) hyy
  rw [show m / 2 = n by omega] at h1
  have h2 := LinearPilot.factorization_two_le_of_dvd hdvd
    (mul_ne_zero two_ne_zero (mul_ne_zero Nat.card_pos.ne' (by omega)))
  rw [factorization_two_mul_card_statedSp_mul (by omega) hf hKc] at h2
  have hv : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have h3 : f * (n ^ 2 + 2) = f * n ^ 2 + 2 * f := by ring
  rw [h3] at h1
  omega

theorem not_card_fixedSubgroup_field_dvd_of_linear [CharP F 2] {n f m : ℕ} (hn : 3 ≤ n)
    (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (hKc : Nat.card K = 2 ^ f)
    (hm : m = 2 * n ∨ m = 2 * n + 1) (A : GL (Fin m) F) {ρ : F ≃+* F} (hρ : ρ ≠ 1)
    (hθ : (conjAut m F A * fieldAut m F ρ) * (conjAut m F A * fieldAut m F ρ) = 1) :
    ¬ Nat.card (fixedSubgroup (conjAut m F A * fieldAut m F ρ)) ∣
      2 * (Nat.card (StatedSp n K) * f) := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hfe, hρx, H, hH⟩ := even_linear_field_involution_descent hf hF (by omega) A ρ hρ
    (by rw [sq]; exact hθ)
  obtain ⟨f', rfl⟩ : ∃ f', f = 2 * f' := ⟨f / 2, by have := Nat.even_iff.1 hfe; omega⟩
  have hf' : 1 ≤ f' := by omega
  have hK₀ : Nat.card (GaloisField 2 f') = 2 ^ f' := GaloisField.card 2 f' (by omega)
  obtain ⟨ι, σ, hσ1, hσσ, hfix⟩ := LinearPilot.exists_subfield_involution hf' hK₀ hF
  obtain ⟨-, hσx⟩ := even_and_eq_pow_of_involution (by omega : 1 ≤ 2 * f') hF hσ1 hσσ
  have hρσ : ρ = σ := RingEquiv.ext fun x => by rw [hρx, hσx]
  rw [hH, hρσ] at hdvd
  have hcore := LinearPilot.card_perfectCore_fixedSubgroup_conj_fieldAut (by omega) ι hfix H
  rw [LinearPilot.natCard_projectiveSL_eq_ordA (by omega) hf' hK₀] at hcore
  have hle : Nat.card (perfectCore (fixedSubgroup
      (conjAut m F H * fieldAut m F σ * (conjAut m F H)⁻¹))) ∣
        Nat.card (fixedSubgroup (conjAut m F H * fieldAut m F σ * (conjAut m F H)⁻¹)) :=
    Subgroup.card_dvd_of_le (CFSG.Quasithin.perfectCore_le _)
  rw [hcore] at hle
  obtain ⟨j, hjodd, hj5, hjm, hnj⟩ := exists_odd_index hn hm
  have hk2 : 2 ≤ f' * j := by nlinarith
  have hk6 : f' * j ≠ 6 := by
    intro h6
    have hj6 : j ∣ 6 := ⟨f', by rw [← h6, mul_comm]⟩
    have := Nat.le_of_dvd (by norm_num) hj6
    interval_cases j <;> simp_all (config := { decide := true })
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor hk2 hk6
  have hpj : p ∣ (2 ^ f') ^ j - 1 := by rw [← pow_mul]; exact hp.2.1
  have hp1 : ¬ p ∣ 2 ^ f' - 1 := hp.2.2 f' (by omega) (by nlinarith)
  have hpA : p ∣ Open.ordA (m - 1) (2 ^ f') :=
    UnitaryPilot.dvd_ordA_of_dvd_pow_sub_one (by omega)
      (Finset.mem_Icc.2 ⟨by omega, by omega⟩) hp.1 hpj hp1
  exact not_dvd_two_mul_card_statedSp_mul_of_ppd (n := n) (K := K) (by omega) hKc hp
    (by nlinarith) (not_dvd_two_mul_mul_of_odd (c := 2) (by omega) hjodd hnj (by ring))
    ((hpA.trans hle).trans hdvd)

omit [Finite F] in
theorem not_card_fixedSubgroup_graphField_dvd_of_linear [CharP F 2] {n f m : ℕ} (hn : 3 ≤ n)
    (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (hKc : Nat.card K = 2 ^ f)
    (hm : m = 2 * n ∨ m = 2 * n + 1) (A : GL (Fin m) F) {ρ : F ≃+* F} (hρ : ρ ≠ 1)
    (hθ : (conjAut m F A * fieldAut m F ρ * dualAut m F) *
        (conjAut m F A * fieldAut m F ρ * dualAut m F) = 1) :
    ¬ Nat.card (fixedSubgroup (conjAut m F A * fieldAut m F ρ * dualAut m F)) ∣
      2 * (Nat.card (StatedSp n K) * f) := by
  intro hdvd
  obtain ⟨hfe, -, -⟩ := UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hF
    (by omega) A ρ hρ (by rw [sq]; exact hθ)
  obtain ⟨f', rfl⟩ : ∃ f', f = 2 * f' := ⟨f / 2, by have := Nat.even_iff.1 hfe; omega⟩
  have hf' : 1 ≤ f' := by omega
  obtain ⟨h, hU⟩ := LinearPilot.card_unitaryPSU_dvd_card_fixedSubgroup hf' (by omega) hF A hρ hθ
  obtain ⟨j, hjodd, hj5, hjm, hnj⟩ := exists_odd_index hn hm
  have hk2 : 2 ≤ 2 * f' * j := by nlinarith
  have hk6 : 2 * f' * j ≠ 6 := by
    intro h6
    have : 2 * f' * 5 ≤ 2 * f' * j := Nat.mul_le_mul_left _ hj5
    omega
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor hk2 hk6
  have hpU := LinearPilot.dvd_card_unitaryPSU_of_ppd h (by omega) hp hjodd (by omega) hjm
  exact not_dvd_two_mul_card_statedSp_mul_of_ppd (n := n) (K := K) (by omega) hKc hp
    (by nlinarith) (not_dvd_two_mul_mul_of_odd (c := 1) (by omega) hjodd hnj (by ring))
    ((hpU.trans hU).trans hdvd)

theorem exists_graph_normal_form_of_card_dvd [CharP F 2] {n f m : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (hKc : Nat.card K = 2 ^ f) (hm : m = 2 * n ∨ m = 2 * n + 1)
    {α : MulAut (projectiveSL m F)} (hαα : α * α = 1)
    (hdvd : Nat.card (fixedSubgroup α) ∣ 2 * (Nat.card (StatedSp n K) * f)) :
    ∃ H C : GL (Fin m) F, ((C : Matrix (Fin m) (Fin m) F) = 1 ∨
        (m = 2 * n ∧ (C : Matrix (Fin m) (Fin m) F) = UnitaryHigher.blockSwapJ m n)) ∧
      α = conjAut m F H * (conjAut m F C * dualAut m F) * (conjAut m F H)⁻¹ := by
  obtain ⟨A, ρ, ε, hε, rfl⟩ := (automorphism_generation (K := F) (by omega : 3 ≤ m)).2 α
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · exfalso
    rw [pow_zero, mul_one] at hαα hdvd
    by_cases hρ : ρ = 1
    · subst hρ
      rw [map_one, mul_one] at hαα hdvd
      by_cases h1 : conjAut m F A = 1
      · rw [h1] at hdvd
        have htop := LinearPilot.fixedSubgroup_mulAut_conj_eq (1 : projectiveSL m F)
        rw [map_one] at htop
        rw [htop] at hdvd
        exact not_card_centralizer_dvd_of_linear hn hf hF hKc hm (one_mul 1) hdvd
      · obtain ⟨y, hy, hyA⟩ :=
          CFSG.ComponentClassification.OutcomeLocal.exists_involution_eq_conjAut
            (by omega) A (by rw [sq, hαα]) h1
        rw [hyA, LinearPilot.fixedSubgroup_mulAut_conj_eq] at hdvd
        have hyy : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
        exact not_card_centralizer_dvd_of_linear hn hf hF hKc hm hyy hdvd
    · exact not_card_fixedSubgroup_field_dvd_of_linear hn hf hF hKc hm A hρ hαα hdvd
  · rw [pow_one] at hαα hdvd ⊢
    by_cases hρ : ρ = 1
    · subst hρ
      rw [map_one, mul_one] at hαα hdvd ⊢
      obtain ⟨-, ⟨H, C, -, hconj, hC⟩, -⟩ :=
        UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hF (by omega) A
          (by rw [sq]; exact hαα)
      refine ⟨H, C, ?_, hconj⟩
      rcases hC with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
      · exact Or.inl h1
      · right
        rcases hm with hm | hm
        · obtain rfl : r = n := by omega
          exact ⟨hm, hJ⟩
        · omega
    · exact absurd hdvd (not_card_fixedSubgroup_graphField_dvd_of_linear hn hf hF hKc hm A hρ hαα)

theorem not_lieModel_PSp_fixedSubgroup_dualAut_one {m f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (hm : 3 ≤ m) (hev : Even m) {C : GL (Fin m) F}
    (hC : (C : Matrix (Fin m) (Fin m) F) = 1) {n' f' : ℕ} :
    ¬ LieModel (fixedSubgroup (conjAut m F C * dualAut m F)) .PSp n' 2 f' := by
  intro hfix
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  obtain ⟨E⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv hf hF hm
    C (Or.inl hC)
  have hch := CFSG.ComponentClassification.CatLeafProof.isCharacteristicP_matrixIsometryGroup_one
    (k := F) hev hm
  rw [← hC] at hch
  have hch' := isCharacteristicP_of_mulEquiv E.symm hch
  exact CFSG.ComponentClassification.CatLeafProof.not_isPComponent_of_isCharacteristicP hch' ⊤
    (isPComponent_top_of_lieModel_PSp hfix)

end Classes

end CFSG.SeitzReduction.SymplecticPilot
