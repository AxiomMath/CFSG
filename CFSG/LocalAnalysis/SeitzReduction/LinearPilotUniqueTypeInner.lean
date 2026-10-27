module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndFieldBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBNormalForm
public import CFSG.LargeExtraspecial.GLRCent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalIso

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

section AutOrder

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem factorization_card_GL_two_pow {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (a : ℕ) :
    (Nat.card (GL (Fin a) K)).factorization 2 = f * (a * (a - 1) / 2) := by
  rw [card_GL_eq, hK]
  have hodd : ¬ 2 ∣ ∏ j ∈ Finset.Icc 1 a, ((2 ^ f) ^ j - 1) := by
    rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
    rintro ⟨j, hj, hdvd⟩
    rw [Finset.mem_Icc] at hj
    have h2 : 2 ∣ (2 ^ f) ^ j := by
      rw [← pow_mul]
      exact dvd_pow_self 2 (Nat.mul_ne_zero (by omega) (by omega))
    have h1 : 1 ≤ (2 ^ f) ^ j := Nat.one_le_pow _ _ (by positivity)
    generalize (2 ^ f) ^ j = s at h1 h2 hdvd
    omega
  have hne : ∏ j ∈ Finset.Icc 1 a, ((2 ^ f) ^ j - 1) ≠ 0 := fun h => hodd (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)) hne, Finsupp.add_apply,
    ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]

theorem factorization_two_le_of_dvd {m m' : ℕ} (h : m ∣ m') (hm' : m' ≠ 0) :
    m.factorization 2 ≤ m'.factorization 2 :=
  (Nat.factorization_le_iff_dvd (fun h0 => hm' (Nat.eq_zero_of_zero_dvd (h0 ▸ h))) hm').2 h 2

theorem factorization_card_mulAut_projectiveSL_le (hn : 3 ≤ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    (Nat.card (MulAut (projectiveSL n K))).factorization 2 ≤
      f * (n * (n - 1) / 2) + 1 + f.factorization 2 := by
  set E := semilinearAutGroup n K with hE
  set D := (conjAut n K).range with hD
  set Φ := (fieldAut n K).range with hΦ
  have hDn : D.Normal := conjAut_range_normal hn
  have hEidx : E.index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨dualAut n K, fun b => ?_⟩
    have hb : b ∈ standardAutGroup n K := by
      rw [(automorphism_generation (K := K) hn).1]
      exact mem_top b
    rcases mem_or_mul_dualAut_mem hb with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hEsup : E = Φ ⊔ D := by
    rw [hE, semilinearAutGroup, Subgroup.closure_union, linearAutGroup_eq_range,
      Subgroup.closure_eq, ← MonoidHom.coe_range, Subgroup.closure_eq, sup_comm]
  have hEDidx : D.relIndex E ∣ f := by
    rw [hEsup, Subgroup.relIndex_sup_right]
    refine (Subgroup.relIndex_dvd_card D Φ).trans ?_
    refine (Subgroup.card_range_dvd (fieldAut n K)).trans ?_
    rw [(card_ringAut_and_isCyclic Nat.prime_two K hK).1]
  have hDE : D ≤ E := by
    rw [hD, ← linearAutGroup_eq_range]
    exact linearAutGroup_le_semilinearAutGroup
  have hEcard : Nat.card E = D.relIndex E * Nat.card D := by
    rw [← Subgroup.relIndex_mul_card D E, inf_eq_left.2 hDE]
  have hDcard : Nat.card D ∣ Nat.card (GL (Fin n) K) := Subgroup.card_range_dvd _
  have hAut : Nat.card (MulAut (projectiveSL n K)) = E.index * (D.relIndex E * Nat.card D) := by
    rw [← hEcard, mul_comm, Subgroup.card_mul_index]
  have hGL0 : Nat.card (GL (Fin n) K) ≠ 0 := Nat.card_pos.ne'
  have hi0 : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hr0 : D.relIndex E ≠ 0 := ne_zero_of_dvd_ne_zero (by omega) hEDidx
  have hD0 : Nat.card D ≠ 0 := Nat.card_pos.ne'
  rw [hAut, Nat.factorization_mul hi0 (mul_ne_zero hr0 hD0), Finsupp.add_apply,
    Nat.factorization_mul hr0 hD0, Finsupp.add_apply]
  have h1 : E.index.factorization 2 ≤ 1 := by
    have := factorization_two_le_of_dvd hEidx two_ne_zero
    rwa [Nat.Prime.factorization_self Nat.prime_two] at this
  have h2 : (D.relIndex E).factorization 2 ≤ f.factorization 2 :=
    factorization_two_le_of_dvd hEDidx (by omega)
  have h3 : (Nat.card D).factorization 2 ≤ f * (n * (n - 1) / 2) := by
    rw [← factorization_card_GL_two_pow hf hK n]
    exact factorization_two_le_of_dvd hDcard hGL0
  omega

end AutOrder

section Centralizer

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Field F] [Finite F] [CharP F 2] in
theorem odd_card_sub_one_of_two_pow {e : ℕ} (he : 1 ≤ e) (hF : Nat.card F = 2 ^ e) :
    Odd (Nat.card F - 1) := by
  rw [hF]
  obtain ⟨r, hr⟩ := (Nat.even_pow' (by omega : e ≠ 0)).2 even_two
  refine ⟨r - 1, ?_⟩
  have : 1 ≤ r := by
    have := Nat.one_le_two_pow (n := e)
    omega
  omega

omit [CharP F 2] in
theorem factorization_card_centralizer_toGL {e : ℕ} (he : 1 ≤ e) (hF : Nat.card F = 2 ^ e)
    (hn : 1 ≤ n) (A : Matrix.SpecialLinearGroup (Fin n) F) :
    (Nat.card (centralizer ({Matrix.SpecialLinearGroup.toGL A} : Set (GL (Fin n) F)))).factorization
        2 = (Nat.card (centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin n) F)))).factorization
          2 := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set B := Matrix.SpecialLinearGroup.toGL A with hB
  set C := centralizer ({B} : Set (GL (Fin n) F)) with hC
  set Kd := (Matrix.GeneralLinearGroup.det : GL (Fin n) F →* Fˣ).ker with hKd
  have hmap : (centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin n) F))).map
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) F →* GL (Fin n) F) =
        Kd ⊓ C := by
    ext x
    constructor
    · rintro ⟨S, hS, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [hKd, MonoidHom.mem_ker]
        exact det_toGL S
      · rw [hC, mem_centralizer_singleton_iff, hB, ← map_mul, ← map_mul,
          mem_centralizer_singleton_iff.1 hS]
    · rintro ⟨hxK, hxC⟩
      have hxK' : Matrix.GeneralLinearGroup.det x = 1 := hxK
      obtain ⟨S, rfl⟩ := exists_toGL_eq hxK'
      refine ⟨S, mem_centralizer_singleton_iff.2 ?_, rfl⟩
      have h := mem_centralizer_singleton_iff.1 hxC
      rw [hB, ← map_mul, ← map_mul] at h
      exact Matrix.SpecialLinearGroup.toGL_injective h
  have hcard1 : Nat.card (Kd ⊓ C : Subgroup (GL (Fin n) F)) =
      Nat.card (centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin n) F))) := by
    rw [← hmap, card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective]
  have hidx : Kd.relIndex C ∣ Nat.card F - 1 := by
    refine (Subgroup.relIndex_dvd_index_of_normal (H := Kd) (K := C)).trans ?_
    rw [hKd, Subgroup.index_ker, MonoidHom.range_eq_top.mpr
      Matrix.GeneralLinearGroup.det_surjective, Subgroup.card_top, Nat.card_units]
  have hodd := odd_card_sub_one_of_two_pow he hF
  have hrel := Subgroup.relIndex_mul_card Kd C
  rw [hcard1] at hrel
  rw [← hrel]
  have hr0 : Kd.relIndex C ≠ 0 := ne_zero_of_dvd_ne_zero (Nat.pos_of_ne_zero
    (by rintro h; rw [h] at hodd; exact absurd hodd (by decide))).ne' hidx
  rw [Nat.factorization_mul hr0 Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.2 hodd)
      (even_iff_two_dvd.2 (h2.trans hidx))), zero_add]

theorem two_mul_choose_two_eq (a : ℕ) : 2 * (a * (a - 1) / 2) = a * (a - 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self a)

theorem choose_two_add_three_le {k m : ℕ} (hn : 3 ≤ 2 * k + m) :
    (2 * k + m) * (2 * k + m - 1) / 2 + 3 ≤
      2 * (k * (k - 1) / 2) + 2 * (m * (m - 1) / 2) + 2 * (k * k + m * k + k * m) := by
  rw [two_mul_choose_two_eq, two_mul_choose_two_eq]
  have h2 := two_mul_choose_two_eq (2 * k + m)
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
  have hN : (2 * k + m) * (2 * k + m - 1) + (2 * k + m) = (2 * k + m) * (2 * k + m) := by
    obtain ⟨j, hj⟩ : ∃ j, 2 * k + m = j + 1 := ⟨2 * k + m - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]
    ring
  rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
  · simp only [Nat.zero_mul, zero_add, Nat.zero_sub, mul_zero] at hm hN h2 ⊢
    nlinarith
  · nlinarith
  · nlinarith

theorem le_factorization_card_centralizer_GL {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ (2 * f)) (hn : 3 ≤ n) {B : GL (Fin n) F} (hB : B * B = 1) :
    f * (n * (n - 1) / 2) + 3 * f ≤
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
  have h2f : 1 ≤ 2 * f := by omega
  have hGk := factorization_card_GL_two_pow h2f hF k
  have hGm := factorization_card_GL_two_pow h2f hF m
  rw [Nat.factorization_mul (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
      (pow_ne_zero _ (by rw [hF]; positivity)), Finsupp.add_apply,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hGk, hGm,
    hF, ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have harith := choose_two_add_three_le (k := k) (m := m) (by omega)
  rw [show 2 * k + m = n by omega] at harith
  have := Nat.mul_le_mul_left f harith
  nlinarith

theorem le_factorization_card_centralizer_projectiveSL {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ (2 * f)) (hn : 3 ≤ n) {y : projectiveSL n F} (hy : orderOf y = 2) :
    f * (n * (n - 1) / 2) + 3 * f ≤
      (Nat.card (centralizer ({y} : Set (projectiveSL n F)))).factorization 2 := by
  have hyy : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  obtain ⟨A, hAA, rfl⟩ := exists_proj_eq_of_mul_self hyy
  rw [InvPlacement.centralizer_proj_eq_map hAA]
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
  have hodd := odd_card_sub_one_of_two_pow (by omega : 1 ≤ 2 * f) hF
  have hker2 : (Nat.card φ.ker).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h2 =>
      (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hkerdvd))
  have hv : (Nat.card (C.map (proj n F))).factorization 2 = (Nat.card C).factorization 2 := by
    rw [← hfac, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      hker2, zero_add]
  rw [hv, ← factorization_card_centralizer_toGL (by omega : 1 ≤ 2 * f) hF (by omega) A]
  exact le_factorization_card_centralizer_GL hf hF hn (by rw [← map_mul, hAA, map_one])

theorem innerInvolutionExclusion {f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ f) (hF : Nat.card F = 2 ^ (2 * f)) :
    InnerInvolutionExclusion n K F := by
  intro y hy hdvd
  have h1 := le_factorization_card_centralizer_projectiveSL hf hF hn hy
  have h2 := factorization_card_mulAut_projectiveSL_le (K := K) hn hf hK
  have h3 := factorization_two_le_of_dvd hdvd (mul_ne_zero two_ne_zero Nat.card_pos.ne')
  rw [Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two] at h3
  have hv : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  omega

end Centralizer

theorem nonFieldInvolutionExclusion_of_graph {n f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) {K F : Type}
    [Field K] [Finite K] [Field F] [Finite F] [CharP F 2] (hK : Nat.card K = 2 ^ f)
    (hF : Nat.card F = 2 ^ (2 * f)) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hG : GraphInvolutionExclusion n K F) (hGF : GraphFieldInvolutionExclusion n K F) :
    NonFieldInvolutionExclusion n K F σ :=
  nonFieldInvolutionExclusion_of_classes hn (by omega : 1 ≤ 2 * f) hF hσ1 hσσ
    (innerInvolutionExclusion hf hn hK hF) hG hGF

theorem fieldCoreTypeDet_of_graph {n f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) {K F : Type} [Field K]
    [Finite K] [Field F] [Finite F] (hK : Nat.card K = 2 ^ f) (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hG : GraphInvolutionExclusion n K F) (hGF : GraphFieldInvolutionExclusion n K F) :
    FieldCoreTypeDet n K F := by
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hK ι hσ1 hσσ hfix
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  exact fieldCoreTypeDet_of_nonFieldInvolutionExclusion hn ι hfix
    (nonFieldInvolutionExclusion_of_graph hf hn hK hF hσ1 hσσ hG hGF)

end CFSG.SeitzReduction.LinearPilot
