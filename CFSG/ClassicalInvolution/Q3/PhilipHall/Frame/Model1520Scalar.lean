module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarCentralizer

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial

section Similarity

variable {K : Type*} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {W : Submodule K V}

@[expose] def EichlerComm (Q : QuadraticForm K V) (W : Submodule K V) (F : V ≃+ V) : Prop :=
  ∀ P : HypPair Q, P.e ∈ W → P.f ∈ W → ∀ w ∈ W ⊓ P.perp, ∀ v,
    F (eichler Q P.e w v) = eichler Q P.e w (F v)

omit [Finite K] in
theorem mem_suppPerp_of_fixed_eichler
    (hWnd : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hW3 : 3 ≤ finrank K W)
    (hsing : ∃ e ∈ W, e ≠ 0 ∧ Q e = 0) {v : V}
    (hv : ∀ P : HypPair Q, P.e ∈ W → P.f ∈ W → ∀ w ∈ W ⊓ P.perp, eichler Q P.e w v = v) :
    v ∈ suppPerp Q W := by
  obtain ⟨e0, he0W, he00, hQe0⟩ := hsing
  obtain ⟨P, hPe, hPf⟩ := exists_hypPair_of_mem hWnd he0W hQe0 he00
  have he : P.e ∈ W := hPe ▸ he0W
  have hW := polarNondegOn_of_nondegenerate hWnd
  obtain ⟨a, ha⟩ := exists_sub_smul_mem_suppPerp hW3 he hPf (z := v) fun w hw =>
    hv P he hPf w hw
  obtain ⟨b, hb⟩ := exists_sub_smul_mem_suppPerp (P := hypPairSwap P) hW3 hPf he (z := v)
    fun w hw => hv (hypPairSwap P) hPf he w hw
  have hb' : v - b • P.f ∈ suppPerp Q W := hb
  have hab : a • P.e - b • P.f ∈ suppPerp Q W := by
    have h := (suppPerp Q W).sub_mem hb' ha
    have h' : v - b • P.f - (v - a • P.e) = a • P.e - b • P.f := by abel
    rwa [h'] at h
  have hab0 : a • P.e - b • P.f = 0 :=
    Submodule.disjoint_def.mp (isCompl_suppPerp hW).disjoint _
      (W.sub_mem (W.smul_mem a he) (W.smul_mem b hPf)) hab
  have ha0 : a = 0 := by
    have h := congrArg (fun t => polar Q t P.f) hab0
    simp only [polar_sub_left, polar_smul_left_eq, P.polar_ef, P.polar_ff,
      polar_zero_left] at h
    linear_combination h
  have hb0 : b = 0 := by
    have h := congrArg (fun t => polar Q t P.e) hab0
    simp only [polar_sub_left, polar_smul_left_eq, P.polar_ee, P.polar_fe,
      polar_zero_left] at h
    linear_combination -h
  rwa [ha0, zero_smul, sub_zero] at ha

omit [Finite K] in
theorem exists_eq_smul_of_singular_eichler (F : V ≃+ V) (hcomm : EichlerComm Q W F)
    (hWnd : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hW3 : 3 ≤ finrank K W)
    (hFW : ∀ x ∈ W, F x ∈ W) {e : V} (he : e ∈ W) (hQe : Q e = 0) (he0 : e ≠ 0) :
    ∃ c : K, F e = c • e := by
  obtain ⟨P, rfl, hPf⟩ := exists_hypPair_of_mem hWnd he hQe he0
  have hW := polarNondegOn_of_nondegenerate hWnd
  obtain ⟨a, ha⟩ := exists_sub_smul_mem_suppPerp hW3 he hPf (z := F P.e) fun w hw => by
    rw [← hcomm P he hPf w hw P.e, eichler_apply_self]
  refine ⟨a, ?_⟩
  have h0 : F P.e - a • P.e = 0 :=
    Submodule.disjoint_def.mp (isCompl_suppPerp hW).disjoint _
      (W.sub_mem (hFW _ he) (W.smul_mem a he)) ha
  exact sub_eq_zero.mp h0

theorem scalar_restriction_of_eichlerComm (F : V ≃+ V) (σ : K ≃+* K) (hcomm : EichlerComm Q W F) (μ : K)
    (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (hQ : (polarBilin Q).Nondegenerate)
    (hWnd : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hW3 : 3 ≤ finrank K W)
    (hsing : ∃ e ∈ W, e ≠ 0 ∧ Q e = 0) (hM : ElementaryMapsMem Q W)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) :
    (∀ c, σ c = c) ∧ ∃ c : K, c ≠ 0 ∧ ∀ w ∈ W, F w = c • w := by
  have hW := polarNondegOn_of_nondegenerate hWnd
  have hFperp : ∀ v ∈ suppPerp Q W, F v ∈ suppPerp Q W := fun v hv =>
    mem_suppPerp_of_fixed_eichler hWnd hW3 hsing fun P he hf w hw => by
      rw [← hcomm P he hf w hw v, supportedDerived_apply_perp (hM P he hf w hw) hv]
  have hFW : ∀ x ∈ W, F x ∈ W := fun x hx => map_mem_of_map_suppPerp F σ μ hFQ hQ hFperp hx
  have hline : ∀ e ∈ W, e ≠ 0 → Q e = 0 → ∃ c : K, F e = c • e := fun e he he0 hQe =>
    exists_eq_smul_of_singular_eichler F hcomm hWnd hW3 hFW he hQe he0
  obtain ⟨e0, he0W, he00, hQe0⟩ := hsing
  obtain ⟨P, hPe, hPf⟩ := exists_hypPair_of_mem hWnd he0W hQe0 he00
  have heW : P.e ∈ W := hPe ▸ he0W
  obtain ⟨a, ha⟩ := hline P.e heW P.e_ne_zero P.Q_e
  obtain ⟨b, hb⟩ := hline P.f hPf P.f_ne_zero P.Q_f
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact P.e_ne_zero (F.injective (by rw [ha, zero_smul, map_zero]))
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact P.f_ne_zero (F.injective (by rw [hb, zero_smul, map_zero]))
  have hU : ∀ u ∈ W ⊓ P.perp, F u ∈ W ⊓ P.perp := by
    intro u hu
    have hu' := HypPair.mem_perp.mp hu.2
    refine ⟨hFW u hu.1, HypPair.mem_perp.mpr ⟨?_, ?_⟩⟩
    · have h := polar_map_semilin F σ μ hFQ P.e u
      rw [ha, polar_smul_left_eq, hu'.1, map_zero, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left ha0
    · have h := polar_map_semilin F σ μ hFQ P.f u
      rw [hb, polar_smul_left_eq, hu'.2, map_zero, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hb0
  have hkey : ∀ u ∈ W ⊓ P.perp, F u = a • u ∧ σ (Q u) * b = a * Q u := by
    intro u hu
    have hu' := HypPair.mem_perp.mp hu.2
    obtain ⟨hFuW, hFuP⟩ := hU u hu
    have hFu' := HypPair.mem_perp.mp hFuP
    have huf : polar Q u P.f = 0 := by rw [polar_comm]; exact hu'.2
    have hue : polar Q u P.e = 0 := by rw [polar_comm]; exact hu'.1
    have hFuf : polar Q (F u) P.f = 0 := by rw [polar_comm]; exact hFu'.2
    have hFue : polar Q (F u) P.e = 0 := by rw [polar_comm]; exact hFu'.1
    set q := Q u with hq
    have hsW : P.e + u - q • P.f ∈ W := W.sub_mem (W.add_mem heW hu.1) (W.smul_mem _ hPf)
    have hQs : Q (P.e + u - q • P.f) = 0 := by
      rw [sub_eq_add_neg, QuadraticMap.map_add Q (P.e + u) (-(q • P.f)),
        QuadraticMap.map_add Q P.e u, QuadraticMap.map_neg, map_smul_eq_sq, P.Q_e, P.Q_f,
        polar_neg_right, polar_smul_right_eq, polar_add_left, P.polar_ef, huf, hu'.1]
      ring
    have hs0 : P.e + u - q • P.f ≠ 0 := by
      intro h
      have h1 := congrArg (fun t => polar Q t P.f) h
      simp only [polar_sub_left, polar_add_left, polar_smul_left_eq, P.polar_ef, huf,
        P.polar_ff, polar_zero_left] at h1
      norm_num at h1
    obtain ⟨l, hl⟩ := hline _ hsW hs0 hQs
    have hFs : F (P.e + u - q • P.f) = a • P.e + F u - (σ q * b) • P.f := by
      rw [map_sub, map_add, hF q P.f, hb, ha, smul_smul]
    have hE := hFs.symm.trans hl
    have h1 : a = l := by
      have h := congrArg (fun t => polar Q t P.f) hE
      simp only [polar_sub_left, polar_add_left, polar_smul_left_eq, P.polar_ef, P.polar_ff,
        hFuf, huf] at h
      linear_combination h
    have h2 : σ q * b = a * q := by
      have h := congrArg (fun t => polar Q t P.e) hE
      simp only [polar_sub_left, polar_add_left, polar_smul_left_eq, P.polar_ee, P.polar_fe,
        hFue, hue] at h
      rw [← h1] at h
      linear_combination -h
    rw [← h1, h2] at hE
    exact ⟨by linear_combination (norm := module) hE, h2⟩
  obtain ⟨u0, hu0U, hu0⟩ : ∃ u0 ∈ W ⊓ P.perp, u0 ≠ 0 := by
    have h := finrank_inf_perp_add_two P heW hPf
    have hpos : 0 < finrank K ↥(W ⊓ P.perp) := by omega
    obtain ⟨u0, hu0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨u0, u0.2, fun h0 => hu0 (Subtype.ext h0)⟩
  have hσ : ∀ c, σ c = c := by
    intro c
    have h1 := (hkey (c • u0) (Submodule.smul_mem _ c hu0U)).1
    rw [hF, (hkey u0 hu0U).1, smul_smul, smul_smul] at h1
    have h2 : (σ c * a - a * c) • u0 = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr h1
    have h3 := (smul_eq_zero.mp h2).resolve_right hu0
    exact mul_right_cancel₀ ha0 (by linear_combination h3)
  obtain ⟨u1, hu1U, hQu1⟩ : ∃ u1 ∈ W ⊓ P.perp, Q u1 ≠ 0 := by
    have hreg : PolarNondegOn Q (W ⊓ P.perp) := PolarNondegOn.inf_perp hW P heW hPf
    obtain ⟨y, hyU, hy⟩ := hreg.exists_polar_ne_zero hu0U hu0
    by_cases h0 : Q u0 = 0
    · by_cases h1 : Q y = 0
      · refine ⟨u0 + y, add_mem hu0U hyU, ?_⟩
        rw [QuadraticMap.map_add Q u0 y, h0, h1, zero_add, zero_add]
        exact hy
      · exact ⟨y, hyU, h1⟩
    · exact ⟨u0, hu0U, h0⟩
  have hba : b = a := by
    have h := (hkey u1 hu1U).2
    rw [hσ] at h
    exact mul_left_cancel₀ hQu1 (by rw [h, mul_comm])
  refine ⟨hσ, a, ha0, fun z hz => ?_⟩
  have hproj : P.proj z ∈ W ⊓ P.perp :=
    ⟨W.sub_mem (W.sub_mem hz (W.smul_mem _ heW)) (W.smul_mem _ hPf), P.proj_mem_perp z⟩
  have h := congrArg F (P.eq_add_proj z)
  rw [map_add, map_add, hF, hF, ha, hb, (hkey _ hproj).1, hba] at h
  simp only [hσ] at h
  have h2 : a • z = a • (polar Q z P.f • P.e + polar Q z P.e • P.f + P.proj z) := by
    rw [← P.eq_add_proj z]
  rw [h, h2]
  module


end Similarity

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
