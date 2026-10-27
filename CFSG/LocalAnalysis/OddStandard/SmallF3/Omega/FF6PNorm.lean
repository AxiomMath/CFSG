module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PMono
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma ff6p_ffC_eq_neg_one {i : Option (Fin 5)} (h : ffC i = -1) : i = none := by
  cases i with
  | none => rfl
  | some a =>
    rw [show ffC (some a) = (1 : ZMod 3) from rfl] at h
    exact absurd h (by decide)

private lemma ff6p_exists_sep (j m : Option (Fin 5)) (hjm : j ≠ m) :
    ∃ K : Finset (Option (Fin 5)), none ∉ K ∧ Even K.card ∧
      ((j ∈ K ∧ m ∉ K) ∨ (m ∈ K ∧ j ∉ K)) := by
  revert j m
  decide

theorem ff6p_eigen_frame (fr : PFrame Q (Option (Fin 5)) ffC) {v : V} (hv : v ≠ 0)
    (h : ∀ K : Finset (Option (Fin 5)), none ∉ K → Even K.card →
      ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) v = v ∨
        ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) v = -v) :
    ∃ (j : Option (Fin 5)) (a : ZMod 3), a ≠ 0 ∧ v = a • fr.b j := by
  obtain ⟨j, hj⟩ : ∃ j : Option (Fin 5), fr.b.repr v j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (fr.b.ext_elem (fun i => by rw [hcon i]; simp))
  have hother : ∀ m : Option (Fin 5), m ≠ j → fr.b.repr v m = 0 := by
    intro m hm
    by_contra hm0
    obtain ⟨K, hKn, hKe, hsep⟩ := ff6p_exists_sep j m hm.symm
    have hK := h K hKn hKe
    rcases hsep with ⟨hjK, hmK⟩ | ⟨hmK, hjK⟩
    · rcases hK with hvv | hvv
      · have hc := congrArg (fun w : V => fr.b.repr w j) hvv
        rw [fr.repr_signChange K v j, if_pos hjK] at hc
        have h2 : (2 : ZMod 3) * fr.b.repr v j = 0 := by
          rw [two_mul]
          exact eq_neg_iff_add_eq_zero.mp hc.symm
        exact hj ((mul_eq_zero.mp h2).resolve_left (by decide))
      · have hc := congrArg (fun w : V => fr.b.repr w m) hvv
        rw [fr.repr_signChange K v m, if_neg hmK, map_neg, Finsupp.neg_apply] at hc
        have h2 : (2 : ZMod 3) * fr.b.repr v m = 0 := by
          rw [two_mul]
          exact eq_neg_iff_add_eq_zero.mp hc
        exact hm0 ((mul_eq_zero.mp h2).resolve_left (by decide))
    · rcases hK with hvv | hvv
      · have hc := congrArg (fun w : V => fr.b.repr w m) hvv
        rw [fr.repr_signChange K v m, if_pos hmK] at hc
        have h2 : (2 : ZMod 3) * fr.b.repr v m = 0 := by
          rw [two_mul]
          exact eq_neg_iff_add_eq_zero.mp hc.symm
        exact hm0 ((mul_eq_zero.mp h2).resolve_left (by decide))
      · have hc := congrArg (fun w : V => fr.b.repr w j) hvv
        rw [fr.repr_signChange K v j, if_neg hjK, map_neg, Finsupp.neg_apply] at hc
        have h2 : (2 : ZMod 3) * fr.b.repr v j = 0 := by
          rw [two_mul]
          exact eq_neg_iff_add_eq_zero.mp hc
        exact hj ((mul_eq_zero.mp h2).resolve_left (by decide))
  refine ⟨j, fr.b.repr v j, hj, ?_⟩
  apply fr.b.ext_elem
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self]
  by_cases hij : i = j
  · subst hij; simp
  · rw [Finsupp.single_eq_of_ne hij, mul_zero]
    exact hother i hij

theorem ff6p_mono_of_normalizes (fr : PFrame Q (Option (Fin 5)) ffC) (γ : simGroup Q)
    (h : ∀ b ∈ ffB0p fr,
      simAct Q γ⁻¹ b ∈ ffB0p fr ∨ piOrth Q * simAct Q γ⁻¹ b ∈ ffB0p fr) :
    ∃ (σ : Equiv.Perm (Fin 5)) (K : Finset (Option (Fin 5))),
      γ = orthToSim Q (fr.pOrth σ * fr.signChange K) := by
  let X : V ≃ₗ[ZMod 3] V := (γ : V ≃ₗ[ZMod 3] V)
  let c : (ZMod 3)ˣ := Classical.choose γ.2
  have hc : IsSimilitude Q X c := Classical.choose_spec γ.2
  have key : ∀ i : Option (Fin 5), ∀ K : Finset (Option (Fin 5)), none ∉ K → Even K.card →
      ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) (X (fr.b i)) = X (fr.b i) ∨
        ((fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) (X (fr.b i)) = -X (fr.b i) := by
    intro i K hKn hKe
    have hb : fr.signChange K ∈ ffB0p fr := ⟨K, hKn, hKe, rfl⟩
    rcases h (fr.signChange K) hb with hcase | hcase
    · obtain ⟨J, _hJn, _hJe, hJeq⟩ := (mem_ffB0p_iff fr).mp hcase
      have hcoe : ((γ⁻¹ : simGroup Q) : V ≃ₗ[ZMod 3] V) *
          (fr.signChange K : V ≃ₗ[ZMod 3] V) *
          ((γ⁻¹ : simGroup Q) : V ≃ₗ[ZMod 3] V)⁻¹ =
          (fr.signChange J : V ≃ₗ[ZMod 3] V) := by
        have hh := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) hJeq
        rwa [coe_simAct] at hh
      have hX : X⁻¹ * (fr.signChange K : V ≃ₗ[ZMod 3] V) * X =
          (fr.signChange J : V ≃ₗ[ZMod 3] V) := by
        rw [Subgroup.coe_inv] at hcoe
        rw [show ((γ : simGroup Q) : V ≃ₗ[ZMod 3] V) = X from rfl] at hcoe
        rwa [inv_inv] at hcoe
      have hbJ : (fr.signChange K : V ≃ₗ[ZMod 3] V) (X (fr.b i)) =
          X ((fr.signChange J : V ≃ₗ[ZMod 3] V) (fr.b i)) := by
        have hh := congrArg (fun e : V ≃ₗ[ZMod 3] V => X (e (fr.b i))) hX
        simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
          LinearEquiv.apply_symm_apply] using hh
      rw [hbJ, fr.signChange_basis J i]
      by_cases hi : i ∈ J
      · right; rw [if_pos hi, map_neg]
      · left; rw [if_neg hi]
    · obtain ⟨J, _hJn, _hJe, hJeq⟩ := (mem_ffB0p_iff fr).mp hcase
      have hcoe : (piOrth Q : V ≃ₗ[ZMod 3] V) *
          (((γ⁻¹ : simGroup Q) : V ≃ₗ[ZMod 3] V) *
            (fr.signChange K : V ≃ₗ[ZMod 3] V) *
            ((γ⁻¹ : simGroup Q) : V ≃ₗ[ZMod 3] V)⁻¹) =
          (fr.signChange J : V ≃ₗ[ZMod 3] V) := by
        have hh := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) hJeq
        rw [Submonoid.coe_mul, coe_simAct, Subgroup.coe_inv] at hh
        rw [show ((γ : simGroup Q) : V ≃ₗ[ZMod 3] V) = X from rfl] at hh
        rwa [inv_inv] at hh
      have happ : (X⁻¹ * (fr.signChange K : V ≃ₗ[ZMod 3] V) * X) (fr.b i) =
          -((fr.signChange J : V ≃ₗ[ZMod 3] V) (fr.b i)) := by
        have hh := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (fr.b i)) hcoe
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, coe_piOrth_apply] at hh
        exact neg_eq_iff_eq_neg.mp hh
      have hbJ : (fr.signChange K : V ≃ₗ[ZMod 3] V) (X (fr.b i)) =
          -X ((fr.signChange J : V ≃ₗ[ZMod 3] V) (fr.b i)) := by
        have hXu : X ((X⁻¹ * (fr.signChange K : V ≃ₗ[ZMod 3] V) * X) (fr.b i)) =
            (fr.signChange K : V ≃ₗ[ZMod 3] V) (X (fr.b i)) := by
          simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
            LinearEquiv.apply_symm_apply]
        rw [← hXu, happ, map_neg]
      rw [hbJ, fr.signChange_basis J i]
      by_cases hi : i ∈ J
      · left; rw [if_pos hi, map_neg, neg_neg]
      · right; rw [if_neg hi]
  have hb : ∀ i : Option (Fin 5), X (fr.b i) ≠ 0 := by
    intro i h0
    exact fr.b.ne_zero i (X.injective (by simpa using h0))
  choose π a ha hXb using fun i => ff6p_eigen_frame fr (hb i) (key i)
  have hπinj : Function.Injective π := by
    intro i i' hii
    have hzero : X (a i' • fr.b i - a i • fr.b i') = 0 := by
      rw [map_sub, map_smul, map_smul, hXb i, hXb i', hii]
      simp [smul_smul, mul_comm]
    have hlin : a i' • fr.b i - a i • fr.b i' = 0 :=
      X.injective (by rw [hzero, map_zero])
    exact ffMonoP_index_eq fr (ha i') (sub_eq_zero.mp hlin)
  have hπbij : Function.Bijective π := hπinj.bijective_of_finite
  let e : Equiv.Perm (Option (Fin 5)) := Equiv.ofBijective π hπbij
  have hnorm : ∀ i : Option (Fin 5), c * ffC i = ffC (π i) := by
    intro i
    have h1 : Q (X (fr.b i)) = (c : ZMod 3) * Q (fr.b i) := hc (fr.b i)
    rw [hXb i, QuadraticMap.map_smul] at h1
    rw [fr.norm (π i), fr.norm i, smul_eq_mul] at h1
    have ha2 : a i * a i = 1 := by
      rcases aux_units_zmod3 (Units.mk0 (a i) (ha i)) with h | h
      · have h1 : a i = 1 := by simpa using congrArg Units.val h
        rw [h1]; decide
      · have h1 : a i = -1 := by simpa using congrArg Units.val h
        rw [h1]; decide
    rw [ha2, one_mul] at h1
    exact h1.symm
  have hc_one : c = 1 := by
    rcases aux_unit_eq_one_or_neg_one c with hc1 | hc1
    · exact hc1
    · exfalso
      have hk : ∀ k : Fin 5, π (some k) = none := by
        intro k
        have h := hnorm (some k)
        rw [show ffC (some k) = (1 : ZMod 3) from rfl, hc1] at h
        have h' : ffC (π (some k)) = -1 := by rw [← h]; simp
        exact ff6p_ffC_eq_neg_one h'
      have h0 := hk 0
      have h1 := hk 1
      have heq : π (some (0 : Fin 5)) = π (some (1 : Fin 5)) := by rw [h0, h1]
      exact (by decide : (0 : Fin 5) ≠ 1) (Option.some.inj (hπinj heq))
  have he_none : e none = none := by
    have h := hnorm none
    rw [show ffC none = (-1 : ZMod 3) from rfl, hc_one] at h
    have h' : ffC (π none) = -1 := by rw [← h]; simp
    change π none = none
    exact ff6p_ffC_eq_neg_one h'
  let σ : Equiv.Perm (Fin 5) := Equiv.removeNone e
  have hcongr : Equiv.optionCongr σ = e := by
    apply Equiv.ext
    intro i
    cases i with
    | none => rw [Equiv.optionCongr_apply, Option.map_none, he_none]
    | some k =>
      have hsome : ∃ x', e (some k) = some x' := by
        cases hk : e (some k) with
        | none =>
          exact absurd (e.injective (by rw [hk, he_none])) (Option.some_ne_none k)
        | some x => exact ⟨x, rfl⟩
      rw [Equiv.optionCongr_apply, Option.map_some]
      exact Equiv.removeNone_some e hsome
  have hπcongr : ∀ i : Option (Fin 5), π i = Equiv.optionCongr σ i := by
    intro i
    change e i = Equiv.optionCongr σ i
    rw [← hcongr]
  let K : Finset (Option (Fin 5)) := Finset.univ.filter (fun i => a i = -1)
  have ha_eq : ∀ i : Option (Fin 5), a i = (if i ∈ K then (-1 : ZMod 3) else 1) := by
    intro i
    by_cases hi : i ∈ K
    · rw [if_pos hi]
      exact (Finset.mem_filter.mp hi).2
    · rw [if_neg hi]
      rcases (by decide : ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = -1) (a i) (ha i) with h1 | h1
      · exact h1
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩) hi
  have hXeq : X = ((fr.pOrth σ * fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) := by
    apply fr.b.ext'
    intro i
    rw [hXb i, ffMonoP_basis, hπcongr i, ha_eq i]
  exact ⟨σ, K, Subtype.ext (by rw [coe_orthToSim]; exact hXeq)⟩

end CFSG.OddStandard.SmallF3.Omega
