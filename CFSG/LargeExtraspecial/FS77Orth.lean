module

public import CFSG.LargeExtraspecial.S45QOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mem_orthogonalGroup HypPair PolarNondegOn)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

namespace Orth

theorem span_singular_eq_top (hq : (polarBilin q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) : Submodule.span (ZMod 2) {s : V | q s = 0} = ⊤ := by
  obtain ⟨a, ha0, ha⟩ := CFSG.ClassicalGroups.Orthogonal.exists_ne_zero_map_eq_zero (Q := q) h3
  obtain ⟨P, -⟩ := CFSG.ClassicalGroups.Orthogonal.exists_hypPair hq ha ha0
  set S := Submodule.span (ZMod 2) {s : V | q s = 0}
  have he : P.e ∈ S := Submodule.subset_span P.Q_e
  have hf : P.f ∈ S := Submodule.subset_span P.Q_f
  refine eq_top_iff.mpr fun v _ => ?_
  set w := P.proj v
  obtain ⟨hew, hfw⟩ := HypPair.mem_perp.mp (P.proj_mem_perp v)
  have hs : w + q w • P.e + P.f ∈ S := by
    refine Submodule.subset_span ?_
    change q (w + q w • P.e + P.f) = 0
    have h1 : polar q w P.e = 0 := by rw [polar_comm]; exact hew
    have h2 : polar q w P.f = 0 := by rw [polar_comm]; exact hfw
    rw [map_add_eq, map_add_eq, map_smul_zmod2, P.Q_e, P.Q_f, polar_add_left, polar_smul_right,
      polar_smul_left, h1, h2, P.polar_ef, smul_eq_mul, smul_eq_mul]
    simp only [mul_zero, add_zero, zero_add, mul_one]
    exact zmod2_add_self _
  have hw : w ∈ S := by
    have h := S.sub_mem (S.sub_mem hs hf) (S.smul_mem (q w) he)
    rwa [add_sub_cancel_right, add_sub_cancel_right] at h
  rw [P.eq_add_proj v]
  exact S.add_mem (S.add_mem (S.smul_mem _ he) (S.smul_mem _ hf)) hw

theorem eq_zero_of_forall_singular {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (hq : (polarBilin q).Nondegenerate) (h3 : 3 ≤ finrank (ZMod 2) V) (φ : V →ₗ[ZMod 2] M)
    (hφ : ∀ s, q s = 0 → φ s = 0) : φ = 0 := by
  have hle : Submodule.span (ZMod 2) {s : V | q s = 0} ≤ LinearMap.ker φ :=
    Submodule.span_le.mpr fun s hs => LinearMap.mem_ker.mpr (hφ s hs)
  rw [span_singular_eq_top hq h3, top_le_iff, LinearMap.ker_eq_top] at hle
  exact hle

theorem exists_singular_polar_eq_one (hq : (polarBilin q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) {x : V} (hx0 : x ≠ 0) : ∃ s, q s = 0 ∧ polar q x s = 1 := by
  by_contra! h
  refine hx0 (hq.1 x fun y => ?_)
  have h0 := eq_zero_of_forall_singular hq h3 (polarBilin q x) fun s hs => by
    rw [polarBilin_apply_apply]
    exact (zmod2_eq_zero_or_eq_one _).resolve_right (h s hs)
  rw [h0, LinearMap.zero_apply]

theorem exists_perp_polar_eq_one (hq : (polarBilin q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) {s : V} (hs0 : s ≠ 0) :
    ∃ u u', polar q s u = 0 ∧ polar q s u' = 0 ∧ polar q u u' = 1 := by
  set K := LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ s)
  obtain ⟨u, huK, hus⟩ : ∃ u ∈ K, u ∉ (ZMod 2) ∙ s := by
    by_contra! h
    have h1 := Submodule.finrank_mono (show K ≤ (ZMod 2) ∙ s from fun u hu => h u hu)
    rw [LinearMap.BilinForm.finrank_orthogonal hq, finrank_span_singleton hs0] at h1
    omega
  have hli : LinearIndependent (ZMod 2) ![u, s] := by
    refine linearIndependent_pair_iff.mpr ⟨fun h => hus ?_, hs0, fun h => hus ?_⟩
    · rw [h]
      exact Submodule.zero_mem _
    · rw [h]
      exact Submodule.mem_span_singleton_self s
  obtain ⟨x, hxu, hxs⟩ := exists_polar_eq_one_polar_eq_zero hq hli
  exact ⟨u, x, mem_orthogonal_span_singleton_iff.mp huK, by rw [polar_comm]; exact hxs,
    by rw [polar_comm]; exact hxu⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem eichler_apply_eq_add_self {s u x : V} (hs : q s = 0) (hsu : polar q s u = 0)
    (hxs : polar q x s = 0) (hxu : polar q x u = 1) : eichler q s u x = x + s := by
  rw [eichler_apply_zmod2 hs hsu, hxs, hxu, zero_smul, add_zero, mul_zero, add_zero, one_smul]

end Orth

open Orth

theorem eichler_invariant_submodule (hq : (polarBilin q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) (W : Submodule (ZMod 2) V)
    (hW : ∀ s u, q s = 0 → polar q s u = 0 → ∀ x ∈ W, eichler q s u x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨s, hs, hxs⟩ := exists_singular_polar_eq_one hq h3 hx0
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hxs
    exact zero_ne_one hxs
  have hd : ∀ u, polar q s u = 0 → u + (polar q x u + q u) • s ∈ W := by
    intro u hsu
    have h := W.sub_mem (hW s u hs hsu x hxW) hxW
    rwa [eichler_apply_zmod2 hs hsu, hxs, one_smul, mul_one, add_assoc, add_sub_cancel_left] at h
  have hsW : s ∈ W := by
    obtain ⟨u, u', hsu, hsu', huu'⟩ := exists_perp_polar_eq_one hq h3 hs0
    have hy := hd u hsu
    have h := W.sub_mem (hW s u' hs hsu' _ hy) hy
    rwa [eichler_apply_eq_add_self hs hsu', add_sub_cancel_left] at h
    · rw [polar_add_left, polar_smul_left, polar_comm, hsu, polar_self_eq_zero, smul_zero,
        add_zero]
    · rw [polar_add_left, polar_smul_left, huu', hsu', smul_zero, add_zero]
  have hperp : ∀ u, polar q s u = 0 → u ∈ W := by
    intro u hsu
    have h := W.sub_mem (hd u hsu) (W.smul_mem (polar q x u + q u) hsW)
    rwa [add_sub_cancel_right] at h
  refine eq_top_iff.mpr fun v _ => ?_
  have h1 : v - polar q v s • x ∈ W := by
    refine hperp _ ?_
    rw [polar_sub_right, polar_smul_right, polar_comm q s x, hxs, smul_eq_mul, mul_one,
      polar_comm, sub_self]
  have h2 := W.add_mem h1 (W.smul_mem (polar q v s) hxW)
  rwa [sub_add_cancel] at h2

theorem eichler_fixed_eq_zero (hq : (polarBilin q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) (v : V)
    (hv : ∀ s u, q s = 0 → polar q s u = 0 → eichler q s u v = v) : v = 0 := by
  by_contra hv0
  have hW : ∀ s u, q s = 0 → polar q s u = 0 →
      ∀ x ∈ (ZMod 2) ∙ v, eichler q s u x ∈ (ZMod 2) ∙ v := by
    intro s u hs hsu x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hv s u hs hsu]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  rcases eichler_invariant_submodule hq h3 _ hW with h | h
  · exact hv0 (Submodule.span_singleton_eq_bot.mp h)
  · have h1 := finrank_span_singleton (K := ZMod 2) hv0
    rw [h, finrank_top] at h1
    omega

namespace Orth

theorem exists_apply_eq_smul_of_commute (hq : (polarBilin q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) (θ : V →ₗ[ZMod 2] V)
    (hθ : ∀ s u, q s = 0 → polar q s u = 0 → ∀ x, θ (eichler q s u x) = eichler q s u (θ x))
    {s : V} (hs : q s = 0) : ∃ c : ZMod 2, θ s = c • s := by
  by_cases hs0 : s = 0
  · exact ⟨0, by rw [hs0, map_zero, smul_zero]⟩
  obtain ⟨u, u', hsu, hsu', huu'⟩ := exists_perp_polar_eq_one hq h3 hs0
  have hu's : polar q u' s = 0 := by rw [polar_comm]; exact hsu'
  have hus : polar q u s = 0 := by rw [polar_comm]; exact hsu
  have hu'u : polar q u' u = 1 := by rw [polar_comm]; exact huu'
  have k1 := hθ s u hs hsu u'
  rw [eichler_apply_eq_add_self hs hsu hu's hu'u, map_add, eichler_apply_zmod2 hs hsu,
    add_assoc] at k1
  have k2 := hθ s u' hs hsu' u
  rw [eichler_apply_eq_add_self hs hsu' hus huu', map_add, eichler_apply_zmod2 hs hsu',
    add_assoc] at k2
  have e1 := add_left_cancel k1
  have e2 := add_left_cancel k2
  have hα : polar q (θ u') s = 0 := by
    have h := congrArg (fun z => polar q z u') (e1.symm.trans e2)
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, huu', hsu', polar_self_eq_zero,
      mul_one, mul_zero, add_zero] at h
    exact h
  exact ⟨_, by rw [e1, hα, zero_smul, zero_add]⟩

end Orth

theorem eichler_commute_endo (hq : (polarBilin q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) (θ : V →ₗ[ZMod 2] V)
    (hθ : ∀ s u, q s = 0 → polar q s u = 0 → ∀ x, θ (eichler q s u x) = eichler q s u (θ x)) :
    θ = 0 ∨ θ = LinearMap.id := by
  have hidem : θ ∘ₗ θ - θ = 0 := by
    refine eq_zero_of_forall_singular hq h3 _ fun s hs => ?_
    obtain ⟨c, hc⟩ := exists_apply_eq_smul_of_commute hq h3 θ hθ hs
    rw [LinearMap.sub_apply, LinearMap.comp_apply, hc, map_smul, hc, smul_smul, zmod2_mul_self,
      sub_self]
  have hker : ∀ s u, q s = 0 → polar q s u = 0 →
      ∀ x ∈ LinearMap.ker θ, eichler q s u x ∈ LinearMap.ker θ := by
    intro s u hs hsu x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hθ s u hs hsu, hx, map_zero]
  rcases eichler_invariant_submodule hq h3 _ hker with h | h
  · right
    refine LinearMap.ext fun v => ?_
    have h' : θ v - v ∈ LinearMap.ker θ := by
      have h1 := LinearMap.congr_fun hidem v
      rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h1
      rw [LinearMap.mem_ker, map_sub, h1]
    rw [h, Submodule.mem_bot, sub_eq_zero] at h'
    exact h'
  · left
    exact LinearMap.ker_eq_top.mp h

namespace Orth

theorem eichler_invariant_eq_zero_of_polar (hq : (polarBilin q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) (r : QuadraticForm (ZMod 2) V) (hr : ∀ x y, polar r x y = 0)
    (hinv : ∀ s u, q s = 0 → polar q s u = 0 → ∀ x, r (eichler q s u x) = r x) : r = 0 := by
  have hadd : ∀ x y, r (x + y) = r x + r y := fun x y => by
    have h := hr x y
    rw [polar] at h
    linear_combination h
  let ℓ : V →ₗ[ZMod 2] ZMod 2 :=
    { toFun := r
      map_add' := hadd
      map_smul' := fun c x => by rw [map_smul_zmod2, RingHom.id_apply, smul_eq_mul] }
  have hℓ : ℓ = 0 := by
    refine eq_zero_of_forall_singular hq h3 ℓ fun s hs => ?_
    change r s = 0
    by_cases hs0 : s = 0
    · rw [hs0, map_zero]
    obtain ⟨u, u', hsu, hsu', huu'⟩ := exists_perp_polar_eq_one hq h3 hs0
    have h := hinv s u hs hsu u'
    rw [eichler_apply_eq_add_self hs hsu (by rw [polar_comm]; exact hsu')
      (by rw [polar_comm]; exact huu'), hadd] at h
    exact add_eq_left.mp h
  ext x
  exact LinearMap.congr_fun hℓ x

end Orth

theorem eichler_invariant_quadraticForm (hq : (polarBilin q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) (q' : QuadraticForm (ZMod 2) V)
    (hq' : ∀ s u, q s = 0 → polar q s u = 0 → ∀ x, q' (eichler q s u x) = q' x) :
    q' = 0 ∨ q' = q := by
  set T := LinearMap.BilinForm.toDual (polarBilin q) hq
  set θ : V →ₗ[ZMod 2] V := T.symm.toLinearMap ∘ₗ polarBilin q'
  have hθ : ∀ x y, polar q (θ x) y = polar q' x y := by
    intro x y
    have h1 : T (θ x) = polarBilin q' x := T.apply_symm_apply _
    have h2 := LinearMap.congr_fun h1 y
    rwa [LinearMap.BilinForm.toDual_def, polarBilin_apply_apply, polarBilin_apply_apply] at h2
  have hcomm : ∀ s u, q s = 0 → polar q s u = 0 →
      ∀ x, θ (eichler q s u x) = eichler q s u (θ x) := by
    intro s u hs hsu x
    have hEE : ∀ y, eichler q s u (eichler q s u y) = y := fun y => by
      rw [← LinearEquiv.mul_apply, eichler_mul_self hsu]
      rfl
    have hE := eichler_mem_orthogonalGroup q s u
    have hpol' : ∀ a b, polar q' (eichler q s u a) (eichler q s u b) = polar q' a b := by
      intro a b
      simp only [polar]
      rw [← map_add (eichler q s u) a b, hq' s u hs hsu, hq' s u hs hsu, hq' s u hs hsu]
    rw [← sub_eq_zero]
    refine CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero hq fun y => ?_
    rw [polar_sub_left, sub_eq_zero, hθ]
    conv_lhs => rw [← hEE y]
    conv_rhs => rw [← hEE y]
    rw [hpol', CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hE, hθ]
  rcases eichler_commute_endo hq h3 θ hcomm with h | h
  · left
    refine eichler_invariant_eq_zero_of_polar hq h3 q' (fun x y => ?_) hq'
    rw [← hθ, h, LinearMap.zero_apply, polar_zero_left]
  · right
    have hpol : ∀ x y, polar (q' - q) x y = 0 := by
      intro x y
      have h1 : polar q' x y = polar q x y := by rw [← hθ, h, LinearMap.id_apply]
      simp only [polar, sub_apply] at h1 ⊢
      linear_combination h1
    have hinv : ∀ s u, q s = 0 → polar q s u = 0 → ∀ x,
        (q' - q) (eichler q s u x) = (q' - q) x := by
      intro s u hs hsu x
      rw [sub_apply, sub_apply, hq' s u hs hsu,
        CFSG.ClassicalGroups.Orthogonal.map_of_mem (eichler_mem_orthogonalGroup q s u)]
    exact sub_eq_zero.mp (eichler_invariant_eq_zero_of_polar hq h3 (q' - q) hpol hinv)

@[expose] def orthQv6 : Fin 6 → ZMod 2 := ![0, 0, 0, 0, 1, 1]

@[expose] def orthBm6 : Fin 6 → Fin 6 → ZMod 2 :=
  ![![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0]]

namespace Orth

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_mem_map_eq_one {C : Submodule (ZMod 2) V} (hC : PolarNondegOn q C)
    (hC0 : C ≠ ⊥) : ∃ z ∈ C, q z = 1 := by
  obtain ⟨v, hvC, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC0
  obtain ⟨w, hwC, hvw⟩ := hC.exists_polar_ne_zero hvC hv0
  by_cases hv : q v = 1
  · exact ⟨v, hvC, hv⟩
  by_cases hw : q w = 1
  · exact ⟨w, hwC, hw⟩
  refine ⟨v + w, C.add_mem hvC hwC, ?_⟩
  rw [map_add_eq, (zmod2_eq_zero_or_eq_one _).resolve_right hv,
    (zmod2_eq_zero_or_eq_one _).resolve_right hw, zmod2_eq_one_of_ne_zero hvw, zero_add, zero_add]

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_minus_pair_of_anisotropic {C : Submodule (ZMod 2) V} (hC : PolarNondegOn q C)
    (hC0 : C ≠ ⊥) (hanis : ∀ c ∈ C, q c = 0 → c = 0) :
    ∃ x ∈ C, ∃ y ∈ C, q x = 1 ∧ q y = 1 ∧ polar q x y = 1 := by
  obtain ⟨x, hxC, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC0
  obtain ⟨y, hyC, hxy⟩ := hC.exists_polar_ne_zero hxC hx0
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hxy (polar_zero_right q x)
  exact ⟨x, hxC, y, hyC, zmod2_eq_one_of_ne_zero fun h => hx0 (hanis x hxC h),
    zmod2_eq_one_of_ne_zero fun h => hy0 (hanis y hyC h), zmod2_eq_one_of_ne_zero hxy⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_minus_pair_of_hypPair {C : Submodule (ZMod 2) V} (hC : PolarNondegOn q C)
    (P : HypPair q) (he : P.e ∈ C) (hf : P.f ∈ C) (hne : C ⊓ P.perp ≠ ⊥) :
    ∃ x ∈ C, ∃ y ∈ C, q x = 1 ∧ q y = 1 ∧ polar q x y = 1 := by
  obtain ⟨z, ⟨hzC, hzP⟩, hz⟩ := exists_mem_map_eq_one (hC.inf_perp P he hf) hne
  obtain ⟨hez, hfz⟩ := HypPair.mem_perp.mp hzP
  refine ⟨P.e + P.f, C.add_mem he hf, P.e + z, C.add_mem he hzC, ?_, ?_, ?_⟩
  · rw [map_add_eq, P.Q_e, P.Q_f, P.polar_ef, zero_add, zero_add]
  · rw [map_add_eq, P.Q_e, hz, hez, zero_add, add_zero]
  · rw [polar_add_left, polar_add_right, polar_add_right, P.polar_ee, hez, P.polar_fe, hfz]
    decide

end Orth

theorem exists_minus_sextuple (hq : (polarBilin q).Nondegenerate)
    (h : 8 ≤ finrank (ZMod 2) V ∨ (finrank (ZMod 2) V = 6 ∧
      ¬ ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 3 ∧ ∀ v ∈ W, q v = 0)) :
    ∃ e : Fin 6 → V, (∀ i, q (e i) = orthQv6 i) ∧ ∀ i j, polar q (e i) (e j) = orthBm6 i j := by
  have h5 : 5 ≤ finrank (ZMod 2) V := by rcases h with h | h <;> omega
  obtain ⟨P₁, P₂, h₁₂, hC, hdC⟩ := S45Q.exists_two_hypPairs hq h5
  have hC0 : P₁.perp ⊓ P₂.perp ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdC
    omega
  obtain ⟨x, hxC, y, hyC, hx, hy, hxy⟩ : ∃ x ∈ P₁.perp ⊓ P₂.perp, ∃ y ∈ P₁.perp ⊓ P₂.perp,
      q x = 1 ∧ q y = 1 ∧ polar q x y = 1 := by
    by_cases hanis : ∀ c ∈ P₁.perp ⊓ P₂.perp, q c = 0 → c = 0
    · exact exists_minus_pair_of_anisotropic hC hC0 hanis
    push Not at hanis
    obtain ⟨c, hcC, hc, hc0⟩ := hanis
    obtain ⟨P₃, rfl, hfC⟩ := S45Q.exists_hypPair_mem hC hcC hc0 hc
    refine exists_minus_pair_of_hypPair hC P₃ hcC hfC fun hbot => ?_
    have hd := S45Q.finrank_le_finrank_inf_perp_add_two P₃ hcC hfC
    rw [hbot, finrank_bot] at hd
    rcases h with h | ⟨-, hno⟩
    · omega
    · have h₁₃ : P₁.Orth P₃ := ⟨(HypPair.mem_perp.mp hcC.1).1, (HypPair.mem_perp.mp hfC.1).1,
        (HypPair.mem_perp.mp hcC.1).2, (HypPair.mem_perp.mp hfC.1).2⟩
      have h₂₃ : P₂.Orth P₃ := ⟨(HypPair.mem_perp.mp hcC.2).1, (HypPair.mem_perp.mp hfC.2).1,
        (HypPair.mem_perp.mp hcC.2).2, (HypPair.mem_perp.mp hfC.2).2⟩
      exact hno (CFSG.ClassicalGroups.Orthogonal.exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃)
  have hs : ∀ a b : V, polar q a b = 0 → polar q b a = 0 := fun a b hab => by
    rw [polar_comm]
    exact hab
  obtain ⟨hx1, hx1'⟩ := HypPair.mem_perp.mp hxC.1
  obtain ⟨hx2, hx2'⟩ := HypPair.mem_perp.mp hxC.2
  obtain ⟨hy1, hy1'⟩ := HypPair.mem_perp.mp hyC.1
  obtain ⟨hy2, hy2'⟩ := HypPair.mem_perp.mp hyC.2
  have hyx : polar q y x = 1 := by rw [polar_comm]; exact hxy
  refine ⟨![P₁.e, P₁.f, P₂.e, P₂.f, x, y], fun i => ?_, fun i j => ?_⟩
  · fin_cases i <;> simp [orthQv6, P₁.Q_e, P₁.Q_f, P₂.Q_e, P₂.Q_f, hx, hy]
  · fin_cases i <;> fin_cases j <;>
      simp [-polar_self, orthBm6, polar_self_eq_zero, P₁.polar_ef, P₁.polar_fe, P₂.polar_ef,
        P₂.polar_fe, h₁₂.ee, h₁₂.ef, h₁₂.fe, h₁₂.ff, hs _ _ h₁₂.ee, hs _ _ h₁₂.ef, hs _ _ h₁₂.fe,
        hs _ _ h₁₂.ff, hx1, hx1', hx2, hx2', hy1, hy1', hy2, hy2', hs _ _ hx1, hs _ _ hx1',
        hs _ _ hx2, hs _ _ hx2', hs _ _ hy1, hs _ _ hy1', hs _ _ hy2, hs _ _ hy2', hxy, hyx]

theorem eichler_mem_omegaGroup (hq : (polarBilin q).Nondegenerate) (s u : V) :
    eichler q s u ∈ omegaGroup q hq :=
  S2.eichler_mem_omegaGroup hq s u

theorem sq_mem_omegaGroup (hq : (polarBilin q).Nondegenerate) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ orthogonalGroup q) : g * g ∈ omegaGroup q hq := by
  refine mem_omegaGroup.mpr ⟨mul_mem hg hg, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hq hg hg]
  exact zmod2_add_self _

theorem mem_omegaGroup_of_pow_three (hq : (polarBilin q).Nondegenerate)
    {H : Subgroup (V ≃ₗ[ZMod 2] V)} (hH : omegaGroup q hq ≤ H) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ orthogonalGroup q) (hg3 : g ^ 3 ∈ H) : g ∈ H := by
  have h2 : g * g ∈ H := hH (sq_mem_omegaGroup hq hg)
  have e : g = g ^ 3 * (g * g)⁻¹ := by group
  rw [e]
  exact H.mul_mem hg3 (H.inv_mem h2)

end CFSG.LargeExtraspecial.FS77
