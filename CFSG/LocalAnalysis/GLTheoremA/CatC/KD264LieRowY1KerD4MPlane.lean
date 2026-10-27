module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MDecomp
public import CFSG.RankThree.PartOne.K159.RowFourType

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

open QuadraticMap Module CFSG.GroupTheory.WeirSylow CFSG.RankThree.PartOne.K159

noncomputable section

section Idem

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable {e f : Module.End K V}

theorem range_eq_of_idem (he : e * e = e) {x : V} (hx : x ∈ LinearMap.range e) : e x = x := by
  obtain ⟨a, rfl⟩ := hx
  have := congrArg (fun g : Module.End K V => g a) he
  simpa [Module.End.mul_apply] using this

theorem disjoint_range_of_orth (he : e * e = e) (hef : e * f = 0) :
    Disjoint (LinearMap.range e) (LinearMap.range f) := by
  rw [Submodule.disjoint_def]
  intro x hxe hxf
  obtain ⟨b, rfl⟩ := hxf
  have h1 := range_eq_of_idem he hxe
  have h2 : e (f b) = 0 := by
    have := congrArg (fun g : Module.End K V => g b) hef
    simpa [Module.End.mul_apply] using this
  rw [h2] at h1
  exact h1.symm

theorem range_add_eq_sup (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) :
    LinearMap.range (e + f) = LinearMap.range e ⊔ LinearMap.range f := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact Submodule.add_mem_sup ⟨a, rfl⟩ ⟨a, rfl⟩
  · apply sup_le
    · rintro _ ⟨a, rfl⟩
      refine ⟨e a, ?_⟩
      have h1 : f (e a) = 0 := by
        have := congrArg (fun g : Module.End K V => g a) hfe
        simpa [Module.End.mul_apply] using this
      have h2 : e (e a) = e a := range_eq_of_idem he ⟨a, rfl⟩
      simp [h1, h2]
    · rintro _ ⟨a, rfl⟩
      refine ⟨f a, ?_⟩
      have h1 : e (f a) = 0 := by
        have := congrArg (fun g : Module.End K V => g a) hef
        simpa [Module.End.mul_apply] using this
      have h2 : f (f a) = f a := range_eq_of_idem hf ⟨a, rfl⟩
      simp [h1, h2]

theorem add_idem (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) :
    (e + f) * (e + f) = e + f := by
  rw [add_mul, mul_add, mul_add, he, hf, hef, hfe]
  simp

theorem finrank_range_add [FiniteDimensional K V] (he : e * e = e) (hf : f * f = f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    finrank K (LinearMap.range (e + f)) =
      finrank K (LinearMap.range e) + finrank K (LinearMap.range f) := by
  rw [range_add_eq_sup he hf hef hfe]
  have := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e) (LinearMap.range f)
  rw [(disjoint_range_of_orth he hef).eq_bot, finrank_bot, add_zero] at this
  exact this

variable {Q : QuadraticForm K V}

theorem polar_range_orth (hse : ∀ u v, polar Q (e u) v = polar Q u (e v)) (hef : e * f = 0) :
    ∀ a ∈ LinearMap.range e, ∀ b ∈ LinearMap.range f, polar Q a b = 0 := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  have h : e (f b) = 0 := by
    have := congrArg (fun g : Module.End K V => g b) hef
    simpa [Module.End.mul_apply] using this
  rw [hse, h, QuadraticMap.polar_zero_right]

theorem nondeg_range (hnd : (polarBilin Q).Nondegenerate) (he : e * e = e)
    (hse : ∀ u v, polar Q (e u) v = polar Q u (e v)) :
    ∀ x ∈ LinearMap.range e, (∀ y ∈ LinearMap.range e, polar Q x y = 0) → x = 0 := by
  intro x hx hxy
  apply hnd.1 x
  intro v
  rw [QuadraticMap.polarBilin_apply_apply]
  have h1 := range_eq_of_idem he hx
  rw [← h1, hse]
  exact hxy _ ⟨v, rfl⟩

end Idem

section Types

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_comp_subtype' (S : Submodule K V) (a b : S) :
    polar (Q.comp S.subtype) a b = polar Q (a : V) (b : V) := by
  simp [polar, QuadraticMap.comp_apply]

theorem nondeg_comp_subtype' {S : Submodule K V}
    (h : ∀ x ∈ S, (∀ y ∈ S, polar Q x y = 0) → x = 0) :
    (polarBilin (Q.comp S.subtype)).Nondegenerate := by
  have key : ∀ a b : S, polarBilin (Q.comp S.subtype) a b = polar Q (a : V) (b : V) := by
    intro a b
    rw [QuadraticMap.polarBilin_apply_apply]
    exact polar_comp_subtype' S a b
  constructor
  · intro x hx
    refine Subtype.ext (h x x.2 (fun y hy => ?_))
    have := hx ⟨y, hy⟩
    rwa [key] at this
  · intro y hy
    refine Subtype.ext (h y y.2 (fun x hx => ?_))
    have := hy ⟨x, hx⟩
    rw [key] at this
    rw [polar_comm]
    exact this

@[expose] def isometryOfEq {A B : Submodule K V} (h : A = B) :
    (Q.comp A.subtype).IsometryEquiv (Q.comp B.subtype) where
  toLinearEquiv := LinearEquiv.ofEq A B h
  map_app' x := by
    simp [QuadraticMap.comp_apply]

theorem isPlusType_congr_eq {A B : Submodule K V} (h : A = B) :
    IsPlusType (Q.comp A.subtype) ↔ IsPlusType (Q.comp B.subtype) :=
  isPlusType_congr (isometryOfEq h)

variable [Finite K]

theorem isPlusType_sup_iff' [FiniteDimensional K V] {A B : Submodule K V} (hdisj : Disjoint A B)
    (horth : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0)
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate) {d₁ d₂ : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (h₁ : finrank K A = 2 * d₁)
    (h₂ : finrank K B = 2 * d₂) :
    IsPlusType (Q.comp (A ⊔ B).subtype) ↔
      (IsPlusType (Q.comp A.subtype) ↔ IsPlusType (Q.comp B.subtype)) := by
  rw [isPlusType_congr (isometryEquivSup Q A B hdisj horth)]
  exact isPlusType_prod_iff hA hB hd₁ hd₂ h₁ h₂

end Types

section Plane

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eig_sq_ne_one (h3 : (3 : K) ≠ 0) {μ : K} (hμ : μ ^ 2 + μ + 1 = 0) : μ * μ ≠ 1 := by
  intro h
  have h1 : μ = -2 := by linear_combination hμ - h
  rw [h1] at h
  apply h3
  linear_combination h

theorem plane_plus_iff {W : Submodule K V} (h3 : (3 : K) ≠ 0) (hW2 : finrank K W = 2)
    {T : V →ₗ[K] V} (hTW : ∀ x ∈ W, T x ∈ W) (hT : ∀ x ∈ W, T (T x) + T x + x = 0)
    (hTQ : ∀ x, Q (T x) = Q x)
    (hnd : ∀ x ∈ W, (∀ y ∈ W, polar Q x y = 0) → x = 0) :
    IsPlusType (Q.comp W.subtype) ↔ ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  have hfdW : FiniteDimensional K W := Module.finite_of_finrank_eq_succ hW2
  constructor
  · rintro ⟨S, hS, hSQ⟩
    have hS1 : finrank K S = 1 := by omega
    have hSne : S ≠ ⊥ := by
      rintro rfl
      rw [finrank_bot] at hS1
      omega
    obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
    have hQv : Q (x : V) = 0 := by
      have := hSQ x hxS
      simpa [QuadraticMap.comp_apply] using this
    have hvW : (x : V) ∈ W := x.2
    have hv0 : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
    generalize (x : V) = v at hQv hvW hv0
    by_cases hcol : ∃ c : K, T v = c • v
    · obtain ⟨c, hc⟩ := hcol
      have hT' := hT v hvW
      rw [hc, map_smul, hc] at hT'
      have h1 : (c * c + c + 1) • v = 0 := by
        rw [add_smul, add_smul, mul_smul, one_smul]
        exact hT'
      rcases smul_eq_zero.1 h1 with h | h
      · exact ⟨c, by linear_combination h⟩
      · exact absurd h hv0
    · exfalso
      push Not at hcol
      have hind : LinearIndependent K ![v, T v] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        by_cases ht : t = 0
        · subst ht
          simp only [zero_smul, add_zero] at hst
          exact ⟨(smul_eq_zero.1 hst).resolve_right hv0, rfl⟩
        · exfalso
          apply hcol (-(s / t))
          have h1 : t • T v = -(s • v) := eq_neg_of_add_eq_zero_right hst
          have h2 : T v = t⁻¹ • (t • T v) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          rw [h2, h1, smul_neg, smul_smul, ← neg_smul]
          congr 1
          field_simp
      have hspan2 : finrank K (Submodule.span K {v, T v}) = 2 := by
        rw [← Matrix.range_cons_cons_empty v (T v) ![], finrank_span_eq_card hind, Fintype.card_fin]
      have hle : Submodule.span K {v, T v} ≤ W := by
        rw [Submodule.span_le]
        intro z hz
        rcases hz with rfl | hz
        · exact hvW
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact hTW v hvW
      have heq : Submodule.span K {v, T v} = W :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan2, hW2])
      have hpolar : ∀ y ∈ W, polar Q v y = 0 := by
        intro y hy
        rw [← heq] at hy
        obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hy
        rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_smul_right, polar_self_map hTQ (hT v hvW),
          QuadraticMap.polar_self, hQv]
        simp
      exact hv0 (hnd v hvW hpolar)
  · rintro ⟨ω, hω⟩
    have hWne : W ≠ ⊥ := by
      rintro rfl
      rw [finrank_bot] at hW2
      omega
    obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    set ω' : K := -1 - ω with hω'
    have hω'2 : ω' ^ 2 + ω' + 1 = 0 := by rw [hω']; linear_combination hω
    have hωω' : ω * ω' = 1 := by rw [hω']; linear_combination -hω
    obtain ⟨v, hvW, hv0, μ, hμ, hTv⟩ : ∃ v ∈ W, v ≠ 0 ∧ ∃ μ : K, μ ^ 2 + μ + 1 = 0 ∧ T v = μ • v := by
      set w := T u - ω' • u with hw
      have hwW : w ∈ W := W.sub_mem (hTW u huW) (W.smul_mem ω' huW)
      by_cases hw0 : w = 0
      · refine ⟨u, huW, hu0, ω', hω'2, ?_⟩
        rw [hw, sub_eq_zero] at hw0
        exact hw0
      · refine ⟨w, hwW, hw0, ω, hω, ?_⟩
        have h2 : T (T u) = -u - T u := by
          have := hT u huW
          calc T (T u) = (T (T u) + T u + u) - T u - u := by abel
            _ = -u - T u := by rw [this]; abel
        rw [hw, map_sub, map_smul, h2, smul_sub, smul_smul, hωω', one_smul]
        have : ω' = -1 - ω := hω'
        rw [this]
        module
    have hQv : Q v = 0 := by
      have h1 : Q (T v) = Q v := hTQ v
      rw [hTv, QuadraticMap.map_smul, smul_eq_mul] at h1
      have h2 : (1 - μ * μ) * Q v = 0 := by linear_combination -h1
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd (by linear_combination -h) (eig_sq_ne_one h3 hμ)
      · exact h
    refine ⟨Submodule.span K {(⟨v, hvW⟩ : W)}, ?_, ?_⟩
    · rw [finrank_span_singleton (fun h => hv0 (congrArg Subtype.val h)), hW2]
    · intro x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      simp only [QuadraticMap.comp_apply, Submodule.subtype_apply, SetLike.val_smul]
      rw [QuadraticMap.map_smul, hQv]
      simp

end Plane

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

end
