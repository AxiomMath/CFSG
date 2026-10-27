module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryFrame

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace ProjectiveGeometry

open Module

variable {K : Type*} {d : ℕ}

@[expose] def extend (x : Fin d → K) (c : K) : Fin (d + 1) → K :=
  Fin.snoc (α := fun _ => K) x c

@[simp]
theorem extend_castSucc (x : Fin d → K) (c : K) (i : Fin d) : extend x c i.castSucc = x i :=
  Fin.snoc_castSucc (α := fun _ => K) _ _ _

@[simp]
theorem extend_last (x : Fin d → K) (c : K) : extend x c (Fin.last d) = c :=
  Fin.snoc_last (α := fun _ => K) _ _

theorem extend_ext {v w : Fin (d + 1) → K} (h1 : ∀ i : Fin d, v i.castSucc = w i.castSucc)
    (h2 : v (Fin.last d) = w (Fin.last d)) : v = w := by
  funext i
  induction i using Fin.lastCases with
  | last => exact h2
  | cast i => exact h1 i

theorem extend_inj {x y : Fin d → K} {c e : K} : extend x c = extend y e ↔ x = y ∧ c = e := by
  constructor
  · intro h
    exact ⟨funext fun i => by simpa using congrFun h i.castSucc,
      by simpa using congrFun h (Fin.last d)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem extend_init (v : Fin (d + 1) → K) : extend (Fin.init v) (v (Fin.last d)) = v :=
  extend_ext (fun i => by simp [Fin.init]) (by simp)

variable [Field K]

theorem extend_add (x y : Fin d → K) (c e : K) :
    extend x c + extend y e = extend (x + y) (c + e) :=
  extend_ext (fun i => by simp) (by simp)

theorem extend_sub (x y : Fin d → K) (c e : K) :
    extend x c - extend y e = extend (x - y) (c - e) :=
  extend_ext (fun i => by simp) (by simp)

theorem extend_smul (a : K) (x : Fin d → K) (c : K) : a • extend x c = extend (a • x) (a * c) :=
  extend_ext (fun i => by simp) (by simp)

theorem extend_zero_zero : extend (0 : Fin d → K) 0 = 0 :=
  extend_ext (fun i => by simp) (by simp)

theorem extend_single (i : Fin d) :
    extend (Pi.single i (1 : K)) 0 = (Pi.single i.castSucc 1 : Fin (d + 1) → K) :=
  extend_ext (fun j => by simp [Pi.single_apply]) (by simp)

theorem extend_zero_one : extend (0 : Fin d → K) 1 = (Pi.single (Fin.last d) 1 : Fin (d + 1) → K) :=
  extend_ext (fun j => by simp) (by simp)

theorem extend_one_one : extend (1 : Fin d → K) 1 = 1 :=
  extend_ext (fun j => by simp) (by simp)

theorem extend_ne_zero_of_last {x : Fin d → K} {c : K} (hc : c ≠ 0) : extend x c ≠ 0 := fun h =>
  hc (by simpa using congrFun h (Fin.last d))

theorem extend_ne_zero_of_ne {u : Fin d → K} (hu : u ≠ 0) (c : K) : extend u c ≠ 0 := fun h =>
  hu (funext fun i => by simpa using congrFun h i.castSucc)

@[expose] def affinePoint (x : Fin d → K) : Submodule K (Fin (d + 1) → K) :=
  K ∙ extend x 1

@[expose] def infinityPoint (u : Fin d → K) : Submodule K (Fin (d + 1) → K) :=
  K ∙ extend u 0

@[expose] def infinityHyperplane (d : ℕ) (K : Type*) [Field K] : Submodule K (Fin (d + 1) → K) :=
  LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ : Fin (d + 1) => K) (Fin.last d))

@[expose] def affineLine (p u : Fin d → K) : Set (Fin d → K) :=
  Set.range fun t : K => p + t • u

@[expose] def projLine (p u : Fin d → K) : Submodule K (Fin (d + 1) → K) :=
  affinePoint p ⊔ infinityPoint u

theorem mem_infinityHyperplane {v : Fin (d + 1) → K} :
    v ∈ infinityHyperplane d K ↔ v (Fin.last d) = 0 :=
  Iff.rfl

theorem finrank_affinePoint (x : Fin d → K) : finrank K (affinePoint x) = 1 :=
  finrank_span_singleton (extend_ne_zero_of_last one_ne_zero)

theorem finrank_infinityPoint {u : Fin d → K} (hu : u ≠ 0) : finrank K (infinityPoint u) = 1 :=
  finrank_span_singleton (extend_ne_zero_of_ne hu 0)

theorem infinityPoint_le (u : Fin d → K) : infinityPoint u ≤ infinityHyperplane d K := by
  rw [infinityPoint, Submodule.span_singleton_le_iff_mem, mem_infinityHyperplane, extend_last]

theorem affinePoint_not_le (x : Fin d → K) : ¬affinePoint x ≤ infinityHyperplane d K := by
  rw [affinePoint, Submodule.span_singleton_le_iff_mem, mem_infinityHyperplane, extend_last]
  exact one_ne_zero

theorem affinePoint_injective : Function.Injective (affinePoint (K := K) (d := d)) := by
  intro x y h
  have hx : extend x 1 ∈ affinePoint y := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  rw [extend_smul, extend_inj, mul_one] at hc
  rw [← hc.1, hc.2, one_smul]

theorem point_cases {L : Submodule K (Fin (d + 1) → K)} (hL : finrank K L = 1) :
    (∃ x, L = affinePoint x) ∨ ∃ u : Fin d → K, u ≠ 0 ∧ L = infinityPoint u := by
  obtain ⟨v, hv0, rfl⟩ := exists_eq_span_singleton hL
  by_cases hvl : v (Fin.last d) = 0
  · refine Or.inr ⟨Fin.init v, fun h => hv0 ?_, ?_⟩
    · rw [← extend_init v, h, hvl, extend_zero_zero]
    · rw [infinityPoint, ← hvl, extend_init]
  · refine Or.inl ⟨(v (Fin.last d))⁻¹ • Fin.init v, ?_⟩
    have hext : extend ((v (Fin.last d))⁻¹ • Fin.init v) 1 = (v (Fin.last d))⁻¹ • v :=
      extend_ext (fun i => by simp [Fin.init]) (by simp [hvl])
    rw [affinePoint, hext, Submodule.span_singleton_smul_eq (inv_ne_zero hvl).isUnit]

theorem eq_smul_of_infinityPoint_eq {u u' : Fin d → K} (hu' : u' ≠ 0)
    (h : infinityPoint u = infinityPoint u') : ∃ c : K, c ≠ 0 ∧ u' = c • u := by
  have hx : extend u' 0 ∈ infinityPoint u := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  rw [extend_smul, extend_inj] at hc
  refine ⟨c, fun hc0 => hu' ?_, hc.1.symm⟩
  rw [← hc.1, hc0, zero_smul]

theorem affineLine_smul {c : K} (hc : c ≠ 0) (p u : Fin d → K) :
    affineLine p (c • u) = affineLine p u := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t * c, by simp only [smul_smul]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t / c, by simp only [smul_smul, div_mul_cancel₀ t hc]⟩

theorem affinePoint_le_projLine {x p u : Fin d → K} :
    affinePoint x ≤ projLine p u ↔ x ∈ affineLine p u := by
  rw [affinePoint, Submodule.span_singleton_le_iff_mem, projLine, affinePoint, infinityPoint,
    Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [extend_smul, extend_smul, extend_add, extend_inj, mul_one, mul_zero, add_zero] at hyz
    refine ⟨b, ?_⟩
    simp only
    rw [← hyz.1, hyz.2, one_smul]
  · rintro ⟨t, rfl⟩
    refine ⟨extend p 1, Submodule.mem_span_singleton_self _, t • extend u 0,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    rw [extend_smul, extend_add, mul_zero, add_zero]

theorem projLine_inf (p u : Fin d → K) :
    projLine p u ⊓ infinityHyperplane d K = infinityPoint u := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [projLine, affinePoint, infinityPoint, Submodule.mem_sup] at hv1
    obtain ⟨y, hy, z, hz, rfl⟩ := hv1
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [mem_infinityHyperplane, extend_smul, extend_smul, extend_add, extend_last, mul_one,
      mul_zero, add_zero] at hv2
    rw [hv2, zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact le_inf le_sup_right (infinityPoint_le u)

theorem affinePoint_sup (p q : Fin d → K) :
    affinePoint p ⊔ affinePoint q = projLine p (q - p) := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [affinePoint_le_projLine]
    exact ⟨1, by simp⟩
  · refine sup_le le_sup_left ?_
    rw [infinityPoint, Submodule.span_singleton_le_iff_mem]
    have h : extend (q - p) 0 = extend q 1 - extend p 1 := by rw [extend_sub, sub_self]
    rw [h]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))

theorem infinityHyperplane_eq_iSup :
    infinityHyperplane d K = ⨆ i : Fin d, K ∙ (Pi.single i.castSucc (1 : K) : Fin (d + 1) → K) := by
  apply le_antisymm
  · intro v hv
    rw [mem_infinityHyperplane] at hv
    have hv' : v = ∑ i : Fin d, Pi.single i.castSucc (v i.castSucc) := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      rw [Fin.sum_univ_castSucc, hv, Pi.single_zero, add_zero]
    rw [hv']
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
    rw [Submodule.mem_span_singleton]
    exact ⟨v i.castSucc, by rw [← Pi.single_smul, smul_eq_mul, mul_one]⟩
  · refine iSup_le fun i => ?_
    rw [Submodule.span_singleton_le_iff_mem, mem_infinityHyperplane]
    simp

theorem affine_coordinates (Ψ : Submodule K (Fin (d + 1) → K) ≃o Submodule K (Fin (d + 1) → K))
    (hΨe : ∀ i : Fin (d + 1), Ψ (K ∙ Pi.single i 1) = K ∙ Pi.single i 1)
    (hΨ1 : Ψ (K ∙ (1 : Fin (d + 1) → K)) = K ∙ (1 : Fin (d + 1) → K)) :
    Ψ (infinityHyperplane d K) = infinityHyperplane d K ∧
    ∃ φ : (Fin d → K) ≃ (Fin d → K), (∀ x, Ψ (affinePoint x) = affinePoint (φ x)) ∧
      (∃ f : Fin d → K ≃ K, (∀ i, f i 0 = 0 ∧ f i 1 = 1) ∧ ∀ x, φ x = fun i => f i (x i)) ∧
      ∀ u : Fin d → K, u ≠ 0 → ∃ u' : Fin d → K, u' ≠ 0 ∧
        Ψ (infinityPoint u) = infinityPoint u' ∧
          ∀ p, φ '' affineLine p u = affineLine (φ p) u' := by
  classical
  have hH : Ψ (infinityHyperplane d K) = infinityHyperplane d K := by
    rw [infinityHyperplane_eq_iSup, OrderIso.map_iSup]
    simp_rw [hΨe]
  have hH' : Ψ.symm (infinityHyperplane d K) = infinityHyperplane d K := by
    rw [OrderIso.symm_apply_eq, hH]
  have haff : ∀ Θ : Submodule K (Fin (d + 1) → K) ≃o Submodule K (Fin (d + 1) → K),
      Θ.symm (infinityHyperplane d K) = infinityHyperplane d K →
        ∀ x, ∃ y, Θ (affinePoint x) = affinePoint y := by
    intro Θ hΘ x
    rcases point_cases ((finrank_orderIso Θ _).trans (finrank_affinePoint x)) with
      ⟨y, hy⟩ | ⟨u, -, hu⟩
    · exact ⟨y, hy⟩
    · exfalso
      apply affinePoint_not_le x
      have h1 : Θ (affinePoint x) ≤ infinityHyperplane d K := hu ▸ infinityPoint_le u
      have h2 := Θ.le_symm_apply.mpr h1
      rwa [hΘ] at h2
  choose φf hφf using haff Ψ hH'
  choose φg hφg using haff Ψ.symm (by rw [OrderIso.symm_symm]; exact hH)
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin d → K) ≃ (Fin d → K), ∀ x, Ψ (affinePoint x) = affinePoint (φ x) :=
    ⟨{ toFun := φf
       invFun := φg
       left_inv := fun x => affinePoint_injective (by
         rw [← hφg, ← hφf, OrderIso.symm_apply_apply])
       right_inv := fun y => affinePoint_injective (by
         rw [← hφf, ← hφg, OrderIso.apply_symm_apply]) }, hφf⟩
  have hinf : ∀ u : Fin d → K, u ≠ 0 → ∃ u', u' ≠ 0 ∧ Ψ (infinityPoint u) = infinityPoint u' := by
    intro u hu
    rcases point_cases ((finrank_orderIso Ψ _).trans (finrank_infinityPoint hu)) with
      ⟨y, hy⟩ | ⟨u', hu', hu'eq⟩
    · exfalso
      apply affinePoint_not_le y
      rw [← hy, ← hH]
      exact Ψ.monotone (infinityPoint_le u)
    · exact ⟨u', hu', hu'eq⟩
  have hline : ∀ u : Fin d → K, u ≠ 0 → ∃ u' : Fin d → K, u' ≠ 0 ∧
      Ψ (infinityPoint u) = infinityPoint u' ∧ ∀ p, φ '' affineLine p u = affineLine (φ p) u' := by
    intro u hu
    obtain ⟨u', hu', hΨu⟩ := hinf u hu
    refine ⟨u', hu', hΨu, fun p => ?_⟩
    have hP : Ψ (projLine p u) = projLine (φ p) u' := by
      rw [projLine, Ψ.map_sup, hφ, hΨu]
      rfl
    have hmem : ∀ x, x ∈ affineLine p u ↔ φ x ∈ affineLine (φ p) u' := fun x => by
      rw [← affinePoint_le_projLine, ← affinePoint_le_projLine, ← hφ, ← hP, Ψ.le_iff_le]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).mp hx
    · intro hy
      refine ⟨φ.symm y, (hmem _).mpr ?_, φ.apply_symm_apply y⟩
      rwa [φ.apply_symm_apply]
  have hdir : ∀ (j : Fin d) (p : Fin d → K),
      φ '' affineLine p (Pi.single j 1) = affineLine (φ p) (Pi.single j 1) := by
    intro j p
    obtain ⟨u', hu', hΨu, hl⟩ := hline (Pi.single j 1) (single_ne_zero j)
    have hfix : Ψ (infinityPoint (Pi.single j (1 : K))) = infinityPoint (Pi.single j 1) := by
      rw [infinityPoint, extend_single, hΨe]
    obtain ⟨c, hc, rfl⟩ := eq_smul_of_infinityPoint_eq hu' (hfix.symm.trans hΨu)
    rw [hl p, affineLine_smul hc]
  have hupd : ∀ (x : Fin d → K) (j : Fin d) (t : K) (i : Fin d), i ≠ j →
      φ (Function.update x j t) i = φ x i := by
    intro x j t i hij
    have hx : Function.update x j t ∈ affineLine x (Pi.single j 1) := by
      refine ⟨t - x j, ?_⟩
      ext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Function.update_apply]
      split_ifs with h
      · subst h
        ring
      · ring
    have h1 : φ (Function.update x j t) ∈ affineLine (φ x) (Pi.single j 1) := by
      rw [← hdir j x]
      exact Set.mem_image_of_mem φ hx
    obtain ⟨s, hs⟩ := h1
    rw [← hs]
    simp [hij]
  have hdep : ∀ (x y : Fin d → K) (i : Fin d), x i = y i → φ x i = φ y i := by
    intro x y i hxy
    have key : ∀ S : Finset (Fin d), φ (fun k => if k ∈ S then y k else x k) i = φ x i := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert a S haS ih =>
        have hz : (fun k => if k ∈ insert a S then y k else x k) =
            Function.update (fun k => if k ∈ S then y k else x k) a (y a) := by
          ext k
          by_cases hka : k = a
          · subst hka
            simp
          · simp [Finset.mem_insert, hka]
        rw [hz]
        by_cases hai : i = a
        · subst hai
          have hself : Function.update (fun k => if k ∈ S then y k else x k) i (y i) =
              fun k => if k ∈ S then y k else x k := by
            rw [Function.update_eq_self_iff]
            simp [haS, hxy]
          rw [hself, ih]
        · rw [hupd _ a (y a) i hai, ih]
    have h := key Finset.univ
    simp only [Finset.mem_univ, ite_true] at h
    exact h.symm
  have hφ0 : φ 0 = 0 := by
    apply affinePoint_injective
    rw [← hφ, affinePoint, extend_zero_one, hΨe]
  have hφ1 : φ 1 = 1 := by
    apply affinePoint_injective
    rw [← hφ, affinePoint, extend_one_one, hΨ1]
  have haxis : ∀ (i : Fin d) (t : K),
      φ (t • Pi.single i 1) = φ (t • Pi.single i 1) i • Pi.single i 1 := by
    intro i t
    have h1 : φ (t • Pi.single i 1) ∈ affineLine (φ 0) (Pi.single i 1) := by
      rw [← hdir i 0]
      exact Set.mem_image_of_mem φ ⟨t, by simp⟩
    obtain ⟨s, hs⟩ := h1
    rw [hφ0] at hs
    rw [← hs]
    simp
  have hfbij : ∀ i : Fin d, Function.Bijective fun t : K => φ (t • Pi.single i 1) i := by
    intro i
    constructor
    · intro t t' htt'
      have h := congrArg (· • (Pi.single i (1 : K) : Fin d → K)) htt'
      simp only at h
      rw [← haxis, ← haxis] at h
      simpa using congrFun (φ.injective h) i
    · intro s
      have h1 : s • (Pi.single i (1 : K) : Fin d → K) ∈ affineLine (φ 0) (Pi.single i 1) := by
        rw [hφ0]
        exact ⟨s, by simp⟩
      rw [← hdir i 0] at h1
      obtain ⟨x, ⟨t, rfl⟩, hx⟩ := h1
      refine ⟨t, ?_⟩
      simp only [zero_add] at hx ⊢
      rw [hx]
      simp
  refine ⟨hH, φ, hφ, ⟨fun i => Equiv.ofBijective _ (hfbij i), fun i => ⟨?_, ?_⟩, fun x => ?_⟩,
    hline⟩
  · change φ ((0 : K) • Pi.single i 1) i = 0
    rw [zero_smul, hφ0]
    rfl
  · change φ ((1 : K) • Pi.single i 1) i = 1
    rw [hdep _ 1 i (by simp), hφ1]
    rfl
  · funext i
    change φ x i = φ (x i • Pi.single i 1) i
    exact hdep _ _ i (by simp)

end ProjectiveGeometry

end CFSG.LocalAnalysis.ComponentInitial
