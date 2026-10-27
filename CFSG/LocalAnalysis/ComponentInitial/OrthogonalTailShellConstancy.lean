module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailNormShell
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailLinearRigidity

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
  (Points pointMk pointMk_submodule exists_eq_pointMk)

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}

section Base

variable (hr : 1 ≤ r)

@[expose] def shellBase (q : K) : Fin r ⊕ Fin r → K :=
  Pi.single (Sum.inl ⟨0, hr⟩) 1 - q • Pi.single (Sum.inr ⟨0, hr⟩) 1

theorem quadPlus_shellBase (q : K) : quadPlus r K (shellBase hr q) = -q := by
  rw [quadPlus_apply, Finset.sum_eq_single ⟨0, hr⟩]
  · simp [shellBase]
  · intro k _ hk
    simp [shellBase, hk]
  · simp

theorem shellBase_ne_zero (q : K) : shellBase hr q ≠ 0 := fun h => by
  have := congrFun h (Sum.inl ⟨0, hr⟩)
  simp [shellBase] at this

end Base

section Adj

variable {q₁ q₂ : QuadraticForm K A} {c : K}

theorem tail_eq_of_shellAdj (φ : Points (quadTail r q₁) ≃ Points (quadTail r q₂))
    (hφ : ∀ L M : Points (quadTail r q₁),
      PolarOrtho (quadTail r q₁) L.val M.val ↔ PolarOrtho (quadTail r q₂) (φ L).val (φ M).val)
    (hani₂ : q₂.Anisotropic) {a : A} {u v : Fin r ⊕ Fin r → K}
    (huv : ShellAdj (quadPlus r K) (-q₁ a) u v) {b b' : A}
    (hu0 : ((u, a) : (Fin r ⊕ Fin r → K) × A) ≠ 0) (hu : quadTail r q₁ (u, a) = 0)
    (hv0 : ((v, a) : (Fin r ⊕ Fin r → K) × A) ≠ 0) (hv : quadTail r q₁ (v, a) = 0)
    (hb : (φ (pointMk (Q := quadTail r q₁) _ hu0 hu)).val = K ∙ (splitScale r K c u, b))
    (hb' : (φ (pointMk (Q := quadTail r q₁) _ hv0 hv)).val = K ∙ (splitScale r K c v, b'))
    (hqb : q₂ b = c * q₁ a) (hqb' : q₂ b' = c * q₁ a) : b = b' := by
  obtain ⟨-, -, -, -, hpol⟩ := huv
  have horth : polar (quadTail r q₁) (u, a) (v, a) = 0 := by
    rw [polar_quadTail]
    dsimp only
    rw [hpol, polar_self_eq_two_mul]
    ring
  have h := (hφ (pointMk _ hu0 hu) (pointMk _ hv0 hv)).1 (by
    rw [pointMk_submodule, pointMk_submodule]
    exact polarOrtho_span_singleton_iff_polar.2 horth)
  rw [hb, hb', polarOrtho_span_singleton_iff_polar, polar_quadTail] at h
  dsimp only at h
  rw [polar_splitScale, hpol] at h
  have hq : q₂ (b - b') = 0 := by
    rw [sub_eq_add_neg, QuadraticMap.map_add q₂, QuadraticMap.map_neg, polar_neg_right, hqb,
      hqb']
    linear_combination -h
  exact sub_eq_zero.1 (hani₂ _ hq)

end Adj


theorem orthogonal_geometry_tail_shell_constancy {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] {r : ℕ} (hr : 3 ≤ r) {q₁ q₂ : QuadraticForm K A}
    (hani₁ : q₁.Anisotropic) (hani₂ : q₂.Anisotropic)
    (φ : Points (quadTail r q₁) ≃ Points (quadTail r q₂))
    (hφ : ∀ L M : Points (quadTail r q₁),
      PolarOrtho (quadTail r q₁) L.val M.val ↔ PolarOrtho (quadTail r q₂) (φ L).val (φ M).val)
    {c : K}
    (hb : ∀ (v : (Fin r ⊕ Fin r → K) × A) (hv0 : v ≠ 0) (hv : quadTail r q₁ v = 0),
      (∃! b : A, (φ (pointMk (Q := quadTail r q₁) v hv0 hv)).val =
        K ∙ (splitScale r K c v.1, b)) ∧
      ∀ b : A, (φ (pointMk (Q := quadTail r q₁) v hv0 hv)).val =
          K ∙ (splitScale r K c v.1, b) → q₂ b = c * q₁ v.2 ∧ (v.2 = 0 → b = 0)) :
    ∃! F : A → A, F 0 = 0 ∧ (∀ a, q₂ (F a) = c * q₁ a) ∧
      ∀ (v : (Fin r ⊕ Fin r → K) × A) (hv0 : v ≠ 0) (hv : quadTail r q₁ v = 0),
        (φ (pointMk (Q := quadTail r q₁) v hv0 hv)).val = K ∙ (splitScale r K c v.1, F v.2) := by
  have hr1 : 1 ≤ r := by omega
  have hbase0 : ∀ a : A, ((shellBase hr1 (q₁ a), a) : (Fin r ⊕ Fin r → K) × A) ≠ 0 :=
    fun a h => shellBase_ne_zero hr1 (q₁ a) (congrArg Prod.fst h)
  have hbaseQ : ∀ a : A, quadTail r q₁ ((shellBase hr1 (q₁ a), a) :
      (Fin r ⊕ Fin r → K) × A) = 0 := fun a => by
    rw [quadTail_apply, quadPlus_shellBase]
    ring
  choose F hFspec using fun a => ((hb _ (hbase0 a) (hbaseQ a)).1).exists
  have hF0 : F 0 = 0 := ((hb _ (hbase0 0) (hbaseQ 0)).2 _ (hFspec 0)).2 rfl
  have hFq : ∀ a, q₂ (F a) = c * q₁ a := fun a => ((hb _ _ _).2 _ (hFspec a)).1
  have hall : ∀ (v : (Fin r ⊕ Fin r → K) × A) (hv0 : v ≠ 0) (hv : quadTail r q₁ v = 0),
      (φ (pointMk (Q := quadTail r q₁) v hv0 hv)).val = K ∙ (splitScale r K c v.1, F v.2) := by
    rintro ⟨u, a⟩ hv0 hv
    obtain ⟨b, hbv, -⟩ := (hb _ hv0 hv).1
    by_cases ha : a = 0
    · subst ha
      have := ((hb _ hv0 hv).2 b hbv).2 rfl
      rw [hbv, this, hF0]
    have hqa : q₁ a ≠ 0 := fun h => ha (hani₁ a h)
    have hu : quadPlus r K u = -q₁ a := by
      rw [quadTail_apply] at hv
      linear_combination hv
    have hu0 : u ≠ 0 := fun h => hqa (by rw [h, QuadraticMap.map_zero] at hu; linear_combination hu)
    have hT : ∃ T : Submodule K (Fin r ⊕ Fin r → K), finrank K T = 3 ∧
        ∀ x ∈ T, quadPlus r K x = 0 :=
      ⟨flag r K 3, finrank_flag hr, fun x hx => quadPlus_eq_zero_of_mem_flag hx⟩
    obtain ⟨l, hl, hlast⟩ := orthogonal_geometry_norm_shell_connected
      (nondegenerate_polarBilin_quadPlus r K) hT (shellBase_ne_zero hr1 (q₁ a)) hu0
      (quadPlus_shellBase hr1 (q₁ a)) hu
    have hR := List.relationReflTransGen_of_exists_isChain_cons l hl hlast
    have key : ∀ w, Relation.ReflTransGen (ShellAdj (quadPlus r K) (-q₁ a))
        (shellBase hr1 (q₁ a)) w → ∀ (hw0 : ((w, a) : (Fin r ⊕ Fin r → K) × A) ≠ 0)
          (hw : quadTail r q₁ (w, a) = 0),
          (φ (pointMk (Q := quadTail r q₁) _ hw0 hw)).val = K ∙ (splitScale r K c w, F a) := by
      intro w hrel
      induction hrel with
      | refl => exact fun _ _ => hFspec a
      | @tail w₁ w₂ _ hadj ih =>
        intro hw0 hw
        have hw₁0' : ((w₁, a) : (Fin r ⊕ Fin r → K) × A) ≠ 0 := fun h =>
          hadj.1 (congrArg Prod.fst h)
        have hw₁ : quadTail r q₁ ((w₁, a) : (Fin r ⊕ Fin r → K) × A) = 0 := by
          rw [quadTail_apply, hadj.2.2.1]
          ring
        have h1 := ih hw₁0' hw₁
        obtain ⟨b', hb', -⟩ := (hb _ hw0 hw).1
        have hb'q := ((hb _ hw0 hw).2 b' hb').1
        have hEq := tail_eq_of_shellAdj φ hφ hani₂ hadj hw₁0' hw₁ hw0 hw h1 hb' (hFq a) hb'q
        rw [hb', ← hEq]
    exact key u hR hv0 hv
  refine ⟨F, ⟨hF0, hFq, hall⟩, fun F' hF' => funext fun a => ?_⟩
  exact ((hb _ (hbase0 a) (hbaseQ a)).1).unique (hF'.2.2 _ (hbase0 a) (hbaseQ a)) (hFspec a)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
