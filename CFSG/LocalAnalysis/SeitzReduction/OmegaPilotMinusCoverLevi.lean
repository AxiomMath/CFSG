module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactLevel

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)
open CFSG.SeitzReduction.SymplecticPilot (planeOf planeEnum planeEnum_injective diagSpEntry
  diagSpEntry_inl diagSpEntry_inr commute_of_diag_iff)
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem conj_inv_facts_of_conj_eq_inv {a g : G} (h : g * a * g⁻¹ = a⁻¹) :
    g * a⁻¹ * g⁻¹ = a ∧ g⁻¹ * a * g = a⁻¹ ∧ g⁻¹ * a⁻¹ * g = a := by
  have h1 : g * a⁻¹ * g⁻¹ = a := by
    have := congrArg (·⁻¹) h
    simpa [mul_assoc] using this
  have h2 : g⁻¹ * a⁻¹ * g = a := by
    calc g⁻¹ * a⁻¹ * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [h]
      _ = a := by group
  have h3 : g⁻¹ * a * g = a⁻¹ := by
    have := congrArg (·⁻¹) h2
    simpa [mul_assoc] using this
  exact ⟨h1, h3, h2⟩

theorem conj_facts_of_conj_eq {a g : G} (h : g * a * g⁻¹ = a) :
    g * a⁻¹ * g⁻¹ = a⁻¹ ∧ g⁻¹ * a * g = a ∧ g⁻¹ * a⁻¹ * g = a⁻¹ := by
  have h1 : g * a⁻¹ * g⁻¹ = a⁻¹ := by
    have := congrArg (·⁻¹) h
    simpa [mul_assoc] using this
  have h2 : g⁻¹ * a * g = a := by
    calc g⁻¹ * a * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [h]
      _ = a := by group
  have h3 : g⁻¹ * a⁻¹ * g = a⁻¹ := by
    have := congrArg (·⁻¹) h2
    simpa [mul_assoc] using this
  exact ⟨h1, h2, h3⟩

theorem commutatorElement_conj_eq_of_conj {a x y : G}
    (hx : x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹) (hy : y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a⁻¹) :
    ⁅x, y⁆ * a * ⁅x, y⁆⁻¹ = a := by
  have e : ⁅x, y⁆ * a * ⁅x, y⁆⁻¹ = x * (y * (x⁻¹ * (y⁻¹ * a * y) * x) * y⁻¹) * x⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · obtain ⟨-, hx2, -⟩ := conj_facts_of_conj_eq hx
    obtain ⟨-, hy2, -⟩ := conj_facts_of_conj_eq hy
    rw [hy2, hx2, hy, hx]
  · obtain ⟨-, -, hx3⟩ := conj_facts_of_conj_eq hx
    obtain ⟨hy1, hy2, -⟩ := conj_inv_facts_of_conj_eq_inv hy
    rw [hy2, hx3, hy1, hx]
  · obtain ⟨hx1, hx2, -⟩ := conj_inv_facts_of_conj_eq_inv hx
    obtain ⟨hy1, hy2, -⟩ := conj_facts_of_conj_eq hy
    rw [hy2, hx2, hy1, hx1]
  · obtain ⟨hx1, -, hx3⟩ := conj_inv_facts_of_conj_eq_inv hx
    obtain ⟨-, hy2, -⟩ := conj_inv_facts_of_conj_eq_inv hy
    rw [hy2, hx3, hy, hx1]

theorem commutator_le_centralizer_of_conj {H : Subgroup G} {a : G}
    (h : ∀ x ∈ H, x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹) :
    ⁅H, H⁆ ≤ centralizer ({a} : Set G) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [mem_centralizer_singleton_iff]
  have h1 := commutatorElement_conj_eq_of_conj (h x hx) (h y hy)
  calc ⁅x, y⁆ * a = ⁅x, y⁆ * a * ⁅x, y⁆⁻¹ * ⁅x, y⁆ := by group
    _ = a * ⁅x, y⁆ := by rw [h1]

end Group

section FreePlane

variable {F : Type} [Field F] {m : ℕ}

theorem mulVec_single_one_apply_minus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F) (j u : ι) : (A *ᵥ Pi.single j 1) u = A u j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem diagSpEntry_mulSingle_of_ne {p : Fin m} (μ : Fˣ) {u : Fin m ⊕ Fin m}
    (hu : planeOf u ≠ p) : diagSpEntry (Pi.mulSingle p μ) u = 1 := by
  rcases u with i | i
  · have hi : i ≠ p := hu
    simp [diagSpEntry, Pi.mulSingle_eq_of_ne hi]
  · have hi : i ≠ p := hu
    simp [diagSpEntry, Pi.mulSingle_eq_of_ne hi]

theorem statedQuadPlus_of_supp {p : Fin m} {w : Fin m ⊕ Fin m → F}
    (hw : ∀ u, planeOf u ≠ p → w u = 0) :
    StatedQuadPlus m F w = w (.inl p) * w (.inr p) := by
  change ∑ i, w (.inl i) * w (.inr i) = _
  rw [Finset.sum_eq_single p]
  · intro i _ hi
    rw [hw (.inl i) hi, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem freePlane_block {A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hA : ∀ v, StatedQuadPlus m F (A *ᵥ v) = StatedQuadPlus m F v) {p : Fin m}
    (hzero : ∀ u v, planeOf u ≠ p → planeOf v = p → A u v = 0) :
    A (.inl p) (.inl p) * A (.inr p) (.inl p) = 0 ∧
      A (.inl p) (.inr p) * A (.inr p) (.inr p) = 0 ∧
      A (.inl p) (.inl p) * A (.inr p) (.inr p) +
        A (.inl p) (.inr p) * A (.inr p) (.inl p) = 1 := by
  have hcol : ∀ j : Fin m ⊕ Fin m, planeOf j = p → ∀ u, planeOf u ≠ p →
      (A *ᵥ Pi.single j 1) u = 0 := by
    intro j hj u hu
    rw [mulVec_single_one_apply_minus]
    exact hzero u j hu hj
  have hsing : ∀ j : Fin m ⊕ Fin m, planeOf j = p → ∀ u, planeOf u ≠ p →
      (Pi.single j (1 : F) : Fin m ⊕ Fin m → F) u = 0 := by
    intro j hj u hu
    have hne : u ≠ j := fun h => hu (h ▸ hj)
    simp [hne]
  have hl : planeOf (Sum.inl p : Fin m ⊕ Fin m) = p := rfl
  have hr : planeOf (Sum.inr p : Fin m ⊕ Fin m) = p := rfl
  have he := hA (Pi.single (.inl p) 1)
  rw [statedQuadPlus_of_supp (hcol _ hl), statedQuadPlus_of_supp (hsing _ hl),
    mulVec_single_one_apply_minus, mulVec_single_one_apply_minus] at he
  have hf := hA (Pi.single (.inr p) 1)
  rw [statedQuadPlus_of_supp (hcol _ hr), statedQuadPlus_of_supp (hsing _ hr),
    mulVec_single_one_apply_minus, mulVec_single_one_apply_minus] at hf
  have hef := hA (Pi.single (.inl p) 1 + Pi.single (.inr p) 1)
  rw [mulVec_add, statedQuadPlus_of_supp (fun u hu => by
      rw [Pi.add_apply, hcol _ hl u hu, hcol _ hr u hu, add_zero]),
    statedQuadPlus_of_supp (fun u hu => by
      rw [Pi.add_apply, hsing _ hl u hu, hsing _ hr u hu, add_zero])] at hef
  simp only [Pi.add_apply, mulVec_single_one_apply_minus] at hef
  simp only [Pi.single_apply, reduceCtorEq, ite_false, ite_true] at he hf hef
  refine ⟨by simpa using he, by simpa using hf, ?_⟩
  have he' : A (.inl p) (.inl p) * A (.inr p) (.inl p) = 0 := by simpa using he
  have hf' : A (.inl p) (.inr p) * A (.inr p) (.inr p) = 0 := by simpa using hf
  have hef' : (A (.inl p) (.inl p) + A (.inl p) (.inr p)) *
      (A (.inr p) (.inl p) + A (.inr p) (.inr p)) = 1 := by simpa using hef
  linear_combination hef' - he' - hf'

theorem eq_inl_or_eq_inr_of_planeOf_eq {p : Fin m} {u : Fin m ⊕ Fin m} (hu : planeOf u = p) :
    u = .inl p ∨ u = .inr p := by
  rcases u with i | i
  · exact Or.inl (congrArg Sum.inl hu)
  · exact Or.inr (congrArg Sum.inr hu)

theorem conj_freeTorus {x : GL (Fin m ⊕ Fin m) F} (hx : x ∈ StatedOmega (StatedQuadPlus m F))
    {p : Fin m} (hzero : ∀ u v, planeOf u ≠ p → planeOf v = p →
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) u v = 0)
    (hzero' : ∀ u v, planeOf u = p → planeOf v ≠ p →
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) u v = 0) (μ : Fˣ) :
    x * diagOmega F m (Pi.mulSingle p μ) * x⁻¹ = diagOmega F m (Pi.mulSingle p μ) ∨
      x * diagOmega F m (Pi.mulSingle p μ) * x⁻¹ = (diagOmega F m (Pi.mulSingle p μ))⁻¹ := by
  have hiso : ∀ v, StatedQuadPlus m F ((x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v) =
      StatedQuadPlus m F v := by
    refine isometry_of_mem_isometryClosure ?_
    rw [statedOmega_eq_commutator_isometryClosure] at hx
    exact Subgroup.commutator_le_self _ hx
  obtain ⟨h1, h2, h3⟩ := freePlane_block hiso hzero
  have hent : ∀ u, planeOf u ≠ p → diagSpEntry (Pi.mulSingle p μ) u = 1 :=
    fun u hu => diagSpEntry_mulSingle_of_ne μ hu
  have hent' : ∀ u, planeOf u ≠ p → diagSpEntry (Pi.mulSingle p μ)⁻¹ u = 1 := fun u hu => by
    rw [← Pi.mulSingle_inv]
    exact diagSpEntry_mulSingle_of_ne μ⁻¹ hu
  by_cases hα : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (.inl p) (.inl p) = 0
  ·
    right
    have hβ : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (.inl p) (.inr p) ≠ 0 := by
      intro h
      rw [hα, h] at h3
      simp at h3
    have hδ : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (.inr p) (.inr p) = 0 :=
      (mul_eq_zero.1 h2).resolve_left hβ
    rw [mul_inv_eq_iff_eq_mul, ← map_inv]
    apply Units.ext
    ext u v
    simp only [Units.val_mul, diagOmega_coe, mul_diagonal, diagonal_mul]
    by_cases hu : planeOf u = p <;> by_cases hv : planeOf v = p
    · rcases eq_inl_or_eq_inr_of_planeOf_eq hu with rfl | rfl <;>
        rcases eq_inl_or_eq_inr_of_planeOf_eq hv with rfl | rfl
      · rw [hα]; simp
      · simp [diagSpEntry, mul_comm]
      · simp [diagSpEntry, mul_comm]
      · rw [hδ]; simp
    · rw [hzero' u v hu hv]; simp
    · rw [hzero u v hu hv]; simp
    · rw [hent v hv, hent' u hu]
      simp
  ·
    left
    have hγ : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (.inr p) (.inl p) = 0 :=
      (mul_eq_zero.1 h1).resolve_left hα
    have hδ : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (.inr p) (.inr p) ≠ 0 := by
      intro h
      rw [hγ, h] at h3
      simp at h3
    have hβ : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (.inl p) (.inr p) = 0 :=
      (mul_eq_zero.1 h2).resolve_right hδ
    rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    ext u v
    simp only [Units.val_mul, diagOmega_coe, mul_diagonal, diagonal_mul]
    by_cases hu : planeOf u = p <;> by_cases hv : planeOf v = p
    · rcases eq_inl_or_eq_inr_of_planeOf_eq hu with rfl | rfl <;>
        rcases eq_inl_or_eq_inr_of_planeOf_eq hv with rfl | rfl
      · ring
      · rw [hβ]; simp
      · rw [hγ]; simp
      · ring
    · rw [hzero' u v hu hv]; simp
    · rw [hzero u v hu hv]; simp
    · rw [hent u hu, hent v hv]
      ring

theorem perfectCore_statedOmega_inf_centralizer_eq_level_of_free [Finite F]
    (hF : 4 ≤ Nat.card F) {J : Finset (Fin m)} (hJ : 2 ≤ J.card) {p : Fin m} (hp : p ∉ J)
    {μ : Fˣ} (hμ : μ * μ ≠ 1) (D : Set (Fin m → Fˣ))
    (hlevel : ∀ s ∈ D, ∀ i ∈ J, ∀ j ∈ J, s i = s j)
    (hsep : ∀ a b : Fin m ⊕ Fin m, a ≠ b → ¬ SameSide J a b →
      ¬ (planeOf a = p ∧ planeOf b = p) → ∃ s ∈ D, diagSpEntry s a ≠ diagSpEntry s b) :
    perfectCore (StatedOmega (StatedQuadPlus m F) ⊓ centralizer (diagOmega F m '' D)) =
      (omegaLeviSL F J.card).map (spEmbedGL (planeEnum J) (planeEnum_injective J)) := by
  set H := StatedOmega (StatedQuadPlus m F) ⊓ centralizer (diagOmega F m '' D) with hH
  set a := diagOmega F m (Pi.mulSingle p μ) with ha
  have hcomm : ∀ x ∈ H, ∀ u v, planeOf u ≠ planeOf v → (planeOf u = p ∨ planeOf v = p) →
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) u v = 0 := by
    intro x hx u v huv hp'
    have hne : u ≠ v := fun h => huv (h ▸ rfl)
    have hss : ¬ SameSide J u v := by
      rintro (⟨i, hi, j, hj, rfl, rfl⟩ | ⟨i, hi, j, hj, rfl, rfl⟩)
      · rcases hp' with h | h
        · exact hp (by rw [← (show i = p from h)]; exact hi)
        · exact hp (by rw [← (show j = p from h)]; exact hj)
      · rcases hp' with h | h
        · exact hp (by rw [← (show i = p from h)]; exact hi)
        · exact hp (by rw [← (show j = p from h)]; exact hj)
    have hpp : ¬ (planeOf u = p ∧ planeOf v = p) := fun h => huv (h.1.trans h.2.symm)
    obtain ⟨s, hs, hsne⟩ := hsep u v hne hss hpp
    have hc : Commute x (diagOmega F m s) :=
      ((mem_centralizer_iff.1 (mem_inf.1 hx).2) _ ⟨s, hs, rfl⟩).symm
    exact (commute_of_diag_iff (fun a b hab => diagOmega_apply_ne s hab) x).1 hc u v (by
      rw [diagOmega_apply_self, diagOmega_apply_self]
      exact hsne)
  have hconj : ∀ x ∈ H, x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹ := by
    intro x hx
    exact conj_freeTorus (mem_inf.1 hx).1
      (fun u v hu hv => hcomm x hx u v (fun h => hu (h.trans hv)) (Or.inr hv))
      (fun u v hu hv => hcomm x hx u v (fun h => hv (h.symm.trans hu)) (Or.inl hu)) μ
  have hpc : perfectCore H ≤ centralizer ({a} : Set (GL (Fin m ⊕ Fin m) F)) := by
    calc perfectCore H = ⁅perfectCore H, perfectCore H⁆ := (perfectCore_perfect H).symm
      _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono (perfectCore_le H) (perfectCore_le H)
      _ ≤ _ := commutator_le_centralizer_of_conj hconj
  set D' : Set (Fin m → Fˣ) := insert (Pi.mulSingle p μ) D with hD'
  have heq : perfectCore H =
      perfectCore (StatedOmega (StatedQuadPlus m F) ⊓ centralizer (diagOmega F m '' D')) := by
    refine le_antisymm (le_perfectCore_of_perfect ?_ (perfectCore_perfect H)) (perfectCore_mono ?_)
    · intro x hx
      refine mem_inf.2 ⟨(mem_inf.1 (perfectCore_le H hx)).1, mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      rcases hs with rfl | hs
      · exact (mem_centralizer_singleton_iff.1 (hpc hx)).symm
      · exact mem_centralizer_iff.1 (mem_inf.1 (perfectCore_le H hx)).2 _ ⟨s, hs, rfl⟩
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.image_mono (Set.subset_insert _ _)))
  rw [heq]
  refine perfectCore_statedOmega_inf_centralizer_eq_level hF hJ D' ?_ ?_
  · intro s hs i hi j hj
    rcases hs with rfl | hs
    · rw [Pi.mulSingle_eq_of_ne (fun h : i = p => hp (h ▸ hi)),
        Pi.mulSingle_eq_of_ne (fun h : j = p => hp (h ▸ hj))]
    · exact hlevel s hs i hi j hj
  · intro u v huv hss
    by_cases hpp : planeOf u = p ∧ planeOf v = p
    · refine ⟨Pi.mulSingle p μ, Set.mem_insert _ _, ?_⟩
      have h3 : (μ : F) ≠ ((μ⁻¹ : Fˣ) : F) := fun e =>
        SymplecticPilot.units_ne_inv_of_mul_self_ne_one hμ (Units.ext e)
      rcases eq_inl_or_eq_inr_of_planeOf_eq hpp.1 with rfl | rfl <;>
        rcases eq_inl_or_eq_inr_of_planeOf_eq hpp.2 with rfl | rfl
      · exact absurd rfl huv
      · simpa [diagSpEntry] using h3
      · simpa [diagSpEntry] using h3.symm
      · exact absurd rfl huv
    · obtain ⟨s, hs, hne⟩ := hsep u v huv hss hpp
      exact ⟨s, Set.mem_insert_of_mem _ hs, hne⟩

end FreePlane

end CFSG.SeitzReduction.OmegaPilot
