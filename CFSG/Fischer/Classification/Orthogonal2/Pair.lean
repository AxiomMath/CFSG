module

public import CFSG.Fischer.Classification.Orthogonal2.Inner

public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex

public section

namespace CFSG.Fischer.Classification.Orth2

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Blueprint.Fischer
open CFSG.Fischer.Classification.Recognition.SymO

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

noncomputable abbrev reflO (Q : QuadraticForm (ZMod 2) V) (v : V) :
    TauCeti.QuadraticMap.orthogonalGroup Q :=
  ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩

theorem reflO_mem_reflClass {v : V} (hv : Q v = 1) : reflO Q v ∈ reflClass Q :=
  ⟨v, hv, rfl⟩

theorem conj_reflO (g : TauCeti.QuadraticMap.orthogonalGroup Q) (v : V) :
    g * reflO Q v * g⁻¹ = reflO Q ((g : V ≃ₗ[ZMod 2] V) v) :=
  Subtype.ext (reflect_conj g.2 v)

theorem reflect_ne_one (hnd : (polarBilin Q).Nondegenerate) {v : V} (hv : Q v = 1) :
    reflect Q v ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := exists_polar_eq_one hnd hv
  have key := DFunLike.congr_fun h x
  rw [reflect_apply_of_map_eq_one hv, hx, one_smul] at key
  change x + v = x at key
  exact ne_zero_of_map_eq_one hv (add_eq_left.mp key)

theorem center_orthogonalGroup_eq_bot [FiniteDimensional (ZMod 2) V]
    (hnd : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V) :
    Subgroup.center (TauCeti.QuadraticMap.orthogonalGroup Q) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hfix : ∀ v, Q v = 1 → (g : V ≃ₗ[ZMod 2] V) v = v := by
    intro v hv
    have hc : g * reflO Q v * g⁻¹ = reflO Q v := by
      rw [(Subgroup.mem_center_iff.mp hg (reflO Q v)).symm, mul_assoc, mul_inv_cancel, mul_one]
    rw [conj_reflO] at hc
    have hgv : Q ((g : V ≃ₗ[ZMod 2] V) v) = 1 := by
      rw [map_of_mem g.2, hv]
    exact eq_of_reflect_eq hnd hgv (congrArg Subtype.val hc) hv
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on (span_map_eq_one_eq_top hnd h5)
  intro v hv
  exact hfix v hv

theorem isConj_reflO [FiniteDimensional (ZMod 2) V] (hnd : (polarBilin Q).Nondegenerate)
    {u w : V} (hu : Q u = 1) (hw : Q w = 1) : IsConj (reflO Q u) (reflO Q w) := by
  obtain ⟨g, hg, hgu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hnd (k := 1) ![u] ![w]
    (linearIndependent_unique_iff.2 (by simpa using ne_zero_of_map_eq_one hu))
    (linearIndependent_unique_iff.2 (by simpa using ne_zero_of_map_eq_one hw))
    (fun i => by fin_cases i; simp only [Matrix.cons_val_fin_one]; rw [hu, hw])
    (fun i j => by
      fin_cases i; fin_cases j
      simp only [Matrix.cons_val_fin_one, polar_self_zmod_two])
  rw [isConj_iff]
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [conj_reflO]
  have := hgu 0
  simp only [Matrix.cons_val_zero] at this
  change reflO Q (g u) = _
  rw [this]

theorem pair_reflClass [FiniteDimensional (ZMod 2) V]
    (hnd : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V) :
    Pair (TauCeti.QuadraticMap.orthogonalGroup Q) (reflClass Q) := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨v₀, hv₀, -⟩ := exists_map_eq_one_polar_eq_one hnd (by omega)
    (Submodule.exists_mem_ne_zero_of_ne_bot (p := (⊤ : Submodule (ZMod 2) V)) (by
      intro h
      have := Submodule.finrank_eq_zero.mpr h
      rw [finrank_top] at this
      omega) |>.choose_spec.2)
  refine ⟨inferInstance, ⟨reflO Q v₀, ?_⟩, ?_, ?_, ?_⟩
  · ext g
    constructor
    · rintro ⟨v, hv, hg⟩
      have : g = reflO Q v := Subtype.ext hg
      rw [this]
      exact isConj_reflO hnd hv₀ hv
    · intro hg
      obtain ⟨c, hc⟩ := isConj_iff.mp hg
      rw [← hc, conj_reflO]
      refine reflO_mem_reflClass ?_
      rw [map_of_mem c.2, hv₀]
  · rintro e ⟨v, hv, he⟩
    have he' : e = reflO Q v := Subtype.ext he
    rw [he']
    apply orderOf_eq_prime
    · exact Subtype.ext (by
        change reflect Q v * reflect Q v = 1
        exact reflect_mul_self Q v)
    · intro h
      exact reflect_ne_one hnd hv (congrArg Subtype.val h)
  · rintro e ⟨u, hu, he⟩ f ⟨w, hw, hf⟩
    have he' : e = reflO Q u := Subtype.ext he
    have hf' : f = reflO Q w := Subtype.ext hf
    rw [he', hf']
    rcases zmod_two_eq_zero_or_eq_one (polar Q u w) with h0 | h1
    · have hc : reflO Q u * reflO Q w = reflO Q w * reflO Q u :=
        Subtype.ext ((reflect_mul_comm_iff hu hw).mpr h0)
      have h2 : (reflO Q u * reflO Q w) ^ 2 = 1 := by
        rw [pow_two, mul_assoc, ← mul_assoc (reflO Q w), ← hc, mul_assoc, ← mul_assoc]
        have hu2 : reflO Q u * reflO Q u = 1 := Subtype.ext (reflect_mul_self Q u)
        have hw2 : reflO Q w * reflO Q w = 1 := Subtype.ext (reflect_mul_self Q w)
        rw [hu2, one_mul, hw2]
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
      · rw [h]; simp
      · rw [h]; simp
    · have hw1 : polar Q w u = 1 := by rw [polar_comm]; exact h1
      have hbr1 : reflO Q u * reflO Q w * reflO Q u = reflO Q (u + w) :=
        Subtype.ext (reflect_mul_reflect_mul_reflect hu h1)
      have hbr2 : reflO Q w * reflO Q u * reflO Q w = reflO Q (w + u) :=
        Subtype.ext (reflect_mul_reflect_mul_reflect hw hw1)
      have h3 : (reflO Q u * reflO Q w) ^ 3 = 1 := by
        have : (reflO Q u * reflO Q w) ^ 3 =
            (reflO Q u * reflO Q w * reflO Q u) * (reflO Q w * reflO Q u * reflO Q w) := by
          rw [pow_succ, pow_succ, pow_one]
          simp only [mul_assoc]
        rw [this, hbr1, hbr2, add_comm]
        exact Subtype.ext (reflect_mul_self Q (w + u))
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
      · rw [h]; simp
      · rw [h]; simp
  ·
    have hgen := orthogonalGroup_eq_closure_reflect hnd (by omega) (Or.inl h5)
    rw [eq_top_iff]
    rintro ⟨g, hg⟩ -
    rw [hgen] at hg
    have hmap : (Subgroup.closure (reflClass Q)).map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype =
        Subgroup.closure (Set.range (reflect Q)) := by
      rw [MonoidHom.map_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro _ ⟨e, ⟨v, hv, he⟩, rfl⟩
        exact Subgroup.subset_closure ⟨v, he.symm⟩
      · rw [Subgroup.closure_le]
        rintro _ ⟨v, rfl⟩
        by_cases hv : Q v = 1
        · exact Subgroup.subset_closure ⟨reflO Q v, ⟨v, hv, rfl⟩, rfl⟩
        · have hv0 : Q v = 0 := (zmod_two_eq_zero_or_eq_one _).resolve_right hv
          rw [SetLike.mem_coe, reflect_of_map_eq_zero hv0]
          exact Subgroup.one_mem _
    rw [← hmap] at hg
    obtain ⟨x, hx, hxg⟩ := hg
    have : x = ⟨g, by rw [hgen, ← hmap]; exact ⟨x, hx, hxg⟩⟩ := Subtype.ext hxg
    rw [← this]
    exact hx

end CFSG.Fischer.Classification.Orth2
