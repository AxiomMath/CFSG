module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OM

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Gauss

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small

variable {F : Type} [Field F] [Finite F] [Fact (Nat.card F = 3)] {V : Type} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] [Module (GaussField F) V]
  [IsScalarTower F (GaussField F) V] {Q : QuadraticForm F V} {a : V ≃ₗ[F] V}

theorem vec3_injective {α : Type*} {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective ![x, y, z] := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all

theorem exists_plane_of_three (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {U : Submodule F V}
    (hUp : ∀ x ∈ U, ∀ y ∈ U, polar Q x y = 0) {x₁ x₂ x₃ : V}
    (hli : LinearIndependent F ![x₁, x₂, x₃]) (h1 : x₁ ∈ U) (h2 : x₂ ∈ U) (h3 : x₃ ∈ U)
    (ha1 : a x₁ ∈ U) (ha2 : a x₂ ∈ U) (ha3 : a x₃ ∈ U) :
    ∃ S : Submodule (GaussField F) V, Module.finrank (GaussField F) S = 2 ∧
      ∀ x ∈ S, gaussQuad Q hω hg x = 0 := by
  classical
  have hβD : ∀ {m : V}, m ∈ U → a m ∈ U → ∀ w ∈ U, gaussBilin Q hω hg m w = 0 := by
    intro m hm ham w hw
    rw [gaussBilin_apply, hUp m hm w hw, hUp (a m) ham w hw]
    ext <;> simp
  have hne : x₁ ≠ 0 := by
    have := hli.ne_zero 0
    simpa using this
  set W := Submodule.span F {x₁, a x₁} with hW
  have hnot : ¬ (x₂ ∈ W ∧ x₃ ∈ W) := by
    rintro ⟨h2m, h3m⟩
    have hle : Submodule.span F (Set.range ![x₁, x₂, x₃]) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      fin_cases k
      · exact Submodule.subset_span (by simp)
      · exact h2m
      · exact h3m
    have h3' := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hli, Fintype.card_fin] at h3'
    have hW2 : Module.finrank F W ≤ 2 := by
      have h := finrank_span_finset_le_card (R := F) ({x₁, a x₁} : Finset V)
      simp only [Finset.coe_insert, Finset.coe_singleton] at h
      exact h.trans Finset.card_le_two
    omega
  obtain ⟨e', he'U, hae', he'W⟩ : ∃ e' : V, e' ∈ U ∧ a e' ∈ U ∧ e' ∉ W := by
    by_cases h : x₂ ∈ W
    · exact ⟨x₃, h3, ha3, fun h' => hnot ⟨h, h'⟩⟩
    · exact ⟨x₂, h2, ha2, h⟩
  have hli2 : LinearIndependent (GaussField F) ![x₁, e'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hne, rfl⟩
    · exfalso
      apply he'W
      have he' : e' = (-(t⁻¹ * s)) • x₁ := by
        have h := congrArg (fun z => t⁻¹ • z) hst
        simp only [smul_add, smul_smul, inv_mul_cancel₀ ht, one_smul, smul_zero] at h
        rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
        exact h
      rw [he', smul_eq hω]
      exact W.add_mem (W.smul_mem _ (Submodule.subset_span (by simp)))
        (W.smul_mem _ (Submodule.subset_span (by simp)))
  exact exists_plane_of_indep hω hg hli2 (hβD h1 ha1 _ h1) (hβD he'U hae' _ he'U)
    (hβD h1 ha1 _ he'U)

theorem exists_ts_plane (hF : Nat.card F = 3) (hQ : (polarBilin Q).Nondegenerate)
    (h8 : Module.finrank F V = 8)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {U : Submodule F V} (hU4 : Module.finrank F U = 4)
    (hU0 : ∀ x ∈ U, Q x = 0) :
    ∃ S : Submodule (GaussField F) V, Module.finrank (GaussField F) S = 2 ∧
      ∀ x ∈ S, gaussQuad Q hω hg x = 0 := by
  classical
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  let _ : Invertible (2 : F) := invertibleOfNonzero h2
  have hUp : ∀ x ∈ U, ∀ y ∈ U, polar Q x y = 0 := fun x hx y hy => by
    rw [polar, hU0 _ (U.add_mem hx hy), hU0 x hx, hU0 y hy]
    ring
  have hb : ∀ x y : V, polar Q x (a y) = polar Q y (a x) := fun x y => by
    rw [polar_a_right hω hg, polar_comm]
  let bU : LinearMap.BilinForm F U :=
    (polarBilin Q).compl₁₂ U.subtype (a.toLinearMap ∘ₗ U.subtype)
  have hbU : ∀ s t : U, bU s t = polar Q s (a t) := fun s t => rfl
  have hsymm : LinearMap.IsSymm bU := LinearMap.isSymm_def.mpr fun s t => by
    rw [RingHom.id_apply, hbU, hbU, hb]
  obtain ⟨v₀, hv₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  set v := v₀.reindex (finCongr hU4) with hv
  have hvo : ∀ i j, i ≠ j → polar Q (v i : V) (a (v j : V)) = 0 := by
    intro i j hij
    have h := hv₀ ((finCongr hU4).symm.injective.ne hij)
    rw [hv, Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    exact h
  have hmem : ∀ i, (v i : V) ∈ U := fun i => (v i).2
  have hne : ∀ i, (v i : V) ≠ 0 := fun i h => v.ne_zero i (Subtype.ext h)
  have hR : ∀ i, polar Q (v i : V) (a (v i : V)) = 0 → a (v i : V) ∈ U := by
    intro i hi
    have hz : bU (v i) = 0 := v.ext fun j => by
      rw [LinearMap.zero_apply]
      by_cases hij : i = j
      · subst hij
        exact hi
      · exact hvo i j hij
    have hsing : Q (a (v i : V)) = 0 := by rw [hg, hU0 _ (hmem i), mul_zero]
    have hperp : ∀ t ∈ U, polar Q t (a (v i : V)) = 0 := fun t ht => by
      rw [hb]
      exact LinearMap.congr_fun hz ⟨t, ht⟩
    have hts : ∀ x ∈ U ⊔ Submodule.span F {a (v i : V)}, Q x = 0 := by
      intro x hx
      obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [QuadraticMap.map_add Q, hU0 u hu, map_smul_eq_sq, hsing, polar_smul_right_eq,
        hperp u hu]
      ring
    have hle := Trip.two_mul_finrank_le hQ hts
    have heq : U = U ⊔ Submodule.span F {a (v i : V)} :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    exact heq.ge (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hβD : ∀ {m : V}, m ∈ U → a m ∈ U → ∀ w ∈ U, gaussBilin Q hω hg m w = 0 := by
    intro m hm ham w hw
    rw [gaussBilin_apply, hUp m hm w hw, hUp (a m) ham w hw]
    ext <;> simp
  have hQq := nondegenerate_gaussQuad h2 hω hg hQ
  have hwit : ∀ {m : V}, m ≠ 0 → ∃ z, gaussBilin Q hω hg m z ≠ 0 := by
    intro m hm
    by_contra hc
    push Not at hc
    apply hm
    refine hQq.1 m fun z => ?_
    rw [polarBilin_apply_apply, polar_gaussQuad, hc z, mul_zero]
  set d : Fin 4 → F := fun i => polar Q (v i : V) (a (v i : V)) with hd
  by_cases hall : ∀ i, d i ≠ 0
  ·
    obtain ⟨x₁, hx₁, hx₁s, hx₁w, u₁, u₁', hu₁, hu₁', rfl, -⟩ :=
      exists_pair hF hω hg hUp (hmem 0) (hmem 1) (hvo 0 1 (by decide)) (hall 0) (hall 1)
    obtain ⟨x₂, hx₂, hx₂s, hx₂w, u₂, u₂', hu₂, hu₂', rfl, hu₂w⟩ :=
      exists_pair hF hω hg hUp (hmem 2) (hmem 3) (hvo 2 3 (by decide)) (hall 2) (hall 3)
    have e0 := hu₂w (v 0 : V) (hvo 0 2 (by decide)) (hvo 0 3 (by decide))
    have e1 := hu₂w (v 1 : V) (hvo 1 2 (by decide)) (hvo 1 3 (by decide))
    have h12 : gaussBilin Q hω hg (u₁ + a u₁') (u₂ + a u₂') = 0 := by
      rw [← hω u₂', map_add, map_smul, hx₁w u₂ hu₂ e0.1 e1.1, hx₁w u₂' hu₂' e0.2 e1.2,
        smul_zero, add_zero]
    exact exists_plane_of_indep hω hg
      (linearIndependent_of_witness hω hg hx₁s
        (hx₂w _ (hmem 0) (hvo 2 0 (by decide)) (hvo 3 0 (by decide))) hx₂s) hx₁ hx₂ h12
  push Not at hall
  obtain ⟨m, hm⟩ := hall
  have ham := hR m hm
  by_cases hB : ∃ i j, i ≠ j ∧ d i ≠ 0 ∧ d j ≠ 0
  ·
    obtain ⟨i, j, hij, hi, hj⟩ := hB
    obtain ⟨x, hx, hxs, hxw, -⟩ :=
      exists_pair hF hω hg hUp (hmem i) (hmem j) (hvo i j hij) hi hj
    have hxd : gaussBilin Q hω hg x (v m) = 0 :=
      hxw _ (hmem m) (hUp _ (hmem i) _ ham) (hUp _ (hmem j) _ ham)
    obtain ⟨z, hz⟩ := hwit (hne m)
    exact exists_plane_of_indep hω hg
      (linearIndependent_of_witness hω hg hxs (hβD (hmem m) ham _ (hmem i)) hz) hx
      (hβD (hmem m) ham _ (hmem m)) hxd
  ·
    push Not at hB
    obtain ⟨m₁, m₂, m₃, h12, h13, h23, z1, z2, z3⟩ : ∃ m₁ m₂ m₃ : Fin 4, m₁ ≠ m₂ ∧ m₁ ≠ m₃ ∧
        m₂ ≠ m₃ ∧ d m₁ = 0 ∧ d m₂ = 0 ∧ d m₃ = 0 := by
      by_cases h0 : d 0 = 0
      · by_cases h1 : d 1 = 0
        · by_cases h2' : d 2 = 0
          · exact ⟨0, 1, 2, by decide, by decide, by decide, h0, h1, h2'⟩
          · exact ⟨0, 1, 3, by decide, by decide, by decide, h0, h1, hB 2 3 (by decide) h2'⟩
        · exact ⟨0, 2, 3, by decide, by decide, by decide, h0, hB 1 2 (by decide) h1,
            hB 1 3 (by decide) h1⟩
      · exact ⟨1, 2, 3, by decide, by decide, by decide, hB 0 1 (by decide) h0,
          hB 0 2 (by decide) h0, hB 0 3 (by decide) h0⟩
    have hinj : Function.Injective ![m₁, m₂, m₃] := vec3_injective h12 h13 h23
    have hli3 : LinearIndependent F ![(v m₁ : V), (v m₂ : V), (v m₃ : V)] := by
      have h := (v.linearIndependent.comp _ hinj).map' U.subtype (Submodule.ker_subtype U)
      have hfun : (U.subtype ∘ (v ∘ ![m₁, m₂, m₃])) =
          ![(v m₁ : V), (v m₂ : V), (v m₃ : V)] := by
        funext k
        fin_cases k <;> rfl
      rwa [hfun] at h
    exact exists_plane_of_three hω hg hUp hli3 (hmem m₁) (hmem m₂) (hmem m₃) (hR m₁ z1)
      (hR m₂ z2) (hR m₃ z3)

end CFSG.ClassicalInvolution.Q3.TL4.Gauss
