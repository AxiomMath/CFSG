module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryRealization

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module Subgroup ProjectiveGeometry

variable {K : Type*} [Field K] {n : ℕ}

theorem mem_scalars_of_forall_point {g : SpecialLinearGroup (Fin n) K}
    (h : ∀ L : Submodule K (Fin n → K), finrank K L = 1 →
      L.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = L) :
    g ∈ scalars n K := by
  classical
  rw [scalars_eq_center, Matrix.SpecialLinearGroup.mem_center_iff]
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := mulVecLin (g : Matrix (Fin n) (Fin n) K)) fun v hli => by
    by_cases hv : v = 0
    · exact hli.ne_zero 0 (by simp [hv])
    · have hmem : mulVecLin (g : Matrix (Fin n) (Fin n) K) v ∈ K ∙ v := by
        rw [← h (K ∙ v) (finrank_span_singleton hv)]
        exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self v)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have := LinearIndependent.pair_iff.mp hli c (-1) (by rw [← hc]; simp)
      exact one_ne_zero (neg_eq_zero.mp this.2)
  have hscalar : (g : Matrix (Fin n) (Fin n) K) = scalar (Fin n) a := by
    ext i j
    have := congrArg (fun φ : (Fin n → K) →ₗ[K] (Fin n → K) => φ (Pi.single j 1) i) ha
    simp only [mulVecLin_apply, mulVec_single_one, LinearMap.smul_apply, Module.End.one_apply,
      Pi.smul_apply, smul_eq_mul] at this
    have h2 : (g : Matrix (Fin n) (Fin n) K) i j = a * (Pi.single j (1 : K) : Fin n → K) i :=
      this
    rw [h2, scalar_apply, diagonal_apply, Pi.single_apply]
    split_ifs <;> simp
  refine ⟨a, ?_, hscalar.symm⟩
  have hdet : (g : Matrix (Fin n) (Fin n) K).det = 1 := g.2
  rwa [hscalar, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ] at hdet

theorem map_map_conj {G : Type*} [Group G] (γ : MulAut G) (x : G) (M : Subgroup G) :
    (M.map (MulAut.conj x : G →* G)).map (γ : G →* G) =
      (M.map (γ : G →* G)).map (MulAut.conj (γ x) : G →* G) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply]

theorem eq_of_map_projStabilizer [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hn : 2 ≤ n)
    (α β : MulAut (projectiveSL n K)) (f : Point n K → Point n K) (hf : Function.Surjective f)
    (hα : ∀ L : Point n K, (projStabilizer L.1).map (α : projectiveSL n K →* projectiveSL n K) =
      projStabilizer (f L).1)
    (hβ : ∀ L : Point n K, (projStabilizer L.1).map (β : projectiveSL n K →* projectiveSL n K) =
      projStabilizer (f L).1) : α = β := by
  classical
  obtain ⟨-, hinj, -⟩ := maximal_parabolics (K := K) p (by omega : 1 ≤ n)
  have hpt : ∀ L : Submodule K (Fin n → K), finrank K L = 1 → ⊥ < L ∧ L < ⊤ := fun L hL =>
    bot_lt_and_lt_top_of_finrank (by omega) (by omega)
  have hgL : ∀ (g : SpecialLinearGroup (Fin n) K) (L : Point n K),
      finrank K (L.1.map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) = 1 := fun g L =>
    (LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) L.1).trans L.2
  have key : ∀ γ : MulAut (projectiveSL n K),
      (∀ L : Point n K, (projStabilizer L.1).map (γ : projectiveSL n K →* projectiveSL n K) =
        projStabilizer (f L).1) →
      ∀ (g s : SpecialLinearGroup (Fin n) K), γ (proj n K g) = proj n K s → ∀ L : Point n K,
        (f ⟨_, hgL g L⟩).1 = (f L).1.map (mulVecLin (s : Matrix (Fin n) (Fin n) K)) := by
    intro γ hγ g s hs L
    apply hinj ⟨(hpt _ (f _).2).1, (hpt _ (f _).2).2⟩
      ⟨(hpt _ (hgL s (f L))).1, (hpt _ (hgL s (f L))).2⟩
    rw [← hγ, ← projStabilizer_map_conj, ← projStabilizer_map_conj, map_map_conj, hγ, hs]
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  obtain ⟨s, hs⟩ := proj_surjective n K (α (proj n K g))
  obtain ⟨t, ht⟩ := proj_surjective n K (β (proj n K g))
  have hst : ∀ L : Point n K, L.1.map (mulVecLin (s : Matrix (Fin n) (Fin n) K)) =
      L.1.map (mulVecLin (t : Matrix (Fin n) (Fin n) K)) := by
    intro L
    obtain ⟨L₀, rfl⟩ := hf L
    rw [← key α hα g s hs.symm L₀, key β hβ g t ht.symm L₀]
  have hts : t⁻¹ * s ∈ scalars n K := by
    refine mem_scalars_of_forall_point fun L hL => ?_
    have hmat : ((t⁻¹ * s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((t⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (s : Matrix (Fin n) (Fin n) K) := rfl
    have htt : ((t⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (t : Matrix (Fin n) (Fin n) K) = 1 := congrArg Subtype.val (inv_mul_cancel t)
    rw [hmat, mulVecLin_mul, Submodule.map_comp, hst ⟨L, hL⟩, ← Submodule.map_comp,
      ← mulVecLin_mul, htt, mulVecLin_one, Submodule.map_id]
  rw [← hs, ← ht]
  exact (proj_eq_proj_iff.mpr hts).symm

theorem type_preserving_automorphisms [Finite K] (hn : 3 ≤ n) (α : MulAut (projectiveSL n K))
    (hα : ∀ L : Submodule K (Fin n → K), finrank K L = 1 →
      ∃ L' : Submodule K (Fin n → K), finrank K L' = 1 ∧
        (projStabilizer L).map (α : projectiveSL n K →* projectiveSL n K) = projStabilizer L') :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), α = conjAut n K A * fieldAut n K σ := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, hbip, -, -, -, hLH, haut⟩ := incidence_graph (K := K) p hn
  obtain ⟨hE, hdisjE, -, -, -⟩ := intrinsic_extremal_parabolics (K := K) p hn
  obtain ⟨-, hinj, -⟩ := maximal_parabolics (K := K) p (by omega : 1 ≤ n)
  have hpt : ∀ W : Submodule K (Fin n → K), finrank K W = 1 → ⊥ < W ∧ W < ⊤ := fun W hW =>
    bot_lt_and_lt_top_of_finrank (by omega) (by omega)
  have hhyp : ∀ W : Submodule K (Fin n → K), finrank K W = n - 1 → ⊥ < W ∧ W < ⊤ := fun W hW =>
    bot_lt_and_lt_top_of_finrank (by omega) (by omega)
  have hmemL : ∀ L : Submodule K (Fin n → K), finrank K L = 1 →
      projStabilizer L ∈ extremalParabolics (projectiveSL n K) p := fun L hL => by
    rw [hE]
    exact Or.inl ⟨L, hL, rfl⟩
  have hmemH : ∀ H : Submodule K (Fin n → K), finrank K H = n - 1 →
      projStabilizer H ∈ extremalParabolics (projectiveSL n K) p := fun H hH => by
    rw [hE]
    exact Or.inr ⟨H, hH, rfl⟩
  obtain ⟨Φ, hΦ, hpres⟩ := haut α
  have hF1 : finrank K (flagSpace n K 1) = 1 := finrank_flagSpace (by omega)
  have hnoswap : ¬((∀ M, M ∈ pointVertices n K p → Φ M ∈ hyperplaneVertices n K p) ∧
      ∀ M, M ∈ hyperplaneVertices n K p → Φ M ∈ pointVertices n K p) := by
    rintro ⟨h1, -⟩
    obtain ⟨H, hH, hMH⟩ := h1 ⟨_, hmemL _ hF1⟩ ⟨_, hF1, rfl⟩
    obtain ⟨L', hL', hL'eq⟩ := hα _ hF1
    rw [hΦ] at hMH
    exact Set.disjoint_left.mp hdisjE ⟨L', hL', rfl⟩ ⟨H, hH, hMH.symm.trans hL'eq⟩
  obtain ⟨hpp, hhh⟩ := hpres.resolve_right hnoswap
  have hfex : ∀ L : Point n K, ∃ L' : Point n K,
      (projStabilizer L.1).map (α : projectiveSL n K →* projectiveSL n K) = projStabilizer L'.1 :=
    fun L => by
      obtain ⟨L', hL', hL'eq⟩ := hpp ⟨_, hmemL _ L.2⟩ ⟨_, L.2, rfl⟩
      rw [hΦ] at hL'eq
      exact ⟨⟨L', hL'⟩, hL'eq⟩
  have hhex : ∀ H : Hyperplane n K, ∃ H' : Hyperplane n K,
      (projStabilizer H.1).map (α : projectiveSL n K →* projectiveSL n K) = projStabilizer H'.1 :=
    fun H => by
      obtain ⟨H', hH', hH'eq⟩ := hhh ⟨_, hmemH _ H.2⟩ ⟨_, H.2, rfl⟩
      rw [hΦ] at hH'eq
      exact ⟨⟨H', hH'⟩, hH'eq⟩
  choose fF hfF using hfex
  choose hF hhF using hhex
  have hαinj : ∀ M N : Subgroup (projectiveSL n K),
      M.map (α : projectiveSL n K →* projectiveSL n K) =
        N.map (α : projectiveSL n K →* projectiveSL n K) → M = N := fun M N h =>
    (MulEquiv.mapSubgroup α).injective h
  have hfinj : Function.Injective fF := fun L₁ L₂ h => Subtype.ext (hinj
    ⟨(hpt _ L₁.2).1, (hpt _ L₁.2).2⟩ ⟨(hpt _ L₂.2).1, (hpt _ L₂.2).2⟩
    (hαinj _ _ (by rw [hfF, hfF, h])))
  have hhinj : Function.Injective hF := fun H₁ H₂ h => Subtype.ext (hinj
    ⟨(hhyp _ H₁.2).1, (hhyp _ H₁.2).2⟩ ⟨(hhyp _ H₂.2).1, (hhyp _ H₂.2).2⟩
    (hαinj _ _ (by rw [hhF, hhF, h])))
  have hfbij : Function.Bijective fF := ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  have hhbij : Function.Bijective hF := ⟨hhinj, Finite.injective_iff_surjective.mp hhinj⟩
  set f := Equiv.ofBijective fF hfbij with hfdef
  set h := Equiv.ofBijective hF hhbij with hhdef
  have hfh : ∀ (L : Point n K) (H : Hyperplane n K),
      (L : Submodule K (Fin n → K)) ≤ H ↔ (f L : Submodule K (Fin n → K)) ≤ h H := by
    intro L H
    have h1 := hLH L.1 H.1 ⟨_, hmemL _ L.2⟩ ⟨_, hmemH _ H.2⟩ L.2 H.2 rfl rfl
    have h2 := hLH (fF L).1 (hF H).1 (Φ ⟨_, hmemL _ L.2⟩) (Φ ⟨_, hmemH _ H.2⟩) (fF L).2 (hF H).2
      (by rw [hΦ, hfF]) (by rw [hΦ, hhF])
    rw [← h1, ← Φ.map_rel_iff, h2]
    rfl
  obtain ⟨A, σ, hAL, -⟩ := semilinear_realization hn f h hfh
  refine ⟨A, σ, eq_of_map_projStabilizer p (by omega) α _ fF hfbij.2 hfF fun L => ?_⟩
  have htrans := standard_automorphism_transport (K := K) (n := n)
  change (projStabilizer L.1).map ((conjAut n K A : projectiveSL n K →* projectiveSL n K).comp
    (fieldAut n K σ : projectiveSL n K →* projectiveSL n K)) = _
  rw [← Subgroup.map_map, htrans.2.2.2.2.2.2.2.1, htrans.2.2.2.2.2.2.1]
  exact congrArg projStabilizer (hAL L).symm

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
