module

public import CFSG.LieType.ChevTwo.OppCl.FormsSplitPair
public import CFSG.LieType.ChevTwo.OppCl.FormsSplitBasic

public section

namespace CFSG.LieType.ChevTwo.OppCl.FS

open CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V] [Finite V]

private theorem β_lin_comb_eq_zero (Φ : ReflForm F V) {ι : Type} [Fintype ι] (u : ι → V)
    (h : ∀ i j, Φ.β (u i) (u j) = 0) (a a' : ι → F) :
    Φ.β (∑ i, a i • u i) (∑ j, a' j • u j) = 0 := by
  simp [β_sum_left, β_sum_right, Φ.smul_left, Φ.smul_right, h]

private theorem Q_lin_comb_eq_zero (Φ : QuadForm F V) {ι : Type} [Fintype ι] (u : ι → V)
    (hQ : ∀ i, Φ.Q (u i) = 0) (hβ : ∀ i j, Φ.polar.β (u i) (u j) = 0) (a : ι → F) :
    Φ.Q (∑ i, a i • u i) = 0 := by
  classical
  have key : ∀ t : Finset ι, Φ.Q (∑ i ∈ t, a i • u i) = 0 := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · rw [Finset.sum_empty, Φ.Q_zero]
    · intro j t hj ih
      have hcross : Φ.polar.β (a j • u j) (∑ i ∈ t, a i • u i) = 0 := by
        simp [β_sum_right, Φ.polar.smul_left, Φ.polar.smul_right, hβ]
      rw [Finset.sum_insert hj, Φ.Q_add, Φ.Q_smul, hQ j, ih, hcross]
      simp
  exact key Finset.univ

private theorem graph_eq_sum {ι : Type} [Fintype ι] {Cc : Submodule F V}
    (b : Module.Basis ι F Cc) (s : V →ₗ[F] V) {x : V} (hx : x ∈ Cc) :
    x + s x = ∑ i, (b.repr ⟨x, hx⟩ i) • ((b i : V) + s (b i : V)) := by
  have key : ∀ a : ι → F, (∑ i, a i • (b i : V)) + s (∑ i, a i • (b i : V)) =
      ∑ i, a i • ((b i : V) + s (b i : V)) := by
    intro a
    simp only [map_sum, map_smul, smul_add, Finset.sum_add_distrib]
  have hx' : ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : V) = x := by
    have h := congrArg (Submodule.subtype Cc) (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at h
    simpa only [map_smul, Submodule.subtype_apply] using h
  have h := key (fun i => b.repr ⟨x, hx⟩ i)
  rw [hx'] at h
  exact h

theorem exists_graph_halfform (Φ : ReflForm F V) (hσ : ∀ c, Φ.σ (Φ.σ c) = c)
    (hsymm : ∀ u v, Φ.β v u = Φ.σ (Φ.β u v)) (W Cc : Submodule F V)
    (hC : IsCompl (Φ.perp W) Cc) {ι : Type} [Fintype ι] (b : Module.Basis ι F Cc)
    (h : ι → ι → F) :
    ∃ s : V →ₗ[F] V, (∀ v, s v ∈ W) ∧ (∀ v ∈ Φ.perp W, s v = 0) ∧
      ∀ i j, Φ.β (b i : V) (s (b j : V)) = h i j := by
  have hφ : ∀ j, ∃ w ∈ W, ∀ c : Cc, Φ.β w (c : V) = b.constr F (fun i => Φ.σ (h i j)) c :=
    fun j => exists_β_eq Φ W Cc hC (b.constr F (fun i => Φ.σ (h i j)))
  choose w hwW hw using hφ
  refine ⟨(b.constr F w).comp (Submodule.projectionOnto Cc (Φ.perp W) hC.symm), ?_, ?_, ?_⟩
  · intro v
    rw [LinearMap.comp_apply, Module.Basis.constr_apply_fintype]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hwW i)
  · intro v hv
    rw [LinearMap.comp_apply, (Submodule.projectionOnto_apply_eq_zero_iff hC.symm).mpr hv, map_zero]
  · intro i j
    rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_left hC.symm (b j),
      Module.Basis.constr_basis, hsymm (w j) (b i), hw j (b i), Module.Basis.constr_basis, hσ]

theorem β_graph_of_basis (Φ : ReflForm F V) {Cc : Submodule F V} {ι : Type} [Fintype ι]
    (b : Module.Basis ι F Cc) (s : V →ₗ[F] V)
    (h : ∀ i j, Φ.β ((b i : V) + s (b i : V)) ((b j : V) + s (b j : V)) = 0) :
    ∀ c ∈ Cc, ∀ c' ∈ Cc, Φ.β (c + s c) (c' + s c') = 0 := by
  intro c hc c' hc'
  rw [graph_eq_sum b s hc, graph_eq_sum b s hc']
  exact β_lin_comb_eq_zero Φ (fun i => (b i : V) + s (b i : V)) h
    (fun i => b.repr ⟨c, hc⟩ i) (fun i => b.repr ⟨c', hc'⟩ i)

theorem Q_graph_of_basis (Φ : QuadForm F V) {Cc : Submodule F V} {ι : Type} [Fintype ι]
    (b : Module.Basis ι F Cc) (s : V →ₗ[F] V)
    (hQ : ∀ i, Φ.Q ((b i : V) + s (b i : V)) = 0)
    (hβ : ∀ i j, Φ.polar.β ((b i : V) + s (b i : V)) ((b j : V) + s (b j : V)) = 0) :
    ∀ c ∈ Cc, Φ.Q (c + s c) = 0 := by
  intro c hc
  rw [graph_eq_sum b s hc]
  exact Q_lin_comb_eq_zero Φ (fun i => (b i : V) + s (b i : V)) hQ hβ
    (fun i => b.repr ⟨c, hc⟩ i)

end CFSG.LieType.ChevTwo.OppCl.FS
