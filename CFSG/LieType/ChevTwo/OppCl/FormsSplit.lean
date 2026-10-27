module

public import CFSG.LieType.ChevTwo.OppCl.Defs
public import CFSG.LieType.BorelTits.Families
import CFSG.LieType.ChevTwo.OppCl.Toolkit
import CFSG.LieType.ChevTwo.OppCl.FormsSplitSplit3
import CFSG.LieType.ChevTwo.OppCl.FormsSplitAvg
import CFSG.LieType.ChevTwo.OppCl.FormsSplitDiag

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.LieType.BorelTits

section Graph

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

variable {p : ℕ} [Fact p.Prime]

theorem exists_isotropic_graph (Φ : ReflForm F V) (hσ : ∀ c, Φ.σ (Φ.σ c) = c)
    (hsymm : ∀ u v, Φ.β v u = Φ.σ (Φ.β u v)) (hdiag : ∀ v, ∃ t, t + Φ.σ t = Φ.β v v)
    (W Cc : Submodule F V) (hW : Φ.IsTotallyIsotropic W) (hC : IsCompl (Φ.perp W) Cc) :
    ∃ s : V →ₗ[F] V, (∀ v, s v ∈ W) ∧ (∀ v ∈ Φ.perp W, s v = 0) ∧
      ∀ c ∈ Cc, ∀ c' ∈ Cc, Φ.β (c + s c) (c' + s c') = 0 := by
  classical
  haveI : Module.Finite F Cc := Module.Finite.of_finite
  let b := Module.finBasis F Cc
  choose t ht using fun i => hdiag (b i : V)
  obtain ⟨s, hsW, hs0, -, hti⟩ := FS.exists_graph_diag Φ hσ hsymm W Cc hW hC b t ht
  exact ⟨s, hsW, hs0, FS.β_graph_of_basis Φ b s hti⟩

theorem exists_equivariant_isotropic_graph (Φ : ReflForm F V) (hσ : ∀ c, Φ.σ (Φ.σ c) = c)
    (hsymm : ∀ u v, Φ.β v u = Φ.σ (Φ.β u v)) (hdiag : ∀ v, ∃ t, t + Φ.σ t = Φ.β v v)
    (hp2 : p ≠ 2) (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V)
    (hiso : ∀ r ∈ Rh, SemiIso Φ r) (hR : IsPGroup p Rh) (W Cc : Submodule F V)
    (hW : Φ.IsTotallyIsotropic W) (hC : IsCompl (Φ.perp W) Cc)
    (hWinv : ∀ r ∈ Rh, ∀ v ∈ W, r v ∈ W) (hCinv : ∀ r ∈ Rh, ∀ v ∈ Cc, r v ∈ Cc) :
    ∃ s : V →ₗ[F] V, (∀ r ∈ Rh, ∀ v, r (s v) = s (r v)) ∧ (∀ v, s v ∈ W) ∧
      (∀ v ∈ Φ.perp W, s v = 0) ∧ ∀ c ∈ Cc, ∀ c' ∈ Cc, Φ.β (c + s c) (c' + s c') = 0 := by
  classical
  obtain ⟨s, hsW, hs0, hti⟩ := exists_isotropic_graph Φ hσ hsymm hdiag W Cc hW hC
  obtain ⟨T, s', hT, hs', hcard, hcomm⟩ := FS.exists_avg p hp2 Rh hs hR s
  have hperp := FS.perp_inv Φ Rh hiso W hWinv
  have hrr : ∀ (r : Equiv.Perm V) (x : V), r (r⁻¹ x) = x := fun r x => r.apply_symm_apply x
  have hsW' : ∀ v, s' v ∈ W := fun v => by
    rw [hs']
    exact Submodule.sum_mem _ fun r hr => hWinv r ((hT r).1 hr) _ (hsW _)
  have key : ∀ c ∈ Cc, ∀ c' ∈ Cc, Φ.β c c' + Φ.β c (s c') + Φ.β (s c) c' = 0 := by
    intro c hc c' hc'
    have h1 := hti c hc c' hc'
    have h2 : Φ.β (s c) (s c') = 0 := hW (hsW c') (s c) (hsW c)
    rw [Φ.add_left, Φ.add_right, Φ.add_right, h2] at h1
    linear_combination h1
  refine ⟨s', hcomm, hsW', ?_, ?_⟩
  · intro v hv
    rw [hs']
    refine Finset.sum_eq_zero fun r hr => ?_
    have hr' := (hT r).1 hr
    rw [hs0 _ (hperp r⁻¹ (inv_mem hr') v hv)]
    exact FS.semilin_zero (hs hr')
  · intro c hc c' hc'
    have hss : Φ.β (s' c) (s' c') = 0 := hW (hsW' c') (s' c) (hsW' c)
    have hexp : Φ.β (c + s' c) (c' + s' c') = Φ.β c c' + Φ.β c (s' c') + Φ.β (s' c) c' := by
      rw [Φ.add_left, Φ.add_right, Φ.add_right, hss]
      ring
    have hterm : ∀ r ∈ T, Φ.β c c' + Φ.β c (r (s (r⁻¹ c'))) + Φ.β (r (s (r⁻¹ c))) c' = 0 := by
      intro r hr
      have hr' := (hT r).1 hr
      obtain ⟨τ, hτ⟩ := hiso r hr'
      have h1 := key _ (hCinv r⁻¹ (inv_mem hr') c hc) _ (hCinv r⁻¹ (inv_mem hr') c' hc')
      have e1 : Φ.β c c' = τ (Φ.β (r⁻¹ c) (r⁻¹ c')) := by
        rw [← hτ, hrr, hrr]
      have e2 : Φ.β c (r (s (r⁻¹ c'))) = τ (Φ.β (r⁻¹ c) (s (r⁻¹ c'))) := by
        rw [← hτ, hrr]
      have e3 : Φ.β (r (s (r⁻¹ c))) c' = τ (Φ.β (s (r⁻¹ c)) (r⁻¹ c')) := by
        rw [← hτ, hrr]
      rw [e1, e2, e3, ← map_add, ← map_add, h1, map_zero]
    have hc1 : Φ.β c c' = ∑ r ∈ T, Φ.β c c' := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, one_mul]
    rw [hexp, hs', hs', FS.β_sum_right, FS.β_sum_left]
    nth_rewrite 1 [hc1]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero hterm

theorem exists_singular_graph (Φ : QuadForm F V) (W Cc : Submodule F V)
    (hW : Φ.IsTotallySingular W) (hC : IsCompl (Φ.polar.perp W) Cc) :
    ∃ s : V →ₗ[F] V, (∀ v, s v ∈ W) ∧ (∀ v ∈ Φ.polar.perp W, s v = 0) ∧
      ∀ c ∈ Cc, Φ.Q (c + s c) = 0 := by
  classical
  haveI : Module.Finite F Cc := Module.Finite.of_finite
  let b := Module.finBasis F Cc
  have hσ : ∀ c, Φ.polar.σ (Φ.polar.σ c) = c := fun c => by
    rw [Φ.polar_σ]; rfl
  have hsymm : ∀ u v, Φ.polar.β v u = Φ.polar.σ (Φ.polar.β u v) := fun u v => by
    rw [Φ.polar_σ]; exact Φ.polar_symm v u
  have ht : ∀ i, Φ.Q (b i : V) + Φ.polar.σ (Φ.Q (b i : V)) = Φ.polar.β (b i : V) (b i : V) := by
    intro i
    rw [Φ.polar_σ, Φ.polar_self]
    show Φ.Q (b i : V) + Φ.Q (b i : V) = 2 * Φ.Q (b i : V)
    ring
  obtain ⟨s, hsW, hs0, hsd, hti⟩ := FS.exists_graph_diag Φ.polar hσ hsymm W Cc
    hW.isTotallyIsotropic hC b (fun i => Φ.Q (b i : V)) ht
  refine ⟨s, hsW, hs0, FS.Q_graph_of_basis Φ b s (fun i => ?_) hti⟩
  rw [Φ.Q_add, hW _ (hsW _), hsd i, add_zero]
  exact CharTwo.add_self_eq_zero _

theorem exists_equivariant_singular_graph (Φ : QuadForm F V) (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V)
    (hiso : ∀ r ∈ Rh, SemiIsoQ Φ r) (hR : IsPGroup p Rh) (W Cc : Submodule F V)
    (hW : Φ.IsTotallySingular W) (hC : IsCompl (Φ.polar.perp W) Cc)
    (hWinv : ∀ r ∈ Rh, ∀ v ∈ W, r v ∈ W) (hCinv : ∀ r ∈ Rh, ∀ v ∈ Cc, r v ∈ Cc) :
    ∃ s : V →ₗ[F] V, (∀ r ∈ Rh, ∀ v, r (s v) = s (r v)) ∧ (∀ v, s v ∈ W) ∧
      (∀ v ∈ Φ.polar.perp W, s v = 0) ∧ ∀ c ∈ Cc, Φ.Q (c + s c) = 0 := by
  classical
  obtain ⟨s, hsW, hs0, hQ⟩ := exists_singular_graph Φ W Cc hW hC
  obtain ⟨T, s', hT, hs', hcard, hcomm⟩ := FS.exists_avg p hp2 Rh hs hR s
  have hperp := FS.perp_inv Φ.polar Rh
    (fun r hr => FS.semiIso_polar Φ (hs hr) (hiso r hr)) W hWinv
  have hrr : ∀ (r : Equiv.Perm V) (x : V), r (r⁻¹ x) = x := fun r x => r.apply_symm_apply x
  have hsW' : ∀ v, s' v ∈ W := fun v => by
    rw [hs']
    exact Submodule.sum_mem _ fun r hr => hWinv r ((hT r).1 hr) _ (hsW _)
  refine ⟨s', hcomm, hsW', ?_, ?_⟩
  · intro v hv
    rw [hs']
    refine Finset.sum_eq_zero fun r hr => ?_
    have hr' := (hT r).1 hr
    rw [hs0 _ (hperp r⁻¹ (inv_mem hr') v hv)]
    exact FS.semilin_zero (hs hr')
  · intro c hc
    have hterm : ∀ r ∈ T, Φ.Q c + Φ.polar.β c (r (s (r⁻¹ c))) = 0 := by
      intro r hr
      have hr' := (hT r).1 hr
      obtain ⟨τ, hτ⟩ := hiso r hr'
      have hw : r (s (r⁻¹ c)) ∈ W := hWinv r hr' _ (hsW _)
      have h1 : c + r (s (r⁻¹ c)) = r (r⁻¹ c + s (r⁻¹ c)) := by
        rw [(hs hr').1, hrr]
      have h2 : Φ.Q (c + r (s (r⁻¹ c))) = 0 := by
        rw [h1, hτ, hQ _ (hCinv r⁻¹ (inv_mem hr') c hc), map_zero]
      rw [Φ.Q_add, hW _ hw, add_zero] at h2
      exact h2
    have hc1 : Φ.Q c = ∑ r ∈ T, Φ.Q c := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, one_mul]
    rw [Φ.Q_add, hW _ (hsW' c), add_zero, hs', FS.β_sum_right]
    nth_rewrite 1 [hc1]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero hterm

end Graph

section Forms

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

variable (Φ : ReflForm F V) (Sing : V → Prop) (ρ : H →* Module.End F V)
  (p : ℕ) [Fact p.Prime] (Rh : Subgroup (Equiv.Perm V))

theorem split_refl (hσ : ∀ c, Φ.σ (Φ.σ c) = c) (hsymm : ∀ u v, Φ.β v u = Φ.σ (Φ.β u v))
    (hdiag : ∀ v, ∃ t, t + Φ.σ t = Φ.β v v) (hp2 : p ≠ 2) (hs : Rh ≤ semilinGroup F V)
    (hiso : ∀ r ∈ Rh, SemiIso Φ r) (hR : IsPGroup p Rh) (W : Submodule F V)
    (hW : Φ.IsTotallyIsotropic W) (hWinv : ∀ r ∈ Rh, ∀ v ∈ W, r v ∈ W) :
    ∃ M W' : Submodule F V, Split3 Φ Φ.IsTotallyIsotropic W M W' ∧
      (∀ r ∈ Rh, ∀ v ∈ M, r v ∈ M) ∧ (∀ r ∈ Rh, ∀ v ∈ W', r v ∈ W') := by
  have hperp := FS.perp_inv Φ Rh hiso W hWinv
  obtain ⟨Cc, hC, hCinv⟩ := exists_invariant_compl p hp2 Rh hs hR (Φ.perp W) hperp
  obtain ⟨s, hsc, hsW, hs0, hti⟩ := exists_equivariant_isotropic_graph Φ hσ hsymm hdiag hp2 Rh
    hs hiso hR W Cc hW hC hWinv hCinv
  let W' : Submodule F V := Submodule.map (LinearMap.id + s) Cc
  have hW' : ∀ v, v ∈ W' ↔ ∃ c ∈ Cc, c + s c = v := fun v => by
    simp [W', Submodule.mem_map]
  have hW'inv : ∀ r ∈ Rh, ∀ v ∈ W', r v ∈ W' := by
    intro r hr v hv
    obtain ⟨c, hc, rfl⟩ := (hW' v).1 hv
    refine (hW' _).2 ⟨r c, hCinv r hr c hc, ?_⟩
    rw [(hs hr).1, hsc r hr c]
  refine ⟨Φ.perp W ⊓ Φ.perp W', W', FS.split3_of_graph Φ Φ.IsTotallyIsotropic W Cc W' _ hW hC
    hsymm s hsW hs0 hW' hti rfl hW ?_, ?_, hW'inv⟩
  · intro v hv w hw
    obtain ⟨c, hc, rfl⟩ := (hW' v).1 hv
    obtain ⟨c', hc', rfl⟩ := (hW' w).1 hw
    exact hti c' hc' c hc
  · intro r hr v hv
    exact ⟨hperp r hr v hv.1, FS.perp_inv Φ Rh hiso W' hW'inv r hr v hv.2⟩

theorem split_quad (Φ : QuadForm F V) (hp2 : p ≠ 2) (hs : Rh ≤ semilinGroup F V)
    (hiso : ∀ r ∈ Rh, SemiIsoQ Φ r) (hR : IsPGroup p Rh) (W : Submodule F V)
    (hW : Φ.IsTotallySingular W) (hWinv : ∀ r ∈ Rh, ∀ v ∈ W, r v ∈ W) :
    ∃ M W' : Submodule F V, Split3 Φ.polar Φ.IsTotallySingular W M W' ∧
      (∀ r ∈ Rh, ∀ v ∈ M, r v ∈ M) ∧ (∀ r ∈ Rh, ∀ v ∈ W', r v ∈ W') := by
  have hisoP : ∀ r ∈ Rh, SemiIso Φ.polar r := fun r hr => FS.semiIso_polar Φ (hs hr) (hiso r hr)
  have hsymm : ∀ u v, Φ.polar.β v u = Φ.polar.σ (Φ.polar.β u v) := fun u v => by
    rw [Φ.polar_σ]; exact Φ.polar_symm v u
  have hperp := FS.perp_inv Φ.polar Rh hisoP W hWinv
  obtain ⟨Cc, hC, hCinv⟩ := exists_invariant_compl p hp2 Rh hs hR (Φ.polar.perp W) hperp
  obtain ⟨s, hsc, hsW, hs0, hQ⟩ := exists_equivariant_singular_graph Φ hp2 Rh hs hiso hR W Cc hW
    hC hWinv hCinv
  let W' : Submodule F V := Submodule.map (LinearMap.id + s) Cc
  have hW' : ∀ v, v ∈ W' ↔ ∃ c ∈ Cc, c + s c = v := fun v => by
    simp [W', Submodule.mem_map]
  have hW'inv : ∀ r ∈ Rh, ∀ v ∈ W', r v ∈ W' := by
    intro r hr v hv
    obtain ⟨c, hc, rfl⟩ := (hW' v).1 hv
    refine (hW' _).2 ⟨r c, hCinv r hr c hc, ?_⟩
    rw [(hs hr).1, hsc r hr c]
  have hW'ts : Φ.IsTotallySingular W' := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := (hW' v).1 hv
    exact hQ c hc
  have hti : ∀ c ∈ Cc, ∀ c' ∈ Cc, Φ.polar.β (c + s c) (c' + s c') = 0 := by
    intro c hc c' hc'
    exact hW'ts.isTotallyIsotropic ((hW' _).2 ⟨c', hc', rfl⟩) _ ((hW' _).2 ⟨c, hc, rfl⟩)
  refine ⟨Φ.polar.perp W ⊓ Φ.polar.perp W', W', FS.split3_of_graph Φ.polar Φ.IsTotallySingular W
    Cc W' _ hW.isTotallyIsotropic hC hsymm s hsW hs0 hW' hti rfl hW hW'ts, ?_, hW'inv⟩
  intro r hr v hv
  exact ⟨hperp r hr v hv.1, FS.perp_inv Φ.polar Rh hisoP W' hW'inv r hr v hv.2⟩

end Forms

end CFSG.LieType.ChevTwo.OppCl
