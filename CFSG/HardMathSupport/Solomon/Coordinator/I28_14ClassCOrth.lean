module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassCConj
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassNOrth
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassCBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module Submodule

section

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem i28_14_C_orth_polar {Q : QuadraticForm (ZMod 2) U}
    {g : LinearMap.GeneralLinearGroup (ZMod 2) U} (hg : g ∈ i28_14_N_OG Q) (x y : U) :
    QuadraticMap.polar Q ((g : U →ₗ[ZMod 2] U) x) ((g : U →ₗ[ZMod 2] U) y) =
      QuadraticMap.polar Q x y := by
  have h := i28_14_N_mem_OG.mp hg
  simp only [QuadraticMap.polar, ← map_add, h]

theorem i28_14_C_orth_step {Q : QuadraticForm (ZMod 2) U} {w w' : U} (hw : Q w = 1)
    (hw' : Q w' = 1) (h : QuadraticMap.polar Q w w' = 1) :
    ∃ g ∈ i28_14_N_OG Q, (g : U →ₗ[ZMod 2] U) w = w' := by
  have hs : Q (w + w') = 1 := by
    rw [i28_14_N_Q_add, hw, hw', h]
    decide
  obtain ⟨h0, hmem⟩ := i28_14_N_orth_reflection_mem Q hs
  refine ⟨_, hmem, ?_⟩
  rw [tv_apply, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_left,
    i28_14_N_polar_self, QuadraticMap.polar_comm Q w' w, h, zero_add, one_smul, ← add_assoc,
    zmod2_add_self, zero_add]

theorem i28_14_C_orth_ne_zero {Q : QuadraticForm (ZMod 2) U} {x : U} (hx : Q x = 1) : x ≠ 0 := by
  rintro rfl
  rw [QuadraticMap.map_zero] at hx
  exact zero_ne_one hx

theorem i28_14_C_orth_transitive {Q : QuadraticForm (ZMod 2) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hirr : IsTvIrred (i28_14_N_OG Q))
    {w w' : U} (hw : Q w = 1) (hw' : Q w' = 1) :
    ∃ g ∈ i28_14_N_OG Q, (g : U →ₗ[ZMod 2] U) w = w' := by
  by_contra hnot
  push Not at hnot
  let N0 : Set U := {x | Q x = 1 ∧ ∃ g ∈ i28_14_N_OG Q, (g : U →ₗ[ZMod 2] U) w = x}
  let N1 : Set U := {x | Q x = 1 ∧ x ∉ N0}
  have hw0 : w ∈ N0 := ⟨hw, 1, Subgroup.one_mem _, by simp⟩
  have hw'1 : w' ∈ N1 := ⟨hw', fun ⟨_, g, hg, hgw⟩ => hnot g hg hgw⟩
  have hN0 : ∀ g ∈ i28_14_N_OG Q, ∀ x ∈ N0, (g : U →ₗ[ZMod 2] U) x ∈ N0 := by
    rintro g hg x ⟨hx, k, hk, rfl⟩
    refine ⟨?_, g * k, (i28_14_N_OG Q).mul_mem hg hk, rfl⟩
    rw [i28_14_N_mem_OG.mp hg, i28_14_N_mem_OG.mp hk, hw]
  have hN1 : ∀ g ∈ i28_14_N_OG Q, ∀ x ∈ N1, (g : U →ₗ[ZMod 2] U) x ∈ N1 := by
    rintro g hg x ⟨hx, hxn⟩
    refine ⟨by rw [i28_14_N_mem_OG.mp hg, hx], fun hgx => hxn ?_⟩
    have := hN0 g⁻¹ ((i28_14_N_OG Q).inv_mem hg) _ hgx
    rwa [i28_14_C_inv_apply] at this
  have hinv : ∀ S : Set U, (∀ g ∈ i28_14_N_OG Q, ∀ x ∈ S, (g : U →ₗ[ZMod 2] U) x ∈ S) →
      ∀ g ∈ i28_14_N_OG Q, ∀ x ∈ span (ZMod 2) S, (g : U →ₗ[ZMod 2] U) x ∈ span (ZMod 2) S := by
    intro S hS g hg x hx
    have : span (ZMod 2) S ≤ (span (ZMod 2) S).comap (g : U →ₗ[ZMod 2] U) :=
      span_le.mpr fun y hy => subset_span (hS g hg y hy)
    exact this hx
  have htop : ∀ S : Set U, (∀ g ∈ i28_14_N_OG Q, ∀ x ∈ S, (g : U →ₗ[ZMod 2] U) x ∈ S) →
      ∀ x ∈ S, x ≠ 0 → span (ZMod 2) S = ⊤ := by
    intro S hS x hx hx0
    rcases hirr.2 _ (hinv S hS) with h | h
    · exact absurd ((mem_bot (ZMod 2)).mp (h ▸ subset_span hx)) hx0
    · exact h
  have h0top := htop N0 hN0 w hw0 (i28_14_C_orth_ne_zero hw)
  have h1top := htop N1 hN1 w' hw'1 (i28_14_C_orth_ne_zero hw')
  have hort : ∀ u ∈ N0, ∀ u' ∈ N1, QuadraticMap.polarBilin Q u u' = 0 := by
    rintro u ⟨hu, hu0⟩ u' ⟨hu', hu'n⟩
    rw [QuadraticMap.polarBilin_apply_apply]
    rcases zmod2_eq_zero_or_one (QuadraticMap.polar Q u u') with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg, hgu⟩ := i28_14_C_orth_step hu hu' h
      obtain ⟨hh, hh2⟩ := hN0 g hg u ⟨hu, hu0⟩
      exact hu'n (hgu ▸ ⟨hh, hh2⟩)
  have hall : ∀ x y : U, QuadraticMap.polarBilin Q x y = 0 := by
    intro x y
    have hy : y ∈ span (ZMod 2) N1 := h1top ▸ mem_top
    have hx : x ∈ span (ZMod 2) N0 := h0top ▸ mem_top
    have h1 : ∀ u ∈ N0, QuadraticMap.polarBilin Q u y = 0 := by
      intro u hu
      have : span (ZMod 2) N1 ≤ LinearMap.ker (QuadraticMap.polarBilin Q u) :=
        span_le.mpr fun u' hu' => LinearMap.mem_ker.mpr (hort u hu u' hu')
      exact LinearMap.mem_ker.mp (this hy)
    have : span (ZMod 2) N0 ≤ LinearMap.ker ((QuadraticMap.polarBilin Q).flip y) :=
      span_le.mpr fun u hu => LinearMap.mem_ker.mpr (h1 u hu)
    exact LinearMap.mem_ker.mp (this hx)
  exact i28_14_C_orth_ne_zero hw (hQ.1 w fun y => hall w y)

variable (E : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)) [Fintype E]

theorem i28_14_C_orth_fixed {Q : QuadraticForm (ZMod 2) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hEG : E ≤ i28_14_N_OG Q)
    (hodd : Odd (Fintype.card E)) {c : U} (hc : c ∈ fixSub E) (hc0 : c ≠ 0) :
    ∃ v ∈ fixSub E, Q v = 1 := by
  by_contra hno
  push Not at hno
  have hQ0 : ∀ v ∈ fixSub E, Q v = 0 := fun v hv => by
    rcases zmod2_eq_zero_or_one (Q v) with h | h
    · exact h
    · exact absurd h (hno v hv)
  have hpol : ∀ y ∈ fixSub E, QuadraticMap.polar Q c y = 0 := fun y hy => by
    rw [QuadraticMap.polar, hQ0 _ (add_mem hc hy), hQ0 _ hc, hQ0 _ hy]
    decide
  obtain ⟨x, hx⟩ : ∃ x, QuadraticMap.polar Q c x ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (hQ.1 c fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h y)
  have hx1 : QuadraticMap.polar Q c x = 1 := (zmod2_eq_zero_or_one _).resolve_left hx
  have h1 := hpol _ (avgOp_mem_fixSub E x)
  rw [← QuadraticMap.polarBilin_apply_apply, avgOp_apply, map_sum] at h1
  have hterm : ∀ e : E, (QuadraticMap.polarBilin Q c)
      (((e : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) x) = 1 := fun e => by
    rw [QuadraticMap.polarBilin_apply_apply]
    have := i28_14_C_orth_polar (hEG e.2) c x
    rw [hc e e.2] at this
    rw [this, hx1]
  simp only [hterm, Finset.sum_const, Finset.card_univ] at h1
  rw [i28_14_C_nsmul_odd hodd] at h1
  exact one_ne_zero h1

end

section

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem i28_14_C_orth_conj {Q : QuadraticForm (ZMod 2) U} {a c : U}
    {g : LinearMap.GeneralLinearGroup (ZMod 2) U} (hg : g ∈ i28_14_N_OG Q)
    (hga : (g : U →ₗ[ZMod 2] U) a = c) (h : QuadraticMap.polarBilin Q a a = 0)
    (h' : QuadraticMap.polarBilin Q c c = 0) :
    g * tv (QuadraticMap.polarBilin Q a) a h * g⁻¹ = tv (QuadraticMap.polarBilin Q c) c h' := by
  have h'' : (QuadraticMap.polarBilin Q a ∘ₗ
      ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U))
      ((g : U →ₗ[ZMod 2] U) a) = 0 := by
    rw [LinearMap.comp_apply, i28_14_C_inv_apply]; exact h
  refine (conj_tv g _ a h h'').trans (i28_14_C_tv_congr _ _ ?_ hga)
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, ← hga, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, ← i28_14_C_orth_polar hg a, i28_14_C_apply_inv]

end

section

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

theorem tvC_orth {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : QuadraticForm (ZMod 2) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hirr : IsTvIrred ((TauCeti.QuadraticMap.orthogonalGroup Q).comap
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom))
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} (hA : IsElemAbelian p A)
    (hAG : A ≤ (TauCeti.QuadraticMap.orthogonalGroup Q).comap
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom)
    {t : LinearMap.GeneralLinearGroup (ZMod 2) U}
    (htG : t ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).comap
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom)
    (ht : IsF2Transvection t) :
    HasCentralizedConj p ((TauCeti.QuadraticMap.orthogonalGroup Q).comap
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom) A t := by
  classical
  change IsTvIrred (i28_14_N_OG Q) at hirr
  change A ≤ i28_14_N_OG Q at hAG
  change t ∈ i28_14_N_OG Q at htG
  change HasCentralizedConj p (i28_14_N_OG Q) A t
  by_cases hc : IsCyclic A
  · exact i28_14_C_of_cyclic hp hA hc t
  obtain ⟨E, hEA, hcard, c, hcE, d, hdE, hc0, hd0, hcd⟩ := i28_14_C_exists_hyperplane hp hp2 hA hc
  have hodd := i28_14_C_odd_card hp hp2 hA hEA
  have : Fintype E := Fintype.ofFinite E
  have hoddF : Odd (Fintype.card E) := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨v, hvE, hv1⟩ := i28_14_C_orth_fixed E hQ (hEA.trans hAG) hoddF hcE hc0
  obtain ⟨φt, a, h, hφt, ha, rfl⟩ := (isF2Transvection_iff t).mp ht
  obtain ⟨rfl, ha1⟩ := i28_14_N_orth_tv_mem hQ h hφt ha htG
  obtain ⟨g, hgG, hga⟩ := i28_14_C_orth_transitive hQ hirr ha1 hv1
  have hvv : QuadraticMap.polarBilin Q v v = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply]; exact i28_14_N_polar_self Q v
  have hconj := i28_14_C_orth_conj hgG hga h hvv
  refine i28_14_C_close (y := g⁻¹) ((i28_14_N_OG Q).inv_mem hgG) hEA hcard.le fun e he => ?_
  rw [inv_inv, hconj]
  refine i28_14_C_comm_tv hvv (hvE e he) fun x => ?_
  have hev : (e : U →ₗ[ZMod 2] U) v = v := hvE e he
  have := i28_14_C_orth_polar (hAG (hEA he)) v x
  rw [hev] at this
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
  exact this

end

end CFSG.HardMathSupport.Solomon.Coordinator
