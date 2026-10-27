module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame
import CFSG.RankThree.PartOne.KC.OrthogonalNormPlanePrimary

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {m : ℕ} {U : Fin m → Submodule F V}
  {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}

theorem eq_zero_of_mem_primaryComponent_of_apply_eq {x : V ≃ₗ[F] V} {h : F[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap h) (hfix : x v = v) : v = 0 := by
  by_contra hv0
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hev : Module.End.HasEigenvector x.toLinearMap 1 v :=
    ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hfix), hv0⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := h) hev
  rw [mem_primaryComponent.1 hv] at h1
  have h2 : h.eval 1 = 0 := by
    rcases smul_eq_zero.1 h1.symm with h3 | h3
    · exact h3
    · exact absurd h3 hv0
  have h3 : (X - C 1 : F[X]) ∣ h := Polynomial.dvd_iff_isRoot.2 h2
  have h4 := (irreducible_X_sub_C (1 : F)).associated_of_dvd hirr h3
  exact hne (by simpa using (Polynomial.eq_of_monic_of_associated (monic_X_sub_C (1 : F)) hmon h4).symm)

private theorem IsPlaneFrame.exists_le_primaryComponent_aux1 {x : V ≃ₗ[F] V} {W : Submodule F V}
    (hxW : ∀ v ∈ W, x v ∈ W) (f : F[X]) (w : W) :
    ((aeval (x.toLinearMap.restrict hxW) f w : W) : V) = aeval x.toLinearMap f (w : V) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul]
    congr 1
    rw [Module.End.pow_restrict n hxW]
    rfl

private theorem IsPlaneFrame.exists_le_primaryComponent_aux3 (hF : IsPlaneFrame Q p U e Bb)
    (hp : p.Prime) (hp2 : p ≠ 2) : Squarefree (X ^ p - 1 : F[X]) := by
  have hpc : (p : F) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec F p).mp h0
    have hℓ : (ringChar F).Prime := by rw [ringChar.eq F 2]; exact Nat.prime_two
    have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact hℓ.one_lt.ne' h2
    · exact hpl h2.symm
  have := Polynomial.separable_X_pow_sub_C (1 : F) hpc one_ne_zero
  simpa using this.squarefree

private theorem IsPlaneFrame.exists_le_primaryComponent_aux2 (hF : IsPlaneFrame Q p U e Bb)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (j : Fin m) :
    ∃ xj : U j ≃ₗ[F] U j, (∀ v : U j, (xj v : V) = (d : V ≃ₗ[F] V) v) ∧
      (∀ f : F[X], ∀ w : U j,
        ((aeval xj.toLinearMap f w : U j) : V) = aeval (d : V ≃ₗ[F] V).toLinearMap f (w : V)) ∧
      xj.toLinearMap ^ p = 1 := by
  have hdpL : (d : V ≃ₗ[F] V).toLinearMap ^ p = 1 := by
    have hdp : (d : V ≃ₗ[F] V) ^ p = 1 := by
      have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hF.isElemAbelian.2 d hd)
      simpa using this
    rw [← toLinearMap_pow, hdp]
    rfl
  have hpow : ∀ i : Fin m, ∀ n, ∀ v ∈ U i, ((e i : V ≃ₗ[F] V) ^ n) v ∈ U i := by
    intro i n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih => intro v hv; rw [pow_succ, LinearEquiv.mul_apply]; exact ih _ (hF.maps_to i v hv)
  have hxW : ∀ v ∈ U j, (d : V ≃ₗ[F] V) v ∈ U j := by
    obtain ⟨k, hk⟩ := hF.exists_pow_apply_eq hd j
    intro v hv; rw [hk v hv]; exact hpow j k v hv
  have hxWsym : ∀ v ∈ U j, (d : V ≃ₗ[F] V).symm v ∈ U j := by
    obtain ⟨k, hk⟩ := hF.exists_pow_apply_eq (Bb.inv_mem hd) j
    intro v hv
    change ((d⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) v ∈ U j
    rw [hk v hv]
    exact hpow j k v hv
  refine ⟨restrictEquiv (U j) (d : V ≃ₗ[F] V) hxW hxWsym, ?_, ?_, ?_⟩
  · intro v; exact coe_restrictEquiv (U j) (d : V ≃ₗ[F] V) hxW hxWsym v
  · intro f w
    rw [show (restrictEquiv (U j) (d : V ≃ₗ[F] V) hxW hxWsym).toLinearMap =
      (d : V ≃ₗ[F] V).toLinearMap.restrict hxW from rfl]
    exact IsPlaneFrame.exists_le_primaryComponent_aux1 hxW f w
  · rw [show (restrictEquiv (U j) (d : V ≃ₗ[F] V) hxW hxWsym).toLinearMap =
      (d : V ≃ₗ[F] V).toLinearMap.restrict hxW from rfl]
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have h1 : ∀ n : ℕ, ((((d : V ≃ₗ[F] V).toLinearMap.restrict hxW) ^ n) w : V) =
        ((d : V ≃ₗ[F] V).toLinearMap ^ n) (w : V) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
        exact congrArg (fun v : V => (d : V ≃ₗ[F] V) v) ih
    rw [h1 p]
    simpa using congrArg (fun f : Module.End F V => f (w : V)) hdpL

private theorem IsPlaneFrame.exists_le_primaryComponent_aux4 (hF : IsPlaneFrame Q p U e Bb)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (j : Fin m) (hno : ∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v → v = 0)
    {xj : U j ≃ₗ[F] U j} (hxjcoe : ∀ v : U j, (xj v : V) = (d : V ≃ₗ[F] V) v)
    (hxjp : xj.toLinearMap ^ p = 1) :
    ∀ a : F, ¬ (minpoly F xj.toLinearMap).IsRoot a := by
  intro a ha
  have hgdvd : minpoly F xj.toLinearMap ∣ (X ^ p - 1 : F[X]) := by
    refine minpoly.dvd F xj.toLinearMap ?_
    rw [map_sub, map_pow, aeval_X, hxjp, map_one, sub_self]
  have h1 : (X - C a : F[X]) ∣ minpoly F xj.toLinearMap := Polynomial.dvd_iff_isRoot.2 ha
  have h2 : (X ^ p - 1 : F[X]).IsRoot a := Polynomial.dvd_iff_isRoot.1 (h1.trans hgdvd)
  have hap : a ^ p = 1 := by
    have h3 : a ^ p - 1 = 0 := by simpa [Polynomial.IsRoot] using h2
    exact sub_eq_zero.mp h3
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hap
    exact zero_ne_one hap
  have hq1 : a ^ (Nat.card F - 1) = 1 := by
    haveI := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one a ha0
  have hnd : ¬ p ∣ Nat.card F - 1 := fun hdiv =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (by
      have hq : 1 ≤ Nat.card F := Nat.card_pos
      have := Nat.dvd_sub hpq hdiv
      rwa [show (Nat.card F + 1) - (Nat.card F - 1) = 2 by omega] at this))
  have hcop : Nat.gcd p (Nat.card F - 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  have h3 : a ^ Nat.gcd p (Nat.card F - 1) = 1 := pow_gcd_eq_one.2 ⟨hap, hq1⟩
  rw [hcop, pow_one] at h3
  have hX1dvd : (X - 1 : F[X]) ∣ minpoly F xj.toLinearMap := by
    have h4 := h1
    rw [h3] at h4
    simpa using h4
  have hgsq : Squarefree (minpoly F xj.toLinearMap) :=
    (hF.exists_le_primaryComponent_aux3 hp hp2).squarefree_of_dvd hgdvd
  have hX1mem : (X - 1 : F[X]) ∈ primaryFactors xj.toLinearMap :=
    mem_primaryFactors.mpr ⟨irreducible_X_sub_one, monic_X_sub_one, hX1dvd⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot hgsq hX1mem)
  have hfix : xj w = w := by
    have := mem_primaryComponent.1 hw
    simpa [map_sub, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero] using this
  exact hw0 (Subtype.ext (hno (w : V) w.2 (by rw [← hxjcoe w, hfix])))

private theorem IsPlaneFrame.exists_le_primaryComponent_aux6 (hF : IsPlaneFrame Q p U e Bb)
    (j : Fin m) : U j ≠ ⊥ := by
  intro hbot
  have := hF.finrank_eq j
  rw [hbot, finrank_bot] at this
  norm_num at this

private theorem IsPlaneFrame.exists_le_primaryComponent_aux5 (hF : IsPlaneFrame Q p U e Bb)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (j : Fin m) (hno : ∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v → v = 0) :
    ∃ k ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap,
      U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap k := by
  haveI : Nontrivial (U j) :=
    Module.nontrivial_of_finrank_pos (by rw [hF.finrank_eq j]; norm_num)
  obtain ⟨xj, hxjcoe, hxjaeval, hxjp⟩ := hF.exists_le_primaryComponent_aux2 hd j
  let g : F[X] := minpoly F xj.toLinearMap
  have hgmon : g.Monic := by
    show (minpoly F xj.toLinearMap).Monic
    exact minpoly.monic (Algebra.IsIntegral.isIntegral xj.toLinearMap)
  have hgdeg : g.natDegree ≤ 2 := by
    have hdvd : g ∣ xj.toLinearMap.charpoly := LinearMap.minpoly_dvd_charpoly xj.toLinearMap
    have hq0 : xj.toLinearMap.charpoly ≠ 0 := (LinearMap.charpoly_monic xj.toLinearMap).ne_zero
    calc g.natDegree ≤ xj.toLinearMap.charpoly.natDegree := natDegree_le_of_dvd hdvd hq0
      _ = Module.finrank F (U j) := LinearMap.charpoly_natDegree xj.toLinearMap
      _ = 2 := hF.finrank_eq j
  have hgpos : 1 ≤ g.natDegree := by
    have h : 0 < (minpoly F xj.toLinearMap).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral xj.toLinearMap)
    exact h
  have hgirr : Irreducible g := irreducible_of_degree_le_three_of_not_isRoot
    (Finset.mem_Icc.mpr ⟨hgpos, by omega⟩)
    (hF.exists_le_primaryComponent_aux4 hp hp2 hpq hd j hno hxjcoe hxjp)
  have hUg : U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap g := by
    intro v hv
    rw [mem_primaryComponent]
    have h1 := hxjaeval g ⟨v, hv⟩
    have h2 : aeval xj.toLinearMap g = 0 := minpoly.aeval F xj.toLinearMap
    rw [← h1, h2]
    simp
  have hnebot : primaryComponent (d : V ≃ₗ[F] V).toLinearMap g ≠ ⊥ :=
    fun hbot => hF.exists_le_primaryComponent_aux6 j (le_bot_iff.mp (hUg.trans (le_of_eq hbot)))
  exact ⟨g, mem_primaryFactors_of_primaryComponent_ne_bot hgirr hgmon hnebot, hUg⟩

theorem IsPlaneFrame.exists_le_primaryComponent (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (j : Fin m) :
    ∃ k ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap,
      U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap k := by
  rcases hF.apply_eq_or_eq_zero hp hd j with hid | hno
  · have hUg : U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - 1) := by
      rw [← fixedSpace_eq_primaryComponent]
      exact fun v hv => mem_fixedSpace.2 (hid v hv)
    refine ⟨X - 1, ?_, hUg⟩
    refine mem_primaryFactors_of_primaryComponent_ne_bot irreducible_X_sub_one monic_X_sub_one ?_
    exact fun hbot => hF.exists_le_primaryComponent_aux6 j (le_bot_iff.mp (hUg.trans (le_of_eq hbot)))
  · exact hF.exists_le_primaryComponent_aux5 hp hp2 hpq hd j hno

private theorem IsPlaneFrame.exists_le_primaryComponent_of_mem_aux1 (hF : IsPlaneFrame Q p U e Bb)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) {f : F[X]} {v : V} (hv : v ∈ ⨆ j, U j) :
    aeval (d : V ≃ₗ[F] V).toLinearMap f v ∈ ⨆ j, U j := by
  have hxWi : ∀ i, ∀ u ∈ U i, (d : V ≃ₗ[F] V) u ∈ U i := by
    intro i
    obtain ⟨k, hk⟩ := hF.exists_pow_apply_eq hd i
    have hpow : ∀ n, ∀ u ∈ U i, ((e i : V ≃ₗ[F] V) ^ n) u ∈ U i := by
      intro n
      induction n with
      | zero => intro u hu; simpa using hu
      | succ n ih => intro u hu; rw [pow_succ, LinearEquiv.mul_apply]; exact ih _ (hF.maps_to i u hu)
    intro u hu; rw [hk u hu]; exact hpow k u hu
  have hWinv : ∀ u ∈ (⨆ i, U i), (d : V ≃ₗ[F] V).toLinearMap u ∈ ⨆ i, U i := by
    intro u hu
    refine Submodule.iSup_induction U (motive := fun u =>
      (d : V ≃ₗ[F] V).toLinearMap u ∈ ⨆ i, U i) hu ?_ ?_ ?_
    · intro i y hy; exact Submodule.mem_iSup_of_mem i (hxWi i y hy)
    · simp
    · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  have hWpow : ∀ n, ∀ u ∈ (⨆ i, U i), ((d : V ≃ₗ[F] V).toLinearMap ^ n) u ∈ ⨆ i, U i := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih =>
      intro u hu; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hWinv u hu)
  induction f using Polynomial.induction_on' with
  | add p q hpa hqa => rw [map_add]; exact Submodule.add_mem _ hpa hqa
  | monomial n c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.smul_mem _ _ (hWpow n v hv)

private theorem IsPlaneFrame.exists_le_primaryComponent_of_mem_aux2
    {d : ↥(orthDerived Q)} {h : F[X]}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hne : h ≠ X - 1) :
    h.eval 1 ≠ 0 := by
  intro h0
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdvd : (X - C 1 : F[X]) ∣ h := Polynomial.dvd_iff_isRoot.2 h0
  have hass := (irreducible_X_sub_C (1 : F)).associated_of_dvd hirr hdvd
  have heq : h = X - C 1 :=
    (Polynomial.eq_of_monic_of_associated (monic_X_sub_C (1 : F)) hmon hass).symm
  exact hne (by rw [heq, Polynomial.C_1])

private theorem IsPlaneFrame.exists_le_primaryComponent_of_mem_aux3 (hF : IsPlaneFrame Q p U e Bb)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) {h : F[X]} (h1 : h.eval 1 ≠ 0) {v : V}
    (hv : v ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) :
    v ∈ ⨆ j, U j := by
  obtain ⟨w, hw, v₀, hv₀, rfl⟩ := Submodule.mem_sup.1
    (show v ∈ (⨆ j, U j) ⊔ polarPerp Q (⨆ j, U j) from by
      rw [hF.isCompl_iSup.sup_eq_top]; exact Submodule.mem_top)
  have hv0fix : (d : V ≃ₗ[F] V) v₀ = v₀ := hF.apply_eq_of_mem_polarPerp_iSup hd hv₀
  have hv0 : aeval (d : V ≃ₗ[F] V).toLinearMap h v₀ = h.eval 1 • v₀ := by
    by_cases h0 : v₀ = 0
    · simp [h0]
    · have hev : Module.End.HasEigenvector (d : V ≃ₗ[F] V).toLinearMap 1 v₀ :=
        ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hv0fix), h0⟩
      exact Module.End.aeval_apply_of_hasEigenvector (p := h) hev
  have hwmem : aeval (d : V ≃ₗ[F] V).toLinearMap h w ∈ ⨆ j, U j :=
    hF.exists_le_primaryComponent_of_mem_aux1 hd hw
  have heq : h.eval 1 • v₀ = -(aeval (d : V ≃ₗ[F] V).toLinearMap h w) := by
    have hthis := hv
    rw [mem_primaryComponent, map_add, hv0] at hthis
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hthis
  have hmem : h.eval 1 • v₀ ∈ (⨆ j, U j) ⊓ polarPerp Q (⨆ j, U j) :=
    ⟨heq.symm ▸ Submodule.neg_mem _ hwmem, Submodule.smul_mem _ _ hv₀⟩
  have hbot : h.eval 1 • v₀ = 0 := by
    rw [disjoint_iff.1 hF.isCompl_iSup.disjoint] at hmem
    exact (Submodule.mem_bot F).1 hmem
  have hv00 : v₀ = 0 := (smul_eq_zero.1 hbot).resolve_left h1
  subst hv00
  simpa using hw

theorem IsPlaneFrame.exists_le_primaryComponent_of_mem (hF : IsPlaneFrame Q p U e Bb)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hne : h ≠ X - 1) :
    ∃ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
  have h1 : h.eval 1 ≠ 0 :=
    IsPlaneFrame.exists_le_primaryComponent_of_mem_aux2 hh hne
  have hdpL : (d : V ≃ₗ[F] V).toLinearMap ^ p = 1 := by
    have hdp : (d : V ≃ₗ[F] V) ^ p = 1 := by
      have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hF.isElemAbelian.2 d hd)
      simpa using this
    rw [← toLinearMap_pow, hdp]
    rfl
  have hhsq : Squarefree (minpoly F (d : V ≃ₗ[F] V).toLinearMap) := by
    refine squarefree_minpoly_of_aeval_eq_zero (hF.exists_le_primaryComponent_aux3 hp hp2) ?_
    rw [map_sub, map_pow, aeval_X, hdpL, map_one, sub_self]
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot hhsq hh)
  have hvW : v ∈ ⨆ j, U j := hF.exists_le_primaryComponent_of_mem_aux3 hd h1 hv
  by_contra hcon
  push Not at hcon
  have hPhW : ∀ u ∈ (⨆ j, U j), primaryProjection (d : V ≃ₗ[F] V).toLinearMap h u = 0 := by
    intro u hu
    refine Submodule.iSup_induction U (motive := fun u =>
      primaryProjection (d : V ≃ₗ[F] V).toLinearMap h u = 0) hu ?_ ?_ ?_
    · intro j y hy
      obtain ⟨k, hk, hUk⟩ := hF.exists_le_primaryComponent hp hp2 hpq hd j
      exact primaryProjection_of_mem_ne hhsq hh hk (fun hkh => hcon j (hkh ▸ hUk)) (hUk hy)
    · simp
    · intro a b ha hb; rw [map_add, ha, hb, add_zero]
  have hvPh : primaryProjection (d : V ≃ₗ[F] V).toLinearMap h v = v :=
    primaryProjection_of_mem hhsq hh hv
  rw [hPhW v hvW] at hvPh
  exact hv0 hvPh.symm

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
