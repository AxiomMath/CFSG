module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCUnitaryPlane

section Generic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem aeval_apply_of_apply_eq {x : Module.End K V} {v : V} (hv : x v = v) (f : K[X]) :
    aeval x f v = f.eval 1 • v := by
  have hk : ∀ k : ℕ, (x ^ k) v = v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, Module.End.mul_apply, hv, ih]
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, LinearMap.add_apply, hf, hg, eval_add, add_smul]
  | monomial k c =>
    rw [aeval_monomial, Module.End.mul_apply, hk, eval_monomial, one_pow, mul_one,
      Module.algebraMap_end_apply]

theorem aeval_mem_range_of_commute {e x : Module.End K V} (h : Commute e x) (f : K[X]) {u : V}
    (hu : u ∈ LinearMap.range e) : aeval x f u ∈ LinearMap.range e := by
  obtain ⟨z, rfl⟩ := hu
  refine ⟨aeval x f z, ?_⟩
  rw [← Module.End.mul_apply, (commute_aeval h f).eq, Module.End.mul_apply]

end Generic

section GeneralLinear

variable {n : ℕ} {K : Type} [Field K]

theorem mem_centralizer_of_commute_toLin' {g a₀ : GL (Fin n) K}
    (h : Commute (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K))
      (Matrix.toLin' (a₀ : Matrix (Fin n) (Fin n) K))) :
    g ∈ Subgroup.centralizer ({a₀} : Set (GL (Fin n) K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Units.ext (Matrix.toLin'.injective ?_)
  rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact h.eq

end GeneralLinear

section Plane

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] (E0 : Subgroup (SpecialLinearGroup (Fin n) K))
  [Fintype E0] [IsMulCommutative E0]

local notation "ρ₀" => planeRep E0

theorem projLine_act_apply (e : ↥E0) (L : Subgroup ↥E0) (v : Fin n → K) :
    projLine ρ₀ L (act ρ₀ e v) = act ρ₀ e (projLine ρ₀ L v) := by
  rw [← Module.End.mul_apply, ← (commute_act_projLine E0 e L).eq, Module.End.mul_apply]

theorem commute_projLine_of_commute {r : Module.End K (Fin n → K)}
    (hr : ∀ e : ↥E0, Commute r (act ρ₀ e)) (L : Subgroup ↥E0) : Commute r (projLine ρ₀ L) := by
  have hs : ∀ M : Subgroup ↥E0, Commute r (sumOp ρ₀ M) := fun M => by
    unfold sumOp
    exact Commute.sum_right _ _ _ fun e _ => hr e
  have ha : ∀ M : Subgroup ↥E0, Commute r (avgOp ρ₀ M) := fun M => by
    unfold avgOp
    exact (hs M).smul_right _
  unfold projLine
  exact (ha L).sub_right (ha ⊤)

@[expose] noncomputable def auxEnd (c d : ↥E0) (L : Subgroup ↥E0) : Module.End K (Fin n → K) :=
  act ρ₀ c * projLine ρ₀ L + act ρ₀ d * (1 - projLine ρ₀ L)

theorem auxEnd_apply (c d : ↥E0) (L : Subgroup ↥E0) (v : Fin n → K) :
    auxEnd E0 c d L v = act ρ₀ c (projLine ρ₀ L v) + act ρ₀ d (v - projLine ρ₀ L v) := by
  simp [auxEnd, Module.End.mul_apply]

theorem commute_auxEnd_of_commute {r : Module.End K (Fin n → K)}
    (hr : ∀ e : ↥E0, Commute r (act ρ₀ e)) (c d : ↥E0) (L : Subgroup ↥E0) :
    Commute r (auxEnd E0 c d L) := by
  have hpi := commute_projLine_of_commute E0 hr L
  exact ((hr c).mul_right hpi).add_right ((hr d).mul_right ((Commute.one_right r).sub_right hpi))

theorem commute_act_auxEnd (e c d : ↥E0) (L : Subgroup ↥E0) :
    Commute (act ρ₀ e) (auxEnd E0 c d L) :=
  commute_auxEnd_of_commute E0 (fun f => commute_act E0 e f) c d L

variable {E0} (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)
include hP hpK

theorem projLine_projLine {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (v : Fin n → K) :
    projLine ρ₀ L (projLine ρ₀ L v) = projLine ρ₀ L v := by
  simpa using LinearMap.congr_fun (projLine_mul_self ρ₀ hP hpK (mem_lines.mp hL)) v

theorem projLine_apply_of_mem_range {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {y : Fin n → K}
    (hy : y ∈ LinearMap.range (projLine ρ₀ L)) : projLine ρ₀ L y = y := by
  obtain ⟨z, rfl⟩ := hy
  exact projLine_projLine hP hpK hL z

theorem eq_zero_of_mem_range_projLine {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {e : ↥E0}
    (heL : e ∉ L) {y : Fin n → K} (hy : y ∈ LinearMap.range (projLine ρ₀ L))
    (hey : act ρ₀ e y = y) : y = 0 := by
  have he1 : e ≠ 1 := fun h => heL (h ▸ L.one_mem)
  have hM := hP.zpowers_mem_lines he1
  have hfix : y ∈ fixedSpace ρ₀ (Subgroup.zpowers e) :=
    fixedSpace_of_apply_eq ρ₀ hP (mem_lines.mp hM) (Subgroup.mem_zpowers e) he1 hey
  have hLM : L ≠ Subgroup.zpowers e := fun h => heL (h ▸ Subgroup.mem_zpowers e)
  have h0 := projLine_apply_of_mem_fixedSpace E0 hP hpK (mem_lines.mp hL) (mem_lines.mp hM) hLM
    hfix
  rwa [projLine_apply_of_mem_range hP hpK hL hy] at h0

theorem auxEnd_apply_of_mem_range {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (c d : ↥E0)
    {y : Fin n → K} (hy : y ∈ LinearMap.range (projLine ρ₀ L)) :
    auxEnd E0 c d L y = act ρ₀ c y := by
  rw [auxEnd_apply, projLine_apply_of_mem_range hP hpK hL hy, sub_self, map_zero, add_zero]

theorem auxEnd_pow_apply {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (c d : ↥E0) (k : ℕ)
    (v : Fin n → K) :
    (auxEnd E0 c d L ^ k) v =
      act ρ₀ (c ^ k) (projLine ρ₀ L v) + act ρ₀ (d ^ k) (v - projLine ρ₀ L v) := by
  induction k with
  | zero => simp [act_one]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, auxEnd_apply]
    have h1 : projLine ρ₀ L (act ρ₀ (c ^ k) (projLine ρ₀ L v)) =
        act ρ₀ (c ^ k) (projLine ρ₀ L v) := by
      rw [projLine_act_apply, projLine_projLine hP hpK hL]
    have h2 : projLine ρ₀ L (act ρ₀ (d ^ k) (v - projLine ρ₀ L v)) = 0 := by
      rw [projLine_act_apply, map_sub, projLine_projLine hP hpK hL, sub_self, map_zero]
    have hc : ∀ (e : ↥E0) (y : Fin n → K), act ρ₀ e (act ρ₀ (e ^ k) y) = act ρ₀ (e ^ (k + 1)) y :=
      fun e y => by rw [pow_succ' e k, act_mul, Module.End.mul_apply]
    rw [map_add, h1, h2, add_zero, add_sub_cancel_left, hc, hc]

theorem auxEnd_pow_eq_one {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (c d : ↥E0) :
    auxEnd E0 c d L ^ p = 1 := by
  refine LinearMap.ext fun v => ?_
  rw [auxEnd_pow_apply hP hpK hL, hP.pow c, hP.pow d, act_one]
  simp

theorem squarefree_minpoly_auxEnd {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (c d : ↥E0) :
    Squarefree (minpoly K (auxEnd E0 c d L)) :=
  squarefree_minpoly_of_pow_eq_one hpK (auxEnd_pow_eq_one hP hpK hL c d)

theorem primaryComponent_auxEnd_X_sub_one {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {c d : ↥E0}
    (hcL : c ∉ L) (hdL : d ∈ L) (hd1 : d ≠ 1) :
    primaryComponent (auxEnd E0 c d L) (X - C 1) = LinearMap.range (projTop ρ₀) := by
  ext v
  rw [mem_primaryComponent]
  simp only [map_sub, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · intro hv
    have h1 : act ρ₀ c (projLine ρ₀ L v) = projLine ρ₀ L v := by
      have := congrArg (projLine ρ₀ L) hv
      rwa [auxEnd_apply, map_add, projLine_act_apply, projLine_projLine hP hpK hL,
        projLine_act_apply, map_sub, projLine_projLine hP hpK hL, sub_self, map_zero,
        add_zero] at this
    have hpi0 : projLine ρ₀ L v = 0 :=
      eq_zero_of_mem_range_projLine hP hpK hL hcL (LinearMap.mem_range_self _ v) h1
    rw [auxEnd_apply, hpi0, map_zero, zero_add, sub_zero] at hv
    have hfix : v ∈ fixedSpace ρ₀ L := fixedSpace_of_apply_eq ρ₀ hP (mem_lines.mp hL) hdL hd1 hv
    have havg : avgOp ρ₀ L v = v :=
      avgOp_apply_of_mem_fixedSpace ρ₀ (natCard_cast_line hpK (mem_lines.mp hL)) hfix
    have h2 : projLine ρ₀ L v = avgOp ρ₀ L v - avgOp ρ₀ ⊤ v := rfl
    rw [hpi0, havg] at h2
    exact ⟨v, (sub_eq_zero.mp h2.symm).symm⟩
  · rintro ⟨u, rfl⟩
    have h0 : projLine ρ₀ L (projTop ρ₀ u) = 0 := by
      simpa using LinearMap.congr_fun (projLine_mul_projTop ρ₀ hP hpK (mem_lines.mp hL)) u
    rw [auxEnd_apply, h0, map_zero, zero_add, sub_zero]
    exact avgOp_apply_mem_fixedSpace ρ₀ ⊤ u d (Subgroup.mem_top d)

theorem eq_zero_of_mem_range_of_auxEnd_apply {L : Subgroup ↥E0} (hL : L ∈ lines p E0)
    {c : ↥E0} (hcL : c ∉ L) (d : ↥E0) {y : Fin n → K} (hy : y ∈ LinearMap.range (projLine ρ₀ L))
    (hwy : auxEnd E0 c d L y = y) : y = 0 := by
  rw [auxEnd_apply_of_mem_range hP hpK hL c d hy] at hwy
  exact eq_zero_of_mem_range_projLine hP hpK hL hcL hy hwy

theorem mem_range_projLine_of_mem_primaryComponent {L : Subgroup ↥E0} (hL : L ∈ lines p E0)
    {c : ↥E0} (hcL : c ∉ L) {h : K[X]} (hh : h ∈ primaryFactors (auxEnd E0 c 1 L))
    (hX : h ≠ X - C 1) {v : Fin n → K} (hv : v ∈ primaryComponent (auxEnd E0 c 1 L) h) :
    v ∈ LinearMap.range (projLine ρ₀ L) := by
  have hcomm : Commute (projLine ρ₀ L) (auxEnd E0 c 1 L) :=
    commute_auxEnd_of_commute E0 (fun e => (commute_act_projLine E0 e L).symm) c 1 L
  set u := v - projLine ρ₀ L v with hu
  have hu1 : u ∈ primaryComponent (auxEnd E0 c 1 L) h :=
    Submodule.sub_mem _ hv (apply_mem_primaryComponent hcomm hv)
  have hpiu : projLine ρ₀ L u = 0 := by
    rw [hu, map_sub, projLine_projLine hP hpK hL, sub_self]
  have hu2 : auxEnd E0 c 1 L u = u := by
    rw [auxEnd_apply, hpiu, map_zero, zero_add, sub_zero, act_one, Module.End.one_apply]
  have hu3 : u ∈ primaryComponent (auxEnd E0 c 1 L) (X - C 1) := by
    rw [mem_primaryComponent]
    simp [hu2]
  by_cases hu0 : u = 0
  · exact ⟨v, (sub_eq_zero.mp hu0).symm⟩
  · have hXmem := mem_primaryFactors_of_ne_zero (irreducible_X_sub_C 1) (monic_X_sub_C 1) hu0 hu3
    exact absurd (eq_zero_of_mem_primaryComponent_ne hh hXmem hX hu1 hu3) hu0

omit hpK in
theorem exists_mem_mul_pow {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {c : ↥E0} (hcL : c ∉ L)
    (e : ↥E0) : ∃ l ∈ L, ∃ j : ℕ, e = l * c ^ j := by
  have hN : (Subgroup.zpowers c).Normal := ⟨fun z _ g => by
    have hgz : g * z = z * g := (IsMulCommutative.is_comm (M := E0)).comm g z
    rwa [hgz, mul_inv_cancel_right]⟩
  set S := L ⊔ Subgroup.zpowers c with hS
  have hLS : L ≤ S := le_sup_left
  have hcS : c ∈ S := le_sup_right (a := L) (Subgroup.mem_zpowers c)
  have hLc : Nat.card L = p := mem_lines.mp hL
  have hdvd : Nat.card S ∣ p ^ 2 := hP.card ▸ Subgroup.card_subgroup_dvd_card S
  obtain ⟨k, hk, hSk⟩ := (Nat.dvd_prime_pow hP.prime).mp hdvd
  have hpS : p ∣ Nat.card S := hLc ▸ Subgroup.card_dvd_of_le hLS
  have htop : S = ⊤ := by
    interval_cases k
    · rw [hSk, pow_zero] at hpS
      exact absurd (Nat.le_of_dvd one_pos hpS) (by have := hP.prime.two_le; omega)
    · exfalso
      have hSL : S = L := (Subgroup.eq_of_le_of_card_ge hLS (by rw [hSk, hLc, pow_one])).symm
      exact hcL (hSL ▸ hcS)
    · exact Subgroup.eq_top_of_card_eq S (by rw [hSk, hP.card])
  have he : e ∈ S := htop ▸ Subgroup.mem_top e
  obtain ⟨l, hl, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp he
  obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hz : z ∈ Submonoid.powers c)
  exact ⟨l, hl, j, rfl⟩

theorem exists_act_eq_auxEnd_pow {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {c : ↥E0} (hcL : c ∉ L)
    (d e : ↥E0) : ∃ j : ℕ, ∀ y ∈ LinearMap.range (projLine ρ₀ L),
      act ρ₀ e y = (auxEnd E0 c d L ^ j) y := by
  obtain ⟨l, hl, j, rfl⟩ := exists_mem_mul_pow hP hL hcL e
  refine ⟨j, fun y hy => ?_⟩
  rw [auxEnd_pow_apply hP hpK hL, projLine_apply_of_mem_range hP hpK hL hy, sub_self, map_zero,
    add_zero, act_mul, Module.End.mul_apply]
  exact fix_range_projLine E0 hl _ (stable_range_projLine E0 (c ^ j) L y hy)

theorem exists_active_not_mem {b : ↥E0} (hb : b ≠ 1) :
    ∃ L ∈ lines p E0, projLine ρ₀ L ≠ 0 ∧ b ∉ L := by
  by_contra hcon
  push Not at hcon
  apply hb
  apply planeRep_injective E0
  rw [map_one]
  refine Units.ext ?_
  change act ρ₀ b = 1
  refine LinearMap.ext fun v => ?_
  have hv : ∑ L ∈ lines p E0, projLine ρ₀ L v + projTop ρ₀ v = v := by
    simpa using LinearMap.congr_fun (sum_projLine_add_projTop ρ₀ hP hpK) v
  rw [Module.End.one_apply, ← hv, map_add, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun L hL => ?_
    by_cases h0 : projLine ρ₀ L = 0
    · rw [h0, LinearMap.zero_apply, map_zero]
    · exact fix_range_projLine E0 (hcon L hL h0) _ (LinearMap.mem_range_self _ v)
  · exact avgOp_apply_mem_fixedSpace ρ₀ ⊤ v b (Subgroup.mem_top b)

theorem exists_goodBlock_of_perfect [Finite K] {R : Subgroup (GL (Fin n) K)} [Group.IsPerfect ↥R]
    (hR : R ≠ ⊥)
    (hRc : ∀ g ∈ R, ∀ e : ↥E0, Commute (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) (act ρ₀ e))
    {L₀ : Subgroup ↥E0} (hL₀ : L₀ ∈ lines p E0) {c d : ↥E0} (hcL₀ : c ∉ L₀) (hdL₀ : d ∈ L₀)
    (hd1 : d ≠ 1) (cL : Subgroup ↥E0 → ↥E0) (hcL : ∀ L ∈ lines p E0, cL L ∉ L) :
    (∃ hX : (X - C 1 : K[X]) ∈ primaryFactors (auxEnd E0 c d L₀),
      GoodBlock (⟨X - C 1, hX⟩ : primaryFactors (auxEnd E0 c d L₀))) ∨
    ∃ L ∈ lines p E0, ∃ h : K[X], ∃ hh : h ∈ primaryFactors (auxEnd E0 (cL L) 1 L),
      h ≠ X - C 1 ∧ GoodBlock (⟨h, hh⟩ : primaryFactors (auxEnd E0 (cL L) 1 L)) := by
  by_contra hcon
  simp only [not_or, not_exists, not_and] at hcon
  obtain ⟨hn0, hnL⟩ := hcon
  have hp0 : p ≠ 0 := hP.prime.ne_zero
  have hRw : ∀ (c' d' : ↥E0) (L : Subgroup ↥E0) (a₀ : GL (Fin n) K),
      Matrix.toLin' (a₀ : Matrix (Fin n) (Fin n) K) = auxEnd E0 c' d' L →
      R ≤ Subgroup.centralizer ({a₀} : Set (GL (Fin n) K)) := by
    intro c' d' L a₀ ha₀ g hg
    refine mem_centralizer_of_commute_toLin' ?_
    rw [ha₀]
    exact commute_auxEnd_of_commute E0 (hRc g hg) c' d' L
  apply hR
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hfix0 : ∀ u ∈ LinearMap.range (projTop ρ₀),
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) u = u := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0, map_zero]
    rw [← primaryComponent_auxEnd_X_sub_one hP hpK hL₀ hcL₀ hdL₀ hd1] at hu
    have hX := mem_primaryFactors_of_ne_zero (irreducible_X_sub_C 1) (monic_X_sub_C 1) hu0 hu
    haveI := isSolvable_of_not_goodBlock (hn0 hX)
    exact apply_eq_of_perfect_of_isSolvable (squarefree_minpoly_auxEnd hP hpK hL₀ c d)
      ⟨X - C 1, hX⟩ (toLin'_glOfPow _ (auxEnd_pow_eq_one hP hpK hL₀ c d) hp0)
      (hRw c d L₀ _ (toLin'_glOfPow _ _ _)) hg hu
  have hfixL : ∀ L ∈ lines p E0, ∀ u ∈ LinearMap.range (projLine ρ₀ L),
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) u = u := by
    intro L hL u hu
    set w := auxEnd E0 (cL L) 1 L with hw
    have hsq := squarefree_minpoly_auxEnd hP hpK hL (cL L) 1
    have hcomm : Commute (projLine ρ₀ L) w :=
      commute_auxEnd_of_commute E0 (fun e => (commute_act_projLine E0 e L).symm) (cL L) 1 L
    have hsum : ∑ h ∈ primaryFactors w, primaryProjection w h u = u := by
      have := LinearMap.congr_fun (sum_primaryProjection hsq) u
      rwa [LinearMap.sum_apply, Module.End.one_apply] at this
    rw [← hsum, map_sum]
    refine Finset.sum_congr rfl fun h hh => ?_
    have h1 : primaryProjection w h u ∈ primaryComponent w h := primaryProjection_mem hsq hh u
    have h2 : primaryProjection w h u ∈ LinearMap.range (projLine ρ₀ L) :=
      aeval_mem_range_of_commute hcomm _ hu
    by_cases hX : h = X - C 1
    · have h1' : primaryProjection w h u ∈ primaryComponent w (X - C 1) := by
        rw [← hX]
        exact h1
      have h3 : w (primaryProjection w h u) = primaryProjection w h u := by
        have := mem_primaryComponent.mp h1'
        simp only [map_sub, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply] at this
        exact sub_eq_zero.mp this
      rw [eq_zero_of_mem_range_of_auxEnd_apply hP hpK hL (hcL L hL) 1 h2 h3, map_zero]
    · haveI := isSolvable_of_not_goodBlock (hnL L hL h hh hX)
      exact apply_eq_of_perfect_of_isSolvable hsq ⟨h, hh⟩
        (toLin'_glOfPow _ (auxEnd_pow_eq_one hP hpK hL (cL L) 1) hp0)
        (hRw (cL L) 1 L _ (toLin'_glOfPow _ _ _)) hg h1
  refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => ?_))
  have hv : ∑ L ∈ lines p E0, projLine ρ₀ L v + projTop ρ₀ v = v := by
    simpa using LinearMap.congr_fun (sum_projLine_add_projTop ρ₀ hP hpK) v
  rw [Units.val_one, Matrix.toLin'_one, LinearMap.id_apply, ← hv, map_add, map_sum,
    hfix0 _ (LinearMap.mem_range_self _ v)]
  congr 1
  exact Finset.sum_congr rfl fun L hL => hfixL L hL _ (LinearMap.mem_range_self _ v)

end Plane

section Order

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_pow_not_mem_center_of_goodBlock {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq1 : ¬ p ∣ Nat.card K - 1) (hq2 : p ∣ Nat.card K ^ 2 - 1)
    {x : Module.End K (Fin n → K)} (hxp : x ^ p = 1) {a : primaryFactors x} (hg : GoodBlock a) :
    ∃ s : SpecialLinearGroup (Fin (mult x a)) (Efac x a), s ^ p = 1 ∧
      s ∉ Subgroup.center (SpecialLinearGroup (Fin (mult x a)) (Efac x a)) := by
  have hm2 : 2 ≤ mult x a := by
    rcases hg with h | ⟨h, _⟩ <;> omega
  have hirr : Irreducible (a : K[X]) := Fact.out
  have hdvd : (a : K[X]) ∣ X ^ p - C 1 :=
    (mem_primaryFactors.mp a.2).2.2.trans (minpoly.dvd K _ (by simp [hxp]))
  by_cases haX : (a : K[X]) = X - C 1
  · have : Module.Finite K (Efac x a) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
    have : Finite (Efac x a) := Module.finite_of_finite K
    letI : Fintype (Efac x a) := Fintype.ofFinite _
    have hc : Fintype.card (Efac x a) = Nat.card K := by
      rw [← Nat.card_eq_fintype_card]
      change Nat.card (AdjoinRoot (a : K[X])) = Nat.card K
      rw [natCard_adjoinRoot, haX, natDegree_X_sub_C, pow_one]
    exact exists_pow_not_mem_center_of_dvd hp hm2 (by rw [hc]; exact hq2) (by rw [hc]; exact hq1)
  · set ζ : Efac x a := AdjoinRoot.root (a : K[X]) with hζ
    have hζp : ζ ^ p = 1 := by
      have h0 : AdjoinRoot.mk (a : K[X]) (X ^ p - C 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hdvd
      simpa [sub_eq_zero] using h0
    have hζ1 : ζ ≠ 1 := by
      intro h1
      apply haX
      have h0 : AdjoinRoot.mk (a : K[X]) (X - C 1) = 0 := by
        simp only [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one]
        rw [← hζ, h1, sub_self]
      exact eq_of_monic_of_associated (monic_of_mem_primaryFactors a.2) (monic_X_sub_C 1)
        (hirr.associated_of_dvd (irreducible_X_sub_C 1) (AdjoinRoot.mk_eq_zero.mp h0))
    exact exists_pow_not_mem_center_of_root hm2 (hp.odd_of_ne_two hp2) hζp hζ1

end Order

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
