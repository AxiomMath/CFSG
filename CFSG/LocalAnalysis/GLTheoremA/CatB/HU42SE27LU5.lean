module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27LDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
import CFSG.RankThree.PartOne.S15K.CommonEigen
import TauCeti.RepresentationTheory.PGroupInvariants
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Fischer Matrix CFSG.Open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.Yardstones.Md0ec50421ce4

noncomputable section

private abbrev SU (n : ℕ) : Type := ↥(StatedSU n (2 ^ 1) F4)

private abbrev gl {n : ℕ} (g : SU n) : GL (Fin n) F4 := (g : GL (Fin n) F4)

private abbrev mat {n : ℕ} (g : SU n) : Matrix (Fin n) (Fin n) F4 :=
  ((g : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4)

private abbrev USig : F4 ≃+* F4 := CFSG.LieType.BorelTits.unitaryInvolution F4 2 1

private abbrev H {n : ℕ} (x y : Fin n → F4) : F4 := herm USig x y

private theorem USig_apply (c : F4) : USig c = c ^ 2 := by
  rw [show USig = CFSG.LieType.BorelTits.unitaryInvolution F4 2 1 from rfl,
    CFSG.LieType.BorelTits.unitaryInvolution_apply]
  norm_num

private theorem USig_invol (c : F4) : USig (USig c) = c := by
  rw [USig_apply, USig_apply, F4.sq_sq]

private theorem USig_one_add_one : (1 : F4) + USig 1 = 0 := by
  rw [USig_apply]
  rfl

private theorem H_apply {n : ℕ} (x y : Fin n → F4) :
    H x y = ∑ i, x i ^ 2 * y i := by
  rw [show H x y = herm USig x y from rfl, herm_def]
  exact Finset.sum_congr rfl fun i _ => by rw [USig_apply]

private theorem stdHermForm_H {n : ℕ} (x y : Fin n → F4) :
    CFSG.LinearGroups.stdHermForm CFSG.LinearGroups.unitaryFieldData_F4 n x y = H x y := rfl

private theorem H_smul_smul {n : ℕ} (g : SU n) (x y : Fin n → F4) :
    H (gl g • x) (gl g • y) = H x y := by
  have h := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry
    CFSG.LinearGroups.unitaryFieldData_F4 (n := n) (A := (g : GL (Fin n) F4))).mp g.2
  rw [← stdHermForm_H, ← stdHermForm_H]
  exact h.2 x y

private theorem exists_smul_ne_self {n : ℕ} {g : GL (Fin n) F4} (hg : g ≠ 1) :
    ∃ v : Fin n → F4, g • v ≠ v := by
  by_contra h
  push Not at h
  apply hg
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  funext i
  have h0 : (g : Matrix (Fin n) (Fin n) F4).mulVec (Pi.single j (1 : F4) : Fin n → F4) =
      ((1 : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4).mulVec
        (Pi.single j (1 : F4) : Fin n → F4) := by
    change g • (Pi.single j (1 : F4) : Fin n → F4) =
      (1 : GL (Fin n) F4) • (Pi.single j (1 : F4) : Fin n → F4)
    rw [h (Pi.single j (1 : F4) : Fin n → F4), one_smul]
  have h1 := congrFun h0 i
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h1
  simpa using h1

private theorem F4_pow_three_eq_one {c : F4} (hc : c ≠ 0) : c ^ 3 = 1 := by
  fin_cases c <;> first | rfl | exact absurd rfl hc

private theorem F4_one_add_one : (1 : F4) + 1 = 0 := by rfl

private def W {n : ℕ} (U₀ : Subgroup (SU n)) : Submodule F4 (Fin n → F4) :=
  Submodule.span F4 {w | ∃ u : ↥U₀, ∃ v : Fin n → F4, w = gl (u : SU n) • v - v}

private def C {n : ℕ} (U₀ : Subgroup (SU n)) : Submodule F4 (Fin n → F4) where
  carrier := {v | ∀ u : ↥U₀, gl (u : SU n) • v = v}
  zero_mem' u := by simp
  add_mem' {x y} hx hy u := by rw [smul_add, hx u, hy u]
  smul_mem' c x hx u := by rw [smul_comm, hx u]

private def R {n : ℕ} (U₀ : Subgroup (SU n)) : Submodule F4 (Fin n → F4) :=
  W U₀ ⊓ C U₀

private theorem mem_W_gen {n : ℕ} {U₀ : Subgroup (SU n)} (u : ↥U₀) (v : Fin n → F4) :
    gl (u : SU n) • v - v ∈ W U₀ :=
  Submodule.subset_span ⟨u, v, rfl⟩

private theorem mem_C_iff {n : ℕ} {U₀ : Subgroup (SU n)} {v : Fin n → F4} :
    v ∈ C U₀ ↔ ∀ u : ↥U₀, gl (u : SU n) • v = v := Iff.rfl

private theorem mem_R_iff {n : ℕ} {U₀ : Subgroup (SU n)} {v : Fin n → F4} :
    v ∈ R U₀ ↔ v ∈ W U₀ ∧ v ∈ C U₀ := Submodule.mem_inf

private theorem W_smul_mem {n : ℕ} {U₀ : Subgroup (SU n)} (u : ↥U₀) {w : Fin n → F4}
    (hw : w ∈ W U₀) : gl (u : SU n) • w ∈ W U₀ := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro w ⟨u', v, rfl⟩
    have h : gl (u : SU n) • (gl (u' : SU n) • v - v) =
        gl ((u * u' * u⁻¹ : ↥U₀) : SU n) • (gl (u : SU n) • v) - gl (u : SU n) • v := by
      rw [smul_sub, smul_smul, smul_smul]
      congr 1
      change gl ((u * u' : ↥U₀) : SU n) • v = gl (((u * u' * u⁻¹) * u : ↥U₀) : SU n) • v
      rw [show ((u * u' * u⁻¹) * u : ↥U₀) = u * u' from by group]
    rw [h]
    exact Submodule.subset_span ⟨u * u' * u⁻¹, gl (u : SU n) • v, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [smul_add]
    exact (W U₀).add_mem hx hy
  · intro c x _ hx
    rw [smul_comm]
    exact (W U₀).smul_mem c hx

private def repOnW {n : ℕ} (U₀ : Subgroup (SU n)) : Representation F4 ↥U₀ ↥(W U₀) where
  toFun u := (Matrix.mulVecLin (gl (u : SU n) : Matrix (Fin n) (Fin n) F4)).restrict
    (fun w hw => W_smul_mem u hw)
  map_one' := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [Matrix.mulVecLin]
  map_mul' u v := by
    apply LinearMap.ext
    intro w
    rw [Module.End.mul_apply]
    apply Subtype.ext
    change (gl (u : SU n) * gl (v : SU n)) • (w : Fin n → F4) =
      gl (u : SU n) • (gl (v : SU n) • (w : Fin n → F4))
    rw [mul_smul]

private theorem repOnW_apply {n : ℕ} (U₀ : Subgroup (SU n)) (u : ↥U₀) (w : ↥(W U₀)) :
    ((repOnW U₀ u w : ↥(W U₀)) : Fin n → F4) = gl (u : SU n) • (w : Fin n → F4) := rfl

private theorem W_ne_bot {n : ℕ} {U₀ : Subgroup (SU n)} (hU0 : U₀ ≠ ⊥) :
    W U₀ ≠ ⊥ := by
  obtain ⟨u, huU, hu1⟩ := U₀.bot_or_exists_ne_one.resolve_left hU0
  have hgl : gl u ≠ 1 := by
    intro h
    exact hu1 (Subtype.ext (Units.ext (by simpa using h)))
  obtain ⟨v, hv⟩ := exists_smul_ne_self hgl
  have hmem : gl u • v - v ∈ W U₀ := mem_W_gen ⟨u, huU⟩ v
  intro hbot
  rw [hbot] at hmem
  have hzero : gl u • v - v = 0 := by simpa using hmem
  exact hv (sub_eq_zero.mp hzero)

private theorem conj_mem_normalizer {n : ℕ} {U₀ : Subgroup (SU n)} {e : SU n}
    (he : e ∈ Subgroup.normalizer (U₀ : Set (SU n))) (u : ↥U₀) :
    e * (u : SU n) * e⁻¹ ∈ U₀ :=
  (Subgroup.mem_normalizer_iff.mp he (u : SU n)).mp u.2

private theorem W_smul_mem_E {n : ℕ} {E : Subgroup (GL (Fin n) F4)}
    {U₀ : Subgroup (SU n)}
    (hE : ∀ e ∈ E, ∀ u ∈ U₀, ∃ u' ∈ U₀,
      e * (u : GL (Fin n) F4) * e⁻¹ = (u' : GL (Fin n) F4))
    {e : GL (Fin n) F4} (he : e ∈ E) {w : Fin n → F4} (hw : w ∈ W U₀) :
    e • w ∈ W U₀ := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro w ⟨u, v, rfl⟩
    obtain ⟨u', hu', hconj⟩ := hE e he u u.2
    have h2 : e * gl (u : SU n) = gl (u' : SU n) * e := by
      calc e * gl (u : SU n) = e * gl (u : SU n) * e⁻¹ * e := by group
        _ = gl (u' : SU n) * e := by rw [hconj]
    have h : e • (gl (u : SU n) • v - v) =
        gl (u' : SU n) • (e • v) - e • v := by
      rw [smul_sub, smul_smul, smul_smul, h2]
    rw [h]
    exact Submodule.subset_span ⟨⟨u', hu'⟩, e • v, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [smul_add]
    exact (W U₀).add_mem hx hy
  · intro c x _ hx
    rw [smul_comm]
    exact (W U₀).smul_mem c hx

private theorem C_smul_mem_E {n : ℕ} {E : Subgroup (GL (Fin n) F4)}
    {U₀ : Subgroup (SU n)}
    (hE : ∀ e ∈ E, ∀ u ∈ U₀, ∃ u' ∈ U₀,
      e * (u : GL (Fin n) F4) * e⁻¹ = (u' : GL (Fin n) F4))
    {e : GL (Fin n) F4} (he : e ∈ E) {c : Fin n → F4} (hc : c ∈ C U₀) :
    e • c ∈ C U₀ := by
  rw [mem_C_iff] at hc ⊢
  intro u
  obtain ⟨u', hu', hconj⟩ := hE e⁻¹ (E.inv_mem he) u u.2
  simp only [inv_inv] at hconj
  have hfix : gl (u' : SU n) • c = c := hc ⟨u', hu'⟩
  have h1 : (u : GL (Fin n) F4) • (e • c) =
      e • ((u' : GL (Fin n) F4) • c) := by
    rw [smul_smul, smul_smul, ← hconj]
    congr 1
    group
  rw [h1, hfix]

private theorem R_smul_mem_E {n : ℕ} {E : Subgroup (GL (Fin n) F4)}
    {U₀ : Subgroup (SU n)}
    (hE : ∀ e ∈ E, ∀ u ∈ U₀, ∃ u' ∈ U₀,
      e * (u : GL (Fin n) F4) * e⁻¹ = (u' : GL (Fin n) F4))
    {e : GL (Fin n) F4} (he : e ∈ E) {x : Fin n → F4} (hx : x ∈ R U₀) :
    e • x ∈ R U₀ :=
  mem_R_iff.2 ⟨W_smul_mem_E hE he hx.1, C_smul_mem_E hE he hx.2⟩

private theorem R_ne_bot {n : ℕ} {U₀ : Subgroup (SU n)} (hU0p : IsPGroup 2 ↥U₀)
    (hU0 : U₀ ≠ ⊥) : R U₀ ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : W U₀ ≠ ⊥ := W_ne_bot hU0
  haveI : Nontrivial ↥(W U₀) := Submodule.nontrivial_iff_ne_bot.2 hW
  have hfix : (repOnW U₀).invariants ≠ ⊥ := by
    refine Representation.invariants_ne_bot_of_forall_pow_eq_one 2 (repOnW U₀) ?_
    intro g
    obtain ⟨m, hm⟩ := hU0p g
    exact ⟨m, by rw [← map_pow, hm, map_one]⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  have hwW : (w : Fin n → F4) ∈ W U₀ := w.2
  have hwC : (w : Fin n → F4) ∈ C U₀ := by
    rw [mem_C_iff]
    intro u
    have h1 := congrArg Subtype.val ((Representation.mem_invariants (repOnW U₀) w).mp hw u)
    rw [repOnW_apply] at h1
    exact h1
  have hwR : (w : Fin n → F4) ∈ R U₀ := mem_R_iff.2 ⟨hwW, hwC⟩
  have hwne : (w : Fin n → F4) ≠ 0 := by
    intro h
    exact hw0 (Subtype.ext h)
  intro hR
  apply hwne
  have hmem := hwR
  rw [hR] at hmem
  simpa using hmem

private theorem H_eq_zero_of_mem_C_of_mem_W {n : ℕ} {U₀ : Subgroup (SU n)}
    {c w : Fin n → F4} (hc : c ∈ C U₀) (hw : w ∈ W U₀) : H c w = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro w ⟨u, v, rfl⟩
    rw [mem_C_iff] at hc
    have hleft : gl (u : SU n) • (gl ((u⁻¹ : ↥U₀) : SU n) • c) = c := by
      rw [smul_smul]
      simp
    have hiso := H_smul_smul (u : SU n) (gl ((u⁻¹ : ↥U₀) : SU n) • c) v
    rw [hleft, hc (u⁻¹)] at hiso
    have hiso' : herm USig c (gl (u : SU n) • v) = herm USig c v := hiso
    change herm USig c (gl (u : SU n) • v - v) = 0
    rw [herm_sub_right, hiso', sub_self]
  · simp
  · intro x y _ _ hx hy
    have hx' : herm USig c x = 0 := hx
    have hy' : herm USig c y = 0 := hy
    change herm USig c (x + y) = 0
    rw [herm_add_right, hx', hy', add_zero]
  · intro a x _ hx
    have hx' : herm USig c x = 0 := hx
    change herm USig c (a • x) = 0
    rw [herm_smul_right, hx', mul_zero]

private theorem H_self_eq_zero_of_mem_R {n : ℕ} {U₀ : Subgroup (SU n)}
    {c : Fin n → F4} (hc : c ∈ R U₀) : H c c = 0 := by
  rw [mem_R_iff] at hc
  exact H_eq_zero_of_mem_C_of_mem_W hc.2 hc.1

private theorem primRoot_omega : IsPrimitiveRoot (F4.ω) 3 := by
  have hω3 : F4.ω ^ 3 = 1 := by rfl
  have hω1 : F4.ω ≠ 1 := by
    intro h
    exact absurd (congrArg F4.code h) (by decide)
  exact IsPrimitiveRoot.mk hω3 fun l hl => by
    have hord : orderOf (F4.ω) = 3 := orderOf_eq_prime hω3 hω1
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hl

private def repOf {n : ℕ} (E : Subgroup (GL (Fin n) F4)) :
    Representation F4 ↥E (Fin n → F4) where
  toFun e := Matrix.mulVecLin ((e : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4)
  map_one' := by
    apply LinearMap.ext
    intro v
    simp [Matrix.mulVecLin]
  map_mul' u v := by
    apply LinearMap.ext
    intro x
    rw [Module.End.mul_apply]
    change Matrix.mulVecLin (((u * v : ↥E) : GL (Fin n) F4) :
        Matrix (Fin n) (Fin n) F4) x =
      Matrix.mulVecLin ((u : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4)
        (Matrix.mulVecLin ((v : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4) x)
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]

private theorem exists_common_eigen_R {n : ℕ} {E : Subgroup (GL (Fin n) F4)}
    {U₀ : Subgroup (SU n)}
    (hE : ∀ e ∈ E, ∀ u ∈ U₀, ∃ u' ∈ U₀,
      e * (u : GL (Fin n) F4) * e⁻¹ = (u' : GL (Fin n) F4))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ e ∈ E, e ^ 3 = 1)
    (hU0p : IsPGroup 2 ↥U₀) (hU0 : U₀ ≠ ⊥) :
    ∃ x ∈ R U₀, x ≠ 0 ∧ ∀ e : ↥E, ∃ c : F4, (e : GL (Fin n) F4) • x = c • x := by
  have hcommT : ∀ e f : ↥E, repOf E e * repOf E f = repOf E f * repOf E e := by
    intro e f
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hcomm (e : GL (Fin n) F4) e.2 (f : GL (Fin n) F4) f.2
  have hpowT : ∀ e : ↥E, repOf E e ^ 3 = 1 := by
    intro e
    rw [← map_pow]
    have he3 : e ^ 3 = 1 := Subtype.ext (hexp (e : GL (Fin n) F4) e.2)
    rw [he3, map_one]
  have hstab : ∀ e : ↥E, ∀ w ∈ R U₀, repOf E e w ∈ R U₀ := by
    intro e w hw
    exact R_smul_mem_E hE e.2 hw
  obtain ⟨x, hxR, hx0, hxeig⟩ :=
    CFSG.RankThree.PartOne.S15K.exists_common_eigenvector (E := F4) (W := Fin n → F4)
      (p := 3) (by norm_num) primRoot_omega (fun e : ↥E => repOf E e) hcommT hpowT
      (R_ne_bot hU0p hU0) hstab
  refine ⟨x, hxR, hx0, fun e => ?_⟩
  obtain ⟨c, hc⟩ := hxeig e
  exact ⟨c, hc⟩

theorem exists_isotropic_common_eigenvector {n : ℕ} (E : Subgroup (GL (Fin n) F4))
    (U₀ : Subgroup ↥(StatedSU n (2 ^ 1) F4))
    (hE : ∀ e ∈ E, ∀ u ∈ U₀, ∃ u' ∈ U₀,
      e * (u : GL (Fin n) F4) * e⁻¹ = (u' : GL (Fin n) F4))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ e ∈ E, e ^ 3 = 1)
    (hU0p : IsPGroup 2 ↥U₀) (hU0 : U₀ ≠ ⊥) :
    ∃ x : Fin n → F4, x ≠ 0 ∧ ∑ i, x i ^ 3 = 0 ∧
      ∀ e ∈ E, ∃ c : F4, (e : Matrix (Fin n) (Fin n) F4) *ᵥ x = c • x := by
  obtain ⟨x, hxR, hx0, hxeig⟩ := exists_common_eigen_R hE hcomm hexp hU0p hU0
  have hsum : H x x = ∑ i, x i ^ 3 := by
    rw [H_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨x, hx0, ?_, ?_⟩
  · rw [← hsum]
    exact H_self_eq_zero_of_mem_R hxR
  · intro e he
    obtain ⟨c, hc⟩ := hxeig ⟨e, he⟩
    exact ⟨c, hc⟩

private theorem exists_common_eigen_R_SU {n : ℕ} {E U₀ : Subgroup (SU n)}
    (hE : E ≤ Subgroup.normalizer (U₀ : Set (SU n)))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ e ∈ E, e ^ 3 = 1)
    (hU0p : IsPGroup 2 ↥U₀) (hU0 : U₀ ≠ ⊥) :
    ∃ x ∈ R U₀, x ≠ 0 ∧ ∀ e : ↥E, ∃ c : F4, gl (e : SU n) • x = c • x := by
  let E' : Subgroup (GL (Fin n) F4) := E.map (Subgroup.subtype (StatedSU n (2 ^ 1) F4))
  have hE' : ∀ e ∈ E', ∀ u ∈ U₀, ∃ u' ∈ U₀,
      e * (u : GL (Fin n) F4) * e⁻¹ = (u' : GL (Fin n) F4) := by
    intro e he u hu
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    refine ⟨e₀ * u * e₀⁻¹, conj_mem_normalizer (hE he₀) ⟨u, hu⟩, ?_⟩
    rfl
  have hcomm' : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    simpa using congrArg (Subgroup.subtype (StatedSU n (2 ^ 1) F4))
      (hcomm a₀ ha₀ b₀ hb₀)
  have hexp' : ∀ e ∈ E', e ^ 3 = 1 := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    simpa using congrArg (Subgroup.subtype (StatedSU n (2 ^ 1) F4)) (hexp e₀ he₀)
  obtain ⟨x, hxR, hx0, hxeig⟩ :=
    exists_common_eigen_R (E := E') (U₀ := U₀) hE' hcomm' hexp' hU0p hU0
  refine ⟨x, hxR, hx0, fun e => ?_⟩
  obtain ⟨c, hc⟩ := hxeig ⟨(e : SU n), Subgroup.mem_map.mpr ⟨(e : SU n), e.2, rfl⟩⟩
  exact ⟨c, hc⟩

private def transvection {n : ℕ} (x : Fin n → F4) (hx : H x x = 0) : SU n :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := 1) (by
    rw [Nat.card_eq_fintype_card, F4.card]; norm_num) n)
    (CFSG.ClassicalGroups.Unitary.tv USig_invol hx USig_one_add_one)

private theorem transvection_matrix {n : ℕ} (x : Fin n → F4) (hx : H x x = 0) :
    mat (transvection x hx) = CFSG.ClassicalGroups.Unitary.tvMat USig x 1 := rfl

private theorem transvection_sq {n : ℕ} (x : Fin n → F4) (hx : H x x = 0) :
    transvection x hx ^ 2 = 1 := by
  rw [transvection]
  rw [← map_pow]
  have htv : CFSG.ClassicalGroups.Unitary.tv USig_invol hx USig_one_add_one ^ 2 = 1 := by
    rw [pow_two]
    rw [CFSG.ClassicalGroups.Unitary.tv_mul_tv USig_invol hx USig_one_add_one
      USig_one_add_one (by rw [USig_apply]; rfl)]
    exact CFSG.ClassicalGroups.Unitary.tv_zero USig_invol hx (by simp)
  rw [htv, map_one]

private theorem transvection_ne_one {n : ℕ} (x : Fin n → F4) (hx : H x x = 0)
    (hx0 : x ≠ 0) : transvection x hx ≠ 1 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  intro h
  have hmat : mat (transvection x hx) = 1 := by
    rw [h]
    simp [mat]
  have hz : mat (transvection x hx) i i = 0 := by
    rw [transvection_matrix]
    have hx3 : x i ^ 3 = 1 := F4_pow_three_eq_one hi
    calc (CFSG.ClassicalGroups.Unitary.tvMat USig x 1) i i
        = 1 + x i * USig (x i) := by
          simp [CFSG.ClassicalGroups.Unitary.tvMat, Matrix.vecMulVec]
      _ = 1 + x i * x i ^ 2 := by rw [USig_apply]
      _ = 1 + x i ^ 3 := by ring
      _ = 1 + 1 := by rw [hx3]
      _ = 0 := F4_one_add_one
  rw [hmat] at hz
  simpa using hz

private theorem transvection_commute_apply {n : ℕ} {E : Subgroup (SU n)}
    (hexp : ∀ e ∈ E, e ^ 3 = 1) {x : Fin n → F4} (hx0 : x ≠ 0)
    (hxeig : ∀ e : ↥E, ∃ c : F4, gl (e : SU n) • x = c • x)
    {e : SU n} (he : e ∈ E) (v : Fin n → F4) :
    CFSG.ClassicalGroups.Unitary.tvMat USig x 1 *ᵥ (gl e • v) =
      gl e • (CFSG.ClassicalGroups.Unitary.tvMat USig x 1 *ᵥ v) := by
  obtain ⟨c, hc⟩ := hxeig ⟨e, he⟩
  have hce : gl e • x = c • x := hc
  have hc3 : c ^ 3 = 1 := by
    have hpow : ∀ k : ℕ, gl (e ^ k) • x = c ^ k • x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ']
        change (gl e * gl (e ^ k)) • x = c ^ (k + 1) • x
        rw [mul_smul, ih, smul_comm, hce, smul_smul, pow_succ]
    have h1 : c ^ 3 • x = x := by
      rw [← hpow 3, hexp e he]
      simp
    have h : (c ^ 3 - 1) • x = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hx0
  have hc4 : c ^ 4 = c := by
    calc c ^ 4 = c ^ 3 * c := by ring
      _ = 1 * c := by rw [hc3]
      _ = c := one_mul c
  have hsig : USig (c * c) = c := by
    rw [map_mul, USig_apply]
    calc c ^ 2 * c ^ 2 = c ^ 4 := by ring
      _ = c := hc4
  have hinv : e⁻¹ = e * e := by
    have he3 : e * (e * e) = 1 := by
      have := hexp e he
      rwa [pow_succ', pow_two] at this
    exact (eq_inv_of_mul_eq_one_right he3).symm
  have he2x : gl (e * e) • x = (c * c) • x := by
    change (gl e * gl e) • x = (c * c) • x
    rw [mul_smul, hce, smul_comm, hce, smul_smul]
  have hinvx : gl e⁻¹ • x = (c * c) • x := by
    rw [hinv]
    exact he2x
  have hiso := H_smul_smul e (gl e⁻¹ • x) v
  have hleft : gl e • (gl e⁻¹ • x) = x := by
    change gl e • ((gl e)⁻¹ • x) = x
    rw [smul_inv_smul]
  rw [hleft, hinvx] at hiso
  have hiso' : herm USig x (gl e • v) = herm USig ((c * c) • x) v := hiso
  rw [herm_smul_left, hsig] at hiso'
  rw [CFSG.ClassicalGroups.Unitary.tvMat_mulVec,
    CFSG.ClassicalGroups.Unitary.tvMat_mulVec]
  rw [hiso']
  simp only [one_mul]
  rw [smul_add, smul_comm (gl e) (herm USig x v) x, hce, smul_smul]
  exact congrArg (fun t => gl e • v + t) (by rw [mul_comm])

private theorem transvection_commute {n : ℕ} {E : Subgroup (SU n)}
    (hexp : ∀ e ∈ E, e ^ 3 = 1) {x : Fin n → F4} (hx : H x x = 0) (hx0 : x ≠ 0)
    (hxeig : ∀ e : ↥E, ∃ c : F4, gl (e : SU n) • x = c • x)
    {e : SU n} (he : e ∈ E) : transvection x hx * e = e * transvection x hx := by
  have hmat : mat (transvection x hx) * mat e = mat e * mat (transvection x hx) := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change CFSG.ClassicalGroups.Unitary.tvMat USig x 1 *ᵥ
        (gl e • (Pi.single j (1 : F4) : Fin n → F4)) =
      gl e • (CFSG.ClassicalGroups.Unitary.tvMat USig x 1 *ᵥ
        (Pi.single j (1 : F4) : Fin n → F4))
    exact transvection_commute_apply hexp hx0 hxeig he (Pi.single j (1 : F4))
  apply Subtype.ext
  apply Units.ext
  exact hmat

theorem suInvCent (n : ℕ) : SUInvCent n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro E U₀ hU0p hU0 hE hcomm hexp
    exfalso
    haveI : Subsingleton (SU 0) := inferInstance
    refine hU0 ((Subgroup.eq_bot_iff_forall U₀).2 ?_)
    intro x _
    exact Subsingleton.elim x 1
  · intro E U₀ hU0p hU0 hE hcomm hexp
    obtain ⟨x, hxR, hx0, hxeig⟩ := exists_common_eigen_R_SU hE hcomm hexp hU0p hU0
    have hx : H x x = 0 := H_self_eq_zero_of_mem_R hxR
    exact ⟨transvection x hx, transvection_sq x hx, transvection_ne_one x hx hx0,
      fun e he => transvection_commute hexp hx hx0 hxeig he⟩

theorem invCentOn_M5 : InvCentOn CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.M5 := by
  intro E U₀ s hEea hEcard hU0p hU0 hE hse hsne hnot
  exact suInvCent 5 E U₀ hU0p hU0 hE
    (fun a ha b hb => hEea.comm ha hb) (fun e he => hEea.2 e he)

end

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
