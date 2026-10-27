module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NLinAlg
public import CFSG.LinearAlgebra.QuadraticPieceDihedral
public import CFSG.RankThree.GF2n.DihedralCompl
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFrame

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

section Basic

theorem eq_zero_of_eq_add_of_add_self {K : Type*} [Field K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] {a b : V} (h : a = b + a) : b = 0 := by
  have h' := congrArg (fun z => z + a) h
  have h'' : a + a = b + a + a := h'
  rw [CFSG.RankThree.GF2n.add_self_eq_zero_of_charTwo K a, add_assoc,
    CFSG.RankThree.GF2n.add_self_eq_zero_of_charTwo K a, add_zero] at h''
  exact h''.symm

end Basic

section FixedSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
lemma fixedSpace_pow_two_eq_of_pow_three {x : V ≃ₗ[K] V} (hx3 : x ^ 3 = 1) :
    fixedSpace (x ^ 2) = fixedSpace x := by
  ext v
  rw [mem_fixedSpace, mem_fixedSpace]
  constructor
  · intro h
    have h' : x (x (x v)) = x v := congrArg (fun w => x w) h
    have h3v : x (x (x v)) = v := by
      have := congrArg (fun e : V ≃ₗ[K] V => e v) hx3
      simpa [pow_succ, pow_two, LinearEquiv.mul_apply] using this
    rw [h3v] at h'
    exact h'.symm
  · intro h
    simp [pow_two, LinearEquiv.mul_apply, h]

end FixedSpace

section Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
lemma polar_eq_zero_of_mem_fixedSpace_of_ker [CharP K 2] {x : V ≃ₗ[K] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {U : Submodule K V}
    (hUx2 : ∀ u ∈ U, x (x u) = x u + u) {w u : V} (hw : x w = w) (hu : u ∈ U) :
    QuadraticMap.polar Q w u = 0 := by
  have hx2O : x ^ 2 ∈ TauCeti.QuadraticMap.orthogonalGroup Q := pow_mem hxO 2
  have hx2w : x (x w) = w := by
    simp [hw]
  have hwu : QuadraticMap.polar Q w (x u) = QuadraticMap.polar Q w u := by
    have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hxO w u
    simpa [hw] using h
  have hwx2 : QuadraticMap.polar Q w (x (x u)) = QuadraticMap.polar Q w u := by
    have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx2O w u
    simpa [pow_two, LinearEquiv.mul_apply, hx2w] using h
  calc QuadraticMap.polar Q w u = QuadraticMap.polar Q w (x (x u)) := hwx2.symm
    _ = QuadraticMap.polar Q w (x u + u) := by rw [hUx2 u hu]
    _ = QuadraticMap.polar Q w (x u) + QuadraticMap.polar Q w u := by
        rw [QuadraticMap.polar_add_right]
    _ = QuadraticMap.polar Q w u + QuadraticMap.polar Q w u := by rw [hwu]
    _ = 0 := CFSG.RankThree.GF2n.add_self_eq_zero_of_charTwo K _

omit [FiniteDimensional K V] in
lemma disjoint_orthogonal_span_pair_of_polar_ne_zero [CharP K 2]
    {B : LinearMap.BilinForm K V} (hB : B.IsSymm) {u w : V} (huu : B u u = 0)
    (hww : B w w = 0) (huw : B u w ≠ 0) :
    Disjoint (K ∙ u ⊔ K ∙ w) (B.orthogonal (K ∙ u ⊔ K ∙ w)) := by
  rw [disjoint_iff_inf_le]
  intro p hp
  rw [Submodule.mem_bot]
  rcases Submodule.mem_sup.mp (Submodule.mem_inf.mp hp).1 with ⟨a, ha, b, hb, rfl⟩
  rcases Submodule.mem_span_singleton.mp ha with ⟨r, rfl⟩
  rcases Submodule.mem_span_singleton.mp hb with ⟨s, rfl⟩
  have hmem := (LinearMap.BilinForm.mem_orthogonal_iff.mp (Submodule.mem_inf.mp hp).2)
  have h1 : B (r • u + s • w) u = 0 := by
    rw [hB.eq]
    exact hmem u (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
  have h2 : B (r • u + s • w) w = 0 := by
    rw [hB.eq]
    exact hmem w (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  have h1' : s * B u w = 0 := by
    simpa [map_add, huu, hww, hB.eq, mul_comm] using h1
  have h2' : r * B u w = 0 := by
    simpa [map_add, huu, hww, mul_comm] using h2
  have hs : s = 0 := (mul_eq_zero.mp h1').resolve_right huw
  have hr : r = 0 := (mul_eq_zero.mp h2').resolve_right huw
  simp [hr, hs]

section Construction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
lemma bilinForm_eq_zero_of_forall_apply_self_eq_zero [CharP K 2]
    {B : LinearMap.BilinForm K V} (hB : B.IsSymm) {x : V ≃ₗ[K] V}
    (hxB : ∀ a b, B (x a) (x b) = B a b) {U : Submodule K V}
    (hUx2 : ∀ u ∈ U, x (x u) = x u + u) (hall : ∀ u ∈ U, B u (x u) = 0) :
    ∀ u ∈ U, ∀ u' ∈ U, B u u' = 0 := by
  intro u hu u' hu'
  have hsum := hall (u + u') (U.add_mem hu hu')
  have h1 : B u (x u') = B u' (x u) := by
    have h2 : B u (x u') + B u' (x u) = 0 := by
      simpa [map_add, hall u hu, hall u' hu', add_assoc, add_comm, add_left_comm] using hsum
    have h3 := congrArg (fun z => z + B u' (x u)) h2
    simpa [add_assoc, CFSG.RankThree.GF2n.add_self_eq_zero_of_charTwo K, add_zero] using h3
  have hstep : B u' (x u) = B u u' + B u (x u') := by
    calc B u' (x u) = B (x u') (x (x u)) := (hxB u' (x u)).symm
      _ = B (x u') (x u + u) := by rw [hUx2 u hu]
      _ = B (x u') (x u) + B (x u') u := by rw [map_add]
      _ = B u' u + B (x u') u := by rw [hxB u' u]
      _ = B u u' + B u (x u') := by rw [hB.eq u' u, hB.eq (x u') u]
  exact eq_zero_of_eq_add_of_add_self (K := K) (h1.trans hstep)

theorem exists_polar_apply_self_ne_zero [CharP K 2] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {x : V ≃ₗ[K] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {W U : Submodule K V}
    (hWU : IsCompl W U) (horth : ∀ w ∈ W, ∀ u ∈ U, QuadraticMap.polar Q w u = 0)
    (hUx2 : ∀ u ∈ U, x (x u) = x u + u) (hUdim : 0 < Module.finrank K U) :
    ∃ u ∈ U, QuadraticMap.polar Q u (x u) ≠ 0 := by
  by_contra hno
  have hxB : ∀ a b, (QuadraticMap.polarBilin Q) (x a) (x b) =
      (QuadraticMap.polarBilin Q) a b := by
    intro a b
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hxO a b
  have hallPolar : ∀ u ∈ U, QuadraticMap.polar Q u (x u) = 0 := by
    intro u hu
    by_contra h
    exact hno ⟨u, hu, h⟩
  have hall : ∀ u ∈ U, (QuadraticMap.polarBilin Q) u (x u) = 0 := by
    intro u hu
    simpa [QuadraticMap.polarBilin_apply_apply] using hallPolar u hu
  have hzero := bilinForm_eq_zero_of_forall_apply_self_eq_zero
    (QuadraticMap.isSymm_polarBilin Q) hxB hUx2 hall
  obtain ⟨u0, hu0ne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hUdim
  have hu0U : (u0 : V) ∈ U := u0.2
  have hrad : ∀ v, QuadraticMap.polar Q (u0 : V) v = 0 := by
    intro v
    obtain ⟨w, r, rfl⟩ := exists_coe_add_of_isCompl hWU v
    rw [QuadraticMap.polar_add_right]
    have hw0 : QuadraticMap.polar Q (u0 : V) (w : V) = 0 := by
      rw [QuadraticMap.polar_comm]
      exact horth w w.2 (u0 : V) hu0U
    have hr0 : QuadraticMap.polar Q (u0 : V) (r : V) = 0 := by
      simpa [QuadraticMap.polarBilin_apply_apply] using hzero (u0 : V) hu0U (r : V) r.2
    rw [hw0, hr0, add_zero]
  have hradB : ∀ v, (QuadraticMap.polarBilin Q) (u0 : V) v = 0 := fun v => by
    simpa [QuadraticMap.polarBilin_apply_apply] using hrad v
  exact hu0ne (Subtype.ext (hQ.1 (u0 : V) hradB))

omit [FiniteDimensional K V] in
lemma glue_mem_orthogonalGroup {Q : QuadraticForm K V} {P R : Submodule K V}
    (hc : IsCompl P R) (horth : ∀ p ∈ P, ∀ r ∈ R, QuadraticMap.polar Q p r = 0)
    {a : P ≃ₗ[K] P} {c : R ≃ₗ[K] R}
    (ha : ∀ p : P, Q (a p : V) = Q (p : V)) (hcQ : ∀ r : R, Q (c r : V) = Q (r : V)) :
    glue hc a c ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨p, r, rfl⟩ := exists_coe_add_of_isCompl hc v
  rw [glue_apply, QuadraticMap.map_add (⇑Q) (a p : V) (c r : V),
    QuadraticMap.map_add (⇑Q) (p : V) (r : V), ha p, hcQ r,
    horth (a p) (a p).2 (c r) (c r).2, horth p p.2 r r.2]


end Construction

end Orthogonal

section Aux

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

structure OrderThreeFixedData (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) where
  W : Submodule K V
  U : Submodule K V
  hW : W = fixedSpace x
  hWU : IsCompl W U
  hdimU : Module.finrank K U = Module.finrank K V - 8
  hUdim : 0 < Module.finrank K U
  hUx2 : ∀ u ∈ U, x (x u) = x u + u
  hUx : ∀ u ∈ U, x u ∈ U
  horth : ∀ w ∈ W, ∀ u ∈ U, QuadraticMap.polar Q w u = 0
  u : V
  huU : u ∈ U
  hbu : QuadraticMap.polar Q u (x u) ≠ 0

noncomputable def exists_orderThreeFixedData [FiniteDimensional K V] [CharP K 2]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {x : V ≃ₗ[K] V} (hx3 : orderOf x = 3)
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : Module.finrank K (fixedSpace x) = 8) (hdim : 12 ≤ Module.finrank K V) :
    OrderThreeFixedData K V Q x := by
  have h3 : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h31 : (3 : K) = 1 := by
      rw [show (3 : K) = (2 : K) + 1 by norm_num, h2, zero_add]
    rw [h31]
    exact one_ne_zero
  set T : Module.End K V := x.toLinearMap with hT
  have hT3 : T ^ 3 = 1 := by
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)) x 3
    rw [show x ^ 3 = 1 by rw [← hx3]; exact pow_orderOf_eq_one x, map_one] at h
    simpa [LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply, hT] using h.symm
  set W : Submodule K V := fixedSpace x with hW
  set U : Submodule K V := LinearMap.ker (T ^ 2 + T + 1) with hU
  have hWU : IsCompl W U := by
    rw [hW, hU]; exact
      CFSG.RankThree.PartTwo.Sec8.Hering88N.isCompl_ker_sub_one_ker_sq_add_add_one h3 T hT3
  have hdimU : Module.finrank K U = Module.finrank K V - 8 := by
    have h := Submodule.finrank_add_eq_of_isCompl hWU
    omega
  have hUdim : 0 < Module.finrank K U := by omega
  have hUx2 : ∀ u ∈ U, x (x u) = x u + u := by
    intro u hu
    rw [hU] at hu
    have h : T (T u) + T u + u = 0 := by
      simpa [pow_two, Module.End.mul_apply] using hu
    have h2 : T (T u) + (T u + u) = 0 := by rw [← h]; abel
    have h3 := congrArg (fun z => z + (T u + u)) h2
    simpa [hT, add_assoc, CFSG.RankThree.GF2n.add_self_eq_zero_of_charTwo K] using h3
  have hUx : ∀ u ∈ U, x u ∈ U := by
    intro u hu
    rw [hU] at hu ⊢
    rw [LinearMap.mem_ker] at hu ⊢
    have hcomm : (T ^ 2 + T + 1) * T = T * (T ^ 2 + T + 1) := by noncomm_ring
    have hxT : x u = T u := rfl
    rw [hxT]
    have h1 := (Module.End.mul_apply (f := T ^ 2 + T + 1) (g := T) u).symm
    rw [h1, hcomm, Module.End.mul_apply, hu, map_zero]
  have horth : ∀ w ∈ W, ∀ u ∈ U, QuadraticMap.polar Q w u = 0 := fun w hw u hu => by
    rw [hW, mem_fixedSpace] at hw
    exact polar_eq_zero_of_mem_fixedSpace_of_ker hxO hUx2 hw hu
  let hex := exists_polar_apply_self_ne_zero hQ hxO hWU horth hUx2 hUdim
  let u : V := hex.choose
  have huU : u ∈ U := hex.choose_spec.1
  have hbu : QuadraticMap.polar Q u (x u) ≠ 0 := hex.choose_spec.2
  exact ⟨W, U, hW, hWU, hdimU, hUdim, hUx2, hUx, horth, u, huU, hbu⟩


theorem exists_orderThreePlaneData [FiniteDimensional K V] [CharP K 2] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V}
    {u : V} (hbu : QuadraticMap.polar Q u (x u) ≠ 0) :
    ∃ P R : Submodule K V, Module.finrank K P = 2 ∧ IsCompl P R ∧
      P = Submodule.span K ({u} : Set V) ⊔ Submodule.span K ({x u} : Set V) ∧
      R = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P ∧
      (∀ p ∈ P, ∀ r ∈ R, QuadraticMap.polar Q p r = 0) := by
  have hu_ne : u ≠ 0 := fun h => hbu (by simp [h])
  have hxu_ne : x u ≠ 0 := fun h => hbu (by simp [h])
  have hxu_not : x u ∉ K ∙ u := by
    intro hmem
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    apply hbu
    have huu : (QuadraticMap.polarBilin Q) u u = 0 := by
      simpa [QuadraticMap.polarBilin_apply_apply] using polar_self_char_two Q u
    rw [QuadraticMap.polarBilin_apply_apply] at huu
    calc QuadraticMap.polar Q u (x u) = QuadraticMap.polar Q u (a • u) := by rw [ha]
      _ = a * QuadraticMap.polar Q u u := by
            rw [QuadraticMap.polar_smul_right, smul_eq_mul]
      _ = 0 := by rw [huu, mul_zero]
  let P : Submodule K V := Submodule.span K ({u} : Set V) ⊔ Submodule.span K ({x u} : Set V)
  have hPdim : Module.finrank K P = 2 := by
    change Module.finrank K ↥(Submodule.span K ({u} : Set V) ⊔
      Submodule.span K ({x u} : Set V)) = 2
    have hdisj : Disjoint (Submodule.span K ({u} : Set V)) (Submodule.span K ({x u} : Set V)) :=
      (Submodule.disjoint_span_singleton' hxu_ne).mpr hxu_not
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span K ({u} : Set V)) (Submodule.span K ({x u} : Set V))
    rw [hdisj.eq_bot, finrank_bot, finrank_span_singleton hu_ne,
      finrank_span_singleton hxu_ne, add_zero] at h
    omega
  have hPdisj : Disjoint P (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P) := by
    change Disjoint (Submodule.span K ({u} : Set V) ⊔ Submodule.span K ({x u} : Set V))
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
        (Submodule.span K ({u} : Set V) ⊔ Submodule.span K ({x u} : Set V)))
    exact disjoint_orthogonal_span_pair_of_polar_ne_zero (QuadraticMap.isSymm_polarBilin Q)
      (by simpa [QuadraticMap.polarBilin_apply_apply] using polar_self_char_two Q u)
      (by simpa [QuadraticMap.polarBilin_apply_apply] using polar_self_char_two Q (x u))
      (by simpa [QuadraticMap.polarBilin_apply_apply] using hbu)
  have hPnondeg : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) P).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal (QuadraticMap.polarBilin Q)
      (QuadraticMap.isSymm_polarBilin Q).isRefl hPdisj
  let R : Submodule K V := LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P
  have hPcompl : IsCompl P R :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (QuadraticMap.isSymm_polarBilin Q).isRefl hPnondeg
  have hRorth : ∀ p ∈ P, ∀ r ∈ R, QuadraticMap.polar Q p r = 0 := by
    intro p hp r hr
    change r ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P at hr
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hr) p hp
    simpa [QuadraticMap.polarBilin_apply_apply] using h
  exact ⟨P, R, hPdim, hPcompl, rfl, rfl, hRorth⟩

theorem plane_maps [CharP K 2] {x : V ≃ₗ[K] V} {P U : Submodule K V}
    {u : V} (hP : P = Submodule.span K ({u} : Set V) ⊔ Submodule.span K ({x u} : Set V))
    (hUx2 : ∀ u ∈ U, x (x u) = x u + u) (hUx : ∀ u ∈ U, x u ∈ U) (huU : u ∈ U) :
    (∀ p ∈ P, x p ∈ P) ∧ P ≤ U := by
  have hPx : ∀ p ∈ P, x p ∈ P := by
    intro p hp
    rw [hP] at hp
    rcases Submodule.mem_sup.mp hp with ⟨a, ha, b, hb, rfl⟩
    rcases Submodule.mem_span_singleton.mp ha with ⟨r, rfl⟩
    rcases Submodule.mem_span_singleton.mp hb with ⟨s, rfl⟩
    have hcalc : x (r • u + s • x u) = s • u + (r + s) • x u := by
      calc x (r • u + s • x u) = r • x u + s • (x u + u) := by
            rw [map_add, map_smul, map_smul, hUx2 u huU]
        _ = r • x u + (s • x u + s • u) := by rw [smul_add]
        _ = s • u + (r • x u + s • x u) := by
            rw [← add_assoc, add_comm (r • x u + s • x u) (s • u)]
        _ = s • u + (r + s) • x u := by rw [← add_smul]
    rw [hcalc, hP]
    refine Submodule.add_mem_sup ?_ ?_
    · exact Submodule.smul_mem (p := Submodule.span K ({u} : Set V)) (r := s)
        (Submodule.mem_span_singleton_self u)
    · exact Submodule.smul_mem (p := Submodule.span K ({x u} : Set V)) (r := r + s)
        (Submodule.mem_span_singleton_self (x u))
  have hPU : P ≤ U := by
    intro p hp
    rw [hP] at hp
    rcases Submodule.mem_sup.mp hp with ⟨a, ha, b, hb, rfl⟩
    rcases Submodule.mem_span_singleton.mp ha with ⟨r, rfl⟩
    rcases Submodule.mem_span_singleton.mp hb with ⟨s, rfl⟩
    exact U.add_mem (U.smul_mem r huU) (U.smul_mem s (hUx u huU))
  exact ⟨hPx, hPU⟩

theorem plane_invariance [CharP K 2] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    {P R : Submodule K V} (hx3' : x ^ 3 = 1)
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hPx : ∀ p ∈ P, x p ∈ P)
    (hR : R = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P) :
    (∀ p ∈ P, x.symm p ∈ P) ∧ (∀ r ∈ R, x r ∈ R) ∧ (∀ r ∈ R, x.symm r ∈ R) := by
  have hx_symm_apply : ∀ v : V, x.symm v = x (x v) := by
    intro v
    apply x.injective
    rw [x.apply_symm_apply]
    have h3 : x (x (x v)) = v := by
      have := congrArg (fun e : V ≃ₗ[K] V => e v) hx3'
      simpa [pow_succ, pow_two, LinearEquiv.mul_apply] using this
    exact h3.symm
  have hPx_inv : ∀ p ∈ P, x.symm p ∈ P := by
    intro p hp
    rw [hx_symm_apply p]
    exact hPx (x p) (hPx p hp)
  have hRx : ∀ r ∈ R, x r ∈ R := by
    intro r hr
    rw [hR] at hr
    rw [hR]
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hr ⊢
    intro p hp
    rw [QuadraticMap.polarBilin_apply_apply]
    have hxp : x.symm p ∈ P := hPx_inv p hp
    have h := hr (x.symm p) hxp
    rw [QuadraticMap.polarBilin_apply_apply] at h
    calc QuadraticMap.polar Q p (x r) = QuadraticMap.polar Q (x (x.symm p)) (x r) := by
          rw [LinearEquiv.apply_symm_apply]
      _ = QuadraticMap.polar Q (x.symm p) r :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hxO _ _
      _ = 0 := h
  have hRx_inv : ∀ r ∈ R, x.symm r ∈ R := by
    intro r hr
    rw [hx_symm_apply r]
    exact hRx (x r) (hRx r hr)
  exact ⟨hPx_inv, hRx, hRx_inv⟩

theorem exists_glueIsometry [FiniteDimensional K V] [CharP K 2]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    {W U P R : Submodule K V} (hx3' : x ^ 3 = 1)
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hPcompl : IsCompl P R)
    (hPx : ∀ p ∈ P, x p ∈ P) (hPx_inv : ∀ p ∈ P, x.symm p ∈ P)
    (hRx : ∀ r ∈ R, x r ∈ R) (hRx_inv : ∀ r ∈ R, x.symm r ∈ R)
    (hRorth : ∀ p ∈ P, ∀ r ∈ R, QuadraticMap.polar Q p r = 0)
    (hPU : P ≤ U) (horth : ∀ w ∈ W, ∀ u ∈ U, QuadraticMap.polar Q w u = 0)
    (hW : W = fixedSpace x) (hR : R = LinearMap.BilinForm.orthogonal
      (QuadraticMap.polarBilin Q) P) :
    ∃ y : V ≃ₗ[K] V, y ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ y ^ 3 = 1 ∧
      y * x = x * y ∧ (∀ v ∈ fixedSpace x, y v = v) ∧ (∀ p ∈ P, y p = x p) ∧
      (∀ r ∈ R, y r = r) := by
  let a : P ≃ₗ[K] P := restrictEquiv P x hPx hPx_inv
  let c : R ≃ₗ[K] R := restrictEquiv R x hRx hRx_inv
  let y : V ≃ₗ[K] V := glue hPcompl a 1
  have hxglue : x = glue hPcompl a c := by
    ext v
    obtain ⟨p, r, rfl⟩ := exists_coe_add_of_isCompl hPcompl v
    rw [glue_apply, coe_restrictEquiv, coe_restrictEquiv, map_add]
  have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    have ha : ∀ p : P, Q (a p : V) = Q (p : V) := fun p => by
      dsimp only [a]
      rw [coe_restrictEquiv]
      exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hxO) (p : V)
    exact glue_mem_orthogonalGroup hPcompl hRorth ha (fun r => rfl)
  have ha3 : a ^ 3 = 1 := by
    ext p; dsimp only [a]; rw [CFSG.LinearAlgebra.restrictEquiv_pow_apply, hx3']; rfl
  have hy3 : y ^ 3 = 1 := by
    dsimp only [y]
    rw [pow_three, ← glue_mul, ← glue_mul,
      show a * (a * a) = 1 by rw [← pow_three, ha3],
      show (1 : R ≃ₗ[K] R) * (1 * 1) = 1 by group, glue_one]
  have hycomm : y * x = x * y := by
    rw [hxglue]
    dsimp only [y]
    rw [← glue_mul, ← glue_mul, one_mul, mul_one]
  have hWR : W ≤ R := by
    intro w hw
    rw [hR, LinearMap.BilinForm.mem_orthogonal_iff]
    intro p hp
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact horth w hw p (hPU hp)
  have hyR : ∀ r ∈ R, y r = r := by
    intro r hr
    have h := glue_apply hPcompl a 1 (0 : P) ⟨r, hr⟩
    simpa using h
  have hyfix : ∀ v ∈ fixedSpace x, y v = v := by
    intro v hv
    exact hyR v (hWR (by rwa [← hW] at hv))
  have hyP : ∀ p ∈ P, y p = x p := by
    intro p hp
    have h := glue_apply hPcompl a 1 ⟨p, hp⟩ 0
    simpa only [a, y, coe_restrictEquiv, Submodule.coe_zero, add_zero, map_zero] using h
  exact ⟨y, hyO, hy3, hycomm, hyfix, hyP, hyR⟩

theorem not_mem_zpowers_of_glue {x y : V ≃ₗ[K] V} {u z : V} (hx3 : orderOf x = 3)
    (hx3' : x ^ 3 = 1) (hyz : y z = z) (hxz : x z ≠ z) (hx2z : (x ^ 2) z ≠ z)
    (hyu : y u = x u) (hxu_ne : x u ≠ u) : y ∉ Subgroup.zpowers x := by
  classical
  have hynot : y ∉ Subgroup.zpowers x := by
    intro hy
    have hxfin : IsOfFinOrder x :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hx3'⟩
    have hymem : y ∈ (Finset.range (orderOf x)).image (x ^ ·) :=
      (hxfin.mem_powers_iff_mem_range_orderOf).mp
        ((hxfin.mem_powers_iff_mem_zpowers).mpr hy)
    rw [hx3] at hymem
    obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hymem
    rw [Finset.mem_range] at hi
    interval_cases i
    · rw [pow_zero] at hiy
      have h1 : y = 1 := hiy.symm
      have h2 : y u = u := by simp [h1]
      exact hxu_ne (by rw [← hyu]; exact h2)
    · rw [pow_one] at hiy
      have h1 : y = x := hiy.symm
      rw [h1] at hyz
      exact hxz hyz
    · rw [pow_two] at hiy
      have h1 : y = x ^ 2 := by rw [← hiy, pow_two]
      rw [h1] at hyz
      exact hx2z hyz
  exact hynot

end Aux

section Main

variable {K : Type*} [Field K] [CharP K 2]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_isometry_of_fixedSpace_eight [Finite K]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : V ≃ₗ[K] V} (hx3 : orderOf x = 3)
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : Module.finrank K (fixedSpace x) = 8) (hdim : 12 ≤ Module.finrank K V) :
    ∃ y : V ≃ₗ[K] V, y ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ y ^ 3 = 1 ∧ y * x = x * y ∧
      (∀ v ∈ fixedSpace x, y v = v) ∧ y ∉ Subgroup.zpowers x := by
  classical
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  obtain ⟨W, U, hW, hWU, hdimU, hUdim, hUx2, hUx, horth, u, huU, hbu⟩ :=
    exists_orderThreeFixedData hQ hx3 hxO hfix hdim
  obtain ⟨P, R, hPdim, hPcompl, hP, hR, hRorth⟩ := exists_orderThreePlaneData hbu
  have huP : u ∈ P := by
    rw [hP]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)
  obtain ⟨hPx, hPU⟩ := plane_maps hP hUx2 hUx huU
  obtain ⟨hPx_inv, hRx, hRx_inv⟩ := plane_invariance hx3' hxO hPx hR
  obtain ⟨y, hyO, hy3, hycomm, hyfix, hyP, hyR⟩ :=
    exists_glueIsometry hx3' hxO hPcompl hPx hPx_inv hRx hRx_inv hRorth hPU horth hW hR
  have hRnotle : ¬ R ≤ W := by
    intro hRW
    have hdimR : Module.finrank K R = Module.finrank K V - 2 := by
      rw [hR]
      rw [LinearMap.BilinForm.finrank_orthogonal hQ P, hPdim]
    have hle := Submodule.finrank_mono hRW
    rw [hdimR, hW, hfix] at hle
    omega
  obtain ⟨z, hzR, hzW⟩ := SetLike.not_le_iff_exists.mp hRnotle
  have hyz : y z = z := hyR z hzR
  have hxz : x z ≠ z := by
    intro h
    apply hzW
    rw [hW, mem_fixedSpace]
    exact h
  have hx2z : (x ^ 2) z ≠ z := by
    intro h
    have h' : z ∈ fixedSpace (x ^ 2) := by rwa [mem_fixedSpace]
    rw [fixedSpace_pow_two_eq_of_pow_three hx3'] at h'
    exact hzW (hW ▸ h')
  have hxu_eq_ne : x u ≠ u := fun h => hbu (by
    rw [h]
    simpa [QuadraticMap.polarBilin_apply_apply] using polar_self_char_two Q u)
  have hynot : y ∉ Subgroup.zpowers x :=
    not_mem_zpowers_of_glue hx3 hx3' hyz hxz hx2z (hyP u huP) hxu_eq_ne
  refine ⟨y, hyO, hy3, hycomm, ?_, hynot⟩
  intro v hv
  exact hyfix v (hW ▸ hv)

end Main

end CFSG.HardMathSupport.Dickson.Sec6

end
