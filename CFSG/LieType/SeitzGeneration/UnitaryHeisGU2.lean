module

public import CFSG.LieType.SeitzGeneration.DicksonSplitPair
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

open scoped commutatorElement MatrixGroups

open CFSG.BenderSuzuki.MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank

namespace CFSG.LieType.SeitzGeneration

variable {ℓ f : ℕ} {K : Type} [Field K]

section SUTwo

variable {r : ℕ} [Fact r.Prime] [CharP K r] [Finite K]

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg in
private theorem nonempty_sl2_mulEquiv_su2 (hK : Nat.card K = (r ^ f) ^ 2) :
    Nonempty (SL(2, fixedSubfield K r f) ≃* StatedSU 2 (r ^ f) K) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
  exact ⟨((hypEquiv hζ0 hζ).trans (conjEquiv P hP)).trans
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 2))⟩

open CFSG.LieType.Steinberg in
private theorem card_su2 (hK : Nat.card K = (r ^ f) ^ 2) :
    Nat.card (StatedSU 2 (r ^ f) K) = r ^ f * ((r ^ f) ^ 2 - 1) := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su2 (f := f) hK
  rw [← Nat.card_congr e.toEquiv, card_specialLinearGroup_fin_two, card_fixedSubfield hK]

private theorem isPerfect_su2 (hK : Nat.card K = (r ^ f) ^ 2) (hq : 4 ≤ r ^ f) :
    Group.IsPerfect (StatedSU 2 (r ^ f) K) := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su2 (f := f) hK
  have : Group.IsPerfect SL(2, CFSG.LieType.Steinberg.fixedSubfield K r f) := by
    apply CFSG.LinearGroups.special_linear_dimension_two_perfect
    classical
    have : Fintype (CFSG.LieType.Steinberg.fixedSubfield K r f) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (CFSG.LieType.Steinberg.fixedSubfield K r f))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        CFSG.LieType.Steinberg.card_fixedSubfield hK]; exact hq)
    exact ⟨s, hs⟩
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

end SUTwo

theorem bar_mul_self_eq_pow (h : UnitaryFieldData ℓ f K) (x : K) :
    h.bar x * x = x ^ (ℓ ^ f + 1) := by
  rw [h.bar_apply, ← pow_succ]

abbrev gu2 (h : UnitaryFieldData ℓ f K) : Subgroup (GL (Fin 2) K) :=
  primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) K)

theorem mem_gu2 (h : UnitaryFieldData ℓ f K) {g : GL (Fin 2) K} :
    g ∈ gu2 h ↔
      ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [gu2, mem_primeFormUnitary, Matrix.mul_one]

theorem norm_det_of_mem_gu2 (h : UnitaryFieldData ℓ f K) {g : GL (Fin 2) K} (hg : g ∈ gu2 h) :
    h.bar (g : Matrix (Fin 2) (Fin 2) K).det * (g : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have h1 := congrArg Matrix.det ((mem_gu2 h).1 hg)
  have h2 : ((g : Matrix (Fin 2) (Fin 2) K).map h.bar).det =
      h.bar (g : Matrix (Fin 2) (Fin 2) K).det :=
    (RingHom.map_det h.bar (g : Matrix (Fin 2) (Fin 2) K)).symm
  rw [Matrix.det_mul, Matrix.det_transpose, h2, Matrix.det_one] at h1
  exact h1

noncomputable def gu2Det (h : UnitaryFieldData ℓ f K) : gu2 h →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp (gu2 h).subtype

theorem coe_gu2Det (h : UnitaryFieldData ℓ f K) (g : gu2 h) :
    (((gu2Det h g : Kˣ)) : K) = ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det := by
  simp [gu2Det, Matrix.GeneralLinearGroup.val_det_apply]

theorem diagHom_mem_gu2 (h : UnitaryFieldData ℓ f K) {u : Kˣ} (hu : h.bar (u : K) * u = 1) :
    (diagHom 2 ![u, 1] : GL (Fin 2) K) ∈ gu2 h := by
  rw [mem_gu2, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hu]

theorem range_gu2Det (h : UnitaryFieldData ℓ f K) :
    (gu2Det h).range = normOne K (ℓ ^ f) := by
  ext u
  rw [mem_normOne]
  constructor
  · rintro ⟨g, rfl⟩
    have := norm_det_of_mem_gu2 h g.2
    rw [bar_mul_self_eq_pow] at this
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_gu2Det, Units.val_one]
    exact this
  · intro hu
    have hu' : h.bar (u : K) * u = 1 := by
      rw [bar_mul_self_eq_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one]
    refine ⟨⟨diagHom 2 ![u, 1], diagHom_mem_gu2 h hu'⟩, ?_⟩
    apply Units.ext
    rw [coe_gu2Det]
    simp [coe_diagHom, Matrix.det_diagonal, Fin.prod_univ_two]

theorem card_gu2 (h : UnitaryFieldData ℓ f K) :
    Nat.card (gu2 h) = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) * (ℓ ^ f + 1) := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  have hker : Nat.card (gu2Det h).ker = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) := by
    rw [← card_su2 hK]
    refine Nat.card_congr
      { toFun := fun g => ⟨(g.1 : GL (Fin 2) K), ?_⟩
        invFun := fun g => ⟨⟨g.1, ?_⟩, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    · have hd : ((g.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
        have := g.2
        rw [MonoidHom.mem_ker] at this
        have h2 := congrArg (fun u : Kˣ => (u : K)) this
        simpa [coe_gu2Det] using h2
      exact (mem_unitarySU_iff h).2 ⟨hd, (mem_gu2 h).1 g.1.2⟩
    · exact (mem_gu2 h).2 ((mem_unitarySU_iff h).1 g.2).2
    · rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [coe_gu2Det]
      exact ((mem_unitarySU_iff h).1 g.2).1
  have hrange : Nat.card (gu2Det h).range = ℓ ^ f + 1 := by
    rw [range_gu2Det, card_normOne hK]
  rw [← Subgroup.card_ker_mul_card_range (gu2Det h), hker, hrange]

noncomputable def gu2Proj (h : UnitaryFieldData ℓ f K) : gu2 h →* PGL(Fin 2, K) :=
  ProjGenLinGroup.mk.comp (gu2 h).subtype

theorem mem_ker_gu2Proj (h : UnitaryFieldData ℓ f K) (g : gu2 h) :
    g ∈ (gu2Proj h).ker ↔ (g : GL (Fin 2) K) ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [MonoidHom.mem_ker]
  exact ProjGenLinGroup.mk_eq_one

theorem scalar_mem_gu2 (h : UnitaryFieldData ℓ f K) {u : Kˣ} (hu : h.bar (u : K) * u = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ gu2 h := by
  rw [mem_gu2, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hu]

theorem card_ker_gu2Proj (h : UnitaryFieldData ℓ f K) :
    Nat.card (gu2Proj h).ker = ℓ ^ f + 1 := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  rw [← card_normOne hK]
  symm
  refine Nat.card_eq_of_bijective
    (fun u => ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 2) (u : Kˣ), scalar_mem_gu2 h ?_⟩, ?_⟩)
    ⟨?_, ?_⟩
  · have := mem_normOne.1 u.2
    rw [bar_mul_self_eq_pow, ← Units.val_pow_eq_pow_val, this, Units.val_one]
  · rw [mem_ker_gu2Proj, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  · intro u u' huu'
    have h1 := congrArg (fun g : gu2 h => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0)
      (congrArg Subtype.val huu')
    simp [Matrix.scalar_apply] at h1
    exact Subtype.ext (Units.ext h1)
  · rintro ⟨⟨g, hg⟩, hker⟩
    have hc := (mem_ker_gu2Proj h ⟨g, hg⟩).1 hker
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨u, hu⟩ := hc
    refine ⟨⟨u, ?_⟩, ?_⟩
    · rw [mem_normOne]
      have h1 := (mem_gu2 h).1 hg
      have hu' : Matrix.GeneralLinearGroup.scalar (Fin 2) u = g := hu
      rw [← hu'] at h1
      have h2 := congrFun (congrFun h1 0) 0
      simp [Matrix.scalar_apply] at h2
      rw [← Units.val_eq_one, Units.val_pow_eq_pow_val, ← bar_mul_self_eq_pow]
      exact h2
    · exact Subtype.ext (Subtype.ext hu)

theorem card_range_gu2Proj (h : UnitaryFieldData ℓ f K) :
    Nat.card (gu2Proj h).range = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) := by
  have h1 := Subgroup.card_ker_mul_card_range (gu2Proj h)
  rw [card_ker_gu2Proj, card_gu2, mul_comm (ℓ ^ f * ((ℓ ^ f) ^ 2 - 1))] at h1
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h1

theorem isSquare_of_norm_one (h : UnitaryFieldData ℓ f K) {u : K} (hu : h.bar u * u = 1) :
    IsSquare u := by
  classical
  have hfin := h.finite
  have := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  rw [bar_mul_self_eq_pow] at hu
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hu
    exact zero_ne_one hu
  by_cases h2 : ringChar K = 2
  · exact FiniteField.isSquare_of_char_two h2 u
  · rw [FiniteField.isSquare_iff h2 hu0]
    have hcard : Fintype.card K = (ℓ ^ f) ^ 2 := by
      rw [← Nat.card_eq_fintype_card, h.card_eq_sq]
    have hℓ2 : ℓ ≠ 2 := by
      intro hh
      apply h2
      rw [ringChar.eq K ℓ, hh]
    have hodd : Odd (ℓ ^ f) := by
      refine Odd.pow ?_
      rcases h.prime.eq_two_or_odd' with h' | h'
      · exact absurd h' hℓ2
      · exact h'
    obtain ⟨m, hm⟩ := hodd
    have hexp : Fintype.card K / 2 = (ℓ ^ f + 1) * m := by
      rw [hcard, hm]
      have : (2 * m + 1) ^ 2 = 2 * ((2 * m + 1 + 1) * m) + 1 := by ring
      rw [this]
      omega
    rw [hexp, pow_mul, hu, one_pow]

theorem mk_mem_range_toPGL (g : GL (Fin 2) K)
    (hsq : IsSquare (g : Matrix (Fin 2) (Fin 2) K).det) :
    ProjGenLinGroup.mk g ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  obtain ⟨l, hl⟩ := hsq
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hl
    exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero hl
  set s : Kˣ := Units.mk0 l hl0
  let g' : GL (Fin 2) K := g * Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹
  have hdet : (g' : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp only [g', Units.val_mul, det_mul, hl, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Units.val_inv_eq_inv_val, Units.val_mk0, s]
    field_simp
  let A : Matrix.SpecialLinearGroup (Fin 2) K := ⟨g', hdet⟩
  refine ⟨(A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K), ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨s, Units.ext ?_⟩
  change (g' : Matrix (Fin 2) (Fin 2) K) *
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [← Units.val_mul]
  congr 1
  simp only [g']
  rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

theorem range_gu2Proj_le (h : UnitaryFieldData ℓ f K) :
    (gu2Proj h).range ≤
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  rintro _ ⟨g, rfl⟩
  exact mk_mem_range_toPGL _ (isSquare_of_norm_one h (norm_det_of_mem_gu2 h g.2))

theorem ker_gu2Proj_le_center (h : UnitaryFieldData ℓ f K) :
    (gu2Proj h).ker ≤ Subgroup.center (gu2 h) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hc := (mem_ker_gu2Proj h z).1 hz
  rw [Subgroup.mem_center_iff] at hc
  exact Subtype.ext (hc g)

theorem commutator_mem_of_index_le_two {G : Type*} [Group G] {T : Subgroup G}
    (hT0 : T.index ≠ 0) (hT : T.index ≤ 2) (x y : G) : ⁅x, y⁆ ∈ T := by
  have hi : T.index = 1 ∨ T.index = 2 := by omega
  rcases hi with hi | hi
  · rw [Subgroup.index_eq_one] at hi
    rw [hi]
    exact Subgroup.mem_top _
  · have := Subgroup.normal_of_index_eq_two hi
    have hcard : Nat.card (G ⧸ T) = 2 := by rw [← Subgroup.index_eq_card]; exact hi
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic (G ⧸ T) := isCyclic_of_prime_card hcard
    let : CommGroup (G ⧸ T) := IsCyclic.commGroup
    rw [← QuotientGroup.eq_one_iff]
    have h1 : (QuotientGroup.mk' T) ⁅x, y⁆ = ⁅QuotientGroup.mk' T x, QuotientGroup.mk' T y⁆ :=
      map_commutatorElement _ _ _
    have h2 : ⁅QuotientGroup.mk' T x, QuotientGroup.mk' T y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
    exact h1.trans h2

theorem commutatorElement_mul_central_right {G : Type*} [Group G] {a b w : G}
    (hw : w ∈ Subgroup.center G) : ⁅a, b * w⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff] at hw
  simp only [commutatorElement_def]
  calc a * (b * w) * a⁻¹ * (b * w)⁻¹ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [← hw a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central_left {G : Type*} [Group G] {a b z : G}
    (hz : z ∈ Subgroup.center G) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff] at hz
  simp only [commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [← hz b]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central {G : Type*} [Group G] {x y z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_central_right hw, commutatorElement_mul_central_left hz]

theorem su2_le_of_card_ge (h : UnitaryFieldData ℓ f K) (hq4 : 4 ≤ ℓ ^ f)
    (Y : Subgroup (gu2 h))
    (hcard : ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) ≤ 2 * Nat.card (Y.map (gu2Proj h))) :
    ∀ g : gu2 h, (g : GL (Fin 2) K) ∈ unitarySU ℓ f K 2 → g ∈ Y := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  set ψ := gu2Proj h with hψ
  set J := Y.map ψ with hJ
  set T : Subgroup (gu2 h) := J.comap ψ with hT
  have hJle : J ≤ ψ.range := Y.map_le_range ψ
  have hTJ : T.map ψ = J := Subgroup.map_comap_eq_self hJle
  have hkT : ψ.ker ≤ T := fun z hz => by
    show ψ z ∈ J
    rw [MonoidHom.mem_ker.1 hz]
    exact J.one_mem
  have h1 : ψ.ker.relIndex T * T.index = ψ.ker.index := Subgroup.relIndex_mul_index hkT
  rw [Subgroup.relIndex_ker, hTJ, Subgroup.index_ker, card_range_gu2Proj h] at h1
  have : Finite PGL(Fin 2, K) :=
    inferInstanceAs (Finite (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)))
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hindex : T.index ≤ 2 := by
    have : Nat.card J * T.index ≤ Nat.card J * 2 := by rw [h1]; linarith
    exact Nat.le_of_mul_le_mul_left this hJpos
  have hindex0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hSUle : unitarySU ℓ f K 2 ≤ gu2 h := fun g hg =>
    (mem_gu2 h).2 ((mem_unitarySU_iff h).1 hg).2
  set S : Subgroup (gu2 h) := (unitarySU ℓ f K 2).subgroupOf (gu2 h) with hS
  have hperf : Group.IsPerfect S := by
    have : Group.IsPerfect (unitarySU ℓ f K 2) :=
      isPerfect_su2 hK hq4
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hSUle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSUle).symm.surjective
  have hSS : ⁅S, S⁆ = S := Subgroup.commutator_eq_self
  have hST : S ≤ T := by
    rw [← hSS]
    exact Subgroup.commutator_le.2 fun x _ y _ => commutator_mem_of_index_le_two hindex0 hindex x y
  have hSY : S ≤ Y := by
    rw [← hSS]
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    obtain ⟨x', hx', hxx'⟩ := hST hx
    obtain ⟨y', hy', hyy'⟩ := hST hy
    have hz : x'⁻¹ * x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel]
    have hw : y'⁻¹ * y ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyy', inv_mul_cancel]
    have e : ⁅x, y⁆ = ⁅x', y'⁆ := by
      have hx2 : x = x' * (x'⁻¹ * x) := by group
      have hy2 : y = y' * (y'⁻¹ * y) := by group
      rw [hx2, hy2]
      exact commutatorElement_mul_central (ker_gu2Proj_le_center h hz) (ker_gu2Proj_le_center h hw)
    rw [e, commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hx' hy') (Y.inv_mem hx')) (Y.inv_mem hy')
  intro g hg
  exact hSY (Subgroup.mem_subgroupOf.2 hg)

theorem card_ge_of_pgl_pair {p f : ℕ} [Fact p.Prime] [CharP K p]
    [Finite K] (hK : Nat.card K = p ^ (2 * f)) (hp3 : p ≠ 3) (h17 : 17 ≤ p ^ f) {M : ℕ}
    (hM6 : 6 ≤ M) (hM : p ^ f + 1 ≤ 3 * M) (J : Subgroup PGL(Fin 2, K))
    (hJ : J ≤ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range)
    {A B : SpecialLinearGroup (Fin 2) K}
    (hA : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) ∈ J)
    (hB : ProjGenLinGroup.mk (SpecialLinearGroup.toGL B) ∈ J)
    {P : Matrix (Fin 2) (Fin 2) K} {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹])
    (hμM : M ≤ orderOf (μ ^ 2)) (hμq : (μ ^ 2) ^ (p ^ f + 1) = 1)
    (hB3 : 2 < orderOf (B : PSL2MatrixGroup K))
    (hno : ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False) :
    p ^ f * ((p ^ f) ^ 2 - 1) ≤ 2 * Nat.card J := by
  set ι := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K) with hι
  set H : Subgroup (PSL2MatrixGroup K) := J.comap ι with hH
  have hmap : H.map ι = J := Subgroup.map_comap_eq_self hJ
  have hcard : Nat.card H = Nat.card J := by
    rw [← hmap]
    exact Nat.card_congr
      (H.equivMapOfInjective ι ProjectiveSpecialLinearGroup.toPGL_injective).toEquiv
  have hAH : (A : PSL2MatrixGroup K) ∈ H := by
    show ι (A : PSL2MatrixGroup K) ∈ J
    rw [hι, ProjectiveSpecialLinearGroup.toPGL_mk]
    exact hA
  have hBH : (B : PSL2MatrixGroup K) ∈ H := by
    show ι (B : PSL2MatrixGroup K) ∈ J
    rw [hι, ProjectiveSpecialLinearGroup.toPGL_mk]
    exact hB
  rw [← hcard]
  exact card_ge_of_split_pair hK hp3 h17 hM6 hM H hAH hBH hP hAP hμM hμq hB3 hno

theorem card_image_ge (h : UnitaryFieldData ℓ f K) (hp3 : ℓ ≠ 3)
    (h17 : 17 ≤ ℓ ^ f) {M : ℕ} (hM6 : 6 ≤ M) (hM : ℓ ^ f + 1 ≤ 3 * M) (Y : Subgroup (gu2 h))
    {μ₁ μ₂ ν₁ ν₂ α β : K} (hμ₁ : h.bar μ₁ * μ₁ = 1) (hμ₂ : h.bar μ₂ * μ₂ = 1)
    (hν₁ : h.bar ν₁ * ν₁ = 1) (hν₂ : h.bar ν₂ * ν₂ = 1) (hαβ : h.bar α * α + h.bar β * β = 1)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hμM : M ≤ orderOf (μ₁ / μ₂)) (hν3 : 3 ≤ orderOf (ν₁ / ν₂))
    {A B : gu2 h}
    (hAm : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = diagonal ![μ₁, μ₂])
    (hBm : ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![ν₂ + (ν₁ - ν₂) * (α * h.bar α), (ν₁ - ν₂) * (α * h.bar β);
        (ν₁ - ν₂) * (β * h.bar α), ν₂ + (ν₁ - ν₂) * (β * h.bar β)])
    (hA : A ∈ Y) (hB : B ∈ Y) :
    ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) ≤ 2 * Nat.card (Y.map (gu2Proj h)) := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hne : ∀ x : K, h.bar x * x = 1 → x ≠ 0 := fun x hx h0 => by
    rw [h0, mul_zero] at hx
    exact zero_ne_one hx
  have hμ₁0 := hne _ hμ₁
  have hμ₂0 := hne _ hμ₂
  have hν₁0 := hne _ hν₁
  have hν₂0 := hne _ hν₂
  have hbα : h.bar α ≠ 0 := by simpa using hα
  have hbβ : h.bar β ≠ 0 := by simpa using hβ
  have hρ : μ₁ / μ₂ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hμM
    omega
  have hρν : ν₁ / ν₂ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hν3
    omega
  have hμ12 : μ₁ ≠ μ₂ := fun h1 => hρ (by rw [h1, div_self hμ₂0])
  have hν12 : ν₁ ≠ ν₂ := fun h1 => hρν (by rw [h1, div_self hν₂0])
  have hnorm : ∀ x y : K, h.bar x * x = 1 → h.bar y * y = 1 → h.bar ((x * y)⁻¹) * (x * y)⁻¹ = 1 :=
    fun x y hx hy => by
      rw [map_inv₀, map_mul, ← mul_inv]
      have : h.bar x * h.bar y * (x * y) = 1 := by
        linear_combination (h.bar y * y) * hx + hy
      rw [this, inv_one]
  obtain ⟨s, hs⟩ := isSquare_of_norm_one h (hnorm μ₁ μ₂ hμ₁ hμ₂)
  obtain ⟨s', hs'⟩ := isSquare_of_norm_one h (hnorm ν₁ ν₂ hν₁ hν₂)
  have hss : s * s * (μ₁ * μ₂) = 1 := by
    rw [← hs]
    exact inv_mul_cancel₀ (mul_ne_zero hμ₁0 hμ₂0)
  have hss' : s' * s' * (ν₁ * ν₂) = 1 := by
    rw [← hs']
    exact inv_mul_cancel₀ (mul_ne_zero hν₁0 hν₂0)
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hss
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    simp at hss'
  set Bmat : Matrix (Fin 2) (Fin 2) K :=
    !![ν₂ + (ν₁ - ν₂) * (α * h.bar α), (ν₁ - ν₂) * (α * h.bar β);
      (ν₁ - ν₂) * (β * h.bar α), ν₂ + (ν₁ - ν₂) * (β * h.bar β)] with hBmat
  have hdetB : Bmat.det = ν₁ * ν₂ := by
    rw [hBmat, Matrix.det_fin_two_of]
    linear_combination (ν₂ * (ν₁ - ν₂)) * hαβ
  let A' : SpecialLinearGroup (Fin 2) K := ⟨s • diagonal ![μ₁, μ₂], by
    rw [Matrix.det_smul, Matrix.det_diagonal, Fin.prod_univ_two]
    simp only [Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hss⟩
  let B' : SpecialLinearGroup (Fin 2) K := ⟨s' • Bmat, by
    rw [Matrix.det_smul, hdetB]
    simp only [Fintype.card_fin]
    linear_combination hss'⟩
  have hinvA : (s * μ₁)⁻¹ = s * μ₂ :=
    (eq_inv_of_mul_eq_one_right (by linear_combination hss : s * μ₁ * (s * μ₂) = 1)).symm
  have hinvB : (s' * ν₁)⁻¹ = s' * ν₂ :=
    (eq_inv_of_mul_eq_one_right (by linear_combination hss' : s' * ν₁ * (s' * ν₂) = 1)).symm
  have hAP : ((A' : Matrix (Fin 2) (Fin 2) K)) * (1 : Matrix (Fin 2) (Fin 2) K) =
      1 * diagonal ![s * μ₁, (s * μ₁)⁻¹] := by
    rw [hinvA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A']
  have hμsq : (s * μ₁) ^ 2 = μ₁ / μ₂ := by
    rw [eq_div_iff hμ₂0]
    linear_combination μ₁ * hss
  have hνsq : (s' * ν₁) ^ 2 = ν₁ / ν₂ := by
    rw [eq_div_iff hν₂0]
    linear_combination ν₁ * hss'
  have hpowne : ∀ x : K, h.bar x * x = 1 → x ^ (ℓ ^ f + 1) = 1 := fun x hx => by
    rw [← bar_mul_self_eq_pow]
    exact hx
  have hμM' : M ≤ orderOf ((s * μ₁) ^ 2) := by rw [hμsq]; exact hμM
  have hμq : ((s * μ₁) ^ 2) ^ (ℓ ^ f + 1) = 1 := by
    rw [hμsq, div_pow, hpowne _ hμ₁, hpowne _ hμ₂, div_one]
  let PB : Matrix (Fin 2) (Fin 2) K := !![α, -h.bar β; β, h.bar α]
  have hPB : PB.det ≠ 0 := by
    have : PB.det = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination hαβ
    rw [this]
    exact one_ne_zero
  have hBP : ((B' : Matrix (Fin 2) (Fin 2) K)) * PB = PB * diagonal ![s' * ν₁, (s' * ν₁)⁻¹] := by
    rw [hinvB]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B', Bmat, PB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;>
      first | ring1 | linear_combination (s' * α * (ν₁ - ν₂)) * hαβ |
        linear_combination (s' * β * (ν₁ - ν₂)) * hαβ
  have hB3 : 2 < orderOf (B' : PSL2MatrixGroup K) := by
    rw [orderOf_mk_eq hPB hBP, hνsq]
    omega
  have hno : ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A' : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B' : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False := by
    rintro x hx0 ⟨c, hc⟩ ⟨c', hc'⟩
    have hA0 := congrFun hc 0
    have hA1 := congrFun hc 1
    have hB0 := congrFun hc' 0
    have hB1 := congrFun hc' 1
    simp [A', B', Bmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hA0 hA1 hB0 hB1
    by_cases hx0' : x 0 = 0
    · have hx1' : x 1 ≠ 0 := fun h1 => hx0 (by
        ext i
        fin_cases i <;> simp [hx0', h1])
      rw [hx0'] at hB0
      have : s' * ((ν₁ - ν₂) * (α * h.bar β)) * x 1 = 0 := by simpa using hB0
      exact (mul_ne_zero (mul_ne_zero hs'0 (mul_ne_zero (sub_ne_zero.2 hν12)
        (mul_ne_zero hα hbβ))) hx1') this
    · by_cases hx1' : x 1 = 0
      · rw [hx1'] at hB1
        have : s' * ((ν₁ - ν₂) * (β * h.bar α)) * x 0 = 0 := by simpa using hB1
        exact (mul_ne_zero (mul_ne_zero hs'0 (mul_ne_zero (sub_ne_zero.2 hν12)
          (mul_ne_zero hβ hbα))) hx0') this
      · have h1 : s * μ₁ = c := hA0.resolve_right hx0'
        have h2 : s * μ₂ = c := hA1.resolve_right hx1'
        exact hμ12 (mul_left_cancel₀ hs0 (h1.trans h2.symm))
  have hmk : ∀ (g : gu2 h) (u : K) (hu : u ≠ 0) (T : SpecialLinearGroup (Fin 2) K),
      ((T : Matrix (Fin 2) (Fin 2) K) = u • ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) →
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL T) = gu2Proj h g := by
    intro g u hu T hT
    show _ = ProjGenLinGroup.mk (g : GL (Fin 2) K)
    symm
    rw [ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 u hu, Units.ext ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hT]
    ext i j
    simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
  have hAJ : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A') ∈ Y.map (gu2Proj h) := by
    rw [hmk A s hs0 A' (by rw [hAm])]
    exact Subgroup.mem_map_of_mem _ hA
  have hBJ : ProjGenLinGroup.mk (SpecialLinearGroup.toGL B') ∈ Y.map (gu2Proj h) := by
    rw [hmk B s' hs'0 B' (by rw [hBm])]
    exact Subgroup.mem_map_of_mem _ hB
  exact card_ge_of_pgl_pair h.card hp3 h17 hM6 hM (Y.map (gu2Proj h))
    ((Y.map_le_range (gu2Proj h)).trans (range_gu2Proj_le h)) hAJ hBJ
    (P := (1 : Matrix (Fin 2) (Fin 2) K)) (Matrix.det_one.trans_ne one_ne_zero) hAP
    (by rw [hμsq]; exact hμM) hμq hB3 hno

theorem su2_le_of_pair (h : UnitaryFieldData ℓ f K) (hp3 : ℓ ≠ 3)
    (h17 : 17 ≤ ℓ ^ f) {M : ℕ} (hM6 : 6 ≤ M) (hM : ℓ ^ f + 1 ≤ 3 * M)
    (Y : Subgroup (GL (Fin 2) K))
    {μ₁ μ₂ ν₁ ν₂ α β : K} (hμ₁ : h.bar μ₁ * μ₁ = 1) (hμ₂ : h.bar μ₂ * μ₂ = 1)
    (hν₁ : h.bar ν₁ * ν₁ = 1) (hν₂ : h.bar ν₂ * ν₂ = 1) (hαβ : h.bar α * α + h.bar β * β = 1)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hμM : M ≤ orderOf (μ₁ / μ₂)) (hν3 : 3 ≤ orderOf (ν₁ / ν₂))
    {A B : GL (Fin 2) K}
    (hAm : (A : Matrix (Fin 2) (Fin 2) K) = diagonal ![μ₁, μ₂])
    (hBm : (B : Matrix (Fin 2) (Fin 2) K) =
      !![ν₂ + (ν₁ - ν₂) * (α * h.bar α), (ν₁ - ν₂) * (α * h.bar β);
        (ν₁ - ν₂) * (β * h.bar α), ν₂ + (ν₁ - ν₂) * (β * h.bar β)])
    (hA : A ∈ Y) (hB : B ∈ Y) :
    ∀ g : GL (Fin 2) K, g ∈ unitarySU ℓ f K 2 → g ∈ Y := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hAu : A ∈ gu2 h := by
    rw [mem_gu2, hAm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hμ₁, hμ₂]
  have hBu : B ∈ gu2 h := by
    rw [mem_gu2, hBm]
    have e1 : h.bar (h.bar α) = α := h.bar_bar α
    have e2 : h.bar (h.bar β) = β := h.bar_bar β
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, e1, e2, map_sub, map_add, map_mul] <;> grind
  have hSUle : unitarySU ℓ f K 2 ≤ gu2 h := fun g hg =>
    (mem_gu2 h).2 ((mem_unitarySU_iff h).1 hg).2
  have hcard := card_image_ge h hp3 h17 hM6 hM (Y.subgroupOf (gu2 h)) hμ₁ hμ₂ hν₁ hν₂ hαβ hα hβ
    hμM hν3 (A := ⟨A, hAu⟩) (B := ⟨B, hBu⟩) hAm hBm hA hB
  have := su2_le_of_card_ge h (by omega) (Y.subgroupOf (gu2 h)) hcard
  intro g hg
  exact this ⟨g, hSUle hg⟩ hg

end CFSG.LieType.SeitzGeneration
