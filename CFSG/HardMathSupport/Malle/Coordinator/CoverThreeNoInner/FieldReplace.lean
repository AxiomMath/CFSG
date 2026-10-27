module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.YLevel
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.CoverIso
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Normal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharEx
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.RankThree.PartTwo.KFacts.AutPSL

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Foote.ModuleExclusions
open Matrix
open scoped MatrixGroups

theorem exists_sl3_equiv_of_cover {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    {F : Type} [Field F] [Finite F] (hF9 : 9 ∣ Nat.card F - 1)
    (ρ : K →* projectiveSL 3 F) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.center K) (hz : 3 ∣ Nat.card (Subgroup.center K)) :
    ∃ ψ : SL(3, F) ≃* K, ∀ g, ρ (ψ g) = proj 3 F g := by
  set ι := LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F with hι
  set ρ' : K →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F := ι.symm.toMonoidHom.comp ρ
    with hρ'
  have hker' : ρ'.ker = Subgroup.center K := by
    rw [← hker]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  obtain ⟨ψ, hψ⟩ := CFSG.HardMathSupport.Malle.Coordinator.CoverThree.exists_mulEquiv_sl3_of_cover_compat
    hF9 ρ' (ι.symm.surjective.comp hρ) hker' hz
  refine ⟨ψ, fun g => ?_⟩
  have h2 : ρ (ψ g) = ι (ρ' (ψ g)) := by
    rw [hρ']
    simp
  rw [h2, hψ g]
  rfl

section Action

variable {Y : Type*} [Group Y] {K : Subgroup Y} [hKn : K.Normal] {F : Type} [Field F]

@[expose] noncomputable def slAct (ψ : SL(3, F) ≃* K) (y : Y) : SL(3, F) →* SL(3, F) :=
  ψ.symm.toMonoidHom.comp ((MulAut.conjNormal y : MulAut K).toMonoidHom.comp ψ.toMonoidHom)

theorem coe_psi_slAct (ψ : SL(3, F) ≃* K) (y : Y) (g : SL(3, F)) :
    ((ψ (slAct ψ y g) : K) : Y) = y * (ψ g : Y) * y⁻¹ := by
  simp [slAct, MulAut.conjNormal_apply]

theorem proj_slAct (e : K ⧸ Subgroup.center K ≃* projectiveSL 3 F) (ψ : SL(3, F) ≃* K)
    (hψ : ∀ g, e (QuotientGroup.mk (ψ g)) = proj 3 F g) (y : Y) (g : SL(3, F)) :
    proj 3 F (slAct ψ y g) = modelAct K e y (proj 3 F g) := by
  have h2 : ψ (slAct ψ y g) = ⟨y * ψ g * y⁻¹, hKn.conj_mem _ (ψ g).2 y⟩ :=
    Subtype.ext (coe_psi_slAct ψ y g)
  rw [← hψ, h2, ← hψ g, modelAct_apply_mk]

@[expose] noncomputable def slTwist (B : GL (Fin 3) F) (σ : F ≃+* F) : MulAut SL(3, F) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F B *
    CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ *
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F B)⁻¹

theorem descendAut_slTwist (B : GL (Fin 3) F) (σ : F ≃+* F) :
    descendAut 3 F (slTwist B σ) = conjAut 3 F B * fieldAut 3 F σ * (conjAut 3 F B)⁻¹ := by
  simp only [slTwist, map_mul, map_inv]
  rfl

theorem slAct_eq_slTwist [Group.IsPerfect SL(3, F)]
    (e : K ⧸ Subgroup.center K ≃* projectiveSL 3 F) (ψ : SL(3, F) ≃* K)
    (hψ : ∀ g, e (QuotientGroup.mk (ψ g)) = proj 3 F g) {y : Y} {B : GL (Fin 3) F}
    {σ : F ≃+* F} (hy : modelAct K e y = conjAut 3 F B * fieldAut 3 F σ * (conjAut 3 F B)⁻¹)
    (g : SL(3, F)) : slAct ψ y g = slTwist B σ g := by
  set h : SL(3, F) →* SL(3, F) := ((slTwist B σ)⁻¹ : MulAut SL(3, F)).toMonoidHom.comp
    (slAct ψ y) with hh
  have hc : ∀ x : SL(3, F), x⁻¹ * h x ∈ Subgroup.center SL(3, F) := by
    intro x
    rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    change proj 3 F x = proj 3 F ((slTwist B σ)⁻¹ (slAct ψ y x))
    rw [← descendAut_proj, map_inv, proj_slAct e ψ hψ, hy, ← descendAut_slTwist,
      MulAut.inv_apply_self]
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    h hc
  have hg : (slTwist B σ)⁻¹ (slAct ψ y g) = g := by
    have := congrArg (fun f : SL(3, F) →* SL(3, F) => f g) hid
    exact this
  have h2 := congrArg (slTwist B σ) hg
  rwa [MulAut.apply_inv_self] at h2

end Action

section Helpers

variable {G : Type*} [Group G]

theorem card_sup_of_commute_disjoint (H K : Subgroup G)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, Commute h k) (hdisj : Disjoint H K) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let φ : H × K →* G := MonoidHom.noncommCoprod H.subtype K.subtype
    (fun h k => hcomm h.1 h.2 k.1 k.2)
  have hr : φ.range = H ⊔ K := by
    have := MonoidHom.noncommCoprod_range H.subtype K.subtype (fun h k => hcomm h.1 h.2 k.1 k.2)
    rw [Subgroup.range_subtype, Subgroup.range_subtype] at this
    exact this
  have hinj : Function.Injective φ := by
    refine (MonoidHom.noncommCoprod_injective H.subtype K.subtype
      (fun h k => hcomm h.1 h.2 k.1 k.2)).2 ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
    simpa only [Subgroup.range_subtype] using hdisj
  have h1 : Nat.card ↥(H ⊔ K) = Nat.card (H × K) := by
    rw [← hr]
    exact (Nat.card_congr (Equiv.ofInjective φ hinj)).symm
  rw [h1, Nat.card_prod]

theorem isElemAbelian_sup_zpowers {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) :
    IsElemAbelian 3 ((Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers c) := by
  have hcl : (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers c =
      Subgroup.closure ({a, b, c} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto
  have hpair : ({a, b, c} : Set G).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _ | exact hab | exact hab.symm | exact hac | exact hac.symm
      | exact hbc | exact hbc.symm
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b, c} : Set G)) :=
    Subgroup.isMulCommutative_closure hpair
  rw [hcl]
  refine ⟨hcomm, fun x hx => ?_⟩
  have hc' : ∀ x ∈ Subgroup.closure ({a, b, c} : Set G),
      ∀ y ∈ Subgroup.closure ({a, b, c} : Set G), x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (hc' x hx y hy) 3), ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem mem_of_zpow_mem_of_pow_three {H : Subgroup G} {x : G} (hx : x ^ 3 = 1) {k : ℤ}
    (hk : ¬ (3 : ℤ) ∣ k) (hxk : x ^ k ∈ H) : x ∈ H := by
  have hmod : k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hx3 : x ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hx
  have hred : x ^ k = x ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [_root_.zpow_add, _root_.zpow_mul, hx3, _root_.one_zpow, mul_one]
  rw [hred] at hxk
  rcases hmod with h | h
  · rw [h, zpow_one] at hxk
    exact hxk
  · rw [h] at hxk
    have : x = (x ^ (2 : ℤ)) ^ (2 : ℤ) * (x ^ (3 : ℤ))⁻¹ := by group
    rw [this, hx3, inv_one, mul_one]
    exact H.zpow_mem hxk 2

end Helpers

theorem apply_eq_of_pow_three_eq_one {F : Type} [Field F] {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {ω : F} (hω : ω ^ 3 = 1) : σ ω = ω := by
  have h3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσ3 : σ (σ (σ ω)) = ω := by
    have := congrArg (fun τ : F ≃+* F => τ ω) h3
    simpa [pow_succ, RingAut.mul_apply] using this
  have hω' : (σ ω) ^ 3 = 1 := by rw [← map_pow, hω, map_one]
  by_cases h1 : ω = 1
  · rw [h1, map_one]
  have hsum : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h1
    · exact h
  have hfac : (σ ω - ω) * (σ ω - ω ^ 2) * (σ ω - 1) = 0 := by
    linear_combination hω' + (σ ω - σ ω ^ 2) * hsum + (σ ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  rcases mul_eq_zero.1 hfac with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact sub_eq_zero.1 h
    · exfalso
      have h2 : σ ω = ω ^ 2 := sub_eq_zero.1 h
      have h4 : σ (σ ω) = ω := by
        rw [h2, map_pow, h2]
        linear_combination ω * hω
      rw [h4, h2] at hσ3
      have : ω * (ω - 1) = 0 := by linear_combination hσ3
      rcases mul_eq_zero.1 this with h | h
      · exact hω0 h
      · exact h1 (sub_eq_zero.1 h)
  · exfalso
    have h2 : σ ω = 1 := sub_eq_zero.1 h
    exact h1 (σ.injective (h2.trans (map_one σ).symm))

@[expose] noncomputable def diagHom (F : Type) [Field F] : (Fin 3 → Fˣ) →* GL (Fin 3) F where
  toFun := diagGL
  map_one' := by
    apply Units.ext
    rw [coe_diagGL]
    simp
  map_mul' d d' := by
    apply Units.ext
    rw [Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, Matrix.diagonal_mul_diagonal]
    simp

theorem coverThreeNoInnerFieldLinear_holds : CoverThreeNoInnerFieldLinear := by
  intro Y _ _ Rb Y₀ h K _ hK hC hcent hZ3 F _ _ h3 e E hER hEN hEa hEc hEKC hout
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ := modelAct K e with hφ
  obtain ⟨y, hyE, hyout⟩ : ∃ y ∈ E, φ y ∉ linearAutGroup 3 F := by
    by_contra hcon
    push Not at hcon
    exact hout (by rintro _ ⟨y, hy, rfl⟩; exact hcon y hy)
  have hy3 : y ^ 3 = 1 := hEa.2 y hyE
  have hφy3 : φ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  obtain ⟨A, σ, hA, hσ3⟩ := exists_semilinear_of_cube_eq_one (n := 3) (K := F) le_rfl hφy3
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hyout
    rw [hA, map_one, mul_one]
    exact conjAut_mem_linearAutGroup A
  obtain ⟨hσ, B, hB⟩ := exists_conj_fieldAut_of_cube_eq_one (n := 3) le_rfl hφy3 σ A hA hσ1 hσ3
  have hF9 : 9 ∣ Nat.card F - 1 := by
    have hq := natCard_eq_pow_three hσ
    have hq₀ : 1 ≤ Nat.card (fixF σ) := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
    have h3₀ : 3 ∣ Nat.card (fixF σ) - 1 := three_dvd_sub_one_of_pow_three hq₀ (hq ▸ h3)
    obtain ⟨t, ht⟩ := h3₀
    have ht' : Nat.card (fixF σ) = 3 * t + 1 := by omega
    have hpow : (3 * t + 1) ^ 3 = 9 * (3 * t ^ 3 + 3 * t ^ 2 + t) + 1 := by ring
    rw [hq, ht', hpow, Nat.add_sub_cancel]
    exact Dvd.intro _ rfl
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  have hz3 : 3 ∣ Nat.card (Subgroup.center K) := by
    have hpos : Nat.card (Subgroup.center K) ≠ 0 := Nat.card_pos.ne'
    exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hpos).2 (by rw [hZ3])
  set ρ : K →* projectiveSL 3 F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hρ
  have hρs : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψ⟩ := exists_sl3_equiv_of_cover hF9 ρ hρs hρk hz3
  have hψ' : ∀ g, e (QuotientGroup.mk (ψ g)) = proj 3 F g := hψ
  have : Group.IsPerfect SL(3, F) :=
    Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
  have hact := fun g => slAct_eq_slTwist e ψ hψ' (y := y) hB g
  obtain ⟨ζ, hζ⟩ := CFSG.HardMathSupport.Malle.Coordinator.CoverThree.exists_primitiveRoot_nine
    (F := F) hF9
  have hω : IsPrimitiveRoot (ζ ^ 3) 3 := by
    simpa using hζ.pow_of_dvd (by norm_num : (3 : ℕ) ≠ 0) (by norm_num : 3 ∣ 9)
  have hω0 : ζ ^ 3 ≠ 0 := hω.ne_zero (by norm_num)
  set ωu : Fˣ := Units.mk0 (ζ ^ 3) hω0 with hωu
  have hωu3 : ωu ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hωu, Units.val_mk0, Units.val_one]
    exact hω.pow_eq_one
  have hωu1 : ωu ≠ 1 := by
    intro h1
    apply hω.ne_one (by norm_num)
    have := congrArg Units.val h1
    rwa [hωu, Units.val_mk0, Units.val_one] at this
  have hσω : σ (ζ ^ 3) = ζ ^ 3 := apply_eq_of_pow_three_eq_one hσ hω.pow_eq_one
  have hσωi : σ ((ωu⁻¹ : Fˣ) : F) = ((ωu⁻¹ : Fˣ) : F) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hωu, Units.val_mk0, hσω]
  set D₀ : SL(3, F) := Dsl (i := 1) (j := 0) (by norm_num) ωu with hD₀
  set D : SL(3, F) :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F B D₀ with hD
  set Z : SL(3, F) := scalarElement ωu hωu3 with hZ
  set z : Y := ((ψ Z : K) : Y) with hz
  set d : Y := ((ψ D : K) : Y) with hd
  have hfD₀ : CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ D₀ =
      D₀ := by
    ext i j
    change σ ((D₀ : Matrix (Fin 3) (Fin 3) F) i j) = (D₀ : Matrix (Fin 3) (Fin 3) F) i j
    rw [hD₀]
    fin_cases i <;> fin_cases j <;>
      simp [Dsl, dvec, Matrix.diagonal, hωu, hσω]
  have hfZ : CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ Z =
      Z := by
    ext i j
    change σ ((Z : Matrix (Fin 3) (Fin 3) F) i j) = (Z : Matrix (Fin 3) (Fin 3) F) i j
    rw [hZ, coe_scalarElement]
    fin_cases i <;> fin_cases j <;> simp [hωu, hσω]
  have hcZ : ∀ C : GL (Fin 3) F,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F C Z = Z := by
    intro C
    have hm : (C : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (ωu : F) *
        ((C⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (ωu : F) := by
      rw [← (Matrix.scalar_commute (ωu : F) (fun r' => Commute.all _ r')
        (C : Matrix (Fin 3) (Fin 3) F)).eq, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.mul_one]
    ext i j
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hZ,
      coe_scalarElement, hm]
  have hTD : slTwist B σ D = D := by
    simp only [slTwist, MulAut.mul_apply, hD, MulAut.inv_apply_self, hfD₀]
  have hTZ : slTwist B σ Z = Z := by
    have hinv : (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F B)⁻¹
        Z = Z := by
      rw [← map_inv]
      exact hcZ B⁻¹
    simp only [slTwist, MulAut.mul_apply, hinv, hfZ, hcZ B]
  have hdy : d * y = y * d := by
    have h1 := coe_psi_slAct ψ y D
    rw [hact D, hTD] at h1
    rw [hd]
    nth_rewrite 1 [h1]
    group
  have hzy : z * y = y * z := by
    have h1 := coe_psi_slAct ψ y Z
    rw [hact Z, hTZ] at h1
    rw [hz]
    nth_rewrite 1 [h1]
    group
  have hZc : Z ∈ Subgroup.center SL(3, F) := by
    rw [← scalars_eq_center]
    exact scalarElement_mem_scalars ωu hωu3
  have hzd : z * d = d * z := by
    have h1 : Z * D = D * Z := (Subgroup.mem_center_iff.1 hZc D).symm
    have h2 := congrArg (fun g => ((ψ g : K) : Y)) h1
    simpa [hz, hd] using h2
  have hz3 : z ^ 3 = 1 := by
    have : Z ^ 3 = 1 := by
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_pow, hZ, coe_scalarElement, ← map_pow]
      have : ((ωu : F)) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hωu3, Units.val_one]
      rw [this, map_one, Matrix.SpecialLinearGroup.coe_one]
    rw [hz, ← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  have hd3 : d ^ 3 = 1 := by
    have : D ^ 3 = 1 := by
      rw [hD, ← map_pow, hD₀, Dsl_pow _ ωu 3 hωu3, map_one]
    rw [hd, ← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  have hφψ : ∀ g : SL(3, F), φ ((ψ g : K) : Y) = conjAut 3 F (Matrix.SpecialLinearGroup.toGL g) := by
    intro g
    rw [hφ, modelAct_coe K e (ψ g), hψ' g, conjAut_toGL]
  set cD : MulAut (projectiveSL 3 F) := conjAut 3 F (diagGL (dvec 1 0 ωu)) with hcD
  have hφz : φ z = 1 := by
    rw [hz, hφψ]
    refine (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff le_rfl _).2
      ⟨ωu, ?_⟩
    apply Units.ext
    rw [hZ]
    rfl
  have hφd : φ d = conjAut 3 F B * cD * (conjAut 3 F B)⁻¹ := by
    rw [hd, hφψ, hD,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
      map_mul, map_inv, hD₀, toGL_Dsl]
  have hcD1 : cD ≠ 1 := by
    intro h1
    obtain ⟨u, hu⟩ :=
      (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff le_rfl _).1 h1
    have h00 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 0 0) hu
    have h11 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 1 1) hu
    simp [coe_diagGL, dvec] at h00 h11
    apply hωu1
    apply Units.ext
    rw [Units.val_one, h11, ← h00]
  have hcD3 : cD ^ 3 = 1 := by
    rw [hcD, ← toGL_Dsl (i := 1) (j := 0) (by norm_num), ← map_pow, ← map_pow,
      Dsl_pow _ ωu 3 hωu3, map_one, map_one]
  have hφd1 : φ d ≠ 1 := by
    rw [hφd]
    intro h1
    apply hcD1
    have : cD = (conjAut 3 F B)⁻¹ * (conjAut 3 F B * cD * (conjAut 3 F B)⁻¹) * conjAut 3 F B := by
      group
    rw [this, h1]
    group
  have hφdL : φ d ∈ linearAutGroup 3 F := by
    rw [hφd]
    exact mul_mem (mul_mem (conjAut_mem_linearAutGroup B) (conjAut_mem_linearAutGroup _))
      (inv_mem (conjAut_mem_linearAutGroup B))
  have hz1 : z ≠ 1 := by
    intro h1
    apply hωu1
    have hZ1 : Z = 1 := by
      apply ψ.injective
      rw [map_one]
      exact Subtype.ext (by rw [← hz, h1]; rfl)
    have := congrArg (fun M : SL(3, F) => (M : Matrix (Fin 3) (Fin 3) F) 0 0) hZ1
    simp [hZ] at this
    exact this
  have hd1 : d ≠ 1 := fun h1 => hφd1 (by rw [h1, map_one])
  have hy1 : y ≠ 1 := fun h1 => hyout (by rw [h1, map_one]; exact one_mem _)
  have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hod : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  set E₁ : Subgroup Y :=
    (Subgroup.zpowers z ⊔ Subgroup.zpowers d) ⊔ Subgroup.zpowers y with hE₁
  have hE₁a : IsElemAbelian 3 E₁ :=
    isElemAbelian_sup_zpowers hzd hzy hdy hz3 hd3 hy3
  have hzdL : Subgroup.zpowers z ⊔ Subgroup.zpowers d ≤ (linearAutGroup 3 F).comap φ := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · change φ z ∈ linearAutGroup 3 F
      rw [hφz]
      exact one_mem _
    · exact hφdL
  have hdisj₁ : Disjoint (Subgroup.zpowers z) (Subgroup.zpowers d) := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxd
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxz
    have hφx : φ (d ^ k) = 1 := by rw [← hm, map_zpow, hφz, _root_.one_zpow]
    rw [map_zpow] at hφx
    have hoφd : orderOf (φ d) = 3 := orderOf_eq_prime (by rw [← map_pow, hd3, map_one]) hφd1
    have h3k : ((orderOf (φ d) : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.2 hφx
    rw [hoφd] at h3k
    exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hod]; exact_mod_cast h3k)
  have hdisj₂ : Disjoint (Subgroup.zpowers z ⊔ Subgroup.zpowers d) (Subgroup.zpowers y) := by
    rw [Subgroup.disjoint_def]
    intro x hxzd hxy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxy
    by_cases h3k : (3 : ℤ) ∣ k
    · exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hoy]; exact_mod_cast h3k)
    · exfalso
      apply hyout
      have hk : φ y ^ k ∈ linearAutGroup 3 F := by
        rw [← map_zpow]
        exact hzdL hxzd
      exact mem_of_zpow_mem_of_pow_three hφy3 h3k hk
  have hcomm₁ : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers d, Commute a b := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow hzd i j)
  have hcomm₂ : ∀ a ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers d, ∀ b ∈ Subgroup.zpowers y,
      Commute a b := by
    intro a ha b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer {y} := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 hzy
      · exact Subgroup.mem_centralizer_singleton_iff.2 hdy
    have hay : Commute a y := Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
    exact hay.zpow_right j
  have hE₁c : Nat.card E₁ = 3 ^ 3 := by
    rw [hE₁, card_sup_of_commute_disjoint _ _ hcomm₂ hdisj₂,
      card_sup_of_commute_disjoint _ _ hcomm₁ hdisj₁, Nat.card_zpowers, Nat.card_zpowers,
      Nat.card_zpowers, hoz, hod, hoy]
    norm_num
  have hyE₁ : y ∈ E₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  obtain ⟨l, hl⟩ := exists_conj_le_sylow Rb hE₁a.2
  set E' : Subgroup Y := E₁.map (MulAut.conj l).toMonoidHom with hE'
  have hE'a : IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hE₁a _
  have hE'c : Nat.card E' = 3 ^ 3 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj l).injective, hE₁c]
  have hKCL : K ⊔ Subgroup.centralizer (K : Set Y) ≤ (linearAutGroup 3 F).comap φ := by
    refine sup_le (fun k hk => ?_) (fun c hc => ?_)
    · change φ k ∈ linearAutGroup 3 F
      have : φ k = MulAut.conj (e (QuotientGroup.mk (⟨k, hk⟩ : K))) := modelAct_coe K e ⟨k, hk⟩
      rw [this]
      exact CFSG.RankThree.PartTwo.KFacts.innAut_le_linearAutGroup 3 F ⟨_, rfl⟩
    · change φ c ∈ linearAutGroup 3 F
      have hck : c ∈ φ.ker := by rw [hφ, modelAct_ker hK e]; exact hc
      rw [MonoidHom.mem_ker.1 hck]
      exact one_mem _
  have hLn : (linearAutGroup 3 F).Normal :=
    (CFSG.RankThree.PartTwo.KFacts.stdPinnedPSL_stable (n := 3) (K := F) le_rfl).normal
  have hE'KC : ¬ E' ≤ K ⊔ Subgroup.centralizer (K : Set Y) := by
    intro hle
    apply hyout
    have h1 : l * y * l⁻¹ ∈ K ⊔ Subgroup.centralizer (K : Set Y) := hle ⟨y, hyE₁, rfl⟩
    have h2 : φ l * φ y * (φ l)⁻¹ ∈ linearAutGroup 3 F := by
      have := hKCL h1
      rwa [Subgroup.mem_comap, map_mul, map_mul, map_inv] at this
    have h3' := hLn.conj_mem _ h2 (φ l)⁻¹
    have he : (φ l)⁻¹ * (φ l * φ y * (φ l)⁻¹) * (φ l)⁻¹⁻¹ = φ y := by group
    rwa [he] at h3'
  set Θ : Y →* MulAut (projectiveSL 3 F) :=
    (MulAut.conj (conjAut 3 F B)⁻¹).toMonoidHom.comp φ with hΘ
  set α : MulAut (projectiveSL 3 F) := (φ l * conjAut 3 F B)⁻¹ with hα
  have hmap : (E'.map φ).map (MulAut.conj α).toMonoidHom = E₁.map Θ := by
    rw [hE', Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x : 1
    change (MulAut.conj α) (φ ((MulAut.conj l) x)) = (MulAut.conj (conjAut 3 F B)⁻¹) (φ x)
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hα]
    group
  have hΘz : Θ z = 1 := by
    simp only [hΘ, MonoidHom.comp_apply, hφz, map_one]
  have hΘd : Θ d = cD := by
    simp only [hΘ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hφd, MulAut.conj_apply]
    group
  have hΘy : Θ y = fieldAut 3 F σ := by
    simp only [hΘ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hB, MulAut.conj_apply]
    group
  have hE₁Θ : E₁.map Θ = (Subgroup.zpowers (1 : MulAut (projectiveSL 3 F)) ⊔
      Subgroup.zpowers cD) ⊔ Subgroup.zpowers (fieldAut 3 F σ) := by
    rw [hE₁, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, hΘz, hΘd, hΘy]
  have hσdiag : Matrix.GeneralLinearGroup.map (σ : F →+* F) (diagGL (dvec 1 0 ωu)) =
      diagGL (dvec 1 0 ωu) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    fin_cases i <;> fin_cases j <;> simp [coe_diagGL, dvec, Matrix.diagonal, hωu, hσω]
  have hfc : Commute (fieldAut 3 F σ) cD := by
    change fieldAut 3 F σ * cD = cD * fieldAut 3 F σ
    rw [hcD, LinearFlag.fieldAut_mul_conjAut, hσdiag]
  have hf3 : fieldAut 3 F σ ^ 3 = 1 := by
    rw [← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
  set A' : Subgroup (MulAut (projectiveSL 3 F)) := Subgroup.zpowers cD with hA'
  have hA'f : ∀ a ∈ A', ∀ k : ℕ, Commute a (fieldAut 3 F σ ^ k) := by
    intro a ha k
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact (hfc.symm.zpow_left i).pow_right k
  let S : Subgroup (MulAut (projectiveSL 3 F)) :=
    { carrier := {b | ∃ k : ℕ, ∃ a ∈ A', b = fieldAut 3 F σ ^ k * a}
      mul_mem' := by
        rintro _ _ ⟨k, a, ha, rfl⟩ ⟨m, b, hb, rfl⟩
        refine ⟨k + m, a * b, A'.mul_mem ha hb, ?_⟩
        rw [pow_add, mul_assoc, ← mul_assoc a, (hA'f a ha m).eq]
        group
      one_mem' := ⟨0, 1, A'.one_mem, by rw [pow_zero, mul_one]⟩
      inv_mem' := by
        rintro _ ⟨k, a, ha, rfl⟩
        refine ⟨2 * k, a⁻¹, A'.inv_mem ha, ?_⟩
        have hk : (fieldAut 3 F σ ^ k)⁻¹ = fieldAut 3 F σ ^ (2 * k) := by
          rw [inv_eq_of_mul_eq_one_right]
          rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hf3, one_pow]
        rw [_root_.mul_inv_rev, ← hk, ((hA'f a ha k).inv_left).inv_right.eq] }
  have hsplit : SplitData σ A' (E₁.map Θ) := by
    refine ⟨fun a ha => ?_, fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
        _root_.zpow_natCast, hcD3, _root_.one_zpow]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      refine ⟨dvec 1 0 ωu ^ i, ?_⟩
      rw [hcD, ← map_zpow]
      congr 1
      exact (map_zpow (diagHom F) (dvec 1 0 ωu) i).symm
    · have hle : E₁.map Θ ≤ S := by
        rw [hE₁Θ]
        refine sup_le (sup_le ?_ ?_) ?_
        · rw [Subgroup.zpowers_one_eq_bot]
          exact bot_le
        · rw [Subgroup.zpowers_le]
          exact ⟨0, cD, Subgroup.mem_zpowers cD, by rw [pow_zero, one_mul]⟩
        · rw [Subgroup.zpowers_le]
          exact ⟨1, 1, A'.one_mem, by rw [pow_one, mul_one]⟩
      exact hle hb
  exact false_of_split_field_cube h hK hC hl hE'a hE'c hE'KC h3 e
    ⟨α, σ, A', hσ, hmap ▸ hsplit⟩

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
