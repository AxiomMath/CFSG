module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Lift
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreLevel
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLDescent
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Dict
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A318PL3Lin
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.Coordinator

section Diag

variable {F : Type} [Field F]

@[expose] noncomputable def diagGL (d : Fin 3 → Fˣ) : GL (Fin 3) F :=
  ⟨Matrix.diagonal fun i => (d i : F), Matrix.diagonal fun i => ((d i)⁻¹ : Fˣ),
    by rw [Matrix.diagonal_mul_diagonal]; simp,
    by rw [Matrix.diagonal_mul_diagonal]; simp⟩

theorem coe_diagGL (d : Fin 3 → Fˣ) :
    ((diagGL d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal fun i => (d i : F) :=
  rfl

theorem coe_diagGL_inv (d : Fin 3 → Fˣ) :
    (((diagGL d)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F) :=
  rfl

theorem conj_diag_tv {i j : Fin 3} (hij : i ≠ j) (d : Fin 3 → Fˣ) (t : F) :
    LinearFlag.conjAut 3 F (diagGL d) (LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij t)) =
      LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij ((d i : F) * (((d j)⁻¹ : Fˣ) : F) * t)) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_diagGL, coe_diagGL_inv, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  ext a b
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_three] <;>
    ring_nf

theorem field_tv {i j : Fin 3} (hij : i ≠ j) (σ : F ≃+* F) (t : F) :
    LinearFlag.fieldAut 3 F σ (LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij t)) =
      LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij (σ t)) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext a b
  rw [SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp_all

theorem mem_c25Fix_closure {Y : Type*} [Group Y] (s : Set (MulAut Y)) (y : Y) :
    y ∈ c25Fix (Subgroup.closure s) ↔ ∀ a ∈ s, a y = y := by
  constructor
  · intro h a ha
    exact h a (Subgroup.subset_closure ha)
  · intro h α hα
    induction hα using Subgroup.closure_induction with
    | mem a ha => exact h a ha
    | one => simp
    | mul a b _ _ ha hb => rw [MulAut.mul_apply, hb, ha]
    | inv a _ ha =>
      have : a⁻¹ y = y := by
        conv_lhs => rw [← ha]
        simp
      exact this

theorem tv_pow_nat {i j : Fin 3} (hij : i ≠ j) (t : F) (n : ℕ) :
    SpecialLinearGroup.transvection hij t ^ n = SpecialLinearGroup.transvection hij (n • t) := by
  induction n with
  | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
  | succ n ih => rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]

theorem tv_pow_char {i j : Fin 3} (hij : i ≠ j) (t : F) :
    LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij t) ^ ringChar F = 1 := by
  rw [← map_pow, tv_pow_nat, nsmul_eq_mul, CharP.cast_eq_zero F (ringChar F), zero_mul,
    SpecialLinearGroup.transvection_coeff_zero, map_one]

theorem coprime_ringChar_three [Finite F] (h3 : 3 ∣ Nat.card F - 1) : Nat.Coprime (ringChar F) 3 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, hn, hcard⟩ := FiniteField.card F (ringChar F)
  rw [Nat.coprime_primes hn Nat.prime_three]
  rintro h
  rw [h] at hcard
  have h1 : 3 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self 3 n.ne_zero
  have h2 : 1 ≤ Nat.card F := Nat.card_pos
  omega

theorem tv_mem_dPart [Finite F] (h3 : 3 ∣ Nat.card F - 1)
    {S : Subgroup (MulAut (projectiveSL 3 F))}
    {i j : Fin 3} (hij : i ≠ j) (t : F)
    (hfix : LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij t) ∈ c25Fix S) :
    LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij t) ∈ dPart 3 (c25Fix S) := by
  refine Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hfix, ?_⟩)
  have hdvd : orderOf (LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij t)) ∣ ringChar F :=
    orderOf_dvd_of_pow_eq_one (tv_pow_char hij t)
  exact Nat.Coprime.coprime_dvd_left hdvd (coprime_ringChar_three h3)

theorem fixSL3_le_closure_tv (σ : F ≃+* F) :
    BGL.fixSL3 σ ≤ Subgroup.closure {x : SpecialLinearGroup (Fin 3) F |
      ∃ (i j : Fin 3) (hij : i ≠ j) (c : F), σ c = c ∧ x = SpecialLinearGroup.transvection hij c} := by
  intro g hg
  set k : Subfield F := RingHom.eqLocusField σ.toRingHom (RingHom.id F) with hkdef
  have hk : ∀ y, y ∈ k ↔ σ y = y := fun y => Iff.rfl
  let gk : Matrix (Fin 3) (Fin 3) k :=
    Matrix.of fun i j => ⟨(g : Matrix (Fin 3) (Fin 3) F) i j, (hk _).2 (hg i j)⟩
  have hmap : k.subtype.mapMatrix gk = (g : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    rfl
  have hdet : gk.det = 1 := by
    apply k.subtype.injective
    rw [map_one, RingHom.map_det, hmap]
    exact g.2
  let G : SpecialLinearGroup (Fin 3) k := ⟨gk, hdet⟩
  have hG : SpecialLinearGroup.map k.subtype G = g := by
    apply Subtype.ext
    rw [SpecialLinearGroup.map_apply_coe]
    exact hmap
  have hGtop : G ∈ Subgroup.closure (Set.range
      (Matrix.TransvectionStruct.toSpecialLinearGroup (ι := Fin 3) (F := k))) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    trivial
  rw [← hG]
  have := Subgroup.mem_map_of_mem (SpecialLinearGroup.map k.subtype) hGtop
  rw [MonoidHom.map_closure] at this
  refine Subgroup.closure_mono ?_ this
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  refine ⟨t.i, t.j, t.hij, (t.c : F), (hk _).1 t.c.2, ?_⟩
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, Matrix.TransvectionStruct.toSpecialLinearGroup_coe,
    SpecialLinearGroup.transvection_coe]
  ext a b
  simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.single_apply,
    Matrix.one_apply, Matrix.add_apply]
  split_ifs <;> simp_all

theorem proj_tv_eq_iff {i j : Fin 3} (hij : i ≠ j) (s t : F) :
    LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij s) =
      LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij t) ↔ s = t := by
  constructor
  · intro h
    have h1 : (SpecialLinearGroup.transvection hij s)⁻¹ *
        SpecialLinearGroup.transvection hij t ∈ (LinearFlag.proj 3 F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [LinearFlag.ker_proj] at h1
    have h2 : (SpecialLinearGroup.transvection hij s)⁻¹ * SpecialLinearGroup.transvection hij t =
        SpecialLinearGroup.transvection hij (t - s) := by
      rw [SpecialLinearGroup.transvection_inv, ← SpecialLinearGroup.transvection_add, neg_add_eq_sub]
    rw [h2] at h1
    have := (SpecialLinearGroup.transvection_mem_center_iff hij (t - s)).1
      (LinearFlag.scalars_le_center 3 F h1)
    exact (sub_eq_zero.1 this).symm
  · rintro rfl
    rfl

@[expose] noncomputable def vD (w : Fˣ) (c : Fin 3) : Fin 3 → Fˣ := fun k => if k = c then w else 1

@[expose] noncomputable def vC (w : Fˣ) (c : Fin 3) : MulAut (projectiveSL 3 F) :=
  LinearFlag.conjAut 3 F (diagGL (vD w c))

theorem vC_tv_other {w : Fˣ} {a b c : Fin 3} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (t : F) :
    vC w c (LinearFlag.proj 3 F (SpecialLinearGroup.transvection hab t)) =
      LinearFlag.proj 3 F (SpecialLinearGroup.transvection hab t) := by
  rw [vC, conj_diag_tv hab]
  simp [vD, hca.symm, hcb.symm]

theorem vC_tv_first {w : Fˣ} {a b : Fin 3} (hab : a ≠ b) (t : F) :
    vC w a (LinearFlag.proj 3 F (SpecialLinearGroup.transvection hab t)) =
      LinearFlag.proj 3 F (SpecialLinearGroup.transvection hab ((w : F) * t)) := by
  rw [vC, conj_diag_tv hab]
  simp [vD, hab.symm]

end Diag

section Main

variable {F : Type} [Field F]

open CFSG.Open CFSG.Quasithin.A318P CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

theorem exists_twisted_fixed [Finite F] {σ : F ≃+* F} (hσ : orderOf σ = 3) {ω : F} (hω0 : ω ≠ 0)
    (hω3 : ω ^ 3 = 1) (hωσ : σ ω = ω) : ∃ t : F, t ≠ 0 ∧ ω * σ t = t := by
  let B : Matrix (Fin 1) (Fin 1) F := Matrix.of fun _ _ => ω
  have hBu : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simpa [B, Matrix.det_unique] using hω0
  have hC : CFSG.Quasithin.SteinbergCB.GDescent.iterMat σ B 3 = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [CFSG.Quasithin.SteinbergCB.GDescent.iterMat_succ,
      CFSG.Quasithin.SteinbergCB.GDescent.iterMat_zero, B, hωσ, Matrix.mul_apply, Matrix.map_apply]
    linear_combination hω3
  obtain ⟨P, hPu, hP⟩ := bgll_exists_fixed_basis σ hσ (by norm_num) hBu hC
  refine ⟨P 0 0, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det] at hPu
    simpa [Matrix.det_unique] using hPu.ne_zero
  · have := congrFun (congrFun hP 0) 0
    simpa [Matrix.mul_apply, B] using this

theorem card_closure_pair_ge_nine {M : Type*} [Group M] {A : Subgroup M} (hA : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) {u e : M} (hu : u ∈ A) (he : e ∈ A) (hu1 : u ≠ 1)
    (hne : e ∉ Subgroup.zpowers u) : 27 ≤ 3 * Nat.card (Subgroup.closure {u, e}) := by
  have hSA : Subgroup.closure {u, e} ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hu
    · exact he
  have hu3 : u ^ 3 = 1 := hA.2 u hu
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have : Finite (Subgroup.closure {u, e}) := Finite.of_injective (Subgroup.inclusion hSA)
    (Subgroup.inclusion_injective hSA)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hzS : Subgroup.zpowers u ≤ Subgroup.closure {u, e} :=
    (Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert _ _)))
  have hdvd27 : Nat.card (Subgroup.closure {u, e}) ∣ 27 :=
    hA27 ▸ Subgroup.card_dvd_of_le hSA
  have hdvd3 : 3 ∣ Nat.card (Subgroup.closure {u, e}) := by
    have := Subgroup.card_dvd_of_le hzS
    rwa [Nat.card_zpowers, hord] at this
  have hne3 : Nat.card (Subgroup.closure {u, e}) ≠ 3 := by
    intro h3
    have heq : Subgroup.zpowers u = Subgroup.closure {u, e} := by
      refine Subgroup.eq_of_le_of_card_ge hzS ?_
      rw [h3, Nat.card_zpowers, hord]
    apply hne
    rw [heq]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hpos : 0 < Nat.card (Subgroup.closure {u, e}) := Nat.card_pos
  have hle : Nat.card (Subgroup.closure {u, e}) ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd27
  obtain ⟨m, hm⟩ := hdvd3
  interval_cases hc : Nat.card (Subgroup.closure {u, e}) <;> omega

theorem toral_core [Finite F] {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (h3 : 3 ∣ Nat.card F - 1) {w : Fˣ} (hw3 : (w : F) ^ 3 = 1) (hw1 : (w : F) ≠ 1)
    (hwσ : σ (w : F) = w) (A : Subgroup (MulAut (projectiveSL 3 F))) (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hv : ∀ c, vC w c ∈ A) (hf : LinearFlag.fieldAut 3 F σ ∈ A) :
    ⊤ ≤ ⨆ (S : Subgroup (MulAut (projectiveSL 3 F)))
        (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), dPart 3 (c25Fix S) := by
  set f := LinearFlag.fieldAut 3 F σ with hfdef
  have hfD : f ∉ linearAutGroup 3 F := fun hD => by
    have := (l3FrameLinear h3).fld_inter σ hD
    rw [this] at hσ
    simp at hσ
  have hvD : ∀ c, vC w c ∈ linearAutGroup 3 F := fun c => conjAut_mem_linearAutGroup _
  have hv1 : ∀ c, vC w c ≠ 1 := by
    intro c hc
    obtain ⟨b, hb⟩ : ∃ b : Fin 3, c ≠ b := by
      fin_cases c
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    have h1 := vC_tv_first (w := w) hb 1
    rw [hc, MulAut.one_apply, proj_tv_eq_iff] at h1
    exact hw1 (by simpa using h1.symm)
  have hrat_third : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by decide
  have hT : ⊤ ≤ ⨆ (S : Subgroup (MulAut (projectiveSL 3 F)))
        (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), dPart 3 (c25Fix S) := by
    set Hb := ⨆ (S : Subgroup (MulAut (projectiveSL 3 F)))
        (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), dPart 3 (c25Fix S) with hHb
    have hbig : ∀ S : Subgroup (MulAut (projectiveSL 3 F)),
        (S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S) → dPart 3 (c25Fix S) ≤ Hb :=
      fun S hS => le_iSup₂_of_le S hS le_rfl
    have hS0 : ∀ k : Fin 3, Subgroup.closure ({vC w k, f} : Set (MulAut (projectiveSL 3 F))) ≤ A ∧
        Nat.card A ≤ 3 * Nat.card (Subgroup.closure ({vC w k, f} :
          Set (MulAut (projectiveSL 3 F)))) := by
      intro k
      refine ⟨(Subgroup.closure_le _).2 (by rintro x (rfl | rfl); exacts [hv k, hf]), ?_⟩
      have := card_closure_pair_ge_nine hAel hA27 (hv k) hf (hv1 k) (fun hm =>
        hfD ((Subgroup.zpowers_le.2 (hvD k)) hm))
      omega
    have hrat : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F), σ c = c →
        LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij c) ∈ Hb := by
      intro i j hij c hc
      obtain ⟨k, hki, hkj⟩ := hrat_third i j hij
      have hfix : LinearFlag.proj 3 F (SpecialLinearGroup.transvection hij c) ∈
          c25Fix (Subgroup.closure ({vC w k, f} : Set (MulAut (projectiveSL 3 F)))) := by
        rw [mem_c25Fix_closure]
        rintro a (rfl | rfl)
        · exact vC_tv_other hij hki hkj c
        · rw [hfdef, field_tv, hc]
      exact hbig _ (hS0 k) (tv_mem_dPart h3 hij c hfix)
    set H' : Subgroup (SpecialLinearGroup (Fin 3) F) := Hb.comap (LinearFlag.proj 3 F) with hH'
    have hA' : BGL.fixSL3 σ ≤ H' := by
      refine (fixSL3_le_closure_tv σ).trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨i, j, hij, c, hc, rfl⟩
      exact hrat i j hij c hc
    obtain ⟨t1, ht10, ht1⟩ := exists_twisted_fixed hσ w.ne_zero hw3 hwσ
    have hS1 : Subgroup.closure ({vC w 2, f * vC w 0} : Set (MulAut (projectiveSL 3 F))) ≤ A ∧
        Nat.card A ≤ 3 * Nat.card (Subgroup.closure ({vC w 2, f * vC w 0} :
          Set (MulAut (projectiveSL 3 F)))) := by
      refine ⟨(Subgroup.closure_le _).2
        (by rintro x (rfl | rfl); exacts [hv 2, A.mul_mem hf (hv 0)]), ?_⟩
      have := card_closure_pair_ge_nine hAel hA27 (hv 2) (A.mul_mem hf (hv 0)) (hv1 2)
        (fun hm => hfD (by
          have h1 := (Subgroup.zpowers_le.2 (hvD 2)) hm
          have h2 := (linearAutGroup 3 F).mul_mem h1 ((linearAutGroup 3 F).inv_mem (hvD 0))
          simpa using h2))
      omega
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    have hfix1 : LinearFlag.proj 3 F (SpecialLinearGroup.transvection h01 t1) ∈
        c25Fix (Subgroup.closure ({vC w 2, f * vC w 0} : Set (MulAut (projectiveSL 3 F)))) := by
      rw [mem_c25Fix_closure]
      rintro a (rfl | rfl)
      · exact vC_tv_other h01 (by decide) (by decide) t1
      · rw [MulAut.mul_apply, vC_tv_first h01, hfdef, field_tv, map_mul, hwσ, ht1]
    have ht1H : SpecialLinearGroup.transvection h01 t1 ∈ H' :=
      hbig _ hS1 (tv_mem_dPart h3 h01 t1 hfix1)
    have hσt : σ t1 ≠ t1 := by
      intro h
      rw [h] at ht1
      have : ((w : F) - 1) * t1 = 0 := by linear_combination ht1
      rcases mul_eq_zero.1 this with h' | h'
      · exact hw1 (sub_eq_zero.1 h')
      · exact ht10 h'
    have htop := BGL.top_le_of_x01 hA' (by rw [hσ]; exact Nat.prime_three) ht1H hσt
    intro x _
    obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 F x
    exact htop (Subgroup.mem_top g)
  exact hT

end Main

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
