module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Six6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269U5
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS11U62Rank
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIPComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I269Six

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4 bar hF4_bar)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.Fischer
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

theorem exists_noncomm_S6 : ∃ x y : S6, x * y ≠ y * x := by
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : F4, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra h
    push_neg at h
    have hc : (Finset.univ : Finset F4) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have := Finset.card_le_card hc
    have h2 : ({0, 1} : Finset F4).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, F4.card] at this
    omega
  have hω3 : ω ^ 3 = 1 := f4_cube ω hω0
  have hω21 : ω ^ 2 + 1 ≠ 0 := by
    intro h
    have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
    have : (ω - 1) ^ 2 = 0 := by linear_combination h - ω * h2
    exact hω1 (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))
  set a : Fin 6 → F4 := fun i => if i = 0 then ω else if i = 1 then ω ^ 2 else 1 with ha_def
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i
    simp only [ha_def]
    split_ifs
    · exact hω0
    · exact pow_ne_zero _ hω0
    · exact one_ne_zero
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    intro i
    simp only [ha_def]
    split_ifs
    · exact hω3
    · rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow]
    · exact one_pow 3
  set A : GL (Fin 6) F4 := dGL a ha0 with hA_def
  have hAU : A ∈ primeFormUnitary hF4 (idGram F4 6) := dGL_mem_UG a ha0 ha3
  have hAdet : (A : Matrix (Fin 6) (Fin 6) F4).det = 1 := by
    rw [hA_def, dGL_val, Matrix.det_diagonal, Fin.prod_univ_six]
    simp only [ha_def]
    simp [hω3]
    linear_combination hω3
  have hAM : A ∈ CFSG.Open.StatedSU 6 (2 ^ 1) F4 := by
    apply CFSG.LocalAnalysis.GLTheoremA.LevelLieU.mem_statedSU_of 6 A hAdet
    have := (mem_primeFormUnitary.1 hAU)
    simpa [idGram, hF4_bar] using this
  set σ : Equiv.Perm (Fin 6) := Equiv.swap 0 2 with hσ
  set P : Matrix (Fin 6) (Fin 6) F4 := σ.permMatrix F4 with hP
  have hPT : P * P.transpose = 1 := by
    rw [hP, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      Matrix.permMatrix_one]
  have hTP : P.transpose * P = 1 := by
    rw [hP, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one]
  have hPdet : P.det = 1 := by
    rw [hP, Matrix.det_permutation, hσ, Equiv.Perm.sign_swap (by decide)]
    simp
    exact CharTwo.neg_eq _
  set B : GL (Fin 6) F4 := Units.mk P P.transpose hPT hTP with hB_def
  have hBM : B ∈ CFSG.Open.StatedSU 6 (2 ^ 1) F4 := by
    apply CFSG.LocalAnalysis.GLTheoremA.LevelLieU.mem_statedSU_of 6 B hPdet
    have hmap : (P.map bar) = P := by
      ext i j
      simp [hP, Equiv.Perm.permMatrix]
    simp only [hB_def, Units.val_mk, hmap]
    exact hTP
  set x : S6 := piS ⟨A, hAM⟩
  set y : S6 := piS ⟨B, hBM⟩
  refine ⟨x, y, fun hxy => ?_⟩
  have hz : (⟨A, hAM⟩ * ⟨B, hBM⟩ : M6) * (⟨B, hBM⟩ * ⟨A, hAM⟩)⁻¹ ∈ Zs := by
    rw [← piS_eq_one, map_mul, map_inv, map_mul, map_mul]
    have hxy' : piS ⟨A, hAM⟩ * piS ⟨B, hBM⟩ = piS ⟨B, hBM⟩ * piS ⟨A, hAM⟩ := hxy
    rw [hxy', mul_inv_cancel]
  obtain ⟨c, hc⟩ := mem_Zs.1 hz
  have h1 : (A : GL (Fin 6) F4) * B = Matrix.GeneralLinearGroup.scalar (Fin 6) c * (B * A) := by
    have hc' : (A : GL (Fin 6) F4) * B * (B * A)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) c := hc
    calc (A : GL (Fin 6) F4) * B = ((A : GL (Fin 6) F4) * B * (B * A)⁻¹) * (B * A) := by group
      _ = _ := by rw [hc']
  have h2 : (A : Matrix (Fin 6) (Fin 6) F4) * (B : Matrix (Fin 6) (Fin 6) F4) =
      (c : F4) • ((B : Matrix (Fin 6) (Fin 6) F4) * (A : Matrix (Fin 6) (Fin 6) F4)) := by
    have := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4)) h1
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
      using this
  have htr : ((A : Matrix (Fin 6) (Fin 6) F4) * (B : Matrix (Fin 6) (Fin 6) F4)).trace =
      (c : F4) * ((A : Matrix (Fin 6) (Fin 6) F4) * (B : Matrix (Fin 6) (Fin 6) F4)).trace := by
    have := congrArg Matrix.trace h2
    rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm (B : Matrix (Fin 6) (Fin 6) F4)
      (A : Matrix (Fin 6) (Fin 6) F4)] at this
    exact this
  have htr' : ((A : Matrix (Fin 6) (Fin 6) F4) * (B : Matrix (Fin 6) (Fin 6) F4)).trace =
      ω ^ 2 + 1 := by
    have hAv : (A : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal a := by
      rw [hA_def, dGL_val]
    have hBv : (B : Matrix (Fin 6) (Fin 6) F4) = P := rfl
    have hPent : ∀ i j, P i j = if σ i = j then 1 else 0 := fun i j => by
      simp [hP, Equiv.Perm.permMatrix]
    have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
    rw [hAv, hBv, Matrix.trace, Fin.sum_univ_six]
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_six, hPent, hσ,
      Equiv.swap_apply_def, ha_def]
    linear_combination h2
  have hc1 : (c : F4) = 1 := by
    have h3 : ((c : F4) - 1) * (ω ^ 2 + 1) = 0 := by
      rw [← htr']
      linear_combination -htr
    rcases mul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hω21
  rw [hc1, one_smul] at h2
  have hAv : (A : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal a := by
    rw [hA_def, dGL_val]
  have hBv : (B : Matrix (Fin 6) (Fin 6) F4) = P := rfl
  have hPent : ∀ i j, P i j = if σ i = j then 1 else 0 := fun i j => by
    simp [hP, Equiv.Perm.permMatrix]
  have h4 := congrFun (congrFun h2 0) 2
  rw [hAv, hBv] at h4
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_six, hPent, hσ,
    Equiv.swap_apply_def, ha_def] at h4
  exact hω1 h4

theorem center_S6 : Subgroup.center S6 = ⊥ := by
  haveI : IsSimpleGroup S6 := isSimple_S6
  exact center_eq_bot_of_simple_nonabelian' (by
    intro h
    obtain ⟨x, y, hxy⟩ := exists_noncomm_S6
    exact hxy (h.is_comm.comm x y))

@[expose] def E9SolvInner (S : Type) [Group S] : Prop :=
  ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 9 →
    (∀ α ∈ E, α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S) →
    Group.IsSolvable ↥(i269Fix E)

theorem E9SolvInner_S6 : E9SolvInner S6 := by
  intro E hE hcard hinn
  set Ē : Subgroup S6 := E.comap (MulAut.conj : S6 →* MulAut S6) with hĒ
  have hinj : Function.Injective (MulAut.conj : S6 → MulAut S6) := fun x y h =>
    conj_injective_of_center' center_S6 h
  have hmem : ∀ x ∈ Ē, MulAut.conj x ∈ E := fun x hx => hx
  have hcomm : ∀ x ∈ Ē, ∀ y ∈ Ē, x * y = y * x := by
    intro x hx y hy
    apply hinj
    have := congrArg Subtype.val (hE.1.is_comm.comm ⟨MulAut.conj x, hmem x hx⟩
      ⟨MulAut.conj y, hmem y hy⟩)
    simpa [map_mul] using this
  have hexp : ∀ x ∈ Ē, x ^ 3 = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ (hmem x hx)
  have hEq : Ē.map (MulAut.conj : S6 →* MulAut S6) = E := by
    ext α
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hmem x hx
    · intro hα
      obtain ⟨s, hs⟩ := hinn α hα
      exact ⟨s, by rw [hĒ]; exact (hs ▸ hα : MulAut.conj s ∈ E), hs⟩
  have hcardĒ : Nat.card Ē = 9 := by
    have h1 : Nat.card (Ē.map (MulAut.conj : S6 →* MulAut S6)) = Nat.card Ē :=
      Subgroup.card_map_of_injective hinj
    rw [hEq] at h1
    omega
  haveI := solvable_centralizer hcomm hexp hcardĒ
  have hle : i269Fix E ≤ Subgroup.centralizer (Ē : Set S6) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := (mem_i269Fix.1 hx) (MulAut.conj s) (hmem s hs)
    rw [MulAut.conj_apply] at h1
    calc s * x = (s * x * s⁻¹) * s := by group
      _ = x * s := by rw [h1]
  exact isSolvable_of_le_isSolvable hle

theorem E9SolvInner.of_mulEquiv {S T : Type} [Group S] [Group T] (hT : E9SolvInner T)
    (e : S ≃* T) : E9SolvInner S := by
  intro E hE hcard hinn
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hE' : IsElemAbelian 3 (E.map (MulAut.congr e).toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨α, hα, hαa⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨β, hβ, hβb⟩ := Subgroup.mem_map.1 b.2
      have hc : α * β = β * α := congrArg Subtype.val (hE.1.is_comm.comm ⟨α, hα⟩ ⟨β, hβ⟩)
      apply Subtype.ext
      show (a : MulAut T) * (b : MulAut T) = (b : MulAut T) * (a : MulAut T)
      rw [← hαa, ← hβb, ← map_mul, ← map_mul, hc]
    · rintro _ ⟨α, hα, rfl⟩
      show (MulAut.congr e α) ^ 3 = 1
      rw [← map_pow, hE.2 α hα, map_one]
  have hcard' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  have hinn' : ∀ α ∈ E.map (MulAut.congr e).toMonoidHom,
      α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner T := by
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨g, rfl⟩ := hinn α hα
    exact ⟨e g, (congr_conj' e g).symm⟩
  have hs := hT _ hE' hcard' hinn'
  rw [i269Fix_map] at hs
  haveI := hs
  exact isSolvable_of_mulEquiv' (Subgroup.equivMapOfInjective (i269Fix E) e.toMonoidHom e.injective)

variable {G : Type} [Group G] [Finite G]

theorem layer_eq_bot_of_E9_inner {X L D : Subgroup G} (hL : GLAPComponent 3 X L)
    (hE : E9SolvInner (PSimple 3 L)) (hDN : D ≤ Subgroup.normalizer (L : Set G))
    (hD : IsElemAbelian 3 D) (hinn : ∀ d ∈ D, InducesInnerMod 3 L d)
    (hcard : Nat.card D = 3 ^ 2 * Nat.card ↥(D ⊓ centModSubgroup 3 L)) :
    GLAPLayer 3 (L ⊓ Subgroup.centralizer (D : Set G)) = ⊥ := by
  classical
  let φ : ↥D →* MulAut (PSimple 3 L) := (chevAut 3 L).comp (Subgroup.inclusion hDN)
  have hφ : ∀ d : ↥D, φ d = chevAut 3 L ⟨d.1, hDN d.2⟩ := fun d => rfl
  have hker : ∀ d : ↥D, φ d = 1 ↔ d.1 ∈ centModSubgroup 3 L := by
    intro d
    rw [hφ, chevAut_eq_one_iff Nat.prime_three hL (hDN d.2), centMod_iff]
  have hEcard : Nat.card φ.range = 9 := by
    have hpos : 0 < Nat.card ↥(D ⊓ centModSubgroup 3 L) := Nat.card_pos
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 : Nat.card (↥D ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have h3 : Nat.card φ.ker = Nat.card ↥(D ⊓ centModSubgroup 3 L) := by
      apply Nat.card_congr
      exact
        { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, (hker x.1).1 (MonoidHom.mem_ker.1 x.2)⟩⟩
          invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
            MonoidHom.mem_ker.2 ((hker ⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩).2 (Subgroup.mem_inf.1 y.2).2)⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    have hc : Nat.card D = Nat.card φ.range * Nat.card ↥(D ⊓ centModSubgroup 3 L) := by
      rw [← h3, ← h2]
      exact h1
    have h9 : Nat.card φ.range = 3 ^ 2 := Nat.eq_of_mul_eq_mul_right hpos (hc.symm.trans hcard)
    rw [h9]
    norm_num
  have hEel : IsElemAbelian 3 φ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨d, hd⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨e, he⟩ := MonoidHom.mem_range.1 b.2
      have hc : d * e = e * d := hD.1.is_comm.comm d e
      apply Subtype.ext
      show (a : MulAut (PSimple 3 L)) * (b : MulAut (PSimple 3 L)) =
        (b : MulAut (PSimple 3 L)) * (a : MulAut (PSimple 3 L))
      rw [← hd, ← he, ← map_mul, ← map_mul, hc]
    · rintro _ ⟨d, rfl⟩
      rw [← map_pow]
      have h3 : d ^ 3 = 1 := Subtype.ext (by simpa using hD.2 d.1 d.2)
      rw [h3, map_one]
  have hinnφ : ∀ α ∈ φ.range, α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (PSimple 3 L) := by
    rintro _ ⟨d, rfl⟩
    rw [hφ]
    have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
    have h1 := (CFSG.LocalAnalysis.GLTheoremA.MI.indAut_mem_inner_iff_any hq (hDN d.2)).2 (hinn d.1 d.2)
    have h2 : CFSG.LocalAnalysis.GLTheoremA.MI.indAut 3 L d.1 (hDN d.2) =
        (chevAut 3 L ⟨d.1, hDN d.2⟩)⁻¹ := by
      rw [CFSG.LocalAnalysis.GLTheoremA.MI.indAut, ← map_inv]; rfl
    rw [h2] at h1
    exact inv_mem_iff.1 h1
  have hsolv : Group.IsSolvable ↥(i269Fix φ.range) := hE φ.range hEel hEcard hinnφ
  haveI := hsolv
  set Y : Subgroup G := L ⊓ Subgroup.centralizer (D : Set G) with hYdef
  have hYL : Y ≤ L := inf_le_left
  have hYC : ∀ y ∈ Y, y ∈ Subgroup.centralizer (D : Set G) := fun y hy => (Subgroup.mem_inf.1 hy).2
  have key : ∀ J : Subgroup G, ¬ GLAPComponent 3 Y J := by
    intro J hJ
    have hJY : J ≤ Y := hJ.1
    have hJL : J ≤ L := hJY.trans hYL
    have hQq : CFSG.Open.IsQuasisimple
        ↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y))) := hJ.2.2.1.2.2
    let ψ : ↥J →* ↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y))) :=
      MonoidHom.codRestrict ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y)).comp (Subgroup.inclusion hJY))
        _ (fun x => Subgroup.mem_map.2 ⟨⟨x.1, hJY x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩)
    have hψsurj : Function.Surjective ψ := by
      intro q
      obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.1 q.2
      exact ⟨⟨y.1, Subgroup.mem_subgroupOf.1 hy⟩, Subtype.ext hyq⟩
    let F : ↥J →* (↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y))) ⧸
        Subgroup.center ↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y)))) :=
      (QuotientGroup.mk' _).comp ψ
    have hFsurj : Function.Surjective F := (QuotientGroup.mk'_surjective _).comp hψsurj
    have hcentral : ∀ x : ↥J, chevQuotHom 3 L ⟨x.1, hJL x.2⟩ = 1 →
        ψ x ∈ Subgroup.center ↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y))) := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hψsurj g
      apply Subtype.ext
      have hmemY : (y.1 * x.1)⁻¹ * (x.1 * y.1) ∈ Y :=
        Y.mul_mem (Y.inv_mem (Y.mul_mem (hJY y.2) (hJY x.2))) (Y.mul_mem (hJY x.2) (hJY y.2))
      have hyx : (y.1 * x.1)⁻¹ * (x.1 * y.1) ∈ GLAPPrimeCoreOf 3 Y :=
        inf_glaPPrimeCoreOf_le Nat.prime_three hYL
          (Subgroup.mem_inf.2 ⟨hmemY, commutator_mem_of_chevQuotHom_eq_one (hJL x.2) hx (hJL y.2)⟩)
      have hmk := mk_eq_of_mem_glaPPrimeCoreOf (Y := Y)
        (Y.mul_mem (hJY y.2) (hJY x.2)) (Y.mul_mem (hJY x.2) (hJY y.2)) hyx
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) (⟨y.1, hJY y.2⟩ : ↥Y) *
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) (⟨x.1, hJY x.2⟩ : ↥Y) =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) (⟨x.1, hJY x.2⟩ : ↥Y) *
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) (⟨y.1, hJY y.2⟩ : ↥Y)
      rw [← map_mul, ← map_mul]
      exact hmk
    let πJ : ↥J →* PSimple 3 L := (chevQuotHom 3 L).comp (Subgroup.inclusion hJL)
    have hkerF : πJ.ker ≤ F.ker := by
      intro x hx
      have hx' : chevQuotHom 3 L ⟨x.1, hJL x.2⟩ = 1 := MonoidHom.mem_ker.1 hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (ψ x)).2 (hcentral x hx')
    have hrange : πJ.range ≤ i269Fix φ.range := by
      intro k hk
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hk
      rw [mem_i269Fix]
      intro α hα
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.1 hα
      rw [hφ]
      exact chevAut_fix_chevQuotHom hDN d.2 (hJL x.2) (hYC x.1 (hJY x.2))
    haveI : Group.IsSolvable ↥πJ.range := isSolvable_of_le_isSolvable hrange
    exact not_isSolvable_quasisimple_mod_center _ hQq (isSolvable_of_factor πJ F hFsurj hkerF)
  show sSup {J : Subgroup G | GLAPComponent 3 Y J} = ⊥
  exact sSup_eq_bot.2 fun J hJ => absurd hJ (key J)

end CFSG.LocalAnalysis.GLTheoremA.I269Six

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.I269Six
open scoped commutatorElement

theorem i269SixAt_holds (G : Type) [Group G] [Finite G] : I269SixAt G := by
  intro X L D _ hL hcat hD hDN hinn hcard
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.U62RankSound.lieIndex_isU6two hcat
  obtain ⟨e'⟩ := LevelLieU6.bridge_u6two_stated hv hq e
  exact layer_eq_bot_of_E9_inner hL (E9SolvInner.of_mulEquiv E9SolvInner_S6 e') hDN hD hinn hcard

end CFSG.LocalAnalysis.GLTheoremA

end
