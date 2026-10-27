module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Small
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Sp
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitOrbit
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnLift
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutModel
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.LargeExtraspecial.A2ModCfg
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB51LnRealB

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section Family

open scoped Classical

variable {P : Type*} [AddCommGroup P] {p : ℕ} [Fact p.Prime] {S : Type*} [Group S] [Finite S]
  {ι : Type} [Fintype ι]

theorem horb_of_family (ψ : Multiplicative P →* S) (t : ι → S) (τ : ι → P →+ P)
    (ht : ∀ i x, t i * ψ x * (t i)⁻¹ = ψ (Multiplicative.ofAdd (τ i (Multiplicative.toAdd x))))
    {T₀ : Subgroup S} (hT : ∀ i, t i ∈ T₀) {D₀ : Subgroup S} (hrel : D₀.relIndex ψ.range = p)
    {m : ℕ} (hm : ∀ l : P →+ ZMod p, l ≠ 0 →
      m ≤ ((Finset.univ : Finset ι).image fun i => (l.comp (τ i)).ker).card) :
    m ≤ (T₀ ⊓ Subgroup.normalizer (D₀ : Set S)).relIndex T₀ := by
  have hDidx : (D₀.comap ψ).index = p := by
    rw [Subgroup.index_comap]
    exact hrel
  have hDaidx : (AddSubgroup.toSubgroup.symm (D₀.comap ψ)).index = p := by
    rw [← AddSubgroup.index_toSubgroup, OrderIso.apply_symm_apply]
    exact hDidx
  obtain ⟨l, hl⟩ := exists_hom_of_index_eq_prime _ hDaidx
  have hlD : ∀ z : P, l z = 0 ↔ ψ (Multiplicative.ofAdd z) ∈ D₀ := fun z =>
    (hl z).trans (mem_toSubgroup_symm _ z)
  have hl0 : l ≠ 0 := by
    intro h0
    have htop : AddSubgroup.toSubgroup.symm (D₀.comap ψ) = ⊤ := by
      rw [eq_top_iff]
      intro z _
      exact (hl z).1 (by rw [h0]; rfl)
    rw [htop, AddSubgroup.index_top] at hDaidx
    exact (Fact.out : p.Prime).one_lt.ne hDaidx
  have hker : ∀ i, (l.comp (τ i)).ker =
      AddSubgroup.toSubgroup.symm ((conjSub (t i)⁻¹ D₀).comap ψ) := by
    intro i
    ext z
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hlD, mem_toSubgroup_symm,
      Subgroup.mem_comap, mem_conjSub, inv_inv, ht i (Multiplicative.ofAdd z), toAdd_ofAdd]
  let s : Finset S := Finset.univ.image fun i : ι => (t i)⁻¹
  have hs : ∀ y ∈ s, y ∈ T₀ := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact T₀.inv_mem (hT i)
  have h1 := card_image_conj_le_relIndex T₀ D₀ s hs
  let G : Subgroup S → AddSubgroup P := fun C => AddSubgroup.toSubgroup.symm (C.comap ψ)
  have hcomp : (Finset.univ.image fun i => (l.comp (τ i)).ker) =
      (s.image fun y => conjSub y D₀).image G := by
    simp only [s, Finset.image_image]
    congr 1
    funext i
    exact hker i
  have h2 : (Finset.univ.image fun i => (l.comp (τ i)).ker).card ≤
      (s.image fun y => conjSub y D₀).card := by
    rw [hcomp]
    exact Finset.card_image_le
  exact (hm l hl0).trans (h2.trans h1)

end Family

section Coeff

abbrev X5 : Type := ZMod 5 × ZMod 5 × ZMod 5

@[expose] def tauHom (B : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5) : X5 →+ X5 where
  toFun x := (B.1 ^ 2 * x.1 + 2 * B.1 * B.2.2.1 * x.2.1 + B.2.2.1 ^ 2 * x.2.2,
    B.1 * B.2.1 * x.1 + (B.1 * B.2.2.2 + B.2.1 * B.2.2.1) * x.2.1 + B.2.2.1 * B.2.2.2 * x.2.2,
    B.2.1 ^ 2 * x.1 + 2 * B.2.1 * B.2.2.2 * x.2.1 + B.2.2.2 ^ 2 * x.2.2)
  map_zero' := by simp
  map_add' x y := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> ring

@[expose] def actC (B : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5) (v : X5) : X5 :=
  (v.1 * B.1 ^ 2 + v.2.1 * B.1 * B.2.1 + v.2.2 * B.2.1 ^ 2,
    2 * v.1 * B.1 * B.2.2.1 + v.2.1 * (B.1 * B.2.2.2 + B.2.1 * B.2.2.1) +
      2 * v.2.2 * B.2.1 * B.2.2.2,
    v.1 * B.2.2.1 ^ 2 + v.2.1 * B.2.2.1 * B.2.2.2 + v.2.2 * B.2.2.2 ^ 2)

@[expose] def norm5 (v : X5) : X5 :=
  if v.1 ≠ 0 then v.1⁻¹ • v else if v.2.1 ≠ 0 then v.2.1⁻¹ • v else
    if v.2.2 ≠ 0 then v.2.2⁻¹ • v else 0

@[expose] def Bs : Fin 8 → ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5
  | 0 => (0, 1, 1, 2)
  | 1 => (4, 1, 3, 3)
  | 2 => (0, 2, 2, 0)
  | 3 => (2, 2, 1, 3)
  | 4 => (2, 4, 3, 3)
  | 5 => (1, 0, 1, 1)
  | 6 => (4, 2, 0, 4)
  | 7 => (0, 3, 2, 3)

theorem Bs_det (i : Fin 8) : (Bs i).1 * (Bs i).2.2.2 - (Bs i).2.1 * (Bs i).2.2.1 ≠ 0 := by
  revert i; decide

theorem norm5_smul : ∀ (k : ZMod 5) (v : X5), k ≠ 0 → v ≠ 0 → norm5 (k • v) = norm5 v := by
  decide +kernel

theorem actC_ne_zero : ∀ (i : Fin 8) (v : X5), v ≠ 0 → actC (Bs i) v ≠ 0 := by decide +kernel

theorem count_ge_six : ∀ v : X5, v ≠ 0 →
    6 ≤ ((Finset.univ : Finset (Fin 8)).image fun i => norm5 (actC (Bs i) v)).card := by
  decide +kernel

theorem exists_coeff (l : X5 →+ ZMod 5) :
    ∃ v : X5, ∀ x : X5, l x = v.1 * x.1 + v.2.1 * x.2.1 + v.2.2 * x.2.2 := by
  refine ⟨(l (1, 0, 0), l (0, 1, 0), l (0, 0, 1)), fun x => ?_⟩
  have hx : x = x.1.val • ((1 : ZMod 5), (0 : ZMod 5), (0 : ZMod 5)) +
      x.2.1.val • ((0 : ZMod 5), (1 : ZMod 5), (0 : ZMod 5)) +
      x.2.2.val • ((0 : ZMod 5), (0 : ZMod 5), (1 : ZMod 5)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  conv_lhs => rw [hx]
  simp only [map_add, map_nsmul]
  simp only [nsmul_eq_mul, ZMod.natCast_zmod_val]
  ring

theorem coeff_comp_tau {l : X5 →+ ZMod 5} {v : X5}
    (hv : ∀ x : X5, l x = v.1 * x.1 + v.2.1 * x.2.1 + v.2.2 * x.2.2)
    (B : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5) :
    ∀ x : X5, (l.comp (tauHom B)) x =
      (actC B v).1 * x.1 + (actC B v).2.1 * x.2.1 + (actC B v).2.2 * x.2.2 := by
  intro x
  rw [AddMonoidHom.comp_apply, hv]
  simp only [tauHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, actC]
  ring

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

open scoped Classical in
theorem six_kernels (l : X5 →+ ZMod 5) (hl : l ≠ 0) :
    6 ≤ ((Finset.univ : Finset (Fin 8)).image fun i => (l.comp (tauHom (Bs i))).ker).card := by
  obtain ⟨v, hv⟩ := exists_coeff l
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hl (AddMonoidHom.ext fun x => by rw [hv]; simp)
  have hcoef : ∀ (B : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5) (w : X5),
      (∀ x : X5, (l.comp (tauHom B)) x = w.1 * x.1 + w.2.1 * x.2.1 + w.2.2 * x.2.2) → w = actC B v := by
    intro B w hw
    have h := coeff_comp_tau hv B
    have e1 := (hw (1, 0, 0)).symm.trans (h (1, 0, 0))
    have e2 := (hw (0, 1, 0)).symm.trans (h (0, 1, 0))
    have e3 := (hw (0, 0, 1)).symm.trans (h (0, 0, 1))
    simp at e1 e2 e3
    exact Prod.ext e1 (Prod.ext e2 e3)
  set f : Fin 8 → X5 := fun i => norm5 (actC (Bs i) v) with hf
  set g : Fin 8 → AddSubgroup X5 := fun i => (l.comp (tauHom (Bs i))).ker with hg
  have hfg : ∀ i j, g i = g j → f i = f j := by
    intro i j hij
    have hne : l.comp (tauHom (Bs i)) ≠ 0 := by
      intro h0
      apply actC_ne_zero i v hv0
      have := coeff_comp_tau hv (Bs i)
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simpa [h0] using (this (1, 0, 0)).symm
      · simpa [h0] using (this (0, 1, 0)).symm
      · simpa [h0] using (this (0, 0, 1)).symm
    have hker : ∀ x, (l.comp (tauHom (Bs i))) x = 0 ↔ (l.comp (tauHom (Bs j))) x = 0 := by
      intro x
      have := SetLike.ext_iff.1 hij x
      simpa [hg] using this
    obtain ⟨k, hk⟩ := exists_smul_of_ker_eq_addHom _ _ hne hker
    have hkv : actC (Bs j) v = k • actC (Bs i) v := by
      refine (hcoef (Bs j) (k • actC (Bs i) v) fun x => ?_).symm
      refine (hk x).trans ?_
      have h3 := coeff_comp_tau hv (Bs i) x
      refine (congrArg (fun y => k * y) h3).trans ?_
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact actC_ne_zero j v hv0 (by rw [hkv, zero_smul])
    simp only [hf]
    rw [hkv, norm5_smul k _ hk0 (actC_ne_zero i v hv0)]
  have hcard : ((Finset.univ : Finset (Fin 8)).image f).card ≤
      ((Finset.univ : Finset (Fin 8)).image g).card := by
    let h : AddSubgroup X5 → X5 := fun D => if hD : ∃ i, g i = D then f hD.choose else 0
    have hfh : ∀ i, f i = h (g i) := by
      intro i
      have hD : ∃ j, g j = g i := ⟨i, rfl⟩
      show f i = if hD : ∃ i', g i' = g i then f hD.choose else 0
      simp only [hD, ↓reduceDIte]
      exact (hfg _ _ hD.choose_spec).symm
    have : (Finset.univ : Finset (Fin 8)).image f = ((Finset.univ : Finset (Fin 8)).image g).image h := by
      rw [Finset.image_image]
      exact Finset.image_congr fun i _ => hfh i
    rw [this]
    exact Finset.card_image_le
  exact (count_ge_six v hv0).trans hcard

end Coeff

section Group

open Matrix CFSG.Assembly.LowTwoRank CFSG.LargeExtraspecial.A2Mod.FrC
open CFSG.LieType.Universal.Symplectic

variable {K : Type} [Field K] (φ : ZMod 5 →+* K)

@[expose] def symM (x : X5) : Matrix (Fin 2) (Fin 2) K :=
  !![φ x.1, φ x.2.1; φ x.2.1, φ x.2.2]

theorem symM_transpose (x : X5) : (symM φ x)ᵀ = symM φ x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symM]

theorem symM_add (x y : X5) : symM φ (x + y) = symM φ x + symM φ y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symM]

theorem symM_zero : symM φ 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symM]

@[expose] noncomputable def psi0 : Multiplicative X5 →* StatedSp 2 K where
  toFun x := lower (symM φ (Multiplicative.toAdd x)) (symM_transpose φ _)
  map_one' := ext_mat (by
    rw [toAdd_one, mat_lower, symM_zero, fromBlocks_one]
    rfl)
  map_mul' x y := ext_mat (by
    rw [toAdd_mul, map_mul, mat_lower, mat_lower, mat_lower, symM_add, fromBlocks_multiply]
    simp [add_comm])

@[expose] noncomputable def psi : Multiplicative X5 →* StatedProj (StatedSp 2 K) :=
  (QuotientGroup.mk' _).comp (psi0 φ)

@[expose] def Bmat (i : Fin 8) : Matrix (Fin 2) (Fin 2) K :=
  !![φ (Bs i).1, φ (Bs i).2.1; φ (Bs i).2.2.1, φ (Bs i).2.2.2]

theorem Bmat_det (hφ : Function.Injective φ) (i : Fin 8) : (Bmat φ i).det ≠ 0 := by
  rw [Matrix.det_fin_two]
  simp only [Bmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← map_mul, ← map_mul, ← map_sub]
  intro h
  exact Bs_det i (hφ (h.trans (map_zero φ).symm))

@[expose] noncomputable def Bgl (hφ : Function.Injective φ) (i : Fin 8) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Bmat φ i) (Bmat_det φ hφ i)

theorem symM_tau (i : Fin 8) (x : X5) :
    symM φ (tauHom (Bs i) x) = (Bmat φ i)ᵀ * symM φ x * Bmat φ i := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [symM, Bmat, tauHom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      map_ofNat] <;> ring

theorem levGL_conj_psi0 (hφ : Function.Injective φ) (i : Fin 8) (x : Multiplicative X5) :
    levGL ((Bgl φ hφ i)⁻¹) * psi0 φ x * (levGL ((Bgl φ hφ i)⁻¹))⁻¹ =
      psi0 φ (Multiplicative.ofAdd (tauHom (Bs i) (Multiplicative.toAdd x))) := by
  refine levGL_conj_lower ((Bgl φ hφ i)⁻¹) (symM_transpose φ _) (symM_transpose φ _) ?_
  rw [toAdd_ofAdd, inv_inv, symM_tau]
  rfl

@[expose] noncomputable def tEl (hφ : Function.Injective φ) (i : Fin 8) :
    StatedProj (StatedSp 2 K) :=
  QuotientGroup.mk' _ (levGL ((Bgl φ hφ i)⁻¹))

theorem tEl_conj (hφ : Function.Injective φ) (i : Fin 8) (x : Multiplicative X5) :
    tEl φ hφ i * psi φ x * (tEl φ hφ i)⁻¹ =
      psi φ (Multiplicative.ofAdd (tauHom (Bs i) (Multiplicative.toAdd x))) := by
  have := congrArg (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
    (StatedSp 2 K))) (levGL_conj_psi0 φ hφ i x)
  simpa [tEl, psi, map_mul, map_inv] using this

theorem mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] [Finite G] {U : Subgroup G} {t : G}
    (h : ∀ y ∈ U, t * y * t⁻¹ ∈ U) : t ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  let f : U → U := fun z => ⟨t * z * t⁻¹, h z z.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨z, hz⟩ := Finite.surjective_of_injective hinj ⟨t * y * t⁻¹, hy⟩
  have : t * (z : G) * t⁻¹ = t * y * t⁻¹ := congrArg Subtype.val hz
  have hzy : (z : G) = y := by simpa using this
  rw [← hzy]
  exact z.2

theorem psi_ne_one : psi φ (Multiplicative.ofAdd ((1 : ZMod 5), (0 : ZMod 5), (0 : ZMod 5))) ≠ 1 := by
  intro h
  rw [psi, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (c : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
  have h1 : SpExtras.mat 2 K (psi0 φ (Multiplicative.ofAdd ((1 : ZMod 5), (0 : ZMod 5),
      (0 : ZMod 5)))) = (c : K) • 1 := by
    rw [SpExtras.mat_apply, ← hs, hc]
  have e := congrFun (congrFun h1 (Sum.inr 0)) (Sum.inl 0)
  simp [psi0, symM] at e

theorem pow_five_eq_one (x : Multiplicative X5) : x ^ 5 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  revert x
  decide +kernel

theorem orderOf_two_zmod_five_eq_four : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

variable {W : Type} [CommGroup W] [Finite W]

set_option maxHeartbeats 400000 in
theorem horb45 [CharP K 5] [Finite K] (hφ : Function.Injective φ)
    (hT : ∀ i, tEl φ hφ i ∈ Subgroup.normalizer ((psi φ).range : Set (StatedProj (StatedSp 2 K))))
    (D₀ : Subgroup (StatedProj (StatedSp 2 K))) (hrel : D₀.relIndex (psi φ).range = 5) :
    6 ≤ (Subgroup.normalizer ((psi φ).range : Set (StatedProj (StatedSp 2 K))) ⊓
      Subgroup.normalizer (D₀ : Set (StatedProj (StatedSp 2 K)))).relIndex
        (Subgroup.normalizer ((psi φ).range : Set (StatedProj (StatedSp 2 K)))) := by
  have : Finite (StatedProj (StatedSp 2 K)) := inferInstance
  exact horb_of_family (P := X5) (p := 5) (ι := Fin 8) (psi φ) (tEl φ hφ) (fun i => tauHom (Bs i))
    (tEl_conj φ hφ) hT hrel six_kernels

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_of_psp45 (hW : ∀ w : W, w * w = 1) [CharP K 5] [Finite K]
    {L : Subgroup (MulAut W)} (θ : ↥L ≃* StatedProj (StatedSp 2 K)) : 2 ^ 24 ≤ Nat.card W := by
  let φ : ZMod 5 →+* K := ZMod.castHom (dvd_refl 5) K
  have hφ : Function.Injective φ := φ.injective
  have hker : (θ.toMonoidHom).ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    exact θ.injective
  have hT : ∀ i, tEl φ hφ i ∈ Subgroup.normalizer ((psi φ).range : Set (StatedProj (StatedSp 2 K))) := by
    intro i
    refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
    obtain ⟨x, rfl⟩ := hy
    rw [tEl_conj]
    exact ⟨_, rfl⟩
  have hUc : ∀ a ∈ (psi φ).range, ∀ b ∈ (psi φ).range, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hUp : ∀ a ∈ (psi φ).range, a ^ 5 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow, pow_five_eq_one x, map_one]
  have hU : (psi φ).range ≠ ⊥ := fun h =>
    psi_ne_one φ (by rw [← Subgroup.mem_bot, ← h]; exact ⟨_, rfl⟩)
  have key := two_pow_le_card_of_lift_orbit (p := 5) hW (by norm_num) θ.toMonoidHom θ.surjective
    (by rw [hker]; exact bot_le) (by rw [hker, Subgroup.card_bot]; norm_num) hUc hUp hU le_rfl
    (m := 6) (fun D₀ _ hrel => horb45 φ hφ hT D₀ hrel)
  rw [orderOf_two_zmod_five_eq_four] at key
  simpa using key

end Group

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator

theorem noIrrFFOffender_smallPSp45 {q : PrimePower} (hv : (LieTypeIndex.B 2 q).Valid)
    (h5 : q.card = 5) : NoIrrFFOffender (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp : q.p.Prime := q.prime_p
  have hcard : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hp5 : q.p = 5 := by
    have h1 : q.p ∣ 5 := by
      rw [← h5, hcard]; exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1
  have he1 : q.exponent = 1 := by
    have h1 : 5 ^ q.exponent = 5 ^ 1 := by rw [← hp5, ← hcard, h5, hp5]; rfl
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) h1
  have hp2 : q.p ≠ 2 := by rw [hp5]; norm_num
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨hcenter, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_psp_model_of_lie_B2 hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv e hp2
      (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = q.p ^ q.exponent := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K q.p := charP_of_card_eq_prime_pow hKcard
  have : CharP K 5 := by rwa [← hp5]
  have hdim := two_pow_le_card_of_psp45 hW θ
  have hord := card_sup_le_of_pspn hW hp2 hK le_rfl hirr hcenter θ hEN hel
  rw [hp5, he1] at hord
  norm_num at hord
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  norm_num at hdim
  omega

theorem smallPSp45 : SmallPSp45 := by
  intro d q hq hd
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_smallPSp45 hv hq)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
