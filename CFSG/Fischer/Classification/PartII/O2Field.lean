module

public import CFSG.Fischer.Classification.PartII.O2Orient
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Fischer.F4

public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace O2Mod

section F4End

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def F4.re (c : F4) : ZMod 2 := (c.code.val % 2 : ℕ)

@[expose] def F4.im (c : F4) : ZMod 2 := (c.code.val / 2 : ℕ)

theorem F4.re_add : ∀ c d : F4, F4.re (c + d) = F4.re c + F4.re d := by decide

theorem F4.im_add : ∀ c d : F4, F4.im (c + d) = F4.im c + F4.im d := by decide

theorem F4.re_mul : ∀ c d : F4, F4.re (c * d) = F4.re c * F4.re d + F4.im c * F4.im d := by
  decide

theorem F4.im_mul : ∀ c d : F4,
    F4.im (c * d) = F4.re c * F4.im d + F4.im c * F4.re d + F4.im c * F4.im d := by
  decide

theorem F4.re_zero : F4.re 0 = 0 := by decide
theorem F4.im_zero : F4.im 0 = 0 := by decide
theorem F4.re_one : F4.re 1 = 1 := by decide
theorem F4.im_one : F4.im 1 = 0 := by decide
theorem F4.re_ω : F4.re F4.ω = 0 := by decide
theorem F4.im_ω : F4.im F4.ω = 1 := by decide

variable (J : V →ₗ[ZMod 2] V)

@[expose] def f4End (hJ : ∀ v, J (J v) = J v + v) : F4 →+* Module.End (ZMod 2) V where
  toFun c := F4.re c • 1 + F4.im c • J
  map_one' := by rw [F4.re_one, F4.im_one, one_smul, zero_smul, add_zero]
  map_zero' := by rw [F4.re_zero, F4.im_zero, zero_smul, zero_smul, add_zero]
  map_add' c d := by rw [F4.re_add, F4.im_add, add_smul, add_smul]; abel
  map_mul' c d := by
    ext v
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Module.End.one_apply, map_add, map_smul, hJ, F4.re_mul, F4.im_mul]
    module

theorem f4End_apply (hJ : ∀ v, J (J v) = J v + v) (c : F4) (v : V) :
    f4End J hJ c v = F4.re c • v + F4.im c • J v := rfl

end F4End

variable {H : Type} [Group H] {E μ : Set H}

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E) (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4)
include hμ hP h4

@[expose] def orient : ∀ s : ↥μ, Equiv.Perm (Fib E μ s) :=
  Classical.choose (hμ.exists_orientation hP h4)

theorem orient_spec :
    (∀ s f, hμ.orient hP h4 s f ≠ f) ∧ (∀ s f, hμ.orient hP h4 s (hμ.orient hP h4 s f) ≠ f) ∧
      (∀ s f, hμ.orient hP h4 s (hμ.orient hP h4 s (hμ.orient hP h4 s f)) = f) ∧
      ∀ (s t : ↥μ) (hst : (s : H) * t ≠ t * s) (f : Fib E μ s),
        hμ.matchEquiv hP (hμ.subset s.2) (hμ.subset t.2) hst (hμ.orient hP h4 s f) =
          hμ.orient hP h4 t (hμ.matchEquiv hP (hμ.subset s.2) (hμ.subset t.2) hst f) :=
  Classical.choose_spec (hμ.exists_orientation hP h4)

@[expose] def base (f : XT E μ) : ↥μ := ⟨sec E μ f, hμ.sec_mem f.2.1⟩

@[expose] def toFib (f : XT E μ) : Fib E μ (hμ.base f) :=
  ⟨f, isTwin_symm (hμ.isTwin_sec f.2.1), f.2.2⟩

@[expose] def jmap (f : XT E μ) : XT E μ :=
  ⟨hμ.orient hP h4 (hμ.base f) (hμ.toFib f), (hμ.orient hP h4 _ _).2.1.2.1,
    (hμ.orient hP h4 _ _).2.2⟩

theorem orient_val {s t : ↥μ} (h : s = t) (x : Fib E μ s) (y : Fib E μ t)
    (hxy : (x : H) = y) : (hμ.orient hP h4 s x : H) = hμ.orient hP h4 t y := by
  subst h
  rw [Subtype.ext hxy]

theorem jmap_eq {s : ↥μ} (f : XT E μ) (x : Fib E μ s) (hx : (x : H) = f) :
    (hμ.jmap hP h4 f : H) = hμ.orient hP h4 s x := by
  refine hμ.orient_val hP h4 ?_ _ _ hx.symm
  refine Subtype.ext ?_
  show sec E μ f = s
  rw [← hx]
  exact (hμ.eq_sec s.2 (isTwin_symm x.2.1)).symm

theorem isTwin_jmap (f : XT E μ) : IsTwin E f (hμ.jmap hP h4 f) :=
  isTwin_trans (hμ.isTwin_sec f.2.1) (hμ.orient hP h4 (hμ.base f) (hμ.toFib f)).2.1

theorem jmap_ne (f : XT E μ) : hμ.jmap hP h4 f ≠ f := fun e => by
  have h1 : ((hμ.jmap hP h4 f : XT E μ) : H) = (f : H) := by rw [e]
  exact (hμ.orient_spec hP h4).1 _ (hμ.toFib f) (Subtype.ext h1)

theorem jmap_jmap_val (f : XT E μ) :
    (hμ.jmap hP h4 (hμ.jmap hP h4 f) : H) =
      hμ.orient hP h4 (hμ.base f) (hμ.orient hP h4 (hμ.base f) (hμ.toFib f)) :=
  hμ.jmap_eq hP h4 _ _ rfl

theorem jmap_jmap_ne (f : XT E μ) : hμ.jmap hP h4 (hμ.jmap hP h4 f) ≠ f := fun e => by
  have h1 : ((hμ.jmap hP h4 (hμ.jmap hP h4 f) : XT E μ) : H) = (f : H) := by rw [e]
  exact (hμ.orient_spec hP h4).2.1 _ (hμ.toFib f)
    (Subtype.ext ((hμ.jmap_jmap_val hP h4 f).symm.trans h1))

theorem jmap_jmap_jmap (f : XT E μ) :
    hμ.jmap hP h4 (hμ.jmap hP h4 (hμ.jmap hP h4 f)) = f := by
  refine Subtype.ext ?_
  rw [hμ.jmap_eq hP h4 _ (hμ.orient hP h4 (hμ.base f) (hμ.orient hP h4 (hμ.base f) (hμ.toFib f)))
    (hμ.jmap_jmap_val hP h4 f).symm]
  exact congrArg Subtype.val ((hμ.orient_spec hP h4).2.2.1 _ (hμ.toFib f))

theorem mate_jmap (f : XT E μ) {g : H} (hg : g ∈ E) (hfg : (f : H) * g ≠ g * f) :
    mate E μ (hμ.jmap hP h4 f) g =
      hμ.jmap hP h4 ⟨mate E μ f g, hμ.mate_mem hP f.2.1 f.2.2 hg hfg,
        hμ.mate_notMem hP f.2.1 f.2.2 hg hfg⟩ := by
  set t : ↥μ := ⟨sec E μ g, hμ.sec_mem hg⟩
  have hgt : IsTwin E g (sec E μ g) := hμ.isTwin_sec hg
  have hst : (hμ.base f : H) * t ≠ t * hμ.base f := by
    have h1 : sec E μ f * g ≠ g * sec E μ f := not_commute_of_isTwin (hμ.isTwin_sec f.2.1) hg hfg
    have h2 := not_commute_of_isTwin hgt (hμ.subset (hμ.sec_mem f.2.1)) fun e => h1 e.symm
    exact fun e => h2 e.symm
  have key := congrArg Subtype.val ((hμ.orient_spec hP h4).2.2.2 (hμ.base f) t hst (hμ.toFib f))
  rw [matchEquiv_apply] at key
  have hjg : (hμ.jmap hP h4 f : H) * g ≠ g * hμ.jmap hP h4 f :=
    not_commute_of_isTwin (hμ.isTwin_jmap hP h4 f) hg hfg
  calc mate E μ (hμ.jmap hP h4 f) g = mate E μ (hμ.jmap hP h4 f) (sec E μ g) :=
        (hμ.mate_congr hP (hμ.jmap hP h4 f).2.1 (hμ.jmap hP h4 f).2.2 hg hjg hgt).symm
    _ = _ := key
    _ = _ := (hμ.jmap_eq hP h4 _ _ (by
        rw [matchEquiv_apply]
        exact hμ.mate_congr hP f.2.1 f.2.2 hg hfg hgt)).symm

theorem jmap_injective : Function.Injective (hμ.jmap hP h4) := fun a b h => by
  have := congrArg (fun x => hμ.jmap hP h4 (hμ.jmap hP h4 x)) h
  simpa only [hμ.jmap_jmap_jmap hP h4] using this

theorem bform_jmap (f g : XT E μ) :
    bform μ (hμ.jmap hP h4 f : H) (hμ.jmap hP h4 g) = bform μ (f : H) g := by
  have hf := hμ.isTwin_jmap hP h4 f
  have hg := hμ.isTwin_jmap hP h4 g
  have hcomm : (f : H) * g = g * f ↔
      (hμ.jmap hP h4 f : H) * hμ.jmap hP h4 g = hμ.jmap hP h4 g * hμ.jmap hP h4 f := by
    rw [(hg.2.2.2 f f.2.1)]
    have := hf.2.2.2 _ (hμ.jmap hP h4 g).2.1
    constructor
    · intro h; exact (this.1 h.symm).symm
    · intro h; exact (this.2 h.symm).symm
  by_cases hfg : (f : H) * g = g * f
  · rw [bform_of_commute hfg, bform_of_commute (hcomm.1 hfg)]
  have hfg' : (hμ.jmap hP h4 f : H) * hμ.jmap hP h4 g ≠ hμ.jmap hP h4 g * hμ.jmap hP h4 f :=
    fun e => hfg (hcomm.2 e)
  have hjg : (hμ.jmap hP h4 f : H) * g ≠ g * hμ.jmap hP h4 f :=
    not_commute_of_isTwin hf g.2.1 hfg
  have hz : ∀ x y : ZMod 2, (x = 0 ↔ y = 0) → x = y := fun x y h => by
    rcases Symplectic.zmod_two_cases x with hx | hx <;>
      rcases Symplectic.zmod_two_cases y with hy | hy <;> simp_all
  refine hz _ _ ?_
  rw [hμ.bform_eq_zero_iff_mate hP (hμ.jmap hP h4 f).2.1 (hμ.jmap hP h4 f).2.2
      (hμ.jmap hP h4 g).2.1 (hμ.jmap hP h4 g).2.2 hfg',
    hμ.bform_eq_zero_iff_mate hP f.2.1 f.2.2 g.2.1 g.2.2 hfg,
    hμ.mate_congr hP (hμ.jmap hP h4 f).2.1 (hμ.jmap hP h4 f).2.2 g.2.1 hjg hg,
    hμ.mate_jmap hP h4 f g.2.1 hfg]
  constructor
  · intro h
    have := hμ.jmap_injective hP h4 (Subtype.ext h)
    exact congrArg Subtype.val this
  · intro h
    exact congrArg Subtype.val (congrArg (hμ.jmap hP h4) (Subtype.ext h :
      (⟨mate E μ f g, hμ.mate_mem hP f.2.1 f.2.2 g.2.1 hfg,
        hμ.mate_notMem hP f.2.1 f.2.2 g.2.1 hfg⟩ : XT E μ) = g))

@[expose] def jfree : (XT E μ →₀ ZMod 2) →ₗ[ZMod 2] (XT E μ →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (hμ.jmap hP h4)

theorem jfree_single (f : XT E μ) (a : ZMod 2) :
    hμ.jfree hP h4 (Finsupp.single f a) = Finsupp.single (hμ.jmap hP h4 f) a := by
  simp [jfree, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem freeForm_jfree (φ ψ : XT E μ →₀ ZMod 2) :
    freeForm E μ (hμ.jfree hP h4 φ) (hμ.jfree hP h4 ψ) = freeForm E μ φ ψ := by
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add φ₁ φ₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | single f a =>
    induction ψ using Finsupp.induction_linear with
    | zero => simp
    | add ψ₁ ψ₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single g c =>
      rw [hμ.jfree_single hP h4, hμ.jfree_single hP h4, freeForm_single, freeForm_single,
        hμ.bform_jmap hP h4]

theorem jfree_jfree_jfree (φ : XT E μ →₀ ZMod 2) :
    hμ.jfree hP h4 (hμ.jfree hP h4 (hμ.jfree hP h4 φ)) = φ := by
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add φ₁ φ₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single f a => rw [hμ.jfree_single hP h4, hμ.jfree_single hP h4, hμ.jfree_single hP h4,
      hμ.jmap_jmap_jmap hP h4]

theorem ker_le_comap_jfree :
    LinearMap.ker (freeForm E μ) ≤ (LinearMap.ker (freeForm E μ)).comap (hμ.jfree hP h4) := by
  intro φ hφ
  rw [Submodule.mem_comap, mem_ker_freeForm]
  intro ψ
  rw [← hμ.jfree_jfree_jfree hP h4 ψ, hμ.freeForm_jfree hP h4]
  exact mem_ker_freeForm.1 hφ _

@[expose] def jmod : SecModule E μ →ₗ[ZMod 2] SecModule E μ :=
  (LinearMap.ker (freeForm E μ)).mapQ (LinearMap.ker (freeForm E μ)) (hμ.jfree hP h4)
    (hμ.ker_le_comap_jfree hP h4)

theorem jmod_vec (f : XT E μ) : hμ.jmod hP h4 (vec f) = vec (hμ.jmap hP h4 f) := by
  simp [jmod, vec, hμ.jfree_single hP h4]

theorem secForm_jmod (u v : SecModule E μ) :
    secForm hP (hμ.jmod hP h4 u) (hμ.jmod hP h4 v) = secForm hP u v := by
  induction u using Submodule.Quotient.induction_on with
  | H φ =>
    induction v using Submodule.Quotient.induction_on with
    | H ψ =>
      simp only [jmod, Submodule.mapQ_apply, secForm_mk]
      exact hμ.freeForm_jfree hP h4 φ ψ

theorem jmod_jmod (v : SecModule E μ) : hμ.jmod hP h4 (hμ.jmod hP h4 v) = hμ.jmod hP h4 v + v := by
  have hv : v ∈ Submodule.span (ZMod 2) (Set.range (vec (E := E) (μ := μ))) := by
    rw [span_range_vec]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    rw [hμ.jmod_vec hP h4, hμ.jmod_vec hP h4]
    have hf := hμ.isTwin_jmap hP h4 f
    have h3 := hμ.vec_add_add hP h4 (a := f) (b := hμ.jmap hP h4 f)
      (c := hμ.jmap hP h4 (hμ.jmap hP h4 f)) hf
      (isTwin_trans hf (hμ.isTwin_jmap hP h4 _))
      (fun e => hμ.jmap_ne hP h4 f (Subtype.ext e.symm))
      (fun e => hμ.jmap_jmap_ne hP h4 f (Subtype.ext e.symm))
      (fun e => hμ.jmap_ne hP h4 _ (Subtype.ext e.symm))
    calc vec (hμ.jmap hP h4 (hμ.jmap hP h4 f))
        = -(vec f + vec (hμ.jmap hP h4 f)) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]; exact h3
      _ = vec (hμ.jmap hP h4 f) + vec f := by rw [Symplectic.zmod_two_neg, add_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]; abel
  | smul a x _ hx => rw [map_smul, map_smul, hx, smul_add]

end IsTwinSection

end O2Mod

end CFSG.Fischer.Classification
