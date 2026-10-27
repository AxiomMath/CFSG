module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four5
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignTori

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.StandardType CFSG.RankThree.PartOne.KE

section FrameCoord

variable {L : Type} [Field L] {p : ℕ} [Fact p.Prime]

theorem frameDiag_mem_twistedTorus_iff_of_weyl (hp2 : p ≠ 2) (w : WeylGroup Tag.E8)
    {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {ζ : Lˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {lam : ZMod p}
    (hq : ((q : ℕ) : ZMod p) * lam = 1) (s : Fin Tag.E8.rank → ZMod p) :
    ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s ∈
        CFSG.RankThree.PartOne.KE.twistedTorus
          (canonicalRep (coxeterSystem Tag.E8) L w) Fr ↔
      s ∈ NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hdet : IsUnit (((Tag.E8).symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) hp2
  have hinj : Function.Injective (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ) :=
    ExcFrames.frameDiag_injective hζo hζ hdet
  have hpow : ∀ (m : ℕ) (t : Fin Tag.E8.rank → ZMod p),
      (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ t) ^ m =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (m • t) := by
    intro m
    induction m with
    | zero => intro t; rw [pow_zero, zero_nsmul, ExcFrames.frameDiag_zero]
    | succ m ih =>
        intro t
        rw [pow_succ, ih, ← ExcFrames.frameDiag_add, ← succ_nsmul]
  have hFx : Units.map (entrywiseHom Fr) (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s) =
      (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s) ^ q := by
    rw [ExcFrames.frameDiag]
    rw [CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit Fr hFr, ← rootDiagUnit_pow]
  have hconj := ExcFrames.canonicalRep_conj_frameDiag (τ := Tag.E8) ζ hζ w s
  have hkey : canonicalRep (coxeterSystem Tag.E8) L w *
        Units.map (entrywiseHom Fr) (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s) *
        (canonicalRep (coxeterSystem Tag.E8) L w)⁻¹ =
      ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
        (q • TableBExc.torusAct Tag.E8 p w s) := by
    rw [hFx, ← conj_pow, hconj, hpow q]
  rw [mem_twistedTorus]
  constructor
  · intro h
    have hqs : q • TableBExc.torusAct Tag.E8 p w s = s := by
      apply hinj
      rw [← hkey, h.2]
    have hsm : TableBExc.torusAct Tag.E8 p w s = lam • s := by
      have h' := congrArg (fun v : Fin Tag.E8.rank → ZMod p => lam • v) hqs
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) q
        (TableBExc.torusAct Tag.E8 p w s)] at h'
      rwa [smul_smul, mul_comm, hq, one_smul] at h'
    rw [NoOffRest.mem_eigSp, NoOffRest.torusLin_apply]
    exact hsm
  · intro hs
    have hsm : TableBExc.torusAct Tag.E8 p w s = lam • s := by
      have hs' := hs
      rw [NoOffRest.mem_eigSp, NoOffRest.torusLin_apply] at hs'
      exact hs'
    refine mem_twistedTorus.2 ⟨?_, ?_⟩
    · change rootDiagUnit Tag.E8
        (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord Tag.E8 p s)) ∈
          torusGroup Tag.E8 L
      exact CFSG.SeitzReduction.E8Pilot.rootDiagUnit_mem_torusGroup_E8 (K := L) _
    · rw [hkey, hinj.eq_iff, hsm, ← Nat.cast_smul_eq_nsmul (R := ZMod p) q (lam • s),
        smul_smul, hq, one_smul]

end FrameCoord

section LangTorsion

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {p : ℕ} [Fact p.Prime]

private noncomputable def frameEltOfWeyl (ζ : Lˣ) (hζ : ζ ^ p = 1) {lam : ZMod p}
    (w : WeylGroup Tag.E8) :
    Multiplicative (NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) →* ModGL Tag.E8 L where
  toFun s := ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
    ((Multiplicative.toAdd s : NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) :
      Fin Tag.E8.rank → ZMod p)
  map_one' := ExcFrames.frameDiag_zero ζ hζ
  map_mul' x y := by
    simp only [toAdd_mul, Submodule.coe_add]
    exact ExcFrames.frameDiag_add ζ hζ _ _

omit [Algebra.IsAlgebraic K L] in
private theorem frameEltOfWeyl_apply (ζ : Lˣ) (hζ : ζ ^ p = 1)
    {lam : ZMod p} (w : WeylGroup Tag.E8)
    (s : Multiplicative (NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam)) :
    frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w s =
      ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
        ((Multiplicative.toAdd s : NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) :
          Fin Tag.E8.rank → ZMod p) :=
  rfl

theorem exists_langTorsionHom_of_weyl (hp2 : p ≠ 2) (hp3 : 3 < p) (w : WeylGroup Tag.E8)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K) {ζ : Lˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {lam : ZMod p} (hq : ((Nat.card K : ℕ) : ZMod p) * lam = 1)
    {g₀ : ModGL Tag.E8 L} (hg₀C : g₀ ∈ adjointGroup Tag.E8 L)
    (hg₀ : Units.map (entrywiseHom Fr) g₀ = g₀ * canonicalRep (coxeterSystem Tag.E8) L w) :
    ∃ ι : Multiplicative (NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) →*
        adjointGroup Tag.E8 K,
      Function.Injective ι ∧ ∀ s : NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam,
        adjEmb Tag.E8 K L (ι (Multiplicative.ofAdd s)) =
          g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
            (s : Fin Tag.E8.rank → ZMod p) * g₀⁻¹ := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let n : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L w
  let F : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr)
  have hFg₀ : F g₀ = g₀ * n := hg₀
  let ψ : Multiplicative (NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) →*
      ModGL Tag.E8 L :=
    (MulAut.conj g₀).toMonoidHom.comp (frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w)
  let X : Subgroup (ModGL Tag.E8 L) := ψ.range
  have hXC : X ≤ adjointGroup Tag.E8 L := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨s, rfl⟩ := hx
    have hd : frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w s ∈ adjointGroup Tag.E8 L := by
      rw [frameEltOfWeyl_apply]
      exact CFSG.SeitzReduction.E8Pilot.rootDiagUnit_mem_adjointGroup_E8 _
    show (MulAut.conj g₀) (frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w s) ∈
      adjointGroup Tag.E8 L
    rw [MulAut.conj_apply]
    exact mul_mem (mul_mem hg₀C hd) (inv_mem hg₀C)
  have hXp : ∀ x ∈ X, x ^ p = 1 := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨s, rfl⟩ := hx
    have hd : frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w s ^ p = 1 := by
      rw [frameEltOfWeyl_apply]
      exact ExcFrames.frameDiag_pow ζ hζ _
    show ((MulAut.conj g₀).toMonoidHom
      (frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w s)) ^ p = 1
    rw [← map_pow, hd, map_one]
  have hXF : ∀ x ∈ X, F x = x := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨s, rfl⟩ := hx
    have hsd : ((Multiplicative.toAdd s :
        NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) : Fin Tag.E8.rank → ZMod p) ∈
        NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam := (Multiplicative.toAdd s).2
    have htor : ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
        ((Multiplicative.toAdd s :
          NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) : Fin Tag.E8.rank → ZMod p) ∈
        CFSG.RankThree.PartOne.KE.twistedTorus n Fr :=
      (frameDiag_mem_twistedTorus_iff_of_weyl hp2 w hFr hζo hζ hq _).2 hsd
    have htd : n * F (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
        ((Multiplicative.toAdd s :
          NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) : Fin Tag.E8.rank → ZMod p)) * n⁻¹ =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((Multiplicative.toAdd s :
            NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) : Fin Tag.E8.rank → ZMod p) :=
      (mem_twistedTorus.1 htor).2
    change F (g₀ * frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w s * g₀⁻¹) =
      g₀ * frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w s * g₀⁻¹
    rw [frameEltOfWeyl_apply, map_mul, map_mul, map_inv, hFg₀]
    have hconf : (g₀ * n) * F (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((Multiplicative.toAdd s :
            NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) :
            Fin Tag.E8.rank → ZMod p)) * (g₀ * n)⁻¹ =
        g₀ * (n * F (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((Multiplicative.toAdd s :
            NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) :
            Fin Tag.E8.rank → ZMod p)) * n⁻¹) * g₀⁻¹ := by group
    rw [hconf, htd]
  have hP : IsPGroup p X := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply orderOf_dvd_iff_pow_eq_one.mpr
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact hXp x x.2
  haveI : Finite X := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have frameElt_injective : Function.Injective
      (frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w) := by
    intro a b hab
    have hdet : IsUnit (((Tag.E8).symmetrizedCartan.det : ℤ) : ZMod p) :=
      ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) hp2
    have hdi := ExcFrames.frameDiag_injective (τ := Tag.E8) (ζ := ζ) hζo hζ hdet
    have h : ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((Multiplicative.toAdd a :
            NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) :
            Fin Tag.E8.rank → ZMod p) =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((Multiplicative.toAdd b :
            NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) :
            Fin Tag.E8.rank → ZMod p) := by
      rw [← frameEltOfWeyl_apply, ← frameEltOfWeyl_apply]
      exact hab
    exact Subtype.ext (hdi h)
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w a =
        frameEltOfWeyl (L := L) (p := p) (lam := lam) ζ hζ w b :=
      (MulAut.conj g₀).injective hab
    exact frameElt_injective h1
  have hrat := finite_fixed_subgroup_rational (τ := Tag.E8) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩))
    Fr hFr X hXC hXF
  have hXK : X ≤ (adjEmb Tag.E8 K L).range := by
    rw [adjEmb_range]
    exact hrat.2 p Fact.out hp3 X le_rfl hP
  let φ : Multiplicative (NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) →*
      (adjEmb Tag.E8 K L).range :=
    { toFun := fun s => ⟨ψ s, hXK (show ψ s ∈ X from MonoidHom.mem_range.2 ⟨s, rfl⟩)⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun a b => Subtype.ext (map_mul ψ a b) }
  have hInj : Function.Injective (adjEmb Tag.E8 K L) := adjEmb_injective
  let e : adjointGroup Tag.E8 K ≃* (adjEmb Tag.E8 K L).range := MonoidHom.ofInjective hInj
  let ι : Multiplicative (NoOffRest.eigSp (NoOffRest.torusLin .E8 p w) lam) →*
      adjointGroup Tag.E8 K :=
    e.symm.toMonoidHom.comp φ
  refine ⟨ι, ?_, ?_⟩
  · intro a b hab
    have h1 : φ a = φ b := e.symm.injective hab
    exact hψinj (congrArg Subtype.val h1)
  · intro s
    have hιs : adjEmb Tag.E8 K L (ι (Multiplicative.ofAdd s)) = ψ (Multiplicative.ofAdd s) :=
      MonoidHom.apply_ofInjective_symm hInj (φ (Multiplicative.ofAdd s))
    rw [hιs]
    rfl

end LangTorsion

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
