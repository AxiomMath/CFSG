module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLinTransPsl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBlockDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinJ

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
  CFSG.LieType.SemisimpleCentralizers.HeldLang CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
  CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup
  glaPComponent_map_fixSubgroup)
open scoped commutatorElement MatrixGroups

theorem linJ_equiv_comm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω}
    (hxp : x ^ p = 1) (hxN : x ∈ Subgroup.normalizer (S : Set Ω))
    (hyN : y ∈ Subgroup.normalizer (S : Set Ω))
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω))
    {d : ℕ} {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) (hd : 1 ≤ d)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (StatedSL d K))
    (A B : GL (Fin d) K) (hcomm : A * B = B * A)
    (φx ψ : MulAut (LargeEvenProj (StatedSL d K)))
    (hA : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      φx (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hψ : ∀ g g' : ↥(StatedSL d K), (g' : GL (Fin d) K) = B * (g : GL (Fin d) K) * B⁻¹ →
      ψ (LargeEvenProjMk (StatedSL d K) g) = LargeEvenProjMk (StatedSL d K) g')
    (hindx : LargeEvenInduces θ (conjRel x) φx)
    (hindy : LargeEvenInduces θ (conjRel y) ψ) :
    ∃ (d₁ : ℕ) (D₁ : Type) (_ : Field D₁) (_ : Finite D₁) (B₁ : GL (Fin d₁) D₁)
      (e₀ : PSimple p J ≃* LargeEvenProj (StatedSL d₁ D₁)),
      (2 : D₁) = 0 ∧ 2 ≤ d₁ ∧ (d₁ ≠ 2 ∨ Nat.card D₁ ≠ 2) ∧ (d₁ ≠ 2 ∨ Nat.card D₁ ≠ 3) ∧
      ∀ m : ↥(StatedSL d₁ D₁),
        MulAut.congr e₀ (MI.indAut p J y hJy)
            (LargeEvenProjMk (StatedSL d₁ D₁) m) =
          LargeEvenProjMk (StatedSL d₁ D₁)
            ⟨B₁ * (m : GL (Fin d₁) D₁) * B₁⁻¹,
              (inferInstance : (StatedSL d₁ D₁).Normal).conj_mem m m.2 B₁⟩ := by
  classical
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  let ρS : ↥S →* LargeEvenProj (StatedSL d K) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))
  have hker : ρS.ker ≤ Subgroup.center ↥S := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h1 : QuotientGroup.mk' (Subgroup.center ↥S) s = 1 := by
      apply θ.injective
      rw [map_one]
      exact hs
    exact (QuotientGroup.eq_one_iff s).1 h1
  have hsurj : Function.Surjective ρS := by
    intro r
    obtain ⟨a, ha⟩ := θ.surjective r
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥S) a
    exact ⟨s, ha⟩
  let α : MulAut ↥S := S.normalizerMonoidHom ⟨x⁻¹, Subgroup.inv_mem _ hxN⟩
  have hα : ∀ s : ↥S, ((α s : ↥S) : Ω) = x⁻¹ * (s : Ω) * x := by
    intro s
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hfix : fixSubgroup α = (S ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S := by
    ext s
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hs
      have h2 : ((α s : ↥S) : Ω) = (s : Ω) := congrArg Subtype.val hs
      rw [hα] at h2
      refine ⟨s.2, ?_⟩
      calc (s : Ω) * x = x * (x⁻¹ * (s : Ω) * x) := by group
        _ = x * (s : Ω) := by rw [h2]
    · rintro ⟨-, hs⟩
      apply Subtype.ext
      rw [hα]
      calc x⁻¹ * (s : Ω) * x = x⁻¹ * ((s : Ω) * x) := by group
        _ = x⁻¹ * (x * (s : Ω)) := by rw [hs]
        _ = (s : Ω) := by group
  have hαβ : ∀ s : ↥S, ρS (α s) = φx (ρS s) := by
    intro s
    exact (hindx s (α s) (hα s)).symm
  have hαpow : α ^ p = 1 := by
    ext s
    have hiter : ∀ k : ℕ, (((α ^ k) s : ↥S) : Ω) = (x⁻¹) ^ k * (s : Ω) * x ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', MulAut.mul_apply, hα, ih, pow_succ', pow_succ]
        group
    rw [hiter p, inv_pow, hxp, inv_one, one_mul, mul_one]
    rfl
  have hφxpow : φx ^ p = 1 := by
    have h1 : ∀ k : ℕ, ∀ s : ↥S, (φx ^ k) (θ (QuotientGroup.mk' (Subgroup.center ↥S) s)) =
        θ (QuotientGroup.mk' (Subgroup.center ↥S) ((α ^ k) s)) := by
      intro k
      induction k with
      | zero => intro s; simp
      | succ k ih =>
        intro s
        rw [pow_succ', MulAut.mul_apply, ih]
        rw [show φx (θ (QuotientGroup.mk' (Subgroup.center ↥S) ((α ^ k) s))) =
            θ (QuotientGroup.mk' (Subgroup.center ↥S) (α ((α ^ k) s))) from
          (hαβ ((α ^ k) s)).symm]
        rw [show α ((α ^ k) s) = (α ^ (k + 1)) s by rw [pow_succ', MulAut.mul_apply]]
    ext r
    obtain ⟨a, rfl⟩ := θ.surjective r
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥S) a
    rw [MulAut.one_apply, h1 p s, hαpow, MulAut.one_apply]
  have hJsub : GLAPComponent p ((S ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S)
      (J.subgroupOf S) := by
    refine (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff (p := p) hp
      (Subgroup.subtype_injective S)).mp ?_
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_left,
      Subgroup.map_subgroupOf_eq_of_le hJS]
  have hJP : GLAPComponent p (fixSubgroup φx) ((J.subgroupOf S).map ρS) :=
    glaPComponent_map_fixSubgroup ρS hker α φx hαβ hsurj hp (hfix ▸ hJsub)
  obtain ⟨d₁, D₁, instD, finD, ι, ιSL, h2', hd₁, h22, h23, hιinj, hιSL, hJPeq, hBk, hSc, E, hE,
    hTv⟩ := exists_linPsl_block h2 hd A hp hp2 φx hA hφxpow _ hJP
  let ρJ : ↥J →* LargeEvenProj (StatedSL d K) := ρS.comp (Subgroup.inclusion hJS)
  let Ψ : ↥(StatedSL d₁ D₁) →* LargeEvenProj (StatedSL d K) :=
    (LargeEvenProjMk (StatedSL d K)).comp ιSL
  let q₁ : ↥(StatedSL d₁ D₁) →* LargeEvenProj (StatedSL d₁ D₁) := LargeEvenProjMk (StatedSL d₁ D₁)
  have hperfJ : commutator ↥J = ⊤ := by
    have h1 := Subgroup.map_subtype_commutator J
    rw [glaPComponent_perfect hJ] at h1
    have h2 : (⊤ : Subgroup ↥J).map J.subtype = J := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective J.subtype_injective (h1.trans h2.symm)
  have hρJmem : ∀ l : ↥J, ρJ l ∈ (J.subgroupOf S).map ρS := fun l =>
    Subgroup.mem_map.mpr ⟨⟨l.1, hJS l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  have hmemJP : ∀ z ∈ (J.subgroupOf S).map ρS, ∃ l : ↥J, ρJ l = z := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨s.1, Subgroup.mem_subgroupOf.mp hs⟩, rfl⟩
  have hρΨ : ∀ l : ↥J, ∃ m, Ψ m = ρJ l := by
    intro l
    have h1 : ρJ l ∈ ιSL.range.map (LargeEvenProjMk (StatedSL d K)) := hJPeq ▸ hρJmem l
    obtain ⟨g, ⟨m, rfl⟩, hg⟩ := Subgroup.mem_map.1 h1
    exact ⟨m, hg⟩
  have hΨρ : ∀ m, ∃ l : ↥J, ρJ l = Ψ m := by
    intro m
    have h1 : Ψ m ∈ (J.subgroupOf S).map ρS := by
      rw [hJPeq]
      exact Subgroup.mem_map.2 ⟨ιSL m, ⟨m, rfl⟩, rfl⟩
    exact hmemJP _ h1
  have hcen₁ : ∀ m : ↥(StatedSL d₁ D₁), q₁ m = 1 →
      m ∈ Subgroup.center ↥(StatedSL d₁ D₁) := by
    intro m hm
    rw [CFSG.GH74.L5U5.center_statedSL_eq (F := D₁) d₁]
    exact (QuotientGroup.eq_one_iff m).1 hm
  have hcen₁' : ∀ m : ↥(StatedSL d₁ D₁), m ∈ Subgroup.center ↥(StatedSL d₁ D₁) → q₁ m = 1 := by
    intro m hm
    rw [CFSG.GH74.L5U5.center_statedSL_eq (F := D₁) d₁] at hm
    exact (QuotientGroup.eq_one_iff m).2 hm
  have hιSLinj : Function.Injective ιSL := fun a b hab =>
    Subtype.ext (hιinj (by rw [← hιSL, ← hιSL, hab]))
  have hker₁ : ∀ m, Ψ m = 1 → q₁ m = 1 := by
    intro m hm
    apply hcen₁'
    have hc : ιSL m ∈ Subgroup.center ↥(StatedSL d K) := ker_projMk_le_center hm
    refine Subgroup.mem_center_iff.2 fun m' => ?_
    apply hιSLinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hc (ιSL m')
  obtain ⟨Θ, hΘ⟩ := l154_exists_hom_lift ρJ Ψ q₁ hρΨ hker₁
  have hΘsurj : Function.Surjective Θ := by
    intro r
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨l, hl⟩ := hΨρ m
    exact ⟨l, hΘ l m hl.symm⟩
  have hρJker : ρJ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : QuotientGroup.mk' (Subgroup.center ↥S) ⟨l.1, hJS l.2⟩ = 1 := by
      apply θ.injective
      rw [map_one]
      exact hl
    have h2 : (⟨l.1, hJS l.2⟩ : ↥S) ∈ Subgroup.center ↥S := (QuotientGroup.eq_one_iff _).1 h1
    refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
    have h3 := Subgroup.mem_center_iff.1 h2 ⟨j.1, hJS j.2⟩
    exact congrArg (fun z : ↥S => (z : Ω)) h3
  have hΘker : Θ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    obtain ⟨m, hm⟩ := hρΨ l
    have hqm : q₁ m = 1 := by rw [← hΘ l m hm]; exact hl
    have hmc := hcen₁ m hqm
    refine mem_center_of_commutator_mem_center hperfJ fun j => ?_
    apply hρJker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    obtain ⟨m', hm'⟩ := hρΨ j
    rw [← hm, ← hm', ← map_commutatorElement]
    have hce : ⁅m, m'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hmc m').symm
    rw [hce, map_one]
  have hR₁ : IsSimpleGroup (LargeEvenProj (StatedSL d₁ D₁)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL D₁ hd₁ h22 h23
  obtain ⟨e₀, he₀⟩ := l154_exists_pSimple_equiv hp hJ hR₁ Θ hΘsurj hΘker
  have hBmem : B ∈ Subgroup.centralizer ({A} : Set (GL (Fin d) K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  obtain ⟨B₁, hB₁⟩ := hBk B hBmem
  refine ⟨d₁, D₁, instD, finD, B₁, e₀, h2', hd₁, h22, h23, fun m => ?_⟩
  obtain ⟨l, hl⟩ := hΨρ m
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (J : Set Ω) := Subgroup.inv_mem _ hJy
  have hl'mem : y⁻¹ * (l : Ω) * y ∈ J := by
    have := (Subgroup.mem_normalizer_iff.1 hyinv (l : Ω)).1 l.2
    simpa using this
  let l' : ↥J := ⟨y⁻¹ * (l : Ω) * y, hl'mem⟩
  have hρl' : ρJ l' = ψ (ρJ l) := by
    have h := hindy ⟨l.1, hJS l.2⟩ ⟨l'.1, hJS l'.2⟩ (by
      show ((l'.1 : Ω)) = y⁻¹ * (l.1 : Ω) * y
      rfl)
    exact h.symm
  set X : ↥(StatedSL d₁ D₁) :=
    ⟨B₁ * (m : GL (Fin d₁) D₁) * B₁⁻¹,
      (inferInstance : (StatedSL d₁ D₁).Normal).conj_mem m m.2 B₁⟩ with hX
  have hBm : B * (ιSL m : GL (Fin d) K) * B⁻¹ = (ιSL X : GL (Fin d) K) :=
    (hB₁ m).trans (hιSL X).symm
  have hgmem : B * (ιSL m : GL (Fin d) K) * B⁻¹ ∈ StatedSL d K :=
    (inferInstance : (StatedSL d K).Normal).conj_mem (ιSL m) (ιSL m).2 B
  have hψm : ψ (Ψ m) = LargeEvenProjMk (StatedSL d K)
      ⟨B * (ιSL m : GL (Fin d) K) * B⁻¹, hgmem⟩ :=
    hψ (ιSL m) ⟨_, hgmem⟩ rfl
  obtain ⟨m', hm'⟩ := hρΨ l'
  have hπeq : LargeEvenProjMk (StatedSL d K) (ιSL m') =
      LargeEvenProjMk (StatedSL d K) ⟨_, hgmem⟩ := by
    show Ψ m' = _
    rw [hm', hρl', hl, hψm]
  have hπeqX : LargeEvenProjMk (StatedSL d K) (ιSL m') =
      LargeEvenProjMk (StatedSL d K) (ιSL X) := by
    rw [hπeq, show (⟨B * (ιSL m : GL (Fin d) K) * B⁻¹, hgmem⟩ : ↥(StatedSL d K)) =
      ιSL X from Subtype.ext hBm]
  obtain ⟨c, hc⟩ := (projMk_eq_iff (ιSL m') (ιSL X)).1 hπeqX
  have hc2 : Matrix.GeneralLinearGroup.scalar (Fin d) c =
      ((ιSL m' : GL (Fin d) K))⁻¹ * (ιSL X : GL (Fin d) K) := hc
  have hscal : ∃ w : D₁ˣ, (↑(m' * X⁻¹ : ↥(StatedSL d₁ D₁)) : GL (Fin d₁) D₁) =
      Matrix.GeneralLinearGroup.scalar (Fin d₁) w := by
    refine hSc (m' * X⁻¹) ⟨c⁻¹, ?_⟩
    rw [← hιSL (m' * X⁻¹)]
    have hsplit : (ιSL (m' * X⁻¹) : GL (Fin d) K) =
        (ιSL m' : GL (Fin d) K) * ((ιSL X : GL (Fin d) K))⁻¹ := by
      rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hsplit]
    have h2 : (ιSL m' : GL (Fin d) K) =
        (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ * (ιSL X : GL (Fin d) K) := by
      have h3 : (ιSL m' : GL (Fin d) K) * Matrix.GeneralLinearGroup.scalar (Fin d) c =
          (ιSL X : GL (Fin d) K) := by
        rw [hc2]
        group
      calc (ιSL m' : GL (Fin d) K) = (ιSL m' : GL (Fin d) K) *
            Matrix.GeneralLinearGroup.scalar (Fin d) c *
            (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by group
        _ = (ιSL X : GL (Fin d) K) *
            (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by rw [h3]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ * (ιSL X : GL (Fin d) K) :=
            (((commute_iff_eq _ _).mpr
              (Matrix.GeneralLinearGroup.scalar_commute c (ιSL X : GL (Fin d) K))).symm.inv_right).eq
    rw [h2, ← map_inv]
    group
  obtain ⟨w, hw⟩ := hscal
  have hscalSL : Matrix.GeneralLinearGroup.scalar (Fin d₁) w ∈ StatedSL d₁ D₁ := by
    rw [← hw]
    exact (m' * X⁻¹).2
  have hm'mul : m' = (⟨Matrix.GeneralLinearGroup.scalar (Fin d₁) w, hscalSL⟩ :
      ↥(StatedSL d₁ D₁)) * X := by
    apply Subtype.ext
    calc ((m' : ↥(StatedSL d₁ D₁)) : GL (Fin d₁) D₁) =
        (((m' * X⁻¹) * X : ↥(StatedSL d₁ D₁)) : GL (Fin d₁) D₁) := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d₁) w) * (X : GL (Fin d₁) D₁) := by
          rw [Subgroup.coe_mul, hw]
  have hmm' : LargeEvenProjMk (StatedSL d₁ D₁) m' =
      LargeEvenProjMk (StatedSL d₁ D₁) X := by
    rw [hm'mul, map_mul]
    have h1 : LargeEvenProjMk (StatedSL d₁ D₁)
        (⟨Matrix.GeneralLinearGroup.scalar (Fin d₁) w, hscalSL⟩ : ↥(StatedSL d₁ D₁)) = 1 := by
      rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf, largeEvenScalars_def]
      exact ⟨w, rfl⟩
    rw [h1, one_mul]
  have e1 : q₁ m = e₀ (QuotientGroup.mk (QuotientGroup.mk l)) := by
    rw [he₀ l]
    exact (hΘ l m hl.symm).symm
  have e2 : q₁ m' = e₀ (QuotientGroup.mk (QuotientGroup.mk l')) := by
    rw [he₀ l']
    exact (hΘ l' m' hm').symm
  have e3 : MI.indAut p J y hJy (QuotientGroup.mk (QuotientGroup.mk l)) =
      QuotientGroup.mk (QuotientGroup.mk l') :=
    MI.indAut_apply_mk hJy ⟨l, l', rfl, rfl, rfl⟩
  calc MulAut.congr e₀ (MI.indAut p J y hJy) (q₁ m) = q₁ m' := by
        rw [e1, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply, e3, ← e2]
    _ = LargeEvenProjMk (StatedSL d₁ D₁) X := hmm'

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
