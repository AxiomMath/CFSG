module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi
public import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Amb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GCase
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict)

private theorem tag_ne_twF4der_of_markTag' {lab : LargeEvenLabel} {t : StatedLieTag}
    (htag : markTag lab = t) (htits : t ≠ .Tits) : lab.tag ≠ .twF4der := by
  obtain ⟨tag, r, m⟩ := lab
  rintro rfl
  exact htits (by rw [← htag]; rfl)

private theorem not_derivedLab_of_markChar' {lab : LargeEvenLabel} (hc : markChar lab = 2)
    (htits : lab.tag ≠ .twF4der) : ¬ MI.DerivedLab lab := by
  obtain ⟨tag, r, m⟩ := lab
  rintro (h | h)
  · have h' : tag = .G2der := h
    rw [h'] at hc
    simp [markChar] at hc
  · exact htits h

theorem congr_conj' {S T : Type*} [Group S] [Group T] (e : S ≃* T) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext t
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem indAut_zpow {Γ : Type} [Group Γ] {p : ℕ} {J : Subgroup Γ} {a : Γ}
    (haJ : a ∈ Subgroup.normalizer (J : Set Γ)) (k : ℤ)
    (hk : a ^ k ∈ Subgroup.normalizer (J : Set Γ)) :
    MI.indAut p J (a ^ k) hk = (MI.indAut p J a haJ) ^ k := by
  unfold MI.indAut
  rw [← map_zpow]
  congr 1
  exact Subtype.ext (by simp [zpow_neg, inv_zpow])

section Inner


theorem innDiagOn_of_lieModel_of_inner
    {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} {J : Subgroup Γ} {a : Γ}
    (haJ : a ∈ Subgroup.normalizer (J : Set Γ))
    (hq : CFSG.IsQuasisimple (PQuot p J))
    {t : StatedLieTag} {n f : ℕ}
    (hLM : CFSG.Blueprint.LieModel (PSimple p J) t n 2 f) (htits : t ≠ .Tits)
    (hmem : MI.indAut p J a haJ ∈ inner (PSimple p J)) :
    InnDiagOn p (Subgroup.zpowers a) J := by
  refine ⟨Subgroup.zpowers_le.2 haJ, ?_⟩
  obtain ⟨hX, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot
      hq.1.commutator_eq_top hLM
  obtain ⟨-, -, -, -, -, -, -, hP⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨htag, -, hchar, -⟩ := hP
  have htitsLab : lab.tag ≠ .twF4der := tag_ne_twF4der_of_markTag' htag htits
  have hnd : ¬ MI.DerivedLab lab := not_derivedLab_of_markChar' hchar htitsLab
  have hsub : MI.CAll lab (LargeEvenSimpleGuard GGRawInnSubgroup) :=
    (MI.canonAll_iff_legacyAll hlab hnd _).2 (largeEvenLabelAll_innSubgroup hlab)
  obtain ⟨r, hr⟩ := hmem
  have hraw' : CFSG.Assembly.LargeEvenRawDatum lab fun R _ I _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : PQuot p J ⧸ Subgroup.center (PQuot p J) ≃* R,
          ∀ a' ∈ Subgroup.zpowers a, ∃ φ ∈ I, LargeEvenInduces θ (indRel p J a') φ := by
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ (hsub _ hraw)
    rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hsubfun⟩
    obtain ⟨-, -, hinn⟩ := hsubfun hs hna
    refine ⟨hs, hna, θ, fun a' ha' => ?_⟩
    have ha'N : a' ∈ Subgroup.normalizer (J : Set Γ) := Subgroup.zpowers_le.2 haJ ha'
    refine ⟨MulAut.congr θ (MI.indAut p J a' ha'N), ?_,
      (MI.induces_indRel_iff ha'N θ).2 rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
    rw [indAut_zpow haJ k ha'N, ← hr, ← map_zpow, congr_conj']
    exact hinn _
  exact ⟨hX, lab, hlab, hraw'⟩

end Inner

section PSimple

variable {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} {J : Subgroup Ω}

noncomputable def pSimpleEquivCenterQuot (hp : p.Prime) (hJ : CFSG.IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    PSimple p J ≃* ↥J ⧸ Subgroup.center ↥J :=
  haveI : Group.IsPerfect ↥J := hJ.1
  (QuotientGroup.congr _ _ (MulEquiv.refl _) (by
    simpa using (CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) (QuotientGroup.mk'_surjective _)
      (by simpa only [QuotientGroup.ker_mk'] using
        T263.DX.glaPPrimeCore_le_center_of_dvd hp hJ hdvd)))).symm.trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _
      (T263.DX.glaPPrimeCore_le_center_of_dvd hp hJ hdvd))

theorem pSimpleEquivCenterQuot_mk_mk (hp : p.Prime) (hJ : CFSG.IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) (j : ↥J) :
    pSimpleEquivCenterQuot hp hJ hdvd
        ((QuotientGroup.mk (QuotientGroup.mk j : PQuot p J)) : PSimple p J) =
      (QuotientGroup.mk j : ↥J ⧸ Subgroup.center ↥J) := by
  rfl

end PSimple

section Transport


theorem innDiagOn_map_conj_of_action {M : Type} [Group M] [Finite M]
    (hZ : Subgroup.center M = ⊥) {Kc : Subgroup M} (φ : MulAut M) (hnorm : ∀ x ∈ Kc, φ x ∈ Kc)
    {H : Type} [Group H] {R : Subgroup H} (e : ↥Kc ≃* ↥R) {y : H}
    (hyStab : MulAut.conj y ∈ subgroupStabAut R)
    (hact : ∀ x : ↥Kc, e ⟨φ x, hnorm x x.2⟩ = y * (e x : H) * y⁻¹)
    (hQS : CFSG.IsQuasisimple ↥R)
    {t : StatedLieTag} {n f : ℕ}
    (hLM : CFSG.Blueprint.LieModel (↥R ⧸ Subgroup.center ↥R) t n 2 f)
    (htits : t ≠ .Tits) (hsz : t ≠ .twistedB2)
    (hcase : ¬ (t = .POmegaPlus ∧ n = 4) ∨
      centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩) ∈
        inner (↥R ⧸ Subgroup.center ↥R))
    (hmem : centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥R ⧸ Subgroup.center ↥R)) :
    InnDiagOn 3 (Subgroup.zpowers φ) (Kc.map (MulAut.conj : M →* MulAut M)) := by
  classical
  set J : Subgroup (MulAut M) := Kc.map (MulAut.conj : M →* MulAut M) with hJdef
  have hinj : Function.Injective (MulAut.conj : M →* MulAut M) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun α : MulAut M => α g) hab
      simp only [MulAut.conj_apply] at h1
      have h2 : g = (a⁻¹ * b) * g * (a⁻¹ * b)⁻¹ := by
        rw [mul_inv_rev, inv_inv]
        calc g = a⁻¹ * (a * g * a⁻¹) * a := by group
          _ = a⁻¹ * (b * g * b⁻¹) * a := by rw [h1]
          _ = a⁻¹ * b * g * (b⁻¹ * a) := by group
      calc g * (a⁻¹ * b) = (a⁻¹ * b) * g * (a⁻¹ * b)⁻¹ * (a⁻¹ * b) := by rw [← h2]
        _ = (a⁻¹ * b) * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    calc a = a * (a⁻¹ * b) := by rw [hc, mul_one]
      _ = b := by group
  let eJ : ↥Kc ≃* ↥J := Kc.equivMapOfInjective _ hinj
  have heJ : ∀ x : ↥Kc, ((eJ x : ↥J) : MulAut M) = MulAut.conj (x : M) := fun _ => rfl
  have hKcmap : Kc.map φ.toMonoidHom = Kc := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hnorm x hx
    · rw [Subgroup.card_map_of_injective φ.injective]
  have hφstab : φ ∈ subgroupStabAut Kc := hKcmap
  have hφinv : ∀ x ∈ Kc, φ⁻¹ x ∈ Kc := fun x hx =>
    CFSG.GroupActions.apply_mem_of_mem_subgroupStabAut (inv_mem hφstab) hx
  have hconj : ∀ z : M, φ * MulAut.conj z * φ⁻¹ = MulAut.conj (φ z) := by
    intro z
    ext w
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  have hconj' : ∀ z : M, φ⁻¹ * MulAut.conj z * φ = MulAut.conj (φ⁻¹ z) := by
    intro z
    have := hconj (φ⁻¹ z)
    rw [show φ (φ⁻¹ z) = z from φ.apply_symm_apply z] at this
    rw [← this]
    group
  have haJ : φ ∈ Subgroup.normalizer (J : Set (MulAut M)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨φ x, hnorm x hx, (hconj x).symm⟩
    · rintro ⟨x, hx, hxg⟩
      refine ⟨φ⁻¹ x, hφinv x hx, ?_⟩
      have hg : g = φ⁻¹ * (φ * g * φ⁻¹) * φ := by group
      rw [hg, ← hxg, hconj']
  set c1 : ↥J ⧸ Subgroup.center ↥J ≃* ↥R ⧸ Subgroup.center ↥R :=
    QuotientGroup.congr _ _ (eJ.symm.trans e) (Subgroup.map_center_eq (eJ.symm.trans e))
    with hc1def
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
      (CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (e.symm.trans eJ)
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hQS))
  have h3R : 3 ∣ Nat.card (↥R ⧸ Subgroup.center ↥R) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.three_dvd_card_of_lieModel hLM.admissible hLM hsz
  have h3J : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rwa [Nat.card_congr c1.toEquiv]
  have hq : CFSG.IsQuasisimple (PQuot 3 J) :=
    T263.DX.isQuasisimple_pQuot_of_dvd Nat.prime_three hJq h3J
  set ψ : PSimple 3 J ≃* ↥R ⧸ Subgroup.center ↥R :=
    (pSimpleEquivCenterQuot Nat.prime_three hJq h3J).trans c1 with hψdef
  have hψ : ∀ x : ↥Kc, ψ ((QuotientGroup.mk (QuotientGroup.mk (eJ x) : PQuot 3 J)) : PSimple 3 J) =
      (QuotientGroup.mk (e x) : ↥R ⧸ Subgroup.center ↥R) := by
    intro x
    rw [hψdef, MulEquiv.trans_apply, pSimpleEquivCenterQuot_mk_mk, hc1def,
      QuotientGroup.congr_mk, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  set β := centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩) with hβ
  have hkey : MulAut.congr ψ (MI.indAut 3 J φ haJ) = β⁻¹ := by
    apply MulEquiv.ext
    intro s
    obtain ⟨u, rfl⟩ := ψ.surjective s
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨x, rfl⟩ := eJ.surjective j
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hx' : φ⁻¹ (x : M) ∈ Kc := hφinv x x.2
    have hrel : indRel 3 J φ (QuotientGroup.mk (eJ x)) (QuotientGroup.mk (eJ ⟨_, hx'⟩)) :=
      ⟨eJ x, eJ ⟨_, hx'⟩, rfl, rfl, by
        rw [heJ, heJ, ← hconj']⟩
    rw [MI.indAut_apply_mk haJ hrel, hψ, hψ]
    have hex : (e x : H) = y * (e ⟨_, hx'⟩ : H) * y⁻¹ := by
      have h := hact ⟨_, hx'⟩
      have hφx : (⟨φ (φ⁻¹ (x : M)), hnorm _ hx'⟩ : ↥Kc) = x :=
        Subtype.ext (φ.apply_symm_apply (x : M))
      rw [hφx] at h
      exact h
    rw [show β⁻¹ = centerQuotientHom ↥R
        (subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩)⁻¹ from (map_inv _ _).symm,
      CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk]
    congr 1
    apply Subtype.ext
    rw [show (subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩)⁻¹ =
        subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩⁻¹ from (map_inv _ _).symm,
      CFSG.GroupActions.subgroupStabRestrict_apply]
    show (e ⟨_, hx'⟩ : H) = (MulAut.conj y)⁻¹ (e x : H)
    rw [hex]
    generalize ((e ⟨_, hx'⟩ : ↥R) : H) = w
    rw [MulAut.conj_inv_apply]
    group
  have hLMJ : CFSG.Blueprint.LieModel (PSimple 3 J) t n 2 f :=
    CFSG.Blueprint.LieModel.of_mulEquiv ψ.symm hLM
  rcases hcase with hnot | hinn
  · have hmemJ : MI.indAut 3 J φ haJ ∈ innAutDerived (PSimple 3 J) := by
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr ψ, hkey]
      exact inv_mem hmem
    exact innDiagOn_of_lieModel haJ hq hLMJ hnot htits hmemJ
  · have hmemJ : MI.indAut 3 J φ haJ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 J) := by
      obtain ⟨r, hr⟩ := inv_mem hinn
      refine ⟨ψ.symm r, ?_⟩
      apply (MulAut.congr ψ).injective
      rw [congr_conj', MulEquiv.apply_symm_apply, hkey, hr]
    exact innDiagOn_of_lieModel_of_inner haJ hq hLMJ htits hmemJ

end Transport

end CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit

end
