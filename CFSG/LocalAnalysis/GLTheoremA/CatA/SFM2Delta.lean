module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

theorem canonMarking_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {P : CFSG.Assembly.LargeEvenMarkProp X} {P' : CFSG.Assembly.LargeEvenMarkProp Y}
    (hPP' : ∀ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : Y ⧸ Subgroup.center Y ≃* R), P' lab R I F θ →
        P lab R I F ((CFSG.StandardType.centerQuotCongr e).trans θ))
    (h : CFSG.Assembly.LargeEvenMarking Y P') : CFSG.Assembly.LargeEvenMarking X P := by
  obtain ⟨hY, lab, hlab, hraw⟩ := h
  have hperf : Group.IsPerfect Y := ⟨hY⟩
  have hX : commutator X = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective).commutator_eq_top
  refine ⟨hX, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, (CFSG.StandardType.centerQuotCongr e).trans θ, hPP' lab R I F θ hθ⟩

abbrev DeltaSD (H : Type) [Group H] (δ : MulAut H) : Type :=
  SemidirectProduct H ↥(Subgroup.zpowers δ) (Subgroup.zpowers δ).subtype

def deltaElt {H : Type} [Group H] (δ : MulAut H) : ↥(Subgroup.zpowers δ) :=
  ⟨δ⁻¹, (Subgroup.zpowers δ).inv_mem (Subgroup.mem_zpowers δ)⟩

abbrev deltaG {H : Type} [Group H] (δ : MulAut H) : DeltaSD H δ :=
  SemidirectProduct.inr (deltaElt δ)

abbrev deltaL {H : Type} [Group H] (δ : MulAut H) : Subgroup (DeltaSD H δ) :=
  (SemidirectProduct.inl : H →* DeltaSD H δ).range

theorem deltaG_inv_mul_inl {H : Type} [Group H] (δ : MulAut H) (n : H) :
    (deltaG δ)⁻¹ * SemidirectProduct.inl n * deltaG δ = SemidirectProduct.inl (δ n) := by
  have h := SemidirectProduct.inl_aut_inv (φ := (Subgroup.zpowers δ).subtype) (deltaElt δ) n
  have hφ : (Subgroup.zpowers δ).subtype (deltaElt δ) = δ⁻¹ := rfl
  rw [hφ, inv_inv, map_inv] at h
  exact h.symm

@[expose] noncomputable def deltaIota {H : Type} [Group H] (δ : MulAut H) : ↥(deltaL δ) ≃* H :=
  (MonoidHom.ofInjective (f := (SemidirectProduct.inl : H →* DeltaSD H δ))
    SemidirectProduct.inl_injective).symm

theorem coe_eq_inl_deltaIota {H : Type} [Group H] (δ : MulAut H) (x : ↥(deltaL δ)) :
    (x : DeltaSD H δ) = SemidirectProduct.inl (deltaIota δ x) := by
  have h := (MonoidHom.ofInjective (f := (SemidirectProduct.inl : H →* DeltaSD H δ))
    SemidirectProduct.inl_injective).apply_symm_apply x
  conv_lhs => rw [← h]
  rfl

@[expose] noncomputable def deltaQuotIso (p : ℕ) {H : Type} [Group H] (δ : MulAut H) :
    PQuot p (deltaL δ) ≃* ppQuot p H :=
  QuotientGroup.congr (GLAPPrimeCore p ↥(deltaL δ)) (GLAPPrimeCore p H) (deltaIota δ)
    (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_map_iso p (deltaIota δ))

theorem deltaQuotIso_mk (p : ℕ) {H : Type} [Group H] (δ : MulAut H) (x : ↥(deltaL δ)) :
    deltaQuotIso p δ (QuotientGroup.mk x) = QuotientGroup.mk (deltaIota δ x) :=
  rfl

instance deltaSD_finite {H : Type} [Group H] [Finite H] (δ : MulAut H) :
    Finite (DeltaSD H δ) := by
  have : Finite (MulAut H) := by
    refine Finite.of_injective (fun f : MulAut H => f.toEquiv) ?_
    intro a b h
    exact MulEquiv.ext (fun x => congrArg (fun e : H ≃ H => e x) h)
  exact Finite.of_surjective
    (fun x : H × ↥(Subgroup.zpowers δ) => (⟨x.1, x.2⟩ : DeltaSD H δ))
    (fun y => ⟨(y.left, y.right), rfl⟩)

theorem deltaG_mem_normalizer {H : Type} [Group H] (δ : MulAut H) :
    deltaG δ ∈ Subgroup.normalizer ((deltaL δ : Subgroup (DeltaSD H δ)) : Set (DeltaSD H δ)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [MonoidHom.mem_range] at hy ⊢
    obtain ⟨m, rfl⟩ := hy
    refine ⟨(Subgroup.zpowers δ).subtype (deltaElt δ) m, ?_⟩
    rw [SemidirectProduct.inl_aut, map_inv]
  · intro hy
    rw [MonoidHom.mem_range] at hy ⊢
    obtain ⟨m, hm⟩ := hy
    refine ⟨((Subgroup.zpowers δ).subtype (deltaElt δ))⁻¹ m, ?_⟩
    rw [SemidirectProduct.inl_aut_inv, hm, map_inv]
    group

theorem indRel_iff_relOfAut (p : ℕ) {H : Type} [Group H] (δ : MulAut H) (q q' : PQuot p (deltaL δ)) :
    indRel p (deltaL δ) (deltaG δ) q q' ↔
      relOfAut p δ (deltaQuotIso p δ q) (deltaQuotIso p δ q') := by
  constructor
  · rintro ⟨l, l', rfl, rfl, hl⟩
    refine ⟨deltaIota δ l, deltaIota δ l', rfl, rfl, ?_⟩
    apply SemidirectProduct.inl_injective (φ := (Subgroup.zpowers δ).subtype)
    rw [← deltaG_inv_mul_inl, ← coe_eq_inl_deltaIota, ← coe_eq_inl_deltaIota]
    exact hl.symm
  · rintro ⟨m, m', hm, hm', hδ⟩
    have hq : QuotientGroup.mk ((deltaIota δ).symm m) = q := by
      apply (deltaQuotIso p δ).injective
      rw [deltaQuotIso_mk, MulEquiv.apply_symm_apply]
      exact hm
    have hq' : QuotientGroup.mk ((deltaIota δ).symm m') = q' := by
      apply (deltaQuotIso p δ).injective
      rw [deltaQuotIso_mk, MulEquiv.apply_symm_apply]
      exact hm'
    refine ⟨(deltaIota δ).symm m, (deltaIota δ).symm m', hq, hq', ?_⟩
    rw [coe_eq_inl_deltaIota, coe_eq_inl_deltaIota, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, deltaG_inv_mul_inl, hδ]

theorem inducesOn_transport {p : ℕ} {H : Type} [Group H] (δ : MulAut H) {R : Type} [Group R]
    (θ : ppQuot p H ⧸ Subgroup.center (ppQuot p H) ≃* R) (φ : MulAut R) :
    GLAInduces ((CFSG.StandardType.centerQuotCongr (deltaQuotIso p δ)).trans θ)
        (indRel p (deltaL δ) (deltaG δ)) φ ↔
      GLAInduces θ (relOfAut p δ) φ := by
  simp only [GLAInduces, CFSG.Assembly.LargeEvenInduces]
  constructor
  · intro h x x' hxx'
    obtain ⟨q, rfl⟩ := (deltaQuotIso p δ).surjective x
    obtain ⟨q', rfl⟩ := (deltaQuotIso p δ).surjective x'
    have := h q q' ((indRel_iff_relOfAut p δ q q').2 hxx')
    simpa only [MulEquiv.trans_apply, CFSG.StandardType.centerQuotCongr_mk] using this
  · intro h q q' hqq'
    have := h _ _ ((indRel_iff_relOfAut p δ q q').1 hqq')
    simpa only [MulEquiv.trans_apply, CFSG.StandardType.centerQuotCongr_mk] using this

theorem fieldOn_deltaG {p : ℕ} {H : Type} [Group H] (δ : MulAut H)
    (hF : GLAMarking (ppQuot p H)
      (fun lab _ _ I F θ => GLAPrimeField p lab I F (GLAInduces θ (relOfAut p δ)))) :
    S10.FieldOn p (deltaG δ) (deltaL δ) := by
  unfold S10.FieldOn
  refine ⟨deltaG_mem_normalizer δ, ?_⟩
  refine canonMarking_congr (deltaQuotIso p δ) ?_ hF
  intro lab R _ I F θ hθ
  have hfun : GLAInduces ((CFSG.StandardType.centerQuotCongr (deltaQuotIso p δ)).trans θ)
      (indRel p (deltaL δ) (deltaG δ)) = GLAInduces θ (relOfAut p δ) := by
    funext φ
    exact propext (inducesOn_transport δ θ φ)
  show GLAPrimeField p lab I F
    (GLAInduces ((CFSG.StandardType.centerQuotCongr (deltaQuotIso p δ)).trans θ)
      (indRel p (deltaL δ) (deltaG δ)))
  rw [hfun]
  exact hθ

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
