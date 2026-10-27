module

public import CFSG.LieType.Ree.ExceptionalAutomorphismData
public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree

variable {L : Type} [Field L]

theorem baseChangeGL_fixes_single_iff
    {τ : Tag} {E : Type} [Field E] (f : E →+* L)
    (g : ModGL τ E) (b : Label τ) :
    ((baseChangeGL f g : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b 1) =
        Finsupp.single b 1 ↔
      (g : Module.End E (RootModule τ E)) (Finsupp.single b 1) = Finsupp.single b 1 := by
  rw [baseChangeGL_apply_single]
  have hs : Finsupp.mapRange f f.map_zero (Finsupp.single b (1 : E)) = Finsupp.single b 1 := by
    simp
  rw [← hs]
  exact (Finsupp.mapRange_injective f f.map_zero f.injective).eq_iff

theorem shortFaithful_G2_of_isAlgebraic
    [Algebra (ZMod 3) L] [Algebra.IsAlgebraic (ZMod 3) L] :
    ReeTag.G2.ShortFaithful L := by
  intro g hg hfix
  obtain ⟨S, hS⟩ := exists_finset_descent hg
  obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := ZMod 3) S
  obtain ⟨y, hy, rfl⟩ := hS E hSE
  have hp : ((ReeTag.G2.prime : ℕ) : E) = 0 := by
    have h3 : ((3 : ℕ) : L) = 0 := by
      rw [← map_natCast (algebraMap (ZMod 3) L), ZMod.natCast_self, map_zero]
    apply E.subtype.injective
    rw [map_natCast, map_zero]
    exact h3
  have hfixE : ∀ v ∈ ReeTag.G2.shortModule E,
      (y : Module.End E (RootModule ReeTag.G2.tag E)) v = v := by
    intro v hv
    have hle : ReeTag.G2.shortModule E ≤
        LinearMap.eqLocus (y : Module.End E (RootModule ReeTag.G2.tag E)) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ (⟨i, hi, rfl⟩ | ⟨α, hα, rfl⟩)
      · have hmem : hVec ReeTag.G2.tag L i ∈ ReeTag.G2.shortModule L :=
          Submodule.subset_span (Or.inl ⟨i, hi, rfl⟩)
        exact (baseChangeGL_fixes_single_iff E.subtype y _).1 (hfix _ hmem)
      · by_cases hr : IsRoot ReeTag.G2.tag α
        · have hmem : rootVec ReeTag.G2.tag L α ∈ ReeTag.G2.shortModule L :=
            Submodule.subset_span (Or.inr ⟨α, hα, rfl⟩)
          have h1 := hfix _ hmem
          simp only [rootVec, hr, dite_true] at h1
          change (y : Module.End E (RootModule ReeTag.G2.tag E)) (rootVec ReeTag.G2.tag E α) =
            rootVec ReeTag.G2.tag E α
          simp only [rootVec, hr, dite_true]
          exact (baseChangeGL_fixes_single_iff E.subtype y _).1 h1
        · change (y : Module.End E (RootModule ReeTag.G2.tag E)) (rootVec ReeTag.G2.tag E α) =
            rootVec ReeTag.G2.tag E α
          simp only [rootVec, hr, dite_false, map_zero]
    exact hle hv
  rw [ReeTag.shortFaithful hp y hy hfixE, map_one]

theorem exceptional_Lang_G2_closure_exceptional_map
    [Algebra (ZMod 3) L]
    [IsAlgClosure (ZMod 3) L] :
    ∃ Φ : MulAut (adjointGroup Tag.G2 L),
      (∀ c : L, Φ (xElement ⟨0, by decide⟩ c) = xElement ⟨1, by decide⟩ c ∧
        Φ (yElement ⟨0, by decide⟩ c) = yElement ⟨1, by decide⟩ c ∧
        Φ (xElement ⟨1, by decide⟩ c) = xElement ⟨0, by decide⟩ (c ^ 3) ∧
        Φ (yElement ⟨1, by decide⟩ c) = yElement ⟨0, by decide⟩ (c ^ 3)) ∧
      (∀ Ψ : MulAut (adjointGroup Tag.G2 L),
        (∀ c : L, Ψ (xElement ⟨0, by decide⟩ c) = xElement ⟨1, by decide⟩ c ∧
          Ψ (yElement ⟨0, by decide⟩ c) = yElement ⟨1, by decide⟩ c ∧
          Ψ (xElement ⟨1, by decide⟩ c) = xElement ⟨0, by decide⟩ (c ^ 3) ∧
          Ψ (yElement ⟨1, by decide⟩ c) = yElement ⟨0, by decide⟩ (c ^ 3)) → Ψ = Φ) ∧
      (∀ Fr : L →+* L, (∀ c, Fr c = c ^ 3) →
        Φ.toMonoidHom.comp Φ.toMonoidHom = frobeniusTwist Tag.G2 L Fr ∧
          Φ.toMonoidHom.comp (frobeniusTwist Tag.G2 L Fr) =
            (frobeniusTwist Tag.G2 L Fr).comp Φ.toMonoidHom) ∧
      ∀ (K : Subfield L) [Finite K], ∀ φK : MulAut (adjointGroup Tag.G2 K),
        (∀ c : K, φK (xElement ⟨0, by decide⟩ c) = xElement ⟨1, by decide⟩ c ∧
          φK (yElement ⟨0, by decide⟩ c) = yElement ⟨1, by decide⟩ c ∧
          φK (xElement ⟨1, by decide⟩ c) = xElement ⟨0, by decide⟩ (c ^ 3) ∧
          φK (yElement ⟨1, by decide⟩ c) = yElement ⟨0, by decide⟩ (c ^ 3)) →
        (((adjointGroup Tag.G2 K).map (baseChangeGL K.subtype)).subgroupOf
            (adjointGroup Tag.G2 L)).map Φ.toMonoidHom =
          ((adjointGroup Tag.G2 K).map (baseChangeGL K.subtype)).subgroupOf
            (adjointGroup Tag.G2 L) ∧
        ∀ g : adjointGroup Tag.G2 K,
          ((Φ ⟨baseChangeGL K.subtype (g : ModGL Tag.G2 K),
              baseChangeGL_mem_adjointGroup _ g.2⟩ : adjointGroup Tag.G2 L) : ModGL Tag.G2 L) =
            baseChangeGL K.subtype ((φK g : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed (ZMod 3)
  have : CharP L 3 := charP_of_injective_algebraMap (algebraMap (ZMod 3) L).injective 3
  have hCh : CharP L ReeTag.G2.prime := ‹CharP L 3›
  have : PerfectRing L 3 := inferInstance
  have hp : ((ReeTag.G2.prime : ℕ) : L) = 0 := CharP.cast_eq_zero L 3
  have hf := shortFaithful_G2_of_isAlgebraic (L := L)
  set e := ReeTag.G2.exceptionalEndo L hp hf with he
  have hsq : e.comp e = frobeniusTwist Tag.G2 L (frobenius L 3) :=
    ReeTag.exceptionalEndo_comp_self hp hf
  have hFrsurj : Function.Surjective (frobeniusTwist Tag.G2 L (frobenius L 3)) := by
    intro g
    have hmap := map_exactEntrywiseAut (τ := Tag.G2) (frobeniusEquiv L 3)
      (H := adjointGroup Tag.G2 L) (Or.inl rfl)
    have hg : (g : ModGL Tag.G2 L) ∈ (adjointGroup Tag.G2 L).map
        (exactEntrywiseAut Tag.G2 (frobeniusEquiv L 3)).toMonoidHom := by
      rw [hmap]
      exact g.2
    obtain ⟨h, hh, hhg⟩ := hg
    exact ⟨⟨h, hh⟩, Subtype.ext hhg⟩
  have hinj : Function.Injective e := ReeTag.exceptionalEndo_injective hp hf
  have hsurj : Function.Surjective e := by
    intro g
    obtain ⟨h, rfl⟩ := hFrsurj g
    exact ⟨e h, DFunLike.congr_fun hsq h⟩
  set Φ : MulAut (adjointGroup Tag.G2 L) := MulEquiv.ofBijective e ⟨hinj, hsurj⟩ with hΦ
  have hΦe : Φ.toMonoidHom = e := MonoidHom.ext fun _ => rfl
  have hgen : ∀ c : L, Φ (xElement ⟨0, by decide⟩ c) = xElement ⟨1, by decide⟩ c ∧
      Φ (yElement ⟨0, by decide⟩ c) = yElement ⟨1, by decide⟩ c ∧
      Φ (xElement ⟨1, by decide⟩ c) = xElement ⟨0, by decide⟩ (c ^ 3) ∧
      Φ (yElement ⟨1, by decide⟩ c) = yElement ⟨0, by decide⟩ (c ^ 3) := by
    have hp0 : ReeTag.G2.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
    have hp1 : ReeTag.G2.perm ⟨1, by decide⟩ = ⟨0, by decide⟩ := by decide
    have he0 : ReeTag.G2.exponent ⟨0, by decide⟩ = 1 := by decide
    have he1 : ReeTag.G2.exponent ⟨1, by decide⟩ = 3 := by decide
    intro c
    refine ⟨(ReeTag.exceptionalEndo_xElement hp hf ⟨0, by decide⟩ c).trans ?_,
      (ReeTag.exceptionalEndo_yElement hp hf ⟨0, by decide⟩ c).trans ?_,
      (ReeTag.exceptionalEndo_xElement hp hf ⟨1, by decide⟩ c).trans ?_,
      (ReeTag.exceptionalEndo_yElement hp hf ⟨1, by decide⟩ c).trans ?_⟩
    · rw [hp0, he0, pow_one]
      rfl
    · rw [hp0, he0, pow_one]
      rfl
    · rw [hp1, he1]
      rfl
    · rw [hp1, he1]
      rfl
  have hext : ∀ {R : Type} [Field R] {M : Type} [Monoid M] (f₁ f₂ : adjointGroup Tag.G2 R →* M),
      (∀ c : R, f₁ (xElement ⟨0, by decide⟩ c) = f₂ (xElement ⟨0, by decide⟩ c) ∧
        f₁ (yElement ⟨0, by decide⟩ c) = f₂ (yElement ⟨0, by decide⟩ c) ∧
        f₁ (xElement ⟨1, by decide⟩ c) = f₂ (xElement ⟨1, by decide⟩ c) ∧
        f₁ (yElement ⟨1, by decide⟩ c) = f₂ (yElement ⟨1, by decide⟩ c)) → f₁ = f₂ := by
    intro R _ M _ f₁ f₂ h
    refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
    · fin_cases i
      exacts [(h c).1, (h c).2.2.1]
    · fin_cases i
      exacts [(h c).2.1, (h c).2.2.2]
  refine ⟨Φ, hgen, fun Ψ hΨ => ?_, fun Fr hFr => ?_, fun K _ φK hφK => ?_⟩
  ·
    refine MulEquiv.ext fun g => DFunLike.congr_fun (hext Ψ.toMonoidHom Φ.toMonoidHom
      fun c => ?_) g
    obtain ⟨h1, h2, h3, h4⟩ := hΨ c
    obtain ⟨g1, g2, g3, g4⟩ := hgen c
    exact ⟨h1.trans g1.symm, h2.trans g2.symm, h3.trans g3.symm, h4.trans g4.symm⟩
  ·
    have hFr' : Fr = frobenius L 3 := RingHom.ext fun c => by rw [hFr, frobenius_def]
    subst hFr'
    rw [hΦe]
    have h2 : e.comp (e.comp e) = (e.comp e).comp e := rfl
    rw [hsq] at h2
    exact ⟨hsq, h2⟩
  ·
    let ιC : adjointGroup Tag.G2 K →* adjointGroup Tag.G2 L :=
      ((baseChangeGL K.subtype).comp (adjointGroup Tag.G2 K).subtype).codRestrict _
        fun g => baseChangeGL_mem_adjointGroup _ g.2
    have hιx : ∀ (i : Fin Tag.G2.rank) (c : K), ιC (xElement i c) = xElement i (c : L) :=
      fun i c => Subtype.ext (baseChangeGL_xUnit _ i c)
    have hιy : ∀ (i : Fin Tag.G2.rank) (c : K), ιC (yElement i c) = yElement i (c : L) :=
      fun i c => Subtype.ext (baseChangeGL_yUnit _ i c)
    have hcomm : Φ.toMonoidHom.comp ιC = ιC.comp φK.toMonoidHom := by
      refine hext _ _ fun c => ?_
      obtain ⟨h1, h2, h3, h4⟩ := hφK c
      obtain ⟨g1, g2, g3, g4⟩ := hgen (c : L)
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hιx, g1, h1, hιx]
      · rw [hιy, g2, h2, hιy]
      · rw [hιx, g3, h3, hιx, SubmonoidClass.coe_pow]
      · rw [hιy, g4, h4, hιy, SubmonoidClass.coe_pow]
    have hval : ∀ g : adjointGroup Tag.G2 K,
        ((Φ ⟨baseChangeGL K.subtype (g : ModGL Tag.G2 K),
            baseChangeGL_mem_adjointGroup _ g.2⟩ : adjointGroup Tag.G2 L) : ModGL Tag.G2 L) =
          baseChangeGL K.subtype ((φK g : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) := fun g =>
      congrArg Subtype.val (DFunLike.congr_fun hcomm g)
    refine ⟨?_, hval⟩
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨w, ⟨g, hg, hgw⟩, rfl⟩
      refine ⟨(φK ⟨g, hg⟩ : ModGL Tag.G2 K), (φK ⟨g, hg⟩).2, ?_⟩
      have hw : w = ⟨baseChangeGL K.subtype g, baseChangeGL_mem_adjointGroup _ hg⟩ :=
        Subtype.ext hgw.symm
      rw [hw]
      exact (hval ⟨g, hg⟩).symm
    · rintro ⟨g, hg, hgx⟩
      obtain ⟨g', hg'⟩ := φK.surjective ⟨g, hg⟩
      refine ⟨⟨baseChangeGL K.subtype (g' : ModGL Tag.G2 K),
        baseChangeGL_mem_adjointGroup _ g'.2⟩, ⟨g', g'.2, rfl⟩, Subtype.ext ?_⟩
      rw [hval, hg', ← hgx]

end CFSG.LieType.Chevalley
