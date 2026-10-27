module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020Defs
public import CFSG.GroupTheory.SylowLiftSurjective
public import CFSG.LinearAlgebra.SpecialLinearSylowFixed
public import CFSG.LinearAlgebra.MovedSpanFixSub
public import CFSG.LinearAlgebra.PrimaryComponentFixSub
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAFactors
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open Polynomial Matrix Subgroup
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.CALinearPrimary
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open scoped commutatorElement Classical Pointwise

private theorem exists_linear_of_good_primaryFactor
    {F : Type} [Field F] [Finite F] {q p n : ℕ} [CharP F q]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : (p : F) ≠ 0) (hpdvd : p ∣ Nat.card F - 1)
    (hn : 3 ≤ n) (hn4 : n ≤ 4)
    {A : GL (Fin n) F} {c : Fˣ} (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    {h : Polynomial F} (hh : h ∈ primaryFactors (glA A : Module.End F (Fin n → F)))
    (hgood : IsGoodFactor A h) : ∃ lam : F, h = X - C lam := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact p.Prime := ⟨hp⟩
  have hEval : aeval (glA A : Module.End F (Fin n → F)) (X ^ p - C (c : F)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C]
    have h1 : ((glA A : LinearMap.GeneralLinearGroup F (Fin n → F)) :
        Module.End F (Fin n → F)) = Matrix.toLin' (A : Matrix (Fin n) (Fin n) F) := rfl
    rw [h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hA]
    ext v i
    by_cases hi : i = v <;> simp [hi]
  have hmindvd : minpoly F (glA A : Module.End F (Fin n → F)) ∣ X ^ p - C (c : F) :=
    minpoly.dvd F _ hEval
  have hdvdpoly : h ∣ X ^ p - C (c : F) :=
    (mem_primaryFactors.mp hh).2.2.trans hmindvd
  by_cases hc : ∃ a : F, a ^ p = (c : F)
  · obtain ⟨a, ha⟩ := hc
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by
      rw [Nat.card_units]; exact hpdvd)
    have hζ : IsPrimitiveRoot (x : F) p :=
      IsPrimitiveRoot.coe_units_iff.mpr (hx ▸ IsPrimitiveRoot.orderOf x)
    obtain ⟨ν, hν, -⟩ :=
      CFSG.AGLEmbedding.ToralCensus.exists_eq_X_sub_C_of_mem_primaryFactors
        hp.pos hζ ha hEval hh
    exact ⟨ν, hν⟩
  · have hc' : ∀ b : F, b ^ p ≠ (c : F) := by
      rintro b hb
      exact hc ⟨b, hb⟩
    have hirr : Irreducible (X ^ p - C (c : F)) := X_pow_sub_C_irreducible_of_prime hp hc'
    have hassoc : Associated h (X ^ p - C (c : F)) :=
      (irreducible_of_mem_primaryFactors hh).associated_of_dvd hirr hdvdpoly
    have heq : h = X ^ p - C (c : F) :=
      eq_of_monic_of_associated (monic_of_mem_primaryFactors hh)
        (monic_X_pow_sub_C _ hp.pos.ne') hassoc
    have hdeg : h.natDegree = p := by rw [heq, Polynomial.natDegree_X_pow_sub_C]
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hm2 : 2 ≤ primaryMultiplicity (glA A : Module.End F (Fin n → F)) h := by
      rcases hgood with h3 | ⟨h2, -⟩ <;> omega
    have hdim : Module.finrank F (primaryComponent (glA A : Module.End F (Fin n → F)) h) =
        p * primaryMultiplicity (glA A : Module.End F (Fin n → F)) h := by
      rw [finrank_primaryComponent, hdeg]
    have hle : Module.finrank F (primaryComponent (glA A : Module.End F (Fin n → F)) h) ≤ n := by
      refine (Submodule.finrank_le _).trans_eq ?_
      exact Module.finrank_fin_fun (R := F) (n := n)
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have h6 : 6 ≤ p * primaryMultiplicity (glA A : Module.End F (Fin n → F)) h :=
      Nat.mul_le_mul hp3 hm2
    omega



private noncomputable def specialFactorBlockHom {F : Type} [Field F] {n : ℕ}
    (A : GL (Fin n) F) (h : F[X]) :
    specialFactor A h →* linearSpecialBlock (glA A) h :=
  { toFun := fun g => ⟨slGL n F (g : Matrix.SpecialLinearGroup (Fin n) F), g.2⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }

private theorem specialFactorBlockHom_bijective {F : Type} [Field F] {n : ℕ}
    {A : GL (Fin n) F} {h : F[X]}
    (hsq : Squarefree (minpoly F (glA A : Module.End F (Fin n → F))))
    (hh : h ∈ primaryFactors (glA A : Module.End F (Fin n → F))) :
    Function.Bijective (specialFactorBlockHom A h) := by
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · apply Subtype.ext
    apply slGL_injective
    exact congrArg Subtype.val hab
  · have hg : (y : LinearMap.GeneralLinearGroup F (Fin n → F)) ∈
        linearSpecialBlock (glA A) h := y.2
    obtain ⟨f, hfg⟩ := mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)
    refine ⟨⟨f, ?_⟩, ?_⟩
    · change (slGL n F) f ∈ linearSpecialBlock (glA A) h
      rw [hfg]
      exact y.2
    · apply Subtype.ext
      exact hfg

private noncomputable def specialFactorRestrictHom {F : Type} [Field F] {n : ℕ}
    (A : GL (Fin n) F) (h : F[X]) :
    specialFactor A h →* SpecialLinearGroup (AdjoinRoot h)
      (primaryComponent (glA A : Module.End F (Fin n → F)) h) :=
  (linearSpecialBlockRestrict (glA A) h).comp (specialFactorBlockHom A h)

private theorem specialFactorRestrictHom_bijective {F : Type} [Field F] {n : ℕ}
    {A : GL (Fin n) F} {h : F[X]}
    (hsq : Squarefree (minpoly F (glA A : Module.End F (Fin n → F))))
    (hh : h ∈ primaryFactors (glA A : Module.End F (Fin n → F))) :
    Function.Bijective (specialFactorRestrictHom A h) := by
  have hg : Function.Bijective (linearSpecialBlockRestrict (glA A) h) :=
    ⟨linearSpecialBlockRestrict_injective hsq, linearSpecialBlockRestrict_surjective hsq hh⟩
  have hf : Function.Bijective (specialFactorBlockHom A h) :=
    specialFactorBlockHom_bijective hsq hh
  change Function.Bijective ((linearSpecialBlockRestrict (glA A) h) ∘
    (specialFactorBlockHom A h))
  exact Function.Bijective.comp hg hf

theorem i2020LinInner : I2020LinInner := by
  intro p q hp hp2 hq hq2 hqp F _ _ _ hpdvd n hn3 hn4 A c hA
  intro J hJ _ T hT S hS2 hST hSβ hScomm s hs j hj
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hpk : (p : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F q]
    intro hdvd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 hdvd)
  have hsq : Squarefree (minpoly F (glA A : Module.End F (Fin n → F))) :=
    squarefree_minpoly_glA hpk hA
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hle : J ≤ GLALayer (fixSubgroup (LinearFlag.conjAut n F A)) :=
    perfectInLayer_conjAut hpk hA J hJ.1 hperf
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hJ hle
  obtain ⟨⟨⟨h, hh⟩, hgood⟩, hJeq⟩ :=
    LieComp.linear_inner_components hpk hA J hcomp
  obtain ⟨lam, hlam⟩ := exists_linear_of_good_primaryFactor hp hp2 hpk hpdvd hn3 hn4 hA hh hgood
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hT
  have hTJ : T.subgroupOf J = (P : Subgroup J) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective (P : Subgroup J)
  have hTodd : Odd (T.subgroupOf J).index := by
    rw [hTJ, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact P.not_dvd_index
  have hTnotdvd : ¬ 2 ∣ (T.subgroupOf J).index := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hTodd
  let Fh : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) := specialFactor A h
  let φ : Fh →* J :=
    { toFun := fun g => ⟨LinearFlag.proj n F (g : Matrix.SpecialLinearGroup (Fin n) F), by
        rw [hJeq]
        exact ⟨(g : Matrix.SpecialLinearGroup (Fin n) F), g.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hφsurj : Function.Surjective φ := by
    intro j
    have hj' : (j : LinearFlag.projectiveSL n F) ∈ Fh.map (LinearFlag.proj n F) := by
      simpa [hJeq] using j.2
    obtain ⟨f, hf, hfj⟩ := hj'
    exact ⟨⟨f, hf⟩, Subtype.ext hfj⟩
  obtain ⟨Tstar, hTstar2, hTstarnotdvd, hTstarmap⟩ :=
    CFSG.GroupTheory.exists_isPGroup_not_dvd_index_map_le φ hφsurj Nat.prime_two hTnotdvd
  have hTstarodd : Odd Tstar.index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hTstarnotdvd
  have hproj_le : Tstar.map ((LinearFlag.proj n F).comp Fh.subtype) ≤ T := by
    have h1 : (Tstar.map φ).map J.subtype ≤ T := by
      calc (Tstar.map φ).map J.subtype ≤ (T.subgroupOf J).map J.subtype :=
            Subgroup.map_mono hTstarmap
        _ = T := Subgroup.map_subgroupOf_eq_of_le hT.1
    calc Tstar.map ((LinearFlag.proj n F).comp Fh.subtype) = (Tstar.map φ).map J.subtype := by
          rw [Subgroup.map_map]
          rfl
      _ ≤ T := h1
  let Tlift : Subgroup (GL (Fin n) F) :=
    Tstar.map (Matrix.SpecialLinearGroup.toGL.comp Fh.subtype)
  have hTlift2 : IsPGroup 2 Tlift := hTstar2.map _
  have hATlift : ∀ t ∈ Tlift, Commute A t := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ht
    have hblock : slGL n F (g : Matrix.SpecialLinearGroup (Fin n) F) ∈
        linearSpecialBlock (glA A) h := g.2
    have hcommSL : ((slGL n F (g : Matrix.SpecialLinearGroup (Fin n) F) :
        LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) *
        ((glA A : LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) =
        ((glA A : LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) *
        ((slGL n F (g : Matrix.SpecialLinearGroup (Fin n) F) :
          LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) :=
      (mem_gl_centralizer.mp (linearSpecialBlock_le_centralizer (glA A) h hblock)).eq
    apply Matrix.GeneralLinearGroup.toLin.injective
    rw [map_mul, map_mul]
    apply Units.ext
    exact hcommSL.symm
  have hSTlift : ∀ s ∈ S, ∀ t ∈ Tlift,
      s * LinearFlag.conjAut n F t = LinearFlag.conjAut n F t * s := by
    intro s hs' t ht
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ht
    have hprojmem : LinearFlag.proj n F (g : Matrix.SpecialLinearGroup (Fin n) F) ∈ T :=
      hproj_le ⟨g, hg, rfl⟩
    change s * LinearFlag.conjAut n F (Matrix.SpecialLinearGroup.toGL
      (g : Matrix.SpecialLinearGroup (Fin n) F)) =
      LinearFlag.conjAut n F (Matrix.SpecialLinearGroup.toGL
        (g : Matrix.SpecialLinearGroup (Fin n) F)) * s
    rw [LinearFlag.conjAut_toGL]
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, hST s hs' _ hprojmem]
  have hcenter : ⁅Subgroup.zpowers A, Tlift⁆ ≤ Subgroup.center (GL (Fin n) F) := by
    rw [Subgroup.commutator_le]
    intro x hx t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [commutatorElement_eq_one_iff_mul_comm.mpr ((hATlift t ht).zpow_left k).eq]
    exact Subgroup.one_mem _
  have hker : (LinearFlag.conjAut n F).ker ≤ Subgroup.center (GL (Fin n) F) := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    obtain ⟨u, hu⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn3 g).1 hg
    rw [← hu, Subgroup.mem_center_iff]
    intro y
    exact (Matrix.GeneralLinearGroup.scalar_commute u y).symm
  have hSle : S ≤ (LinearFlag.conjAut n F).range := by
    have hlin : ⁅S, Subgroup.zpowers (LinearFlag.conjAut n F A)⁆ ≤
        LinearFlag.linearAutGroup n F := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup
        hn3 a _
    have hrange : LinearFlag.linearAutGroup n F = (LinearFlag.conjAut n F).range := by
      rw [LinearFlag.linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rwa [hScomm, hrange] at hlin
  let S₁ : Subgroup (GL (Fin n) F) := ⁅S.comap (LinearFlag.conjAut n F), Subgroup.zpowers A⁆
  have hS₁_cent : ∀ s ∈ S₁, ∀ t ∈ Tlift, Commute s t := by
    intro s₁ hs₁ t ht
    have hlift := CFSG.GroupTheory.commutator_commutator_comap_zpowers_eq_bot
      (π := LinearFlag.conjAut n F) hker (S := S) (x := A) (T := Tlift) hcenter hSTlift
    have hmem : ⁅s₁, t⁆ ∈ (⊥ : Subgroup (GL (Fin n) F)) := by
      rw [← hlift]
      exact Subgroup.commutator_mem_commutator hs₁ ht
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  have hS₁map : S₁.map (LinearFlag.conjAut n F) = S :=
    CFSG.GroupTheory.map_commutator_comap_zpowers_eq (LinearFlag.conjAut n F) hSle hScomm
  let S₂ : Subgroup (GL (Fin n) F) := ⁅S₁, Subgroup.zpowers A⁆
  have hS₂map : S₂.map (LinearFlag.conjAut n F) = S :=
    CFSG.GroupTheory.map_commutator_commutator_comap_zpowers_eq
      (LinearFlag.conjAut n F) hSle hScomm
  let W : Submodule F (Fin n → F) := primaryComponent (glA A : Module.End F (Fin n → F)) h
  let linHom : GL (Fin n) F →* ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := F)).toMonoidHom
  have hlinHom_inj : Function.Injective linHom :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F)).injective.comp
      (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := F)).injective
  let TL : Subgroup ((Fin n → F) ≃ₗ[F] (Fin n → F)) := Tlift.map linHom
  haveI : Fintype ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
    Fintype.ofInjective (fun f : (Fin n → F) ≃ₗ[F] (Fin n → F) =>
      (f : (Fin n → F) → (Fin n → F))) DFunLike.coe_injective
  haveI : Fintype TL := Fintype.ofFinite _
  have hTL2 : IsPGroup 2 TL := hTlift2.map _
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hm2 : 2 ≤ Module.finrank (AdjoinRoot h) W := by
    rcases hgood with h3 | ⟨h2, -⟩
    · exact le_trans (by norm_num : 2 ≤ 3) h3
    · exact h2
  have hA_scalar : ∀ v ∈ W, (linHom A : (Fin n → F) →ₗ[F] (Fin n → F)) v = lam • v := by
    intro v hv
    have h := (mem_primaryComponent.mp hv)
    rw [hlam] at h
    have h' : (A : Matrix (Fin n) (Fin n) F) *ᵥ v = lam • v := by
      simpa [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sub_eq_zero] using h
    simpa [linHom, Matrix.GeneralLinearGroup.toLin_apply] using h'
  have hφ'bij : Function.Bijective (specialFactorRestrictHom A h) :=
    specialFactorRestrictHom_bijective hsq hh
  let T' := Tstar.map (specialFactorRestrictHom A h)
  have hT'2 : IsPGroup 2 T' := hTstar2.map _
  have hT'odd : Odd T'.index := by
    rw [show T' = Tstar.map (specialFactorRestrictHom A h) from rfl,
      Subgroup.index_map_of_bijective hφ'bij]
    exact hTstarodd
  have hfixedzero : ∀ v ∈ W, (∀ t ∈ TL, (t : (Fin n → F) ≃ₗ[F] (Fin n → F)) v = v) → v = 0 := by
    intro v hv hfix
    haveI : Finite (AdjoinRoot h) := Module.finite_of_finite F
    haveI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
    have hch : ringChar (AdjoinRoot h) ≠ 2 := by
      rw [← Algebra.ringChar_eq F (AdjoinRoot h), ringChar.eq F q]
      exact hq2
    have hfix' : ∀ t ∈ T', (t : W ≃ₗ[AdjoinRoot h] W) (⟨v, hv⟩ : W) = ⟨v, hv⟩ := by
      intro t ht
      obtain ⟨g, hgT, rfl⟩ := Subgroup.mem_map.mp ht
      have hTLmem : linHom
          (Matrix.SpecialLinearGroup.toGL (g : Matrix.SpecialLinearGroup (Fin n) F)) ∈ TL := by
        refine Subgroup.mem_map.mpr ⟨Matrix.SpecialLinearGroup.toGL (g : _), ?_, rfl⟩
        exact Subgroup.mem_map.mpr ⟨g, hgT, rfl⟩
      have hfixg := hfix _ hTLmem
      apply Subtype.ext
      change ((linearSpecialBlockRestrict (glA A) h (specialFactorBlockHom A h g)
        (⟨v, hv⟩ : W) : W) : Fin n → F) = v
      rw [coe_linearSpecialBlockRestrict]
      exact hfixg
    have hzero := CFSG.LinearAlgebra.eq_zero_of_forall_apply_eq_of_odd_index hm2 hch T' hT'odd hfix'
    exact Subtype.ext_iff.mp hzero
  have hW_fix : W ⊓ fixSub TL = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact hfixedzero v hv.1 (mem_fixSub.mp hv.2)
  have hFh_triv : ∀ (g : Fh) (a : Polynomial F),
      a ∈ primaryFactors (glA A : Module.End F (Fin n → F)) →
      a ≠ h → ∀ v ∈ primaryComponent (glA A : Module.End F (Fin n → F)) a,
        (linHom (Matrix.SpecialLinearGroup.toGL (g : Matrix.SpecialLinearGroup (Fin n) F)) :
          (Fin n → F) →ₗ[F] (Fin n → F)) v = v := by
    intro g a ha hah v hv
    have hmem : slGL n F (g : Matrix.SpecialLinearGroup (Fin n) F) ∈
        linearSpecialBlock (glA A) h := g.2
    obtain ⟨-, htriv, -⟩ := mem_linearSpecialBlock.mp hmem
    exact htriv a ha hah v hv
  have hFh_maps_W : ∀ g : Fh, ∀ v ∈ W,
      linHom (Matrix.SpecialLinearGroup.toGL (g : Matrix.SpecialLinearGroup (Fin n) F)) v ∈ W := by
    intro g v hv
    have hmem : slGL n F (g : Matrix.SpecialLinearGroup (Fin n) F) ∈
        linearSpecialBlock (glA A) h := g.2
    have hcomm : Commute (slGL n F (g : Matrix.SpecialLinearGroup (Fin n) F) :
        Module.End F (Fin n → F)) (glA A : Module.End F (Fin n → F)) :=
      mem_gl_centralizer.mp (linearSpecialBlock_le_centralizer (glA A) h hmem)
    exact apply_mem_primaryComponent hcomm hv
  have hU_le_W : CFSG.LinearAlgebra.movedSpan TL ≤ W := by
    rw [CFSG.LinearAlgebra.movedSpan, Submodule.span_le]
    rintro w ⟨t, ht, v, rfl⟩
    obtain ⟨g, hgT, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hgT
    have hdecomp : v = ∑ a ∈ primaryFactors (glA A : Module.End F (Fin n → F)),
        primaryProjection (glA A : Module.End F (Fin n → F)) a v := by
      have h := (LinearMap.congr_fun (sum_primaryProjection hsq) v).symm
      simpa using h
    have hsplit : (linHom ((Matrix.SpecialLinearGroup.toGL.comp Fh.subtype) g₀) :
          (Fin n → F) →ₗ[F] (Fin n → F)) v - v =
        ∑ a ∈ primaryFactors (glA A : Module.End F (Fin n → F)),
          ((linHom ((Matrix.SpecialLinearGroup.toGL.comp Fh.subtype) g₀) :
              (Fin n → F) →ₗ[F] (Fin n → F))
              (primaryProjection (glA A : Module.End F (Fin n → F)) a v) -
            primaryProjection (glA A : Module.End F (Fin n → F)) a v) := by
      conv_lhs => rw [hdecomp]
      rw [map_sum, Finset.sum_sub_distrib]
    change (↑(linHom ((Matrix.SpecialLinearGroup.toGL.comp Fh.subtype) g₀)) :
      (Fin n → F) →ₗ[F] (Fin n → F)) v - v ∈ W
    rw [hsplit]
    refine Submodule.sum_mem _ (fun a ha' => ?_)
    by_cases hah : a = h
    · subst hah
      have hp : primaryProjection (glA A : Module.End F (Fin n → F)) a v ∈ W :=
        primaryProjection_mem hsq ha' v
      exact Submodule.sub_mem _ (hFh_maps_W g₀ _ hp) hp
    · have hp : primaryProjection (glA A : Module.End F (Fin n → F)) a v ∈
          primaryComponent (glA A : Module.End F (Fin n → F)) a :=
        primaryProjection_mem hsq ha' v
      change (↑(linHom (Matrix.SpecialLinearGroup.toGL
        (g₀ : Matrix.SpecialLinearGroup (Fin n) F))) :
          (Fin n → F) →ₗ[F] (Fin n → F)) (primaryProjection
            (glA A : Module.End F (Fin n → F)) a v) -
          primaryProjection (glA A : Module.End F (Fin n → F)) a v ∈ W
      rw [hFh_triv g₀ a ha' hah _ hp, sub_self]
      exact Submodule.zero_mem _
  have hTLcard : (Fintype.card TL : F) ≠ 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hTL2.exists_card_eq
    have h2F : (2 : F) ≠ 0 := by
      intro h
      have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff F q 2).mp h
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hdvd)
    rw [Nat.card_eq_fintype_card] at hk
    rw [hk]
    simpa [Nat.cast_pow] using pow_ne_zero k h2F
  have hcompl : IsCompl (CFSG.LinearAlgebra.movedSpan TL) (fixSub TL) :=
    CFSG.LinearAlgebra.isCompl_movedSpan_fixSub TL hTLcard
  have hTL_maps_W : ∀ t ∈ TL, ∀ w ∈ W, t w ∈ W := by
    intro t ht w hw
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg
    exact hFh_maps_W g₀ w hw
  have hcomplW : IsCompl W (fixSub TL) := by
    refine ⟨disjoint_iff.mpr hW_fix, ?_⟩
    rw [codisjoint_iff]
    exact top_le_iff.mp (by
      rw [← hcompl.sup_eq_top]
      exact sup_le_sup hU_le_W le_rfl)
  have hW_eq_U : W = CFSG.LinearAlgebra.movedSpan TL := by
    have h := (CFSG.LinearAlgebra.movedSpan_eq_of_isCompl_fixSub TL hTLcard hcomplW
      hTL_maps_W (fun t ht w hw => mem_fixSub.mp hw t ht) hW_fix).1
    exact h.symm
  let FhL : Subgroup ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
    (Fh.map (Matrix.SpecialLinearGroup.toGL)).map linHom
  have hFhL_triv : ∀ g ∈ FhL, ∀ b ∈ primaryFactors (glA A : Module.End F (Fin n → F)),
      b ≠ h → ∀ v ∈ primaryComponent (glA A : Module.End F (Fin n → F)) b,
        (g : (Fin n → F) ≃ₗ[F] (Fin n → F)) v = v := by
    rintro g ⟨g₁, ⟨g₀, hg₀, rfl⟩, rfl⟩ b hb hbh v hv
    exact hFh_triv ⟨g₀, hg₀⟩ b hb hbh v hv
  have hTL_comm : ∀ t ∈ TL,
      Commute ((t : (Fin n → F) ≃ₗ[F] (Fin n → F)) : Module.End F (Fin n → F))
        (primaryProjection (glA A : Module.End F (Fin n → F)) h) := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp ht₀
    have hblock : slGL n F (g₀ : Matrix.SpecialLinearGroup (Fin n) F) ∈
        linearSpecialBlock (glA A) h := g₀.2
    have hcomm := mem_gl_centralizer.mp (linearSpecialBlock_le_centralizer (glA A) h hblock)
    have hcoe : ((linHom ((Matrix.SpecialLinearGroup.toGL.comp Fh.subtype) g₀) :
        (Fin n → F) ≃ₗ[F] (Fin n → F)) : Module.End F (Fin n → F)) =
        ((slGL n F (g₀ : Matrix.SpecialLinearGroup (Fin n) F) :
          LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) := by
      ext v
      rfl
    rw [hcoe]
    exact commute_aeval hcomm _
  have hfix_fixSub : ∀ g : Fh, ∀ c' ∈ fixSub TL,
      (linHom (Matrix.SpecialLinearGroup.toGL (g : Matrix.SpecialLinearGroup (Fin n) F)) :
        (Fin n → F) →ₗ[F] (Fin n → F)) c' = c' := by
    intro g c' hc'
    have hg : linHom (Matrix.SpecialLinearGroup.toGL
        (g : Matrix.SpecialLinearGroup (Fin n) F)) ∈ FhL :=
      Subgroup.mem_map.mpr ⟨Matrix.SpecialLinearGroup.toGL
        (g : Matrix.SpecialLinearGroup (Fin n) F),
        Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩, rfl⟩
    exact CFSG.LinearAlgebra.fixes_fixSub_of_trivial_off (x := (glA A : Module.End F (Fin n → F)))
      (a := h) hh hsq FhL TL hFhL_triv hTL_comm hW_fix _ hg c' hc'
  let S₁L : Subgroup ((Fin n → F) ≃ₗ[F] (Fin n → F)) := S₁.map linHom
  let S₂L : Subgroup ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
    ⁅S₁L, Subgroup.zpowers (linHom A)⁆
  have hS₂L_eq : S₂L = S₂.map linHom := by
    rw [show S₂L = ⁅S₁L, Subgroup.zpowers (linHom A)⁆ from rfl,
      show S₂ = ⁅S₁, Subgroup.zpowers A⁆ from rfl]
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
  have hS₁L_cent : ∀ s ∈ S₁L, ∀ t ∈ TL, Commute s t := by
    intro s hs' t ht
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs'
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
    change linHom s₀ * linHom t₀ = linHom t₀ * linHom s₀
    rw [← map_mul, ← map_mul]
    exact congrArg linHom (hS₁_cent s₀ hs₀ t₀ ht₀).eq
  have hA_cent_TL : ∀ t ∈ TL, Commute (linHom A) t := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg
    change linHom A * linHom (Matrix.SpecialLinearGroup.toGL
        (g₀ : Matrix.SpecialLinearGroup (Fin n) F)) =
      linHom (Matrix.SpecialLinearGroup.toGL (g₀ : Matrix.SpecialLinearGroup (Fin n) F)) *
        linHom A
    rw [← map_mul, ← map_mul]
    exact congrArg linHom (hATlift _ ⟨g₀, hg₀, rfl⟩).eq
  have hx_moved : ∀ u ∈ CFSG.LinearAlgebra.movedSpan TL, linHom A u = lam • u := by
    intro u hu
    rw [← hW_eq_U] at hu
    exact hA_scalar u hu
  have hcommute_Fh : ∀ g ∈ S₂L, ∀ hf : Fh,
      Commute g (linHom
        (Matrix.SpecialLinearGroup.toGL (hf : Matrix.SpecialLinearGroup (Fin n) F))) := by
    intro g hg hf
    refine CFSG.LinearAlgebra.commutator_commute_of_scalar_on_movedSpan TL hTLcard
      hS₁L_cent hA_cent_TL hx_moved g hg _ (hfix_fixSub hf) ?_
    intro w hw
    rw [← hW_eq_U]
    exact hFh_maps_W hf w (by rw [hW_eq_U]; exact hw)
  have hS₂_comm : ∀ g ∈ S₂, ∀ hf : Fh,
      Commute g (Matrix.SpecialLinearGroup.toGL (hf : Matrix.SpecialLinearGroup (Fin n) F)) := by
    intro g hg hf
    have hg' : linHom g ∈ S₂L := by
      rw [hS₂L_eq]
      exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have h := hcommute_Fh _ hg' hf
    apply hlinHom_inj
    rw [map_mul, map_mul]
    exact h.eq
  have hsS₂ : s ∈ S₂.map (LinearFlag.conjAut n F) := by
    rw [hS₂map]
    exact hs
  obtain ⟨g, hg, hgconj⟩ := Subgroup.mem_map.mp hsS₂
  have hj' : (j : LinearFlag.projectiveSL n F) ∈ Fh.map (LinearFlag.proj n F) := by
    simpa [hJeq] using hj
  obtain ⟨f, hf, hfj⟩ := hj'
  have hcommg : g * Matrix.SpecialLinearGroup.toGL f = Matrix.SpecialLinearGroup.toGL f * g :=
    (hS₂_comm g hg ⟨f, hf⟩).eq
  rw [← hfj, ← hgconj, LinearFlag.conjAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  calc g * Matrix.SpecialLinearGroup.toGL f * g⁻¹ =
      Matrix.SpecialLinearGroup.toGL f * g * g⁻¹ := by rw [hcommg]
    _ = Matrix.SpecialLinearGroup.toGL f := by group

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
