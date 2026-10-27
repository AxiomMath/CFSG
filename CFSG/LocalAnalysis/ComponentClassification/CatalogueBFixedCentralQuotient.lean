module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientAlgebra
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient

public section

namespace CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

variable {X : Type*} [Group X] [Finite X]

theorem fixedImage_pComponent_quasisimple (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (ψ : MulAut X)
    (hinvariant : Z.map ψ.toMonoidHom = Z)
    (p : ℕ) [Fact p.Prime]
    (hfixed : ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup ψ),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (M : Subgroup (fixedImage Z ψ hinvariant)) (hM : CFSG.IsPComponent p M) :
    CFSG.IsQuasisimple M := by
  let f := fixedImageProjection Z ψ hinvariant
  have hsurjective := fixedImageProjection_surjective Z ψ hinvariant
  have hkernel := fixedImageProjection_kernel_central Z ψ hinvariant hcentral
  obtain ⟨L, hL, hmap, _⟩ :=
    CatalogueBCentralQuotient.pComponent_exists_lift p f hsurjective hkernel M hM
  rw [← hmap]
  exact (CatalogueBCentralQuotient.pComponent_quasisimple_iff f hkernel p L hL).mp
    (hfixed L hL)

theorem quotientFixed_pComponent_quasisimple (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (ψ : MulAut X)
    (hinvariant : Z.map ψ.toMonoidHom = Z)
    (p : ℕ) [Fact p.Prime]
    (hfixed : ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup ψ),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let := fixedImage_normal Z ψ hinvariant hcentral
  let := fixed_quotient_abelian Z ψ hinvariant hcentral
  exact pComponent_quasisimple_of_normal_solvable_quotient p (fixedImage Z ψ hinvariant)
    (fixedImage_pComponent_quasisimple Z hcentral ψ hinvariant p hfixed) L hL

theorem central_quotient_fixed_p_component_transfer (Z : Subgroup X)
    (hcentral : Z ≤ Subgroup.center X) (ψ : MulAut X)
    (hinvariant : Z.map ψ.toMonoidHom = Z) :
    letI := Subgroup.normal_of_le_center hcentral
    (fixedImage Z ψ hinvariant).Normal ∧
      (letI := fixedImage_normal Z ψ hinvariant hcentral;
        IsMulCommutative
          ((FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)) ⧸
            fixedImage Z ψ hinvariant)) ∧
      Function.Surjective (fixedImageProjection Z ψ hinvariant) ∧
      (fixedImageProjection Z ψ hinvariant).ker =
        Z.subgroupOf (FixedCommutingProduct.fixedSubgroup ψ) ∧
      (fixedImageProjection Z ψ hinvariant).ker ≤
        Subgroup.center (FixedCommutingProduct.fixedSubgroup ψ) ∧
      (∀ p : ℕ, p.Prime →
        (∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup ψ),
          CFSG.IsPComponent p L → CFSG.IsQuasisimple L) →
        ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)),
          CFSG.IsPComponent p L → CFSG.IsQuasisimple L) := by
  let := Subgroup.normal_of_le_center hcentral
  refine ⟨fixedImage_normal Z ψ hinvariant hcentral,
    fixed_quotient_abelian Z ψ hinvariant hcentral,
    fixedImageProjection_surjective Z ψ hinvariant,
    fixedImageProjection_kernel Z ψ hinvariant,
    fixedImageProjection_kernel_central Z ψ hinvariant hcentral, ?_⟩
  intro p hp hfixed L hL
  let : Fact p.Prime := ⟨hp⟩
  exact quotientFixed_pComponent_quasisimple Z hcentral ψ hinvariant p hfixed L hL


theorem coreQuot_equiv_of_ker_le_core {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hsurj : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center A) (hker : f.ker ≤ pPrimeCore 2 A) :
    Nonempty (A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g := CatalogueBCentralQuotient.coreQuotientMap 2 f hsurj
  have hker_bot : g.ker = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 A) x
    have hzero := MonoidHom.mem_ker.mp hx
    rw [show g ((QuotientGroup.mk' (pPrimeCore 2 A)) z) =
        (QuotientGroup.mk' (pPrimeCore 2 B)) (f z) from
      CatalogueBCentralQuotient.coreQuotientMap_mk 2 f hsurj z] at hzero
    have hcoreB : f z ∈ pPrimeCore 2 B :=
      (QuotientGroup.eq_one_iff (N := pPrimeCore 2 B) (f z)).mp hzero
    rw [← CatalogueBCentralQuotient.primeCore_map 2 f hsurj hcentral] at hcoreB
    obtain ⟨u, hu, hfu⟩ := Subgroup.mem_map.mp hcoreB
    have hkeru : z * u⁻¹ ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, hfu, mul_inv_cancel]
    have h1 : z * u⁻¹ ∈ pPrimeCore 2 A := hker hkeru
    have hz : z ∈ pPrimeCore 2 A := by
      have e : z = (z * u⁻¹) * u := by group
      rw [e]
      exact Subgroup.mul_mem _ h1 hu
    exact (QuotientGroup.eq_one_iff (N := pPrimeCore 2 A) z).mpr hz
  have hinj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hker_bot
  exact ⟨MulEquiv.ofBijective g ⟨hinj,
    CatalogueBCentralQuotient.coreQuotientMap_surjective 2 f hsurj⟩⟩

theorem fixed_pComponent_image_transport
    (Z : Subgroup X) [Z.Normal] (hcentral : Z ≤ Subgroup.center X)
    (ψ : MulAut X) (hinvariant : Z.map ψ.toMonoidHom = Z)
    (M : Subgroup X)
    (hM : CFSG.GH74.GLS.IsPCompIn 2 (FixedCommutingProduct.fixedSubgroup ψ) M)
    (hA7 : Nonempty ((↥M ⧸ pPrimeCore 2 ↥M) ≃* alternatingGroup (Fin 7))) :
    ∃ _e : (↥(M.map (QuotientGroup.mk' Z)) ⧸
        pPrimeCore 2 ↥(M.map (QuotientGroup.mk' Z))) ≃* alternatingGroup (Fin 7),
      CFSG.GH74.GLS.IsPCompIn 2
        (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant))
        (M.map (QuotientGroup.mk' Z)) := by
  classical
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  let N : Subgroup (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)) :=
    fixedImage Z ψ hinvariant
  let L1 : Subgroup N :=
    (M.subgroupOf (FixedCommutingProduct.fixedSubgroup ψ)).map
      (fixedImageProjection Z ψ hinvariant)
  haveI hNnormal : N.Normal := fixedImage_normal Z ψ hinvariant hcentral
  have hM1 : CFSG.IsPComponent 2 L1 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CatalogueBCentralQuotient.pComponent_map 2
      (fixedImageProjection Z ψ hinvariant)
      (fixedImageProjection_surjective Z ψ hinvariant)
      (fixedImageProjection_kernel_central Z ψ hinvariant hcentral)
      _ hM.2
  have hM2 : CFSG.IsPComponent 2 (L1.map N.subtype) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CatalogueBAlternating.pComponent_of_normal_subgroup 2 N L1 hM1
  have hmap_eq : L1.map N.subtype =
      (M.map π).subgroupOf (FixedCommutingProduct.fixedSubgroup
        (onQuotient Z ψ hinvariant)) := by
    ext y
    constructor
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
      rcases Subgroup.mem_map.mp hz with ⟨w, hw, hwz⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      rw [← hzy, ← hwz]
      change π (w : X) ∈ M.map π
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mp hw)
    · intro hy
      rcases Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy) with ⟨x, hxM, hxy⟩
      have hx : x ∈ FixedCommutingProduct.fixedSubgroup ψ := hM.1 hxM
      refine Subgroup.mem_map.mpr ⟨fixedImageProjection Z ψ hinvariant ⟨x, hx⟩,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxM), ?_⟩
      apply Subtype.ext
      change π x = (y : X ⧸ Z)
      exact hxy
  have hM2canon : CFSG.IsPComponent 2 ((M.map π).subgroupOf
      (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant))) := by
    rwa [← hmap_eq]
  have hle : M.map π ≤ FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant) := by
    intro y hy
    rcases hy with ⟨x, hxM, rfl⟩
    exact (fixedProjection Z ψ hinvariant ⟨x, hM.1 hxM⟩).property
  have hcomp : CFSG.GH74.GLS.IsPCompIn 2
      (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)) (M.map π) :=
    ⟨hle, hM2canon⟩
  let K : Subgroup (X ⧸ Z) := M.map π
  let fM : ↥M →* ↥K :=
    { toFun := fun x => ⟨π x, Subgroup.mem_map_of_mem π x.property⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hfsurj : Function.Surjective fM := by
    intro y
    rcases y.property with ⟨x, hxM, hxy⟩
    refine ⟨⟨x, hxM⟩, ?_⟩
    exact Subtype.ext hxy
  have hker_center : fM.ker ≤ Subgroup.center ↥M := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxπ : π (x : X) = 1 := by
      have := congrArg Subtype.val hx
      simpa [fM] using this
    have hxZ : (x : X) ∈ Z :=
      (QuotientGroup.eq_one_iff (N := Z) (x : X)).mp hxπ
    exact Subgroup.mem_center_iff.mp (hcentral hxZ) (y : X)
  have hcenter_bar : Subgroup.center (↥M ⧸ pPrimeCore 2 ↥M) = ⊥ := by
    have hmap : Subgroup.map (hA7.some :
        (↥M ⧸ pPrimeCore 2 ↥M) →* alternatingGroup (Fin 7))
        (Subgroup.center (↥M ⧸ pPrimeCore 2 ↥M)) = ⊥ := by
      calc
        Subgroup.map (hA7.some :
            (↥M ⧸ pPrimeCore 2 ↥M) →* alternatingGroup (Fin 7))
            (Subgroup.center (↥M ⧸ pPrimeCore 2 ↥M)) =
            Subgroup.center (alternatingGroup (Fin 7)) :=
          Subgroup.map_center_eq hA7.some
        _ = ⊥ := alternatingGroup.center_eq_bot (by simp)
    exact Subgroup.map_injective hA7.some.injective
      (hmap.trans (Subgroup.map_bot _).symm)
  have hMZ_le_core : M ⊓ Z ≤ CFSG.GH74.GLS.pPrimeCoreOf 2 M := by
    intro x hx
    have hxM : x ∈ M := hx.1
    have hxZ : x ∈ Z := hx.2
    have hxq : (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ⟨x, hxM⟩ ∈
        Subgroup.center (↥M ⧸ pPrimeCore 2 ↥M) := by
      rw [Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H y =>
          change (QuotientGroup.mk' (pPrimeCore 2 ↥M)) y *
              (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ⟨x, hxM⟩ =
            (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ⟨x, hxM⟩ *
              (QuotientGroup.mk' (pPrimeCore 2 ↥M)) y
          rw [← map_mul, ← map_mul]
          exact congrArg (QuotientGroup.mk' (pPrimeCore 2 ↥M))
            (Subtype.ext (Subgroup.mem_center_iff.mp (hcentral hxZ) (y : X)))
    have hx1 : (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ⟨x, hxM⟩ = 1 := by
      have := hxq
      rw [hcenter_bar] at this
      exact Subgroup.mem_bot.mp this
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hxM⟩, (QuotientGroup.eq_one_iff (N := pPrimeCore 2 ↥M) ⟨x, hxM⟩).mp hx1, rfl⟩
  have hker_core : fM.ker ≤ pPrimeCore 2 ↥M := by
    intro x hx
    have hxπ : π (x : X) = 1 := by
      have := congrArg Subtype.val hx
      simpa [fM] using this
    have hxZ : (x : X) ∈ Z :=
      (QuotientGroup.eq_one_iff (N := Z) (x : X)).mp hxπ
    have hxO : (x : X) ∈ CFSG.GH74.GLS.pPrimeCoreOf 2 M :=
      hMZ_le_core ⟨x.property, hxZ⟩
    rcases Subgroup.mem_map.mp hxO with ⟨y, hy, hyx⟩
    have hyx' : (⟨(x : X), x.property⟩ : ↥M) = y := Subtype.ext hyx.symm
    rw [← hyx'] at hy
    exact hy
  obtain ⟨e⟩ := coreQuot_equiv_of_ker_le_core fM hfsurj hker_center hker_core
  exact ⟨e.symm.trans hA7.some, hcomp⟩

theorem center_fixed_pComponent_image_transport
    (ψ : MulAut X) (M : Subgroup X)
    (hM : CFSG.GH74.GLS.IsPCompIn 2 (FixedCommutingProduct.fixedSubgroup ψ) M)
    (hA7 : Nonempty ((↥M ⧸ pPrimeCore 2 ↥M) ≃* alternatingGroup (Fin 7))) :
    ∃ _e : (↥(M.map (QuotientGroup.mk' (Subgroup.center X))) ⧸
        pPrimeCore 2 ↥(M.map (QuotientGroup.mk' (Subgroup.center X)))) ≃*
        alternatingGroup (Fin 7),
      CFSG.GH74.GLS.IsPCompIn 2
        (FixedCommutingProduct.fixedSubgroup
          (onQuotient (Subgroup.center X) ψ
            (Subgroup.characteristic_iff_map_eq.mp inferInstance ψ)))
        (M.map (QuotientGroup.mk' (Subgroup.center X))) :=
  fixed_pComponent_image_transport (Subgroup.center X) le_rfl ψ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance ψ) M hM hA7

end CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
