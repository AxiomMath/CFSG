module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.RingTheory.FiniteType.PointSeparation
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import CFSG.Mathlib.RingTheory.ConnectedRegular
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

public noncomputable section

open WithConv

namespace CFSG.LieType.AlgebraicGroups.TorusConjugacy

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

section Dense

omit [IsAlgClosed k] in
theorem eq_zero_of_forall_mem_of_forall_exists_mul_inv_mem {H : Type u} [CommRing H]
    [HopfAlgebra k H] [IsDomain H] {Γ Γ' : Set (WithConv (H →ₐ[k] k))}
    (hΓ : ∀ x : H, (∀ g ∈ Γ, g.ofConv x = 0) → x = 0)
    (F : Finset (WithConv (H →ₐ[k] k))) (hF : ∀ g ∈ Γ, ∃ f ∈ F, g * f⁻¹ ∈ Γ')
    {x : H} (hx : ∀ g ∈ Γ', g.ofConv x = 0) : x = 0 := by
  have hprod : ∏ f ∈ F, TauCeti.HopfAlgebra.rightTranslationAlgHom f⁻¹ x = 0 := by
    apply hΓ
    intro g hg
    obtain ⟨f, hf, hgf⟩ := hF g hg
    rw [map_prod]
    refine Finset.prod_eq_zero hf ?_
    rw [TauCeti.HopfAlgebra.ofConv_rightTranslationAlgHom]
    exact hx _ hgf
  obtain ⟨f, -, hf⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hinj : Function.Injective (TauCeti.HopfAlgebra.rightTranslationAlgHom (k := k) f⁻¹) := by
    rw [← TauCeti.HopfAlgebra.rightTranslationAlgEquiv_toAlgHom]
    exact (TauCeti.HopfAlgebra.rightTranslationAlgEquiv f⁻¹).injective
  exact hinj (hf.trans (map_zero _).symm)


theorem exists_forall_apply_eq_zero_of_forall_exists {Z : Type*} [CommRing Z] [Algebra k Z]
    [Algebra.FiniteType k Z] [IsDomain Z] {ι : Type*} [Finite ι] (P : ι → Set Z)
    (hcover : ∀ y : Z →ₐ[k] k, ∃ i, ∀ g ∈ P i, y g = 0) :
    ∃ i, ∀ y : Z →ₐ[k] k, ∀ g ∈ P i, y g = 0 := by
  classical
  by_contra hne
  push Not at hne
  choose y g hg hyg using hne
  let : Fintype ι := Fintype.ofFinite ι
  have hprod : ∏ i, g i = 0 := by
    refine TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k) fun z => ?_
    obtain ⟨i, hi⟩ := hcover z
    rw [map_prod, map_zero]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hi _ (hg i))
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
  exact hyg i (by rw [hi, map_zero])

end Dense

section Component

variable (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)

theorem isDomain_of_isReduced_of_connectedSpace (A : Type u) [CommRing A] [HopfAlgebra k A]
    [Algebra.FiniteType k A] [IsReduced A] [ConnectedSpace (PrimeSpectrum A)] : IsDomain A := by
  have hsm : Algebra.Smooth k A :=
    (TauCeti.smoothCommHopfAlgProperty_iff (_root_.CommHopfAlgCat.of k A)).mp
      (TauCeti.smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k
        (_root_.CommHopfAlgCat.of k A))
  exact @CFSG.isDomain_of_smooth_of_connected k _ A _ _ hsm _

theorem isReduced_quotient_identityComponentHopfIdeal
    (Q : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced Q] :
    IsReduced (Q ⧸ (TauCeti.HopfAlgebra.identityComponentHopfIdeal
      (k := k) (H := Q)).toIdeal) := by
  let _ : IsNoetherianRing ↥Q := Algebra.FiniteType.isNoetherianRing k ↥Q
  let _ : LocallyConnectedSpace (PrimeSpectrum ↥Q) := inferInstance
  let z : PrimeSpectrum ↥Q := TauCeti.Bialgebra.augmentationPoint k ↥Q
  let e : ↥Q := PrimeSpectrum.connectedComponentIdempotent z
  have he : IsIdempotentElem e := PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent z
  have hIC : (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Q)).toIdeal =
      PrimeSpectrum.connectedComponentIdeal z := by
    rw [TauCeti.HopfAlgebra.identityComponentHopfIdeal_toIdeal]
  rw [← Ideal.isRadical_iff_quotient_reduced, hIC,
    Ideal.isRadical_iff_pow_one_lt 2 (by norm_num)]
  intro r hr
  obtain ⟨a, ha⟩ := PrimeSpectrum.mem_connectedComponentIdeal_iff.mp hr
  have he1 : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, he.eq, sub_self]
  have hsq : (e * r) ^ 2 = 0 := by
    calc (e * r) ^ 2 = e ^ 2 * r ^ 2 := mul_pow e r 2
      _ = e * r ^ 2 := by rw [pow_two, he.eq]
      _ = e * (a * (1 - e)) := by rw [← ha]
      _ = a * (e * (1 - e)) := by ring
      _ = 0 := by rw [he1, mul_zero]
  have hQ : IsReduced ↥Q := ‹IsReduced Q›
  have her : e * r = 0 :=
    (isReduced_iff_pow_one_lt (R := ↥Q) 2 (by norm_num)).mp hQ (e * r) hsq
  exact PrimeSpectrum.mem_connectedComponentIdeal_iff.mpr ⟨r, by
    rw [mul_sub, mul_one, mul_comm r e, her, sub_zero]⟩

abbrev closureMap (S : Subgroup (WithConv (H →ₐ[k] k))) :
    H →ₐc[k] TauCeti.FiniteTypeCommHopfAlgCat.quotient H (TauCeti.HopfIdeal.vanishingIdeal S) :=
  TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H _)

@[expose] def closureIdentityComponent (S : Subgroup (WithConv (H →ₐ[k] k))) :
    TauCeti.HopfIdeal k H :=
  TauCeti.HopfIdeal.comapOfSurjective
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
      (H := TauCeti.FiniteTypeCommHopfAlgCat.quotient H (TauCeti.HopfIdeal.vanishingIdeal S)))
    (closureMap H S) (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj _)

theorem isDomain_quotient_closureIdentityComponent (S : Subgroup (WithConv (H →ₐ[k] k))) :
    IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient H (closureIdentityComponent H S)) := by
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H (TauCeti.HopfIdeal.vanishingIdeal S)
  let IC : TauCeti.HopfIdeal k Q :=
    TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Q)
  have hQred : IsReduced Q := TauCeti.HopfIdeal.isReduced_quotient_vanishingIdeal S
  have hred : IsReduced (Q ⧸ IC.toIdeal) :=
    @isReduced_quotient_identityComponentHopfIdeal k _ _ Q hQred
  have hconn : ConnectedSpace (PrimeSpectrum (Q ⧸ IC.toIdeal)) := by
    let _ : IsNoetherianRing ↥Q := Algebra.FiniteType.isNoetherianRing k ↥Q
    let _ : LocallyConnectedSpace (PrimeSpectrum ↥Q) := inferInstance
    have hIC' : IC.toIdeal = PrimeSpectrum.connectedComponentIdeal
        (TauCeti.Bialgebra.augmentationPoint k ↥Q) := by
      rw [TauCeti.HopfAlgebra.identityComponentHopfIdeal_toIdeal]
    rw [hIC']
    exact PrimeSpectrum.connectedSpace_quotient_connectedComponentIdeal _
  have hdom : IsDomain (Q ⧸ IC.toIdeal) :=
    @isDomain_of_isReduced_of_connectedSpace k _ _ (Q ⧸ IC.toIdeal) _ _ _ hred hconn
  let e : TauCeti.CommHopfAlgCat.quotient H.obj (closureIdentityComponent H S) ≅
      TauCeti.CommHopfAlgCat.quotient Q.obj IC :=
    TauCeti.CommHopfAlgCat.quotientIsoOfSurjective
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H
        (TauCeti.HopfIdeal.vanishingIdeal S)).hom
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj
        (TauCeti.HopfIdeal.vanishingIdeal S)) IC
  let E := _root_.CommHopfAlgCat.isoEquivBialgEquiv e
  exact @MulEquiv.isDomain _ (Q ⧸ IC.toIdeal) _ _ hdom E.toAlgEquiv.toRingEquiv.toMulEquiv

theorem quotientPointsSubgroup_closureIdentityComponent_le
    (S : Subgroup (WithConv (H →ₐ[k] k))) :
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj (closureIdentityComponent H S)
        (CommAlgCat.of k k) ≤
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj (TauCeti.HopfIdeal.vanishingIdeal S)
        (CommAlgCat.of k k) := by
  have hdef : closureIdentityComponent H S =
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
        (H := TauCeti.FiniteTypeCommHopfAlgCat.quotient H
          (TauCeti.HopfIdeal.vanishingIdeal S))).comapOfSurjective
        (closureMap H S) (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj _) := rfl
  have hle : TauCeti.HopfIdeal.vanishingIdeal S ≤ closureIdentityComponent H S := by
    intro x hx
    have h0 : closureMap H S x = 0 := by
      rw [TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff H
        (TauCeti.HopfIdeal.vanishingIdeal S) x]
      exact hx
    rw [hdef, TauCeti.HopfIdeal.mem_comapOfSurjective, h0]
    exact Submodule.zero_mem _
  intro g hg
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg ⊢
  intro x hx
  exact hg x (hle hx)

theorem closureIdentityComponent_le_of_vanishingIdeal_le {S : Subgroup (WithConv (H →ₐ[k] k))}
    {I : TauCeti.HopfIdeal k H}
    [IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)]
    [ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I))]
    (hv : TauCeti.HopfIdeal.vanishingIdeal S ≤ I) :
    closureIdentityComponent H S ≤ I := by
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H (TauCeti.HopfIdeal.vanishingIdeal S)
  let IC : TauCeti.HopfIdeal k Q :=
    TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Q)
  have hdef : closureIdentityComponent H S =
      IC.comapOfSurjective (closureMap H S)
        (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj _) := rfl
  have hker : IC.toIdeal ≤
      RingHom.ker (TauCeti.CommHopfAlgCat.quotientMapOfLe H.obj hv).hom.toAlgHom.toRingHom :=
    TauCeti.CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected
      (TauCeti.CommHopfAlgCat.quotientMapOfLe H.obj hv)
  intro x hx
  have hx' : closureMap H S x ∈ IC :=
    TauCeti.HopfIdeal.mem_comapOfSurjective.mp (hdef ▸ hx)
  have hz : (TauCeti.CommHopfAlgCat.quotientMapOfLe H.obj hv).hom (closureMap H S x) = 0 :=
    RingHom.mem_ker.mp (hker hx')
  have hcl : closureMap H S x =
      Ideal.Quotient.mkₐ k (TauCeti.HopfIdeal.vanishingIdeal S).toIdeal x :=
    TauCeti.CommHopfAlgCat.mkQuotient_apply H.obj
      (TauCeti.HopfIdeal.vanishingIdeal S) x
  rw [hcl, TauCeti.CommHopfAlgCat.quotientMapOfLe_mk] at hz
  exact (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff H I x).mp (by
    rw [← hz]
    exact TauCeti.CommHopfAlgCat.mkQuotient_apply H.obj I x)

theorem closureIdentityComponent_le {S : Subgroup (WithConv (H →ₐ[k] k))}
    {I : TauCeti.HopfIdeal k H}
    [IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)]
    [ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I))]
    (hI : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) ≤ S) :
    closureIdentityComponent H S ≤ I := by
  have hv : TauCeti.HopfIdeal.vanishingIdeal S ≤ I := by
    intro x hx
    refine (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff H I x).mp ?_
    refine TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k) (x := _) (y := 0) ?_
    intro f
    rw [map_zero]
    let g : WithConv (H →ₐ[k] k) := WithConv.toConv
      (f.comp (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I)))
    have hg : g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I
        (CommAlgCat.of k k) := by
      rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      intro y hy
      have hy0 : TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I) y = 0 :=
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff H I y).mpr hy
      show f (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I) y) = 0
      rw [hy0, map_zero]
    exact (TauCeti.HopfIdeal.mem_vanishingIdeal S x).mp hx ⟨g, hI hg⟩
  exact closureIdentityComponent_le_of_vanishingIdeal_le H hv

theorem vanishingIdeal_le_closureIdentityComponent (S : Subgroup (WithConv (H →ₐ[k] k))) :
    TauCeti.HopfIdeal.vanishingIdeal S ≤ closureIdentityComponent H S := by
  have hdef : closureIdentityComponent H S =
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
        (H := TauCeti.FiniteTypeCommHopfAlgCat.quotient H
          (TauCeti.HopfIdeal.vanishingIdeal S))).comapOfSurjective
        (closureMap H S) (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj _) := rfl
  intro x hx
  have h0 : closureMap H S x = 0 := by
    rw [TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff H
      (TauCeti.HopfIdeal.vanishingIdeal S) x]
    exact hx
  rw [hdef, TauCeti.HopfIdeal.mem_comapOfSurjective, h0]
  exact Submodule.zero_mem _

omit [IsAlgClosed k] in
theorem isDomain_quotient_conjugate (I : TauCeti.HopfIdeal k H)
    [IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)] (g : WithConv (H →ₐ[k] k)) :
    IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient H (I.conjugate g)) := by
  let f : H.obj ⟶ H.obj :=
    _root_.CommHopfAlgCat.ofHom (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom
  have hf : Function.Surjective f.hom := by
    change Function.Surjective (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom
    simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
      EquivLike.surjective (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g)
  have hconj : I.conjugate g = I.comapOfSurjective f.hom hf :=
    TauCeti.HopfIdeal.conjugate_eq_comapOfSurjective I g
  let e := TauCeti.CommHopfAlgCat.quotientIsoOfSurjective f hf I
  let E := _root_.CommHopfAlgCat.isoEquivBialgEquiv e
  rw [hconj]
  exact @MulEquiv.isDomain _ (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I) _ _ ‹_›
    E.toAlgEquiv.toRingEquiv.toMulEquiv

theorem conj_mem_closureIdentityComponent {S : Subgroup (WithConv (H →ₐ[k] k))}
    {g : WithConv (H →ₐ[k] k)} (hg : ∀ s ∈ S, g * s * g⁻¹ ∈ S) {x : WithConv (H →ₐ[k] k)}
    (hx : x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj (closureIdentityComponent H S)
      (CommAlgCat.of k k)) :
    g * x * g⁻¹ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj
      (closureIdentityComponent H S) (CommAlgCat.of k k) := by
  let J := closureIdentityComponent H S
  have : IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) :=
    isDomain_quotient_closureIdentityComponent H S
  have : IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient H (J.conjugate g)) :=
    isDomain_quotient_conjugate H J g
  have : ConnectedSpace (PrimeSpectrum
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient H (J.conjugate g))) :=
    connectedSpace_iff_univ.mpr (IrreducibleSpace.isIrreducible_univ _).isConnected
  have hmv : TauCeti.AlgHom.mapValue (H := H) (Algebra.ofId k k) g = g := by
    apply WithConv.ofConv_injective
    ext a
    rw [TauCeti.AlgHom.mapValue_apply]
    exact (Algebra.ofId k k).commutes (g.ofConv a)
  have hv : TauCeti.HopfIdeal.vanishingIdeal S ≤ J.conjugate g := by
    intro f hf
    rw [TauCeti.HopfIdeal.mem_conjugate]
    apply vanishingIdeal_le_closureIdentityComponent H S
    rw [TauCeti.HopfIdeal.mem_vanishingIdeal] at hf ⊢
    intro s
    have he : toConv (s.val.ofConv.comp (TauCeti.HopfAlgebra.pointConjugationAlgHom g)) =
        g * s.val * g⁻¹ := by
      rw [TauCeti.HopfAlgebra.comp_pointConjugationAlgHom, hmv]
    have heval := congrArg (fun p : WithConv (H →ₐ[k] k) => p.ofConv f) he
    exact heval.trans (hf ⟨_, hg s.val s.2⟩)
  have hle : J ≤ J.conjugate g := closureIdentityComponent_le_of_vanishingIdeal_le H hv
  have hmem := (TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff J g
    (CommAlgCat.of k k) x).mpr hx
  rw [hmv] at hmem
  exact TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj hle _ hmem

omit [IsAlgClosed k] in
theorem ringKrullDim_quotient_lt [IsDomain H] {J : TauCeti.HopfIdeal k H} (hJ : J ≠ ⊥) :
    ringKrullDim (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) < ringKrullDim H := by
  have hne : J.toIdeal ≠ ⊥ := by
    intro h
    apply hJ
    refine TauCeti.HopfIdeal.ext fun y => ?_
    rw [TauCeti.HopfIdeal.mem_bot, ← TauCeti.HopfIdeal.mem_toIdeal, h]
    simp
  obtain ⟨x, hxJ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxdiv : x ∈ nonZeroDivisors ↥H := mem_nonZeroDivisors_of_ne_zero hx0
  have hstep : ringKrullDim ((↥H) ⧸ Ideal.span {x}) + 1 ≤ ringKrullDim ↥H :=
    ringKrullDim_quotient_succ_le_of_nonZeroDivisor hxdiv
  have hspan : Ideal.span {x} ≤ J.toIdeal := Ideal.span_le.mpr (by simpa using hxJ)
  have hmono : ringKrullDim (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) ≤
      ringKrullDim ((↥H) ⧸ Ideal.span {x}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hspan)
      (Ideal.Quotient.factor_surjective hspan)
  have hchain : ringKrullDim (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) + 1 ≤
      ringKrullDim ↥H := by
    have h1 := add_le_add_right hmono 1
    rw [add_comm 1 (ringKrullDim (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J)),
      add_comm 1 (ringKrullDim ((↥H) ⧸ Ideal.span {x}))] at h1
    exact h1.trans hstep
  have htop : ringKrullDim ↥H < ⊤ := by
    have : FiniteRingKrullDim ↥H := TauCeti.finiteRingKrullDim_of_finiteType k ↥H
    exact ringKrullDim_lt_top
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim ↥H := ringKrullDim_nonneg_of_nontrivial
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim ↥H = (m : WithBot ℕ∞) := by
    generalize ringKrullDim ↥H = z at htop h0 ⊢
    induction z using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe y =>
      induction y using ENat.recTopCoe with
      | top => exact absurd htop (by simp)
      | coe n => exact ⟨n, rfl⟩
  generalize hdim : ringKrullDim (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) = a at hchain ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞)) h0
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      have hbad : (⊤ : WithBot ℕ∞) < ⊤ := by
        simpa using hchain.trans_lt htop
      exact absurd hbad (lt_irrefl ⊤)
    | coe n =>
      rw [hm] at hchain ⊢
      have h1 : ((n : ℕ) : WithBot ℕ∞) + 1 ≤ ((m : ℕ) : WithBot ℕ∞) := by
        simpa using hchain
      rw [ENat.WithBot.add_one_le_iff] at h1
      exact_mod_cast h1

theorem relIndex_closureIdentityComponent_ne_zero (S : Subgroup (WithConv (H →ₐ[k] k))) :
    (TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj (closureIdentityComponent H S)
      (CommAlgCat.of k k)).relIndex S ≠ 0 := by
  let J := TauCeti.HopfIdeal.vanishingIdeal S
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H J
  let IC : TauCeti.HopfIdeal k Q :=
    TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Q)
  let ψ := (TauCeti.CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k)).hom
  have hψ : Function.Injective ψ :=
    TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj J (CommAlgCat.of k k)
  have hdef : closureIdentityComponent H S =
      IC.comapOfSurjective (closureMap H S)
        (TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj _) := rfl
  have hcl : ∀ x, closureMap H S x = Ideal.Quotient.mkₐ k J.toIdeal x := fun x =>
    TauCeti.CommHopfAlgCat.mkQuotient_apply H.obj J x
  have hmap : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj (closureIdentityComponent H S)
      (CommAlgCat.of k k) =
      (TauCeti.CommHopfAlgCat.quotientPointsSubgroup Q.obj IC (CommAlgCat.of k k)).map ψ := by
    ext g
    constructor
    · intro hg
      obtain ⟨q, rfl⟩ := quotientPointsSubgroup_closureIdentityComponent_le H S hg
      refine ⟨q, ?_, rfl⟩
      rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg
      rw [SetLike.mem_coe, TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj J y
      have hx : x ∈ closureIdentityComponent H S := by
        rw [hdef, TauCeti.HopfIdeal.mem_comapOfSurjective]
        exact hy
      have h := hg x hx
      rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply_apply] at h
      rw [← hcl] at h
      exact h
    · rintro ⟨q, hq, rfl⟩
      rw [SetLike.mem_coe, TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hq
      rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      intro x hx
      have hx' : closureMap H S x ∈ IC := by
        rw [hdef, TauCeti.HopfIdeal.mem_comapOfSurjective] at hx
        exact hx
      rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply_apply, ← hcl]
      exact hq _ hx'
  have hS : S ≤ (⊤ : Subgroup _).map ψ := by
    intro s hs
    have hs' : s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k) := by
      rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      intro x hx
      exact (TauCeti.HopfIdeal.mem_vanishingIdeal S x).mp hx ⟨s, hs⟩
    obtain ⟨q, rfl⟩ := hs'
    exact ⟨q, trivial, rfl⟩
  have hfin : (TauCeti.CommHopfAlgCat.quotientPointsSubgroup Q.obj IC
      (CommAlgCat.of k k)).index ≠ 0 :=
    Subgroup.index_ne_zero_iff_finite.mpr
      (TauCeti.FiniteTypeCommHopfAlgCat.instFiniteComponentGroupPoints Q)
  rw [hmap]
  refine mt (Subgroup.relIndex_eq_zero_of_le_right hS) ?_
  rw [Subgroup.relIndex_map_map_of_injective _ _ hψ, Subgroup.relIndex_top_right]
  exact hfin

theorem range_mapDomain_le_of_relIndex_ne_zero {Z : Type u} [CommRing Z] [HopfAlgebra k Z]
    [Algebra.FiniteType k Z] [IsDomain Z] (φ : H →ₐc[k] Z) (I : TauCeti.HopfIdeal k H)
    (h : (TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)).relIndex
      (TauCeti.AlgHom.mapDomain (A := k) φ).range ≠ 0) :
    (TauCeti.AlgHom.mapDomain (A := k) φ).range ≤
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := by
  classical
  let T := TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)
  let ι := TauCeti.AlgHom.mapDomain (A := k) φ
  have hindex : (T.comap ι).index ≠ 0 := by
    rw [Subgroup.index_comap]
    exact h
  have : Finite (WithConv (Z →ₐ[k] k) ⧸ T.comap ι) :=
    Subgroup.index_ne_zero_iff_finite.mp hindex
  let : Fintype (WithConv (Z →ₐ[k] k) ⧸ T.comap ι) := Fintype.ofFinite _
  let F : Finset (WithConv (Z →ₐ[k] k)) :=
    Finset.univ.image fun q : WithConv (Z →ₐ[k] k) ⧸ T.comap ι => (Quotient.out q)⁻¹
  have hcover : ∀ z ∈ (Set.univ : Set (WithConv (Z →ₐ[k] k))),
      ∃ f ∈ F, z * f⁻¹ ∈ (T.comap ι : Set (WithConv (Z →ₐ[k] k))) := by
    intro z _
    obtain ⟨g, hg⟩ := QuotientGroup.mk_out_eq_mul (T.comap ι) z⁻¹
    refine ⟨(Quotient.out (QuotientGroup.mk z⁻¹ : WithConv (Z →ₐ[k] k) ⧸ T.comap ι))⁻¹,
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    rw [inv_inv, show Quotient.out (QuotientGroup.mk z⁻¹ : WithConv (Z →ₐ[k] k) ⧸ T.comap ι) =
      z⁻¹ * (g : WithConv (Z →ₐ[k] k)) from hg, mul_inv_cancel_left]
    exact g.2
  have hdense : ∀ y : Z, (∀ z ∈ (Set.univ : Set (WithConv (Z →ₐ[k] k))), z.ofConv y = 0) →
      y = 0 := fun y hy => TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k) fun f => by
    rw [map_zero]
    exact hy (toConv f) (Set.mem_univ _)
  rintro _ ⟨z, rfl⟩
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro a ha
  have h0 : φ a = 0 := by
    refine eq_zero_of_forall_mem_of_forall_exists_mul_inv_mem hdense F hcover fun z' hz' => ?_
    have hz'' : ι z' ∈ T := hz'
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hz''
    rw [← TauCeti.AlgHom.mapDomain_apply_apply]
    exact hz'' a ha
  rw [TauCeti.AlgHom.mapDomain_apply_apply, h0, map_zero]

end Component

end CFSG.LieType.AlgebraicGroups.TorusConjugacy
