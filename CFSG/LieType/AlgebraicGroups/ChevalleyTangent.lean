module

public import TauCeti.Algebra.AlgebraicGroup.Representation.SubspaceStabilizer
public import TauCeti.Algebra.AlgebraicGroup.Tangent.InvariantDerivation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent

public noncomputable section

open scoped TensorProduct
open TauCeti

namespace TauCeti.Bialgebra

universe u v w

variable {k : Type u} [CommRing k]
variable {H : Type v} [CommRing H] [_root_.Bialgebra k H]
variable {A : Type w} [CommRing A] [_root_.Bialgebra k A]

theorem map_leftInvariantDerivation (φ : H →ₐc[k] A)
    (d : Derivation k A (CounitAlgebra k A k)) (x : H) :
    φ (leftInvariantDerivation (derivationComp (B := k) φ d) x) =
      leftInvariantDerivation d (φ x) := by
  have hδ :
      (CounitAlgebra.algEquivSelf k H k).toLinearMap ∘ₗ
          (derivationComp (B := k) φ d).toLinearMap =
        ((CounitAlgebra.algEquivSelf k A k).toLinearMap ∘ₗ d.toLinearMap) ∘ₗ
          φ.toLinearMap := by
    ext h
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe]
    exact algEquivSelf_derivationComp_apply φ d h
  have hΔ : TensorProduct.map φ.toLinearMap φ.toLinearMap (Coalgebra.comul (R := k) x) =
      Coalgebra.comul (R := k) (φ x) := by
    simp [BialgHom.toCoalgHom_apply]
  rw [leftInvariantDerivation_apply, leftInvariantDerivation_apply, ← hΔ,
    LinearMap.tensorComponent_map]
  exact congrArg (fun ψ => φ (LinearMap.tensorComponent ψ (Coalgebra.comul (R := k) x))) hδ

end TauCeti.Bialgebra

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k}

theorem leftInvariantDerivation_mem {I : HopfIdeal k H}
    {d : Derivation k H (Bialgebra.CounitAlgebra k H k)}
    (hd : d ∈ I.lieSubalgebra (B := k)) {x : H} (hx : x ∈ I) :
    Bialgebra.leftInvariantDerivation d x ∈ I := by
  let e := (I.quotientLieEquiv (B := k)).symm ⟨d, hd⟩
  have he : I.quotientLieHom e = d :=
    (quotientLieEquiv_apply_coe I e).symm.trans
      (congrArg Subtype.val ((I.quotientLieEquiv (B := k)).apply_symm_apply ⟨d, hd⟩))
  rw [← he]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal)
    (Bialgebra.leftInvariantDerivation (I.quotientLieHom e) x) = 0
  rw [quotientLieHom_apply, Bialgebra.map_leftInvariantDerivation]
  have hx' : (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [hx', map_zero]

theorem coe_differential_regularSubcomodule
    (V : Subcomodule k H H)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (v : V) :
    letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
    ((Comodule.differential (R := k) (H := H) (M := V) d v : V) : H) =
      Bialgebra.leftInvariantDerivation d (v : H) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  rw [← Derivation.coeFn_coe, Bialgebra.toLinearMap_leftInvariantDerivation]
  simpa only [Subcomodule.subtype_apply] using
    (Subcomodule.subtype V).map_differential d v

theorem mem_lieSubalgebra_iff_preserves_definingSubspace
    (I : HopfIdeal k H) (V : Subcomodule k H H)
    (hgen : I.toIdeal ≤ Ideal.span ((V : Set H) ∩ (I : Set H)))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
    d ∈ I.lieSubalgebra (B := k) ↔
      ∀ v ∈ I.definingSubspace V,
        Comodule.differential (R := k) (H := H) (M := V) d v ∈
          I.definingSubspace V := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  constructor
  · intro hd v hv
    rw [mem_definingSubspace, coe_differential_regularSubcomodule (k := k) (H := H)]
    exact leftInvariantDerivation_mem hd ((mem_definingSubspace I V v).mp hv)
  · intro hpres
    have hspan : I.toIdeal = Ideal.span ((V : Set H) ∩ (I : Set H)) := by
      apply le_antisymm hgen
      exact Ideal.span_le.mpr fun x hx => hx.2
    rw [mem_lieSubalgebra_iff_of_toIdeal_eq_span I hspan]
    rintro x ⟨hxV, hxI⟩
    have hv := hpres (⟨x, hxV⟩ : V) ((mem_definingSubspace I V _).mpr hxI)
    rw [mem_definingSubspace, coe_differential_regularSubcomodule (k := k) (H := H)] at hv
    apply (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
    rw [map_zero, ← Bialgebra.counit_leftInvariantDerivation]
    exact I.counit_eq_zero hv

end TauCeti.HopfIdeal
