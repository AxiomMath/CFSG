module

public import CFSG.GroupTheory.CocycleCentralizer
public import CFSG.LieType.AlgebraicGroups.TorusCentralizerTorsion
public import CFSG.LieType.AlgebraicGroups.G2ExceptionalComorphism
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TauCeti WithConv CategoryTheory

universe u

theorem exists_primePower_torus_cocycle_hom
    {k : Type u} [Field k] [IsAlgClosed k]
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k) (hT : TauCeti.torusCommHopfAlgProperty k T)
    (π : H.obj ⟶ T.obj) {p : ℕ} (hp : p.Prime) (hpk : (p : k) ≠ 0) :
    ∃ (n : ℕ) (F : Subgroup (WithConv (T →ₐ[k] k))),
      0 < n ∧ Finite F ∧ (∀ t, t ∈ F ↔ t ^ (p ^ n) = 1) ∧
      ∀ (c : WithConv (T →ₐ[k] k) → WithConv (H →ₐ[k] k)),
        (∀ a b, c (a * b) = c a * ((AlgHom.mapDomain π.hom a) * c b *
          (AlgHom.mapDomain π.hom a)⁻¹)) →
        (∀ t ∈ F, c t = 1) →
        ∃ f : WithConv (T →ₐ[k] k) →* WithConv (H →ₐ[k] k),
          (∀ t, f t = c t) ∧
            f.range ≤ Subgroup.centralizer (Set.range (AlgHom.mapDomain (A := k) π.hom)) := by
  obtain ⟨n, F, hn, hF, hmem, hdet⟩ :=
    exists_primePower_torus_centralizer_detector H T hT π hp hpk
  obtain ⟨r, ⟨e⟩⟩ := exists_coordinateEquiv_of_torus T hT
  let E : WithConv (T →ₐ[k] k) ≃* (Fin r → kˣ) :=
    (AlgHom.mapDomainMulEquiv (A := k) e).trans SplitTorus.pointsMulEquiv
  have hcomm (a b : WithConv (T →ₐ[k] k)) : a * b = b * a := by
    apply E.injective
    rw [map_mul, map_mul, mul_comm]
  refine ⟨n, F, hn, hF, hmem, ?_⟩
  intro c hc hzero
  exact CFSG.GroupTheory.exists_monoidHom_of_cocycle_centralizer_eq
    (AlgHom.mapDomain π.hom) c hcomm hc F hzero hdet

private theorem torus_cocycle_eq_one_of_hom
    {k : Type u} [Field k] [IsAlgClosed k]
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (hT : TauCeti.torusCommHopfAlgProperty k T)
    (φ : H →ₐ[k] T) (f : WithConv (T →ₐ[k] k) →* WithConv (H →ₐ[k] k))
    (hf : ∀ t, f t = toConv (t.ofConv.comp φ))
    (hunip : ∀ t : WithConv (T →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint (toConv (t.ofConv.comp φ))) :
    ∀ t : WithConv (T →ₐ[k] k), toConv (t.ofConv.comp φ) = 1 := by
  let c : WithConv (T →ₐ[k] k) → WithConv (H →ₐ[k] k) := fun t => toConv (t.ofConv.comp φ)
  have hmul (a b) : c (a * b) = c a * c b := by
    change toConv ((a * b).ofConv.comp φ) =
      toConv (a.ofConv.comp φ) * toConv (b.ofConv.comp φ)
    rw [← hf (a * b), map_mul, hf a, hf b]
  have hTsm : Algebra.Smooth k T := (TauCeti.smoothCommHopfAlgProperty_iff T.obj).mp (hT.smooth k T)
  let := hTsm
  let : IsReduced T := TauCeti.isReduced_of_smooth k T
  let φ' := bialgHomOfPointMulTo φ hmul
  have heq (t) : AlgHom.mapDomain (A := k) φ' t = c t := rfl
  intro t
  have hs := (isSemisimplePoint_of_torus T hT t).mapDomain φ'
  rw [heq] at hs
  exact hs.eq_one_of_isUnipotent (hunip t)

theorem exists_primePower_torus_cocycle_eq_one
    {k : Type u} [Field k] [IsAlgClosed k]
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k) (hT : TauCeti.torusCommHopfAlgProperty k T)
    (π : H.obj ⟶ T.obj) {p : ℕ} (hp : p.Prime) (hpk : (p : k) ≠ 0) :
    ∃ (n : ℕ) (F : Subgroup (WithConv (T →ₐ[k] k))),
      0 < n ∧ Finite F ∧ (∀ t, t ∈ F ↔ t ^ (p ^ n) = 1) ∧
      ∀ φ : H →ₐ[k] T,
        let c : WithConv (T →ₐ[k] k) → WithConv (H →ₐ[k] k) :=
          fun t => toConv (t.ofConv.comp φ)
        (∀ a b, c (a * b) = c a * ((AlgHom.mapDomain π.hom a) * c b *
          (AlgHom.mapDomain π.hom a)⁻¹)) →
        (∀ t ∈ F, c t = 1) →
        (∀ t, TauCeti.HopfAlgebra.IsUnipotentPoint (c t)) → ∀ t, c t = 1 := by
  obtain ⟨n, F, hn, hF, hmem, hhom⟩ := exists_primePower_torus_cocycle_hom H T hT π hp hpk
  refine ⟨n, F, hn, hF, hmem, ?_⟩
  intro φ c hc hzero hunip
  obtain ⟨f, hf, _⟩ := hhom c hc hzero
  exact torus_cocycle_eq_one_of_hom H T hT φ f hf hunip

end CFSG.LieType.AlgebraicGroups
