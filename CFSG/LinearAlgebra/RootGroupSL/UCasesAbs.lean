module

public import CFSG.LinearAlgebra.RootGroupSL.UCases
public import CFSG.LinearAlgebra.RootGroupSL.DatumTransport

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E V : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]
  [Module.Finite k V] [Finite k] [Finite E] [CharP k 2]

private lemma datumElt_proof_irrel [Module.Finite k E] (ι : E →ₗ[k] V) (π : V →ₗ[k] E)
    (h1 h2 : ∀ t, π (ι t) = 0) (t : E) :
    datumElt ι π h1 t = datumElt ι π h2 t := by
  apply Subtype.ext
  ext v
  rfl

private lemma datumRoot_proof_irrel [Module.Finite k E] (ι : E →ₗ[k] V) (π : V →ₗ[k] E)
    (h1 h2 : ∀ t, π (ι t) = 0) : datumRoot ι π h1 = datumRoot ι π h2 := by
  unfold datumRoot
  have hset : Set.range (datumElt ι π h1) = Set.range (datumElt ι π h2) := by
    ext g
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [← datumElt_proof_irrel ι π h1 h2 t, ht]⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [← datumElt_proof_irrel ι π h1 h2 t, ht]⟩
  rw [hset]

private lemma datumRoot_congr [Module.Finite k E] {ι1 ι2 : E →ₗ[k] V} {π1 π2 : V →ₗ[k] E}
    (h1 : ∀ t, π1 (ι1 t) = 0) (h2 : ∀ t, π2 (ι2 t) = 0) (hι : ι1 = ι2) (hπ : π1 = π2) :
    datumRoot ι1 π1 h1 = datumRoot ι2 π2 h2 := by
  subst hι
  subst hπ
  exact datumRoot_proof_irrel _ _ h1 h2

theorem eq_datumU1_or_eq_datumU2 (hd : 2 ≤ Module.finrank k E) (ι : E →ₗ[k] V)
    (π : V →ₗ[k] E) (h : ∀ t, π (ι t) = 0) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (U : Subgroup (SpecialLinearGroup k V))
    (hQ0 : datumQ0 ι π ≤ U) (hUQ : U ≤ datumQ ι π) (hne : U ≠ datumQ ι π)
    (hN : Subgroup.normalizer (datumRoot ι π h : Set (SpecialLinearGroup k V)) ≤
      Subgroup.normalizer (U : Set (SpecialLinearGroup k V)))
    (hnc : ¬ datumQ ι π ≤ Subgroup.centralizer (U : Set (SpecialLinearGroup k V))) :
    U = datumU1 ι ∨ U = datumU2 π := by
  classical
  haveI : Module.Finite k E := by
    rw [Module.finite_def, Submodule.fg_def]
    exact ⟨Set.univ, Set.finite_univ, Submodule.span_univ⟩
  obtain ⟨X', hX'AC, hX'Mod, hX'Fin, L, hLι, hLπ⟩ := exists_datumLin ι π h hι hπ
  letI : AddCommGroup X' := hX'AC
  letI : Module k X' := hX'Mod
  letI : Module.Finite k X' := hX'Fin
  let T : SpecialLinearGroup k V ≃* SpecialLinearGroup k (DSpace E X') :=
    SpecialLinearGroup.congr_linearEquiv L
  have hιL : L.toLinearMap ∘ₗ ι = stdIota k E X' := by
    apply LinearMap.ext
    intro t
    rw [stdIota_apply]
    exact hLι t
  have hπL : π ∘ₗ L.symm.toLinearMap = stdPi k E X' := by
    apply LinearMap.ext
    intro v
    show π (L.symm v) = v.2.2
    have hv := (hLπ (L.symm v)).symm
    simpa [LinearEquiv.apply_symm_apply] using hv
  have h' : ∀ t, (π ∘ₗ L.symm.toLinearMap) ((L.toLinearMap ∘ₗ ι) t) = 0 := by
    intro t
    show π (L.symm (L (ι t))) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact h t
  have hQ0map : (datumQ0 ι π).map T.toMonoidHom =
      datumQ0 (stdIota k E X') (stdPi k E X') := by
    rw [map_datumQ0_congr L ι π, hιL, hπL]
  have hQmap : (datumQ ι π).map T.toMonoidHom = QK k E X' := by
    rw [map_datumQ_congr L ι π, hιL, hπL, datumQ_std]
  have hroot : (datumRoot ι π h).map T.toMonoidHom = rootSL k E X' := by
    rw [map_datumRoot_congr L ι π h h']
    exact (datumRoot_congr h' (fun t => stdPi_stdIota t) hιL hπL).trans
      (datumRoot_std (fun t => stdPi_stdIota t))
  have hQ0' : datumQ0 (stdIota k E X') (stdPi k E X') ≤ U.map T.toMonoidHom := by
    rw [← hQ0map]
    exact Subgroup.map_mono hQ0
  have hUQ' : U.map T.toMonoidHom ≤ QK k E X' := by
    rw [← hQmap]
    exact Subgroup.map_mono hUQ
  have hne' : U.map T.toMonoidHom ≠ QK k E X' := by
    intro hc
    exact hne (Subgroup.map_injective T.injective (hc.trans hQmap.symm))
  have hNroot : (Subgroup.normalizer (datumRoot ι π h : Set (SpecialLinearGroup k V))).map
        T.toMonoidHom =
      Subgroup.normalizer (rootSL k E X' : Set (SpecialLinearGroup k (DSpace E X'))) := by
    rw [Subgroup.map_equiv_normalizer_eq, hroot]
  have hNU : (Subgroup.normalizer (U : Set (SpecialLinearGroup k V))).map T.toMonoidHom =
      Subgroup.normalizer (U.map T.toMonoidHom :
        Set (SpecialLinearGroup k (DSpace E X'))) := by
    rw [Subgroup.map_equiv_normalizer_eq]
  have hN' : Subgroup.normalizer (rootSL k E X' :
        Set (SpecialLinearGroup k (DSpace E X'))) ≤
      Subgroup.normalizer (U.map T.toMonoidHom :
        Set (SpecialLinearGroup k (DSpace E X'))) := by
    rw [← hNroot, ← hNU]
    exact Subgroup.map_mono hN
  have hnc' : ¬ QK k E X' ≤ Subgroup.centralizer
      (U.map T.toMonoidHom : Set (SpecialLinearGroup k (DSpace E X'))) := by
    intro hc
    apply hnc
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hq' : T q ∈ QK k E X' := by
      rw [← hQmap]
      exact Subgroup.mem_map_of_mem T.toMonoidHom hq
    have hu' : T u ∈ U.map T.toMonoidHom := Subgroup.mem_map_of_mem T.toMonoidHom hu
    have hcomm : T u * T q = T q * T u :=
      (Subgroup.mem_centralizer_iff.mp (hc hq')) (T u) hu'
    apply T.injective
    rw [map_mul, map_mul]
    exact hcomm
  rcases eq_datumU1_or_eq_datumU2_std hd (U.map T.toMonoidHom) hQ0' hUQ' hne' hN' hnc' with
    hcase | hcase
  · left
    have h1 : (datumU1 ι).map T.toMonoidHom = datumU1 (stdIota k E X') := by
      rw [map_datumU1_congr L ι, hιL]
    exact (Subgroup.map_injective T.injective (h1.trans hcase.symm)).symm
  · right
    have h2 : (datumU2 π).map T.toMonoidHom = datumU2 (stdPi k E X') := by
      rw [map_datumU2_congr L π, hπL]
    exact (Subgroup.map_injective T.injective (h2.trans hcase.symm)).symm

end CFSG.LinearAlgebra.RootGroupSL
