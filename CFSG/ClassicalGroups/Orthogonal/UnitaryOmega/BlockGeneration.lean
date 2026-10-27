module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportCharts
import CFSG.ClassicalInvolution.Phan.PhanDn.NormFormType

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem finrank_coordAnchor_refl (n : ℕ) :
    Module.finrank F (coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K)))) = 2 := by
  have hdim : Module.finrank F (coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K)))) =
      Module.finrank F (F × F) := by
    dsimp only [coordAnchor]
    exact LinearMap.finrank_range_of_inj LinearMap.inl_injective
  rw [hdim, Module.finrank_prod, Module.finrank_self]

private theorem finrank_coordPlane_refl (E : QuadExt F K (unitaryInvolution K 2 f))
    (n : ℕ) (i : Fin n) :
    Module.finrank F (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i) = 2 := by
  have hdim : Module.finrank F (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i) =
      Module.finrank F K := by
    let L : K →ₗ[F] (Fin n → K) := LinearMap.single F (fun _ => K) i
    have hL : Function.Injective L := by
      intro x y hxy
      have h := congrFun hxy i
      simpa [L] using h
    have hinj : Function.Injective
        ((LinearMap.inr F (F × F) (Fin n → K)).comp L) :=
      LinearMap.inr_injective.comp hL
    dsimp only [coordPlane]
    exact LinearMap.finrank_range_of_inj hinj
  rw [hdim, E.finrank_eq]

private theorem supportedDerived_coordSupport_le (n : ℕ) (S : Finset (Fin n)) :
    supportedDerived (normHypForm E n)
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S) ≤ normOmega E n := by
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  exact supportedDerived_le_orthDerived_of_regular
    (coordSupport_nondegenerate (ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)))
      (hψ := normHypForm_apply_coord E n)
      (hQ := normHypForm_polarBilin_nondegenerate E n)
      (hQE := normQuad_polarBilin_nondegenerate E) S)

theorem normBlock_eq_iSup_pairs (n : ℕ) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    normBlock E n S =
      ⨆ P : CFSG.Permutation.ProperSupportMaps.PairBelow S, normBlock E n (P : Finset (Fin n)) := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have hpairGen : supportedDerived (normHypForm E n)
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S) =
      ⨆ P : CFSG.Permutation.ProperSupportMaps.PairBelow S,
        supportedDerived (normHypForm E n)
          (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
            (P : Finset (Fin n))) := by
    simpa only [coordSupport] using
      supportedDerived_anchor_finset_sup_eq_iSup_pair (K := F) (V := (F × F) × (Fin n → K))
        (Q := normHypForm E n) (I := Fin n)
        (U := coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))))
        (W := coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K))))
        (hWreg := coordAnchor_nondegenerate
          (ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)))
          (hψ := normHypForm_apply_coord E n)
          (hQ := normHypForm_polarBilin_nondegenerate E n)
          (hQE := normQuad_polarBilin_nondegenerate E))
        (hWdim := finrank_coordAnchor_refl (F := F) (K := K) n)
        (hWU := fun i w hw u hu =>
          polar_coordAnchor_plane (ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)))
            (normHypForm_apply_coord E n) hw hu)
        (hUreg := fun i => nondegenerate_polarBilin_restrict
          (coordPlane_polarNondegOn (ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)))
            (normHypForm_apply_coord E n) (normQuad_polarBilin_nondegenerate E) i))
        (hUdim := fun i => finrank_coordPlane_refl E n i)
        (hUorth := fun i j hij u hu v hv =>
          polar_coordPlane_plane (ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)))
            (normHypForm_apply_coord E n) hij hu hv)
        S hS
  apply Subgroup.map_injective (f := (normOmega E n).subtype) (normOmega E n).subtype_injective
  calc
    (normBlock E n S).map (normOmega E n).subtype =
        supportedDerived (normHypForm E n)
          (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S) := by
      rw [normBlock, Subgroup.map_subgroupOf_eq_of_le (supportedDerived_coordSupport_le E n S)]
    _ = ⨆ P : CFSG.Permutation.ProperSupportMaps.PairBelow S,
          supportedDerived (normHypForm E n)
            (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
              (P : Finset (Fin n))) := hpairGen
    _ = (⨆ P : CFSG.Permutation.ProperSupportMaps.PairBelow S,
          normBlock E n (P : Finset (Fin n))).map (normOmega E n).subtype := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun P => ?_
      rw [normBlock, Subgroup.map_subgroupOf_eq_of_le
        (supportedDerived_coordSupport_le E n (P : Finset (Fin n)))]
private theorem coordAnchor_refl_eq_span_hypPair (n : ℕ) :
    coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K))) =
      Submodule.span F
        {(((1, 0), 0) : (F × F) × (Fin n → K)),
          (((0, 1), 0) : (F × F) × (Fin n → K))} := by
  have hrange : coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K))) =
      LinearMap.range (LinearMap.inl F (F × F) (Fin n → K)) := by
    simp [coordAnchor]
  rw [hrange]
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    rw [Submodule.mem_span_pair]
    refine ⟨r.1, r.2, ?_⟩
    ext <;> simp
  · intro hv
    rw [Submodule.mem_span_pair] at hv
    obtain ⟨a, b, rfl⟩ := hv
    exact ⟨(a, b), by ext <;> simp⟩

private theorem normHypForm_coordPlane_single
    (E : QuadExt F K (unitaryInvolution K 2 f)) (n : ℕ) (i : Fin n) (x : K) :
    normHypForm E n (((0, 0), Pi.single i x) : (F × F) × (Fin n → K)) =
      normQuad E x := by
  rw [normHypForm_apply_coord]
  have hsum : (∑ j : Fin n, normQuad E ((Pi.single i x : Fin n → K) j)) =
      normQuad E x := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp [hypPlane_apply, hsum]

private theorem normHypForm_coordPlane_anisotropic
    (E : QuadExt F K (unitaryInvolution K 2 f)) (n : ℕ) (i : Fin n) :
    ∀ u ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i,
      normHypForm E n u = 0 → u = 0 := by
  intro u hu hQu
  obtain ⟨x, rfl⟩ := mem_coordPlane.mp hu
  change normHypForm E n (((0, 0), Pi.single i x) : (F × F) × (Fin n → K)) = 0 at hQu
  have hQx : normQuad E x = 0 := by
    rwa [normHypForm_coordPlane_single E n i x] at hQu
  have hx : x = 0 := (normQuad_eq_zero_iff E).1 hQx
  subst hx
  simp

theorem iSup_singleton_normBlock_eq_top
    (E : QuadExt F K (unitaryInvolution K 2 f)) {n : ℕ} (hn : 2 ≤ n) :
    (⨆ i : Fin n, normBlock E n {i}) = ⊤ := by
  classical
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let V := (F × F) × (Fin n → K)
  let Q : QuadraticForm F V := normHypForm E n
  let W : Submodule F V := coordAnchor (LinearEquiv.refl F V)
  let U : Fin n → Submodule F V := fun i => coordPlane (LinearEquiv.refl F V) i
  have hspanW : W = Submodule.span F
      {(hypPair (Qn E n)).e, (hypPair (Qn E n)).f} := by
    rw [show (hypPair (Qn E n)).e = ((1, 0), 0) from hypPair_e (Qn E n),
      show (hypPair (Qn E n)).f = ((0, 1), 0) from hypPair_f (Qn E n)]
    exact coordAnchor_refl_eq_span_hypPair n
  have hUdim : ∀ i, Module.finrank F (U i) = 2 :=
    fun i => finrank_coordPlane_refl E n i
  have hψ : ∀ v : V, Q v =
      hypPlane F ((LinearEquiv.refl F V) v).1 +
        ∑ i, normQuad E (((LinearEquiv.refl F V) v).2 i) :=
    normHypForm_apply_coord E n
  have hUaniso : ∀ i, ∀ u ∈ U i, Q u = 0 → u = 0 :=
    fun i => normHypForm_coordPlane_anisotropic E n i
  have hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0 := by
    intro i w hw u hu
    exact polar_coordAnchor_plane (Q := Q) (QR := hypPlane F) (QE := normQuad E)
      (ψ := LinearEquiv.refl F V) hψ hw hu
  have hUU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0 := by
    intro i j hij u hu v hv
    exact polar_coordPlane_plane (Q := Q) (QR := hypPlane F) (QE := normQuad E)
      (ψ := LinearEquiv.refl F V) hψ hij hu hv
  have hspan : W ⊔ ⨆ i, U i = ⊤ := by
    simpa [W, U, coordActive] using
      coordAnchor_sup_coordActive (ψ := LinearEquiv.refl F V)
  have hgen := orthDerived_eq_iSup_supportedDerived_of_hypPair (Q := Q)
    (P := hypPair (Qn E n)) (W := W) (U := U) hn hspanW hUdim hUaniso hWU hUU hspan
  have hblock : ∀ i : Fin n, normBlock E n {i} =
      (supportedDerived Q (W ⊔ U i)).subgroupOf (normOmega E n) := by
    intro i
    simp only [normBlock, Q, W, U, V, coordSupport, Finset.sup_singleton]
  have hSle : ∀ i, supportedDerived Q (W ⊔ U i) ≤ normOmega E n := by
    intro i
    change supportedDerived Q (W ⊔ U i) ≤ orthDerived Q
    rw [hgen]
    exact le_iSup (fun i => supportedDerived Q (W ⊔ U i)) i
  have hmap : (⨆ i,
        (supportedDerived Q (W ⊔ U i)).subgroupOf (normOmega E n)).map
        (normOmega E n).subtype = normOmega E n := by
    rw [Subgroup.map_iSup]
    have hcongr : (⨆ i,
          ((supportedDerived Q (W ⊔ U i)).subgroupOf (normOmega E n)).map
            (normOmega E n).subtype) = ⨆ i, supportedDerived Q (W ⊔ U i) :=
      iSup_congr fun i => Subgroup.map_subgroupOf_eq_of_le (hSle i)
    rw [hcongr, ← hgen]
  have htop : (⨆ i,
        (supportedDerived Q (W ⊔ U i)).subgroupOf (normOmega E n)) = ⊤ := by
    apply Subgroup.map_injective (f := (normOmega E n).subtype)
      (normOmega E n).subtype_injective
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype]
  simpa only [hblock] using htop

theorem normBlock_singleton_sup_singleton
    (E : QuadExt F K (unitaryInvolution K 2 f)) {n : ℕ} (i j : Fin n) :
    normBlock E n {i} ⊔ normBlock E n {j} = normBlock E n {i, j} := by
  classical
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  by_cases hij : i = j
  · subst j
    simp
  let V := (F × F) × (Fin n → K)
  let Q : QuadraticForm F V := normHypForm E n
  let W : Submodule F V := coordAnchor (LinearEquiv.refl F V)
  let U : Fin n → Submodule F V := fun k => coordPlane (LinearEquiv.refl F V) k
  let A : Submodule F V := W ⊔ (U i ⊔ U j)
  let P0 : HypPair Q := hypPair (Qn E n)
  have hspanW : W = Submodule.span F {P0.e, P0.f} := by
    rw [show P0.e = ((1, 0), 0) from hypPair_e (Qn E n),
      show P0.f = ((0, 1), 0) from hypPair_f (Qn E n)]
    exact coordAnchor_refl_eq_span_hypPair n
  have hWA : W ≤ A := le_sup_left
  have hUA : ∀ k : Fin 2, U (if k = 0 then i else j) ≤ A := by
    intro k
    fin_cases k
    · exact (le_sup_left : U i ≤ U i ⊔ U j).trans le_sup_right
    · exact (le_sup_right : U j ≤ U i ⊔ U j).trans le_sup_right
  have heA : P0.e ∈ A := hWA (by
    rw [hspanW]
    exact Submodule.subset_span (by simp))
  have hfA : P0.f ∈ A := hWA (by
    rw [hspanW]
    exact Submodule.subset_span (by simp))
  let PA : HypPair (Q.comp A.subtype) :=
    { e := ⟨P0.e, heA⟩
      f := ⟨P0.f, hfA⟩
      Q_e := P0.Q_e
      Q_f := P0.Q_f
      polar_ef := by
        rw [polar_comp_subtype_eq]
        exact P0.polar_ef }
  let W' : Submodule F A := W.comap A.subtype
  let U' : Fin 2 → Submodule F A := fun k =>
    (U (if k = 0 then i else j)).comap A.subtype
  have hWspan' : W' = Submodule.span F {PA.e, PA.f} := by
    apply Submodule.map_injective_of_injective A.subtype_injective
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hWA, Submodule.map_span, Set.image_pair]
    simpa [PA, hspanW]
  have hsup_i : ({i} : Finset (Fin n)).sup
      (fun k => coordPlane (LinearEquiv.refl F V) k) = U i := by
    rw [Finset.sup_singleton]
  have hsup_j : ({j} : Finset (Fin n)).sup
      (fun k => coordPlane (LinearEquiv.refl F V) k) = U j := by
    rw [Finset.sup_singleton]
  have hsup_pair : ({i, j} : Finset (Fin n)).sup
      (fun k => coordPlane (LinearEquiv.refl F V) k) = U i ⊔ U j := by
    rw [Finset.sup_insert, Finset.sup_singleton]
  have hWreg : (polarBilin (Q.comp W.subtype)).Nondegenerate :=
    coordAnchor_nondegenerate (ψ := LinearEquiv.refl F V)
      (hψ := normHypForm_apply_coord E n)
      (hQ := normHypForm_polarBilin_nondegenerate E n)
      (hQE := normQuad_polarBilin_nondegenerate E)
  have hWU0 : ∀ k : Fin n, ∀ w ∈ W, ∀ u ∈ U k, polar Q w u = 0 := by
    intro k w hw u hu
    exact polar_coordAnchor_plane (ψ := LinearEquiv.refl F V)
      (normHypForm_apply_coord E n) hw hu
  have hUpoly : ∀ k : Fin n, PolarNondegOn Q (U k) := fun k =>
    coordPlane_polarNondegOn (ψ := LinearEquiv.refl F V)
      (normHypForm_apply_coord E n) (normQuad_polarBilin_nondegenerate E) k
  have hUorth0 : ∀ k l : Fin n, k ≠ l → ∀ u ∈ U k, ∀ v ∈ U l, polar Q u v = 0 := by
    intro k l hkl u hu v hv
    exact polar_coordPlane_plane (ψ := LinearEquiv.refl F V)
      (normHypForm_apply_coord E n) hkl hu hv
  have hAreg : (polarBilin (Q.comp A.subtype)).Nondegenerate := by
    have h := nondegenerate_finset_sup_of_sup
      (fun k => coordPlane (LinearEquiv.refl F V) k) W hWreg hWU0 hUpoly hUorth0
      ({i, j} : Finset (Fin n))
    rw [hsup_pair] at h
    exact h
  have hAireg : ∀ k : Fin 2,
      (polarBilin (Q.comp (W ⊔ U (if k = 0 then i else j)).subtype)).Nondegenerate := by
    intro k
    fin_cases k
    · have h := nondegenerate_finset_sup_of_sup
        (fun k => coordPlane (LinearEquiv.refl F V) k) W hWreg hWU0 hUpoly hUorth0
        ({i} : Finset (Fin n))
      rw [hsup_i] at h
      exact h
    · have h := nondegenerate_finset_sup_of_sup
        (fun k => coordPlane (LinearEquiv.refl F V) k) W hWreg hWU0 hUpoly hUorth0
        ({j} : Finset (Fin n))
      rw [hsup_j] at h
      exact h
  have hUdim : ∀ k : Fin 2, Module.finrank F (U' k) = 2 := by
    intro k
    exact (Submodule.comapSubtypeEquivOfLe (hUA k)).finrank_eq.trans
      (finrank_coordPlane_refl E n (if k = 0 then i else j))
  have hUaniso0 : ∀ k : Fin n, ∀ u ∈ U k, Q u = 0 → u = 0 :=
    fun k => normHypForm_coordPlane_anisotropic E n k
  have hUaniso : ∀ k : Fin 2, ∀ u ∈ U' k, (Q.comp A.subtype) u = 0 → u = 0 := by
    intro k u hu hQu
    have hzero : (u : V) = 0 :=
      hUaniso0 (if k = 0 then i else j) u hu hQu
    exact Subtype.ext hzero
  have hWU : ∀ k : Fin 2, ∀ w ∈ W', ∀ u ∈ U' k,
      polar (Q.comp A.subtype) w u = 0 := by
    intro k w hw u hu
    rw [polar_comp_subtype_eq]
    exact polar_coordAnchor_plane (Q := Q) (QR := hypPlane F) (QE := normQuad E)
      (ψ := LinearEquiv.refl F V) (normHypForm_apply_coord E n) hw hu
  have hUU : ∀ k l : Fin 2, k ≠ l → ∀ u ∈ U' k, ∀ v ∈ U' l,
      polar (Q.comp A.subtype) u v = 0 := by
    intro k l hkl u hu v hv
    rw [polar_comp_subtype_eq]
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · exact polar_coordPlane_plane (Q := Q) (QR := hypPlane F) (QE := normQuad E)
        (ψ := LinearEquiv.refl F V) (normHypForm_apply_coord E n) hij
        (by simpa [U'] using hu) (by simpa [U'] using hv)
    · exact polar_coordPlane_plane (Q := Q) (QR := hypPlane F) (QE := normQuad E)
        (ψ := LinearEquiv.refl F V) (normHypForm_apply_coord E n) (Ne.symm hij)
        (by simpa [U'] using hu) (by simpa [U'] using hv)
    · exact absurd rfl hkl
  have hmapW : W'.map A.subtype = W := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hWA]
  have hmapU : ∀ k : Fin 2, (U' k).map A.subtype =
      U (if k = 0 then i else j) := by
    intro k
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hUA k)]
  have hpair : (⨆ k : Fin 2, U (if k = 0 then i else j)) = U i ⊔ U j := by
    have hsup : (Finset.univ : Finset (Fin 2)).sup
        (fun k => U (if k = 0 then i else j)) =
        ⨆ k : Fin 2, U (if k = 0 then i else j) := by
      rw [Finset.sup_eq_iSup]
      simp
    rw [← hsup, show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]
    simp
  have hspan : W' ⊔ ⨆ k : Fin 2, U' k = ⊤ := by
    apply Submodule.map_injective_of_injective A.subtype_injective
    rw [Submodule.map_sup, hmapW, Submodule.map_iSup, Submodule.map_top,
      Submodule.range_subtype]
    rw [show (⨆ k : Fin 2, (U' k).map A.subtype) = U i ⊔ U j from
      (iSup_congr hmapU).trans hpair]
  have hgen := orthDerived_eq_iSup_supportedDerived_of_hypPair
    (Q := Q.comp A.subtype) (P := PA) (W := W') (U := U') (m := 2)
    (by norm_num) hWspan' hUdim hUaniso hWU hUU hspan
  let ext := orthExtend (isCompl_suppPerp (polarNondegOn_of_nondegenerate hAreg))
  have hmap := congrArg (Subgroup.map ext) hgen
  rw [map_orthDerived_orthExtend_eq_supportedDerived_of_regular hAreg,
    Subgroup.map_iSup] at hmap
  have hcomap : ∀ k : Fin 2,
      (W ⊔ U (if k = 0 then i else j)).comap A.subtype = W' ⊔ U' k := by
    intro k
    apply Submodule.map_injective_of_injective A.subtype_injective
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (sup_le hWA (hUA k)),
      Submodule.map_sup, hmapW, hmapU k]
  have hmapTerm : ∀ k : Fin 2,
      (supportedDerived (Q.comp A.subtype) (W' ⊔ U' k)).map ext =
        supportedDerived Q (W ⊔ U (if k = 0 then i else j)) := by
    intro k
    rw [← hcomap k]
    exact map_supportedDerived_comap_subtype_eq_supportedDerived
      (sup_le hWA (hUA k)) (hAireg k) hAreg
  have hsupp : supportedDerived Q A =
      supportedDerived Q (W ⊔ U i) ⊔ supportedDerived Q (W ⊔ U j) := by
    calc
      supportedDerived Q A = ⨆ k : Fin 2,
          (supportedDerived (Q.comp A.subtype) (W' ⊔ U' k)).map ext := hmap
      _ = ⨆ k : Fin 2,
          supportedDerived Q (W ⊔ U (if k = 0 then i else j)) := iSup_congr hmapTerm
      _ = supportedDerived Q (W ⊔ U i) ⊔ supportedDerived Q (W ⊔ U j) := by
        have hsup : (Finset.univ : Finset (Fin 2)).sup
            (fun k => supportedDerived Q (W ⊔ U (if k = 0 then i else j))) =
            ⨆ k : Fin 2,
              supportedDerived Q (W ⊔ U (if k = 0 then i else j)) := by
          rw [Finset.sup_eq_iSup]
          simp
        rw [← hsup, show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]
        simp
  have hle_i : supportedDerived Q (W ⊔ U i) ≤ normOmega E n := by
    change supportedDerived Q (W ⊔ U i) ≤ orthDerived Q
    simpa using supportedDerived_le_orthDerived_of_regular (hAireg 0)
  have hle_j : supportedDerived Q (W ⊔ U j) ≤ normOmega E n := by
    change supportedDerived Q (W ⊔ U j) ≤ orthDerived Q
    simpa using supportedDerived_le_orthDerived_of_regular (hAireg 1)
  have hle_A : supportedDerived Q A ≤ normOmega E n := by
    change supportedDerived Q A ≤ orthDerived Q
    exact supportedDerived_le_orthDerived_of_regular hAreg
  have hblock_i : normBlock E n {i} =
      (supportedDerived Q (W ⊔ U i)).subgroupOf (normOmega E n) := by
    simp only [normBlock, Q, W, U, V, coordSupport]
    rw [hsup_i]
  have hblock_j : normBlock E n {j} =
      (supportedDerived Q (W ⊔ U j)).subgroupOf (normOmega E n) := by
    simp only [normBlock, Q, W, U, V, coordSupport]
    rw [hsup_j]
  have hblock_pair : normBlock E n {i, j} =
      (supportedDerived Q A).subgroupOf (normOmega E n) := by
    have hA' : A = coordSupport (LinearEquiv.refl F V) ({i, j} : Finset (Fin n)) := by
      simp only [A, W, coordSupport, hsup_pair]
    rw [hA']
    rfl
  apply Subgroup.map_injective (f := (normOmega E n).subtype) (normOmega E n).subtype_injective
  rw [Subgroup.map_sup, hblock_i, hblock_j, hblock_pair,
    Subgroup.map_subgroupOf_eq_of_le hle_i, Subgroup.map_subgroupOf_eq_of_le hle_j,
    Subgroup.map_subgroupOf_eq_of_le hle_A]
  exact hsupp.symm

theorem normBlock_eq_iSup_singletons (n : ℕ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    normBlock E n S = ⨆ i ∈ S, normBlock E n {i} := by
  classical
  refine le_antisymm ?_ ?_
  · by_cases h2 : 2 ≤ S.card
    · rw [normBlock_eq_iSup_pairs E n S h2]
      refine iSup_le fun P => ?_
      obtain ⟨a, b, _hab, hPab⟩ := Finset.card_eq_two.mp P.2.2
      have ha : a ∈ S := P.2.1 (by rw [hPab]; simp)
      have hb : b ∈ S := P.2.1 (by rw [hPab]; simp)
      rw [hPab, ← normBlock_singleton_sup_singleton E a b]
      exact sup_le
        (le_iSup₂ (f := fun i (_ : i ∈ S) => normBlock E n {i}) a ha)
        (le_iSup₂ (f := fun i (_ : i ∈ S) => normBlock E n {i}) b hb)
    · have hpos : 0 < S.card := Finset.card_pos.mpr hS
      have h1 : S.card = 1 := by
        have hlt : S.card < 2 := not_le.mp h2
        omega
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
      rw [← Finset.sup_eq_iSup]
      simp
  · refine iSup_le fun i => iSup_le fun hi => ?_
    exact normBlock_mono E n (Finset.singleton_subset_iff.mpr hi)

section FieldTwoPair

variable {L : Type} [Field L] [Algebra (ZMod 2) L] [Finite L] [CharP L 2]

theorem normBlock_zero_sup_one_eq_top
    (E : QuadExt (ZMod 2) L (unitaryInvolution L 2 1)) :
    normBlock E 2 {0} ⊔ normBlock E 2 {1} = ⊤ := by
  have h := iSup_singleton_normBlock_eq_top (F := ZMod 2) (K := L) (f := 1) E
    (n := 2) (by norm_num)
  have hpair : (⨆ i : Fin 2, normBlock E 2 {i}) =
      normBlock E 2 {0} ⊔ normBlock E 2 {1} := by
    have hsup : (Finset.univ : Finset (Fin 2)).sup
        (fun i => normBlock E 2 {i}) = ⨆ i : Fin 2, normBlock E 2 {i} := by
      rw [Finset.sup_eq_iSup]
      simp
    rw [← hsup]
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [huniv, Finset.sup_insert, Finset.sup_singleton]
  rwa [hpair] at h

end FieldTwoPair

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
