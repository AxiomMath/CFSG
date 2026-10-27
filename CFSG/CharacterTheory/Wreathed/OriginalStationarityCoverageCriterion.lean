module

public import CFSG.CharacterTheory.Wreathed.OriginalSylowCentralizerCoverage
public import CFSG.CharacterTheory.Wreathed.OriginalNonstationaryWreathAction

public noncomputable section
namespace CFSG.Wreathed.OriginalStationarityCoverageCriterion
open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Wreathed.OriginalSylowCentralizerCoverage
open CFSG.Wreathed.OriginalNonstationaryWreathAction
open CFSG.Wreathed.OriginalCoveringSylowNormalizer
open scoped Classical Pointwise
universe u v

theorem cyclic_Sylow_two_oddCore_factorization {X : Type u} [Group X] [Finite X]
    (T : Sylow 2 X) (hT : IsCyclic (T : Subgroup X)) :
    CFSG.oddCore X ⊔ (T : Subgroup X) = ⊤ := by
  by_cases heven : Even (Nat.card X)
  · obtain ⟨D, hDchar, hDodd, hDT, hDmem⟩ :=
      CFSG.TwoRankLowerBound.Helpers.exists_characteristic_odd_complement_of_cyclic_sylow_two
        T hT heven
    let : D.Characteristic := hDchar
    have hDle : D ≤ CFSG.oddCore X := le_sSup ⟨inferInstance, hDodd⟩
    have hcorele : CFSG.oddCore X ≤ D := by
      intro d hd
      exact (hDmem d).mpr ((CFSG.ComponentClassification.OddCore.odd_card X).of_dvd_nat
        ((CFSG.oddCore X).orderOf_dvd_natCard hd))
    rw [le_antisymm hcorele hDle]
    exact hDT.sup_eq_top
  · have hodd : Odd (Nat.card X) := Nat.not_even_iff_odd.mp heven
    have hcore : CFSG.oddCore X = ⊤ := by
      apply top_le_iff.mp
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      simpa only [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toEquiv]
        using hodd
    rw [hcore, top_sup_eq]


theorem core_Sylow_centralizer_absorption {X : Type u} [Group X] [Finite X]
    {ell : ℕ} (hell : ell.Prime) (Q : Sylow ell (CFSG.oddCore X))
    (T : Sylow 2 X)
    (hTQ : (T : Subgroup X) ≤ Subgroup.normalizer
      (((Q : Subgroup (CFSG.oddCore X)).map (CFSG.oddCore X).subtype) : Set X))
    (hcyclic : IsCyclic ((Subgroup.centralizer
      (((Q : Subgroup (CFSG.oddCore X)).map (CFSG.oddCore X).subtype) : Set X)).subgroupOf
        (T : Subgroup X))) :
    Subgroup.centralizer
      (((Q : Subgroup (CFSG.oddCore X)).map (CFSG.oddCore X).subtype) : Set X) ≤
        CFSG.oddCore X ⊔ (T : Subgroup X) ⊓ Subgroup.centralizer
          (((Q : Subgroup (CFSG.oddCore X)).map (CFSG.oddCore X).subtype) : Set X) := by
  let A := (Q : Subgroup (CFSG.oddCore X)).map (CFSG.oddCore X).subtype
  let B := Subgroup.normalizer (A : Set X)
  let C := Subgroup.centralizer (A : Set X)
  let Cb := C.subgroupOf B
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Cb.Normal := inferInstance
  let Tb : Sylow 2 B := T.subtype hTQ
  obtain ⟨U, hU⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection
    2 Cb Tb
  let Dc := CFSG.oddCore Cb
  let : Dc.Characteristic := CFSG.ComponentClassification.OddCore.characteristic Cb
  let Db := Dc.map Cb.subtype
  let : Db.Normal := inferInstance
  let D := Db.map B.subtype
  have hDB : D ≤ B := Subgroup.map_subtype_le _
  have hDn : (D.subgroupOf B).Normal := by
    dsimp only [D, Subgroup.subgroupOf]
    rw [Subgroup.comap_map_eq_self_of_injective B.subtype_injective]
    infer_instance
  have hDodd : Odd (Nat.card D) := by
    rw [Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.card_map_of_injective Cb.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card Cb
  have hDcore : D ≤ CFSG.oddCore X :=
    normal_odd_normalizer_subgroup_le_oddCore hell Q D hDB hDn hDodd
  have hUmap : ((U : Subgroup Cb).map Cb.subtype).map B.subtype =
      (T : Subgroup X) ⊓ C := by
    rw [hU, Subgroup.subgroupOf_map_subtype, Subgroup.map_inf _ _ _ B.subtype_injective,
      Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hTQ,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.centralizer_le_normalizer _)]
  have hUc : IsCyclic (U : Subgroup Cb) := by
    have hUmem (g : U) : (B.subtype.comp Cb.subtype) g ∈ (T : Subgroup X) ⊓ C := by
      rw [← hUmap, Subgroup.map_map]
      exact Subgroup.mem_map_of_mem _ g.property
    let f : (U : Subgroup Cb) →* (C.subgroupOf (T : Subgroup X)) :=
      { toFun := fun g => ⟨⟨(B.subtype.comp Cb.subtype) g, (hUmem g).1⟩, (hUmem g).2⟩
        map_one' := by apply Subtype.ext; apply Subtype.ext; rfl
        map_mul' := by intro a b; apply Subtype.ext; apply Subtype.ext; rfl }
    let : IsCyclic (C.subgroupOf (T : Subgroup X)) := hcyclic
    apply isCyclic_of_injective (f := f)
    intro a b h
    apply (B.subtype_injective.comp Cb.subtype_injective).comp
      (U : Subgroup Cb).subtype_injective
    exact congrArg (fun g : C.subgroupOf (T : Subgroup X) => ((g : T) : X)) h
  have hfactor := congrArg (fun H : Subgroup Cb => (H.map Cb.subtype).map B.subtype)
    (cyclic_Sylow_two_oddCore_factorization U hUc)
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.centralizer_le_normalizer _), hUmap] at hfactor
  change D ⊔ (T : Subgroup X) ⊓ C = C at hfactor
  change C ≤ _
  rw [← hfactor]
  exact sup_le_sup hDcore le_rfl

theorem map_centralizer_of_equiv {X : Type u} {Y : Type v} [Group X] [Group Y]
    (f : X ≃* Y) (A : Subgroup X) :
    (Subgroup.centralizer (A : Set X)).map f.toMonoidHom =
      Subgroup.centralizer ((A.map f.toMonoidHom) : Set Y) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image (A : Set X) f.toMonoidHom
  · intro g hg
    refine Subgroup.mem_map.mpr ⟨f.symm g, ?_, f.apply_symm_apply g⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using
      Subgroup.mem_centralizer_iff.mp hg (f a) (Subgroup.mem_map_of_mem _ ha)

theorem ambientSylow_conjugation {X : Type u} [Group X] {ell : ℕ}
    (N : Subgroup X) (r : CFSG.oddCore N) (P : Sylow ell (CFSG.oddCore N)) :
    ambientSylow N (r • P) = (ambientSylow N P).map
      (MulAut.conj (((r : N) : X))).toMonoidHom := by
  have hconj : ((r • P : Sylow ell (CFSG.oddCore N)) : Subgroup (CFSG.oddCore N)) =
      (P : Subgroup (CFSG.oddCore N)).map (MulAut.conj r).toMonoidHom := rfl
  simp only [ambientSylow, hconj, Subgroup.map_map]
  congr 1

theorem map_kernel_conjugate {X : Type u} {Y : Type v} [Group X] [Group Y]
    (pi : X →* Y) {r : X} (hr : pi r = 1) (A : Subgroup X) :
    (A.map (MulAut.conj r).toMonoidHom).map pi = A.map pi := by
  rw [Subgroup.map_map]
  congr 1
  ext a
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    MulAut.conj_apply, map_mul, map_inv, hr, one_mul, inv_one, mul_one]

theorem kernel_conjugation_coverage_image {X : Type u} {Y : Type v}
    [Group X] [Group Y] (pi : X →* Y) {r : X} (hr : pi r = 1)
    (A : Subgroup X) (M : Subgroup Y) :
    ((Subgroup.centralizer ((A.map (MulAut.conj r).toMonoidHom) : Set X)) ⊓
      M.comap pi).map pi = (Subgroup.centralizer (A : Set X) ⊓ M.comap pi).map pi := by
  have hV : (M.comap pi).map (MulAut.conj r).toMonoidHom = M.comap pi := by
    ext g
    rw [Subgroup.mem_map_equiv]
    change pi ((MulAut.conj r).symm g) ∈ M ↔ pi g ∈ M
    simp only [MulAut.conj_symm_apply, map_mul, map_inv, hr, inv_one, one_mul, mul_one]
  calc
    _ = ((Subgroup.centralizer (A : Set X) ⊓ M.comap pi).map
        (MulAut.conj r).toMonoidHom).map pi := by
      rw [Subgroup.map_inf _ _ (MulAut.conj r).toMonoidHom (MulAut.conj r).injective,
        map_centralizer_of_equiv, hV]
    _ = _ := map_kernel_conjugate pi hr _


theorem ambientOddCore_map_equiv {X : Type u} {Y : Type v} [Group X] [Group Y]
    (f : X ≃* Y) (H : Subgroup X) :
    ambientOddCore (H.map (f : X →* Y)) = (ambientOddCore H).map (f : X →* Y) := by
  have hcore : (CFSG.oddCore H).map (f.subgroupMap H).toMonoidHom =
      CFSG.oddCore (H.map (f : X →* Y)) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant (f.subgroupMap H)
  simp only [ambientOddCore]
  rw [← hcore]
  simp only [Subgroup.map_map]
  congr 1

theorem actual_Sylow_map_equiv {X : Type u} {Y : Type v} [Group X] [Group Y]
    [Finite X] {ell : ℕ} (hell : ell.Prime) (f : X ≃* Y)
    (A O : Subgroup X)
    (h : ∃ P : Sylow ell O, (P : Subgroup O).map O.subtype = A) :
    ∃ P : Sylow ell (O.map (f : X →* Y)),
      (P : Subgroup (O.map (f : X →* Y))).map (O.map (f : X →* Y)).subtype =
        A.map (f : X →* Y) := by
  let : Fact ell.Prime := ⟨hell⟩
  obtain ⟨P, hP⟩ := h
  let E : O ≃* (O.map (f : X →* Y)) := f.subgroupMap O
  have hEsurj : Function.Surjective E.toMonoidHom := E.surjective
  let U : Sylow ell (O.map (f : X →* Y)) := P.mapSurjective (f := E.toMonoidHom) hEsurj
  refine ⟨U, ?_⟩
  have hU : (U : Subgroup (O.map (f : X →* Y))) =
      (P : Subgroup O).map (E : O →* (O.map (f : X →* Y))) :=
    Sylow.coe_mapSurjective hEsurj P
  rw [hU, ← hP]
  simp only [Subgroup.map_map]
  congr 1

theorem actual_Sylow_map_equiv_iff {X : Type u} {Y : Type v} [Group X] [Group Y]
    [Finite X] [Finite Y] {ell : ℕ} (hell : ell.Prime) (f : X ≃* Y)
    {A O : Subgroup X} :
    (∃ P : Sylow ell (O.map (f : X →* Y)),
      (P : Subgroup (O.map (f : X →* Y))).map (O.map (f : X →* Y)).subtype =
        A.map (f : X →* Y)) ↔
    ∃ P : Sylow ell O, (P : Subgroup O).map O.subtype = A := by
  constructor
  · intro h
    have h' := actual_Sylow_map_equiv hell f.symm (A.map (f : X →* Y))
      (O.map (f : X →* Y)) h
    have hO : (O.map (f : X →* Y)).map (f.symm : Y →* X) = O := by
      rw [Subgroup.map_map, MulEquiv.toMonoidHom_symm_comp_toMonoidHom, Subgroup.map_id]
    have hA : (A.map (f : X →* Y)).map (f.symm : Y →* X) = A := by
      rw [Subgroup.map_map, MulEquiv.toMonoidHom_symm_comp_toMonoidHom, Subgroup.map_id]
    rw [hO, hA] at h'
    exact h'
  · exact actual_Sylow_map_equiv hell f A O

theorem ambient_stationarity_conjugation_iff {X : Type u} [Group X] [Finite X]
    {ell : ℕ} (hell : ell.Prime) (r : X) {A : Subgroup X} :
    (∃ Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      ((A.map (MulAut.conj r : X →* X)) : Set X))),
      (Q : Subgroup _).map
        (ambientOddCore (Subgroup.normalizer
          ((A.map (MulAut.conj r : X →* X)) : Set X))).subtype =
            A.map (MulAut.conj r : X →* X)) ↔
    ∃ Q : Sylow ell (ambientOddCore (Subgroup.normalizer (A : Set X))),
      (Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer (A : Set X))).subtype = A := by
  have hnormalizer : (Subgroup.normalizer (A : Set X)).map (MulAut.conj r : X →* X) =
      Subgroup.normalizer ((A.map (MulAut.conj r : X →* X)) : Set X) :=
    Subgroup.map_equiv_normalizer_eq A (MulAut.conj r)
  rw [← hnormalizer, ambientOddCore_map_equiv]
  exact actual_Sylow_map_equiv_iff hell (MulAut.conj r)


@[expose] def OriginalStationarity {X : Type u} [Group X] {ell : ℕ}
    (N : Subgroup X) (P : Sylow ell (CFSG.oddCore N)) : Prop :=
  ∃ Q : Sylow ell (ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set X))),
    (Q : Subgroup _).map (ambientOddCore
      (Subgroup.normalizer (ambientSylow N P : Set X))).subtype = ambientSylow N P

@[expose] def OriginalCoverage {X : Type u} [Group X] {ell : ℕ}
    (n : ℕ) (S : Sylow 2 X) (e : S ≃* Wreath (2 ^ n))
    (P : Sylow ell (centralizerOddCore n S e)) : Prop :=
  (originalPrimeCentralizer n S e P ⊓
    (CFSG.layer (centralizerOddCoreQuotient n S e)).comap
      (centralizerOddCoreMap n S e)).map (centralizerOddCoreMap n S e) =
        CFSG.layer (centralizerOddCoreQuotient n S e)

theorem original_stationarity_R_conjugation_iff {X : Type u} [Group X] [Finite X]
    {ell : ℕ} (hell : ell.Prime) {N : Subgroup X} (r : CFSG.oddCore N)
    {P : Sylow ell (CFSG.oddCore N)} :
    OriginalStationarity N (r • P) ↔ OriginalStationarity N P := by
  unfold OriginalStationarity
  rw [ambientSylow_conjugation]
  exact ambient_stationarity_conjugation_iff hell (((r : N) : X))

theorem original_coverage_R_conjugation_iff {X : Type u} [Group X]
    {n : ℕ} {S : Sylow 2 X} {e : S ≃* Wreath (2 ^ n)} {ell : ℕ}
    (r : centralizerOddCore n S e) {P : Sylow ell (centralizerOddCore n S e)} :
    OriginalCoverage n S e (r • P) ↔ OriginalCoverage n S e P := by
  let N := involutionCentralizer n S e
  let R := centralizerOddCore n S e
  let pi := centralizerOddCoreMap n S e
  have hr : pi (r : N) = 1 := by
    exact (QuotientGroup.eq_one_iff (N := R) (r : N)).mpr r.property
  have hP : originalPrimeSubgroup n S e (r • P) =
      (originalPrimeSubgroup n S e P).map (MulAut.conj (r : N)).toMonoidHom := by
    have hconj : ((r • P : Sylow ell R) : Subgroup R) =
        (P : Subgroup R).map (MulAut.conj r).toMonoidHom := rfl
    simp only [originalPrimeSubgroup, hconj, Subgroup.map_map]
    congr 1
  unfold OriginalCoverage originalPrimeCentralizer
  rw [hP, kernel_conjugation_coverage_image pi hr]

theorem original_independent_witnesses_coincide {X : Type u} [Group X] [Finite X]
    (n : ℕ) (S : Sylow 2 X) (e : S ≃* Wreath (2 ^ n))
    {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (centralizerOddCore n S e))
    (hstationary : ∃ A : Sylow ell (centralizerOddCore n S e),
      OriginalStationarity (involutionCentralizer n S e) A)
    (hcovering : ∃ B : Sylow ell (centralizerOddCore n S e), OriginalCoverage n S e B) :
    OriginalStationarity (involutionCentralizer n S e) P ∧ OriginalCoverage n S e P := by
  let : Fact ell.Prime := ⟨hell⟩
  obtain ⟨A, hA⟩ := hstationary
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq (centralizerOddCore n S e) A P
  have hst : OriginalStationarity (involutionCentralizer n S e) P := by
    rw [← hr]
    exact (original_stationarity_R_conjugation_iff hell r (P := A)).mpr hA
  obtain ⟨B, hB⟩ := hcovering
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (centralizerOddCore n S e) B P
  have hcov : OriginalCoverage n S e P := by
    rw [← ht]
    exact (original_coverage_R_conjugation_iff t (P := B)).mpr hB
  exact ⟨hst, hcov⟩

variable {G : Type u} [Group G] [Finite G]

theorem ambient_core_Sylow_centralizer_absorption {ell : ℕ} (hell : ell.Prime)
    (K : Subgroup G) (S : Sylow 2 G) (hSK : (S : Subgroup G) ≤ K)
    (Q : Sylow ell (ambientOddCore K))
    (hSQ : (S : Subgroup G) ≤ Subgroup.normalizer
      (((Q : Subgroup (ambientOddCore K)).map (ambientOddCore K).subtype) : Set G))
    (hcyclic : IsCyclic ((Subgroup.centralizer
      (((Q : Subgroup (ambientOddCore K)).map (ambientOddCore K).subtype) : Set G)).subgroupOf
        (S : Subgroup G))) :
    K ⊓ Subgroup.centralizer
      (((Q : Subgroup (ambientOddCore K)).map (ambientOddCore K).subtype) : Set G) ≤
        ambientOddCore K ⊔ (S : Subgroup G) ⊓ Subgroup.centralizer
          (((Q : Subgroup (ambientOddCore K)).map (ambientOddCore K).subtype) : Set G) := by
  let : Fact ell.Prime := ⟨hell⟩
  let O := ambientOddCore K
  let F : CFSG.oddCore K ≃* O :=
    (CFSG.oddCore K).equivMapOfInjective K.subtype K.subtype_injective
  let f : O →* CFSG.oddCore K := F.symm.toMonoidHom
  have hf : Function.Surjective f := by
    intro a
    exact ⟨F a, F.symm_apply_apply a⟩
  let Q0 : Sylow ell (CFSG.oddCore K) := Q.mapSurjective (f := f) hf
  let A := (Q0 : Subgroup (CFSG.oddCore K)).map (CFSG.oddCore K).subtype
  let B := (Q : Subgroup O).map O.subtype
  have hcomp : K.subtype.comp ((CFSG.oddCore K).subtype.comp f) = O.subtype := by
    ext o
    exact congrArg (fun z : O => (z : G)) (F.apply_symm_apply o)
  have hAB : A.map K.subtype = B := by
    dsimp only [A, Q0]
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map,
      MonoidHom.comp_assoc, hcomp]
  let C := Subgroup.centralizer (A : Set K)
  have hC : (Subgroup.centralizer (B : Set G)).subgroupOf K = C := by
    rw [← hAB]
    exact centralizer_map_subtype K A
  let T := S.subtype hSK
  have hT : (T : Subgroup K).map K.subtype = (S : Subgroup G) := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSK]
  have hTQ : (T : Subgroup K) ≤ Subgroup.normalizer (A : Set K) := by
    have hn : (Subgroup.normalizer (B : Set G)).comap K.subtype =
        Subgroup.normalizer (A : Set K) := by
      rw [← hAB, Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range K.subtype A),
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    rw [← hn]
    intro t ht
    exact hSQ (hT ▸ Subgroup.mem_map_of_mem K.subtype ht)
  have hTcyc : IsCyclic (C.subgroupOf (T : Subgroup K)) := by
    let g : C.subgroupOf (T : Subgroup K) →*
        (Subgroup.centralizer (B : Set G)).subgroupOf (S : Subgroup G) :=
      { toFun := fun t => ⟨⟨(((t : T) : K) : G),
          hT ▸ Subgroup.mem_map_of_mem K.subtype (t : T).property⟩,
          by
            change (((t : T) : K) : G) ∈ Subgroup.centralizer (B : Set G)
            have ht : ((t : T) : K) ∈ (Subgroup.centralizer (B : Set G)).subgroupOf K := by
              rw [hC]
              exact t.property
            exact ht⟩
        map_one' := by apply Subtype.ext; apply Subtype.ext; rfl
        map_mul' := by intro a b; apply Subtype.ext; apply Subtype.ext; rfl }
    let : IsCyclic ((Subgroup.centralizer (B : Set G)).subgroupOf (S : Subgroup G)) := hcyclic
    apply isCyclic_of_injective g
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    apply K.subtype_injective
    exact congrArg (fun t : (Subgroup.centralizer (B : Set G)).subgroupOf (S : Subgroup G) =>
      ((t : S) : G)) h
  have habs := core_Sylow_centralizer_absorption hell Q0 T hTQ hTcyc
  have hm := Subgroup.map_mono (f := K.subtype) habs
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ K.subtype_injective, hT] at hm
  have hCm : C.map K.subtype = K ⊓ Subgroup.centralizer (B : Set G) := by
    rw [← hC, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hCm] at hm
  change K ⊓ Subgroup.centralizer (B : Set G) ≤
    O ⊔ (S : Subgroup G) ⊓ (K ⊓ Subgroup.centralizer (B : Set G)) at hm
  simpa only [← inf_assoc, inf_eq_left.mpr hSK] using hm

theorem oddCore_join_cyclic_isSolvable (K A : Subgroup G) (hAK : A ≤ K)
    (hA : IsCyclic A) : Group.IsSolvable (ambientOddCore K ⊔ A : Subgroup G) := by
  let : IsCyclic A := hA
  let : CommGroup A := IsCyclic.commGroup
  exact CFSG.SignalizerFunctor.Helpers.solvable_sup_of_normalizing (ambientOddCore K) A
    (hAK.trans (ambientOddCore_normalized K))
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (ambientOddCore_odd K))
    (Group.isSolvable_of_comm (fun a b : A => mul_comm a b))


theorem original_stationarity_gives_core_Sylow_eq {ell : ℕ} (hell : ell.Prime)
    (N : Subgroup G) (P : Sylow ell (CFSG.oddCore N))
    (hP : OriginalStationarity N P)
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set G)))) :
    (Q : Subgroup _).map (ambientOddCore
      (Subgroup.normalizer (ambientSylow N P : Set G))).subtype = ambientSylow N P := by
  let : Fact ell.Prime := ⟨hell⟩
  obtain ⟨U, hU⟩ := hP
  let O := ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set G))
  have hcard : Nat.card ((Q : Subgroup O).map O.subtype) = Nat.card (ambientSylow N P) := by
    calc
      _ = Nat.card Q := Subgroup.card_map_of_injective O.subtype_injective
      _ = Nat.card U := Nat.card_congr (Sylow.equiv Q U).toEquiv
      _ = Nat.card ((U : Subgroup O).map O.subtype) :=
        (Subgroup.card_map_of_injective O.subtype_injective).symm
      _ = Nat.card (ambientSylow N P) := congrArg (fun D : Subgroup G => Nat.card D) hU
  exact (Subgroup.eq_of_le_of_card_ge (original_sylow_le_every_normalizer_core_sylow N P Q)
    (le_of_eq hcard)).symm

theorem original_failed_coverage_core_centralizer
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))))
    (hSQ : (S : Subgroup G) ≤ Subgroup.normalizer (((Q : Subgroup _).map
      (ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G))
    (hfailure : ¬ OriginalCoverage n S e P) :
    let N := involutionCentralizer n S e
    let A := ambientSylow N P
    let K := Subgroup.normalizer (A : Set G)
    let O := ambientOddCore K
    let B := (Q : Subgroup O).map O.subtype
    let Z := (Subgroup.center S).map (S : Subgroup G).subtype
    K ⊓ Subgroup.centralizer (B : Set G) ≤ O ⊔ Z ∧
      Group.IsSolvable (K ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) ∧
      (Subgroup.centralizer (B : Set G)).subgroupOf (S : Subgroup G) ≤ Subgroup.center S := by
  dsimp only
  let N := involutionCentralizer n S e
  let A := ambientSylow N P
  let K := Subgroup.normalizer (A : Set G)
  let O := ambientOddCore K
  let B := (Q : Subgroup O).map O.subtype
  let Z := (Subgroup.center S).map (S : Subgroup G).subtype
  have hPQ : A ≤ B := original_sylow_le_every_normalizer_core_sylow N P Q
  have hCQP : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.centralizer_le hPQ
  have hcov := original_Sylow_centralizer_coverage_equivalent_to_noncentral_wreath_action_kernel
    hnonab n hn S e hfour hell hdiv P
  have hCP : originalSylowCentralizer n S e P ≤ Subgroup.center S :=
    (hcov.2.2.2 hfailure).2.2.2.1
  have hCQ : (Subgroup.centralizer (B : Set G)).subgroupOf (S : Subgroup G) ≤
      Subgroup.center S := by
    rw [originalSylowCentralizer_eq_ambient n hn S e P] at hCP
    exact (Subgroup.comap_mono hCQP).trans hCP
  let : IsCyclic (Subgroup.center S) := original_Sylow_center_isCyclic n hn S e
  have hcyclic : IsCyclic ((Subgroup.centralizer (B : Set G)).subgroupOf (S : Subgroup G)) :=
    Subgroup.isCyclic_of_le hCQ
  have hCZ : (S : Subgroup G) ⊓ Subgroup.centralizer (B : Set G) ≤ Z := by
    have hm := Subgroup.map_mono (f := (S : Subgroup G).subtype) hCQ
    rw [Subgroup.subgroupOf_map_subtype, inf_comm] at hm
    exact hm
  have hconf : K ⊓ Subgroup.centralizer (B : Set G) ≤ O ⊔ Z :=
    (ambient_core_Sylow_centralizer_absorption hell K S hSP Q hSQ hcyclic).trans
      (sup_le_sup le_rfl hCZ)
  have hZK : Z ≤ K := (Subgroup.map_subtype_le _).trans hSP
  have hZcyc : IsCyclic Z := by
    exact isCyclic_of_surjective ((S : Subgroup G).subtype.subgroupMap (Subgroup.center S))
      ((S : Subgroup G).subtype.subgroupMap_surjective _)
  let : Group.IsSolvable (O ⊔ Z : Subgroup G) := oddCore_join_cyclic_isSolvable K Z hZK hZcyc
  exact ⟨hconf, Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hconf), hCQ⟩


theorem original_coverage_gives_normalizer_centralizer_nonsolvable
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hstationary : OriginalStationarity (involutionCentralizer n S e) P)
    (hcoverage : OriginalCoverage n S e P)
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G)))) :
    ¬ Group.IsSolvable (Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G) ⊓
        Subgroup.centralizer (((Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer
          (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G) :
            Subgroup G) := by
  let N := involutionCentralizer n S e
  let A := ambientSylow N P
  let K := Subgroup.normalizer (A : Set G)
  let C := originalPrimeCentralizer n S e P
  have hQ := original_stationarity_gives_core_Sylow_eq hell N P hstationary Q
  rw [hQ]
  have hCnonsolvable : ¬ Group.IsSolvable C :=
    (original_Sylow_centralizer_coverage_equivalent_to_noncentral_wreath_action_kernel
      hnonab n hn S e hfour hell hdiv P).2.1.mp hcoverage
  have hCmap : C.map N.subtype ≤ K ⊓ Subgroup.centralizer (A : Set G) := by
    have hCentralizer := Subgroup.map_centralizer_le_centralizer_image
      (originalPrimeSubgroup n S e P : Set N) N.subtype
    exact le_inf (hCentralizer.trans (Subgroup.centralizer_le_normalizer _)) hCentralizer
  let f : C →* ↥(K ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
    (N.subtype.comp C.subtype).codRestrict _ (fun c =>
      hCmap (Subgroup.mem_map_of_mem N.subtype c.property))
  have hf : Function.Injective f := by
    intro a b h
    apply C.subtype_injective
    apply N.subtype_injective
    exact congrArg (fun c : ↥(K ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) => (c : G)) h
  intro hsolvable
  let : Group.IsSolvable (K ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := hsolvable
  exact hCnonsolvable (Group.isSolvable_of_isSolvable_injective hf)

theorem original_failed_stationarity_or_coverage
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))))
    (hSQ : (S : Subgroup G) ≤ Subgroup.normalizer (((Q : Subgroup _).map
      (ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G))
    (hfailure : ¬ (OriginalStationarity (involutionCentralizer n S e) P ∧
      OriginalCoverage n S e P)) :
    let N := involutionCentralizer n S e
    let A := ambientSylow N P
    let K := Subgroup.normalizer (A : Set G)
    let O := ambientOddCore K
    let B := (Q : Subgroup O).map O.subtype
    let Z := (Subgroup.center S).map (S : Subgroup G).subtype
    K ⊓ Subgroup.centralizer (B : Set G) ≤ O ⊔ Z ∧
      Group.IsSolvable (K ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) := by
  dsimp only
  by_cases hstationary : OriginalStationarity (involutionCentralizer n S e) P
  · have hcov : ¬ OriginalCoverage n S e P := fun h => hfailure ⟨hstationary, h⟩
    have h := original_failed_coverage_core_centralizer hnonab n hn S e hfour hell hdiv P
      hSP Q hSQ hcov
    exact ⟨h.1, h.2.1⟩
  · have h := original_nonstationarity_forces_faithful_wreath_action_and_odd_core_centralizer
      n hn S e hell hdiv P hSP hstationary
    have hCO := (h.2.2.2 Q hSQ).2.2.2.1
    let : Group.IsSolvable (ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (ambientOddCore_odd _)
    exact ⟨hCO.trans le_sup_left, Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hCO)⟩


theorem original_stationarity_and_coverage_iff_nonsolvable_core_Sylow_centralizer
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    {P : Sylow ell (centralizerOddCore n S e)}
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))))
    (hSQ : (S : Subgroup G) ≤ Subgroup.normalizer (((Q : Subgroup _).map
      (ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G)) :
    (OriginalStationarity (involutionCentralizer n S e) P ∧ OriginalCoverage n S e P) ↔
      ¬ Group.IsSolvable (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G) ⊓
          Subgroup.centralizer (((Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer
            (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G) :
              Subgroup G) := by
  constructor
  · rintro ⟨hstationary, hcoverage⟩
    exact original_coverage_gives_normalizer_centralizer_nonsolvable
      hnonab n hn S e hfour hell hdiv P hstationary hcoverage Q
  · intro hnonsolvable
    by_contra hfailure
    exact hnonsolvable ((original_failed_stationarity_or_coverage
      hnonab n hn S e hfour hell hdiv P hSP Q hSQ hfailure).2)

theorem original_stationarity_and_coverage_equivalent_to_nonsolvable_Sylow_centralizer
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (involutionCentralizer n S e) P : Set G))))
    (hSQ : (S : Subgroup G) ≤ Subgroup.normalizer (((Q : Subgroup _).map
      (ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G)) :
    let N := involutionCentralizer n S e
    let A := ambientSylow N P
    let K := Subgroup.normalizer (A : Set G)
    let O := ambientOddCore K
    let B := (Q : Subgroup O).map O.subtype
    let C := K ⊓ Subgroup.centralizer (B : Set G)
    let Z := (Subgroup.center S).map (S : Subgroup G).subtype
    let combined := OriginalStationarity N P ∧ OriginalCoverage n S e P
    (∃ P0 : Sylow ell (centralizerOddCore n S e), (S : Subgroup G) ≤
      Subgroup.normalizer (ambientSylow N P0 : Set G)) ∧
    (∃ Q0 : Sylow ell O, A ≤ (Q0 : Subgroup O).map O.subtype ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (((Q0 : Subgroup O).map O.subtype) : Set G)) ∧
    A ≤ B ∧
    (combined ↔ ¬ Group.IsSolvable C) ∧
    (¬ combined → C ≤ O ⊔ Z ∧ Group.IsSolvable C) ∧
    (¬ OriginalStationarity N P → A < B ∧
      (Subgroup.centralizer (B : Set G)).subgroupOf (S : Subgroup G) = ⊥ ∧ C ≤ O) ∧
    (¬ OriginalCoverage n S e P → C ≤ O ⊔ Z ∧
      (Subgroup.centralizer (B : Set G)).subgroupOf (S : Subgroup G) ≤ Subgroup.center S) ∧
    (combined → B = A ∧
      (modelY S e).subgroupOf (S : Subgroup G) ≤ originalSylowCentralizer n S e P) := by
  dsimp only
  refine ⟨original_invariant_prime_Sylow_exists n hn S e hell,
    original_full_invariant_normalizer_core_Sylow hell _ P S hSP,
    original_sylow_le_every_normalizer_core_sylow _ P Q,
    original_stationarity_and_coverage_iff_nonsolvable_core_Sylow_centralizer
      hnonab hn hfour hell hdiv hSP Q hSQ,
    original_failed_stationarity_or_coverage hnonab n hn S e hfour hell hdiv P hSP Q hSQ,
    ?_, ?_, ?_⟩
  · intro hstationary
    have h := (original_nonstationarity_forces_faithful_wreath_action_and_odd_core_centralizer
      n hn S e hell hdiv P hSP hstationary).2.2.2 Q hSQ
    have hS := h.2.2.1
    have hSubgroup : (Subgroup.centralizer (((Q : Subgroup _).map (ambientOddCore
      (Subgroup.normalizer (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) :
        Set G)).subgroupOf (S : Subgroup G) = ⊥ := by
      ext s
      change (s : G) ∈ Subgroup.centralizer _ ↔ s = 1
      constructor
      · intro hs
        exact Subtype.ext (Subgroup.mem_bot.mp (hS ▸ ⟨s.property, hs⟩))
      · rintro rfl
        exact (Subgroup.centralizer _).one_mem
    exact ⟨h.1, hSubgroup, h.2.2.2.1⟩
  · intro hcoverage
    have h := original_failed_coverage_core_centralizer
      hnonab n hn S e hfour hell hdiv P hSP Q hSQ hcoverage
    exact ⟨h.1, h.2.2⟩
  · rintro ⟨hstationary, hcoverage⟩
    refine ⟨original_stationarity_gives_core_Sylow_eq hell _ P hstationary Q, ?_⟩
    exact ((original_Sylow_centralizer_coverage_equivalent_to_noncentral_wreath_action_kernel
      hnonab n hn S e hfour hell hdiv P).2.2.1 hSP).2.1.mp hcoverage


@[expose] def OriginalAllPrimeStationarity (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Prop :=
  ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
    ∃ P : Sylow ell (centralizerOddCore n S e),
      OriginalStationarity (involutionCentralizer n S e) P

@[expose] def OriginalAllPrimeCoverage (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Prop :=
  ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
    ∃ P : Sylow ell (centralizerOddCore n S e), OriginalCoverage n S e P

@[expose] def OriginalAllPrimeNonsolvableCentralizers (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Prop :=
  ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
    ∃ P : Sylow ell (centralizerOddCore n S e),
      (S : Subgroup G) ≤ Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G) ∧
      ∃ Q : Sylow ell (ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))),
        (S : Subgroup G) ≤ Subgroup.normalizer (((Q : Subgroup _).map
          (ambientOddCore (Subgroup.normalizer
            (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G) ∧
        ¬ Group.IsSolvable (Subgroup.normalizer
          (ambientSylow (involutionCentralizer n S e) P : Set G) ⊓
            Subgroup.centralizer (((Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer
              (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G) :
                Subgroup G)

theorem original_all_prime_stationarity_and_coverage_iff_nonsolvable_centralizers
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4))) :
    (OriginalAllPrimeStationarity n S e ∧ OriginalAllPrimeCoverage n S e) ↔
      OriginalAllPrimeNonsolvableCentralizers n S e := by
  constructor
  · rintro ⟨hstationary, hcoverage⟩ ell hell hdiv
    obtain ⟨P, hSP⟩ := original_invariant_prime_Sylow_exists n hn S e hell
    obtain ⟨Q, _, hSQ⟩ := original_full_invariant_normalizer_core_Sylow hell _ P S hSP
    have h := original_independent_witnesses_coincide n S e hell P
      (hstationary ell hell hdiv) (hcoverage ell hell hdiv)
    exact ⟨P, hSP, Q, hSQ,
      (original_stationarity_and_coverage_iff_nonsolvable_core_Sylow_centralizer
        hnonab hn hfour hell hdiv hSP Q hSQ).mp h⟩
  · intro hcentralizers
    constructor
    · intro ell hell hdiv
      obtain ⟨P, hSP, Q, hSQ, hC⟩ := hcentralizers ell hell hdiv
      exact ⟨P, ((original_stationarity_and_coverage_iff_nonsolvable_core_Sylow_centralizer
        hnonab hn hfour hell hdiv hSP Q hSQ).mpr hC).1⟩
    · intro ell hell hdiv
      obtain ⟨P, hSP, Q, hSQ, hC⟩ := hcentralizers ell hell hdiv
      exact ⟨P, ((original_stationarity_and_coverage_iff_nonsolvable_core_Sylow_centralizer
        hnonab hn hfour hell hdiv hSP Q hSQ).mpr hC).2⟩

omit [Finite G] in
theorem original_trivial_oddCore_all_prime_vacuity
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hR : centralizerOddCore n S e = ⊥) :
    OriginalAllPrimeStationarity n S e ∧ OriginalAllPrimeCoverage n S e ∧
      OriginalAllPrimeNonsolvableCentralizers n S e := by
  have hno : ∀ ell : ℕ, ell.Prime → ¬ ell ∣ Nat.card (centralizerOddCore n S e) := by
    intro ell hell hdiv
    have hcard : Nat.card (centralizerOddCore n S e) = 1 := by rw [hR]; simp
    exact hell.not_dvd_one (hcard ▸ hdiv)
  exact ⟨fun ell hell hdiv => (hno ell hell hdiv).elim,
    fun ell hell hdiv => (hno ell hell hdiv).elim,
    fun ell hell hdiv => (hno ell hell hdiv).elim⟩

end CFSG.Wreathed.OriginalStationarityCoverageCriterion
