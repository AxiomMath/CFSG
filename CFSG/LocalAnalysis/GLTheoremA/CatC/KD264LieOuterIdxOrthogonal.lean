module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterOrthogonal
public import CFSG.LieType.SeitzGeneration.OuterOrthThreeSubfield
public import CFSG.Adapters.CatalogueFieldBridges.Orthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open TauCeti CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne.KCOrthogonalD4
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ClassicalInvolution.Upgrade
open CFSG.Adapters.RankTwoModelTransports
open CFSG.ClassicalModels
open CFSG.RankThree.PartTwo.Census.Carrier
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux
open CFSG.HardMathSupport.Lang.Proving
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Adapters.CatalogueFieldBridges

theorem idxCoreAt_pomegaOdd_of_mem_image {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] [Finite G] (h : StatedClassicalModel G .POmegaOdd n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f)
    {a : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))}
    (haE : a ∈ matrixProjectiveImage (coordinateQuadOdd n K))
    (haD : a ∉ (linearConjugationHom (coordinateQuadOdd n K)).range)
    (hap : orderOf a = p)
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadOdd n K))) :
    IdxCoreAt p (.B n q) a := by
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_odd h K hK e
  have hd : 0 < 2 * n + 1 := by have := h.1.2.2.1; omega
  have hinj : Function.Injective (MulAut.conj :
      matrixProjectiveDerived (coordinateQuadOdd n K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))) :=
    conj_injective_matrixProjectiveDerived _ hd hnd hT
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd
    (Or.inl rfl) n ℓ f p h hp hp2 K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT'⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  obtain ⟨s, rfl⟩ := hpf
  rw [Nat.mul_div_cancel_left s hp.pos] at hcard hCM
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ s := by
    rw [hUr]; exact hcard
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hK' : Nat.card K = ℓ ^ (s * p) := by rw [mul_comm]; exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  let kk : Subfield K := semilinearFixedSubfield U.val.right
  have hcardk : Nat.card kk = ℓ ^ s := hcard'
  have hσkk : ∀ x, x ∈ kk ↔ U.val.right x = x := hσk
  obtain ⟨-, hconc⟩ :=
    CFSG.LieType.SeitzGeneration.orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd
      .POmegaOdd (Or.inl rfl) n ℓ s p hCM.1 hp hp2 hpℓ K kk hcardk hK' U.val.right hord' hσkk
  obtain ⟨⟨-, hJsimple, hJnab⟩, -, hfix, hJN, hJn, hquot, -, -, -, -⟩ := hconc
  clear hFFD
  have hg' : g' = fieldPair (coordinateQuadOdd n K) U.val.right
      (coordinateQuadOdd_fieldAut n U.val.right) :=
    Subtype.ext (SemidirectProduct.ext hg'l hg'r)
  have hδ : matrixProjectiveConjugationHom (coordinateQuadOdd n K) g' =
      fieldAutT (coordinateQuadOdd n K) U.val.right (coordinateQuadOdd_fieldAut n U.val.right) := by
    rw [hg']; rfl
  have hΘa : MulAut.congr Θ a = matrixProjectiveConjugationHom (coordinateQuadOdd n K) g' := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
    rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]
  let NN : Subgroup (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    subfieldFixedGroup kk (coordinateQuadOdd n kk) (coordinateQuadOdd n K)
  let JJ : Subgroup (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    subfieldDerivedImage kk (coordinateQuadOdd_isExtension kk n)
  have hN : ∀ t, matrixProjectiveConjugationHom (coordinateQuadOdd n K) g' t = t ↔ t ∈ NN := by
    intro t
    rw [hδ]
    exact hfix t
  have hJN' : JJ ≤ NN := hJN
  have hJn' : (JJ.subgroupOf NN).Normal := hJn
  have hI : IsSimpleGroup ↥JJ := hJsimple
  haveI := hI
  have hJq : CFSG.IsQuasisimple JJ :=
    isQuasisimple_of_simple_nonabelian (fun hc => by
      obtain ⟨x, y, hxy⟩ := hJnab
      exact hxy (hc x y))
  have hap' : a ^ p = 1 := by rw [← hap]; exact pow_orderOf_eq_one a
  obtain ⟨y, hy, hy1, hyp, hcomm⟩ := exists_innerAut_orderOf_prime_commute hp hinj hap' hpdvd
  obtain ⟨c, hkfix, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj (δ := a) (x := a)
    (h := 1) (by group) hy hy1 hyp hcomm
  have hkδ : matrixProjectiveConjugationHom (coordinateQuadOdd n K) g' (Θ c) = Θ c := by
    have h1 : (MulAut.congr Θ a) (Θ c) = Θ (a c) := by simp [MulAut.congr_apply]
    rw [← hΘa, h1, hkfix]
  have hkN : Θ c ∈ NN := (hN (Θ c)).1 hkδ
  have hkcJ : Θ c ∈ JJ := by
    haveI : (JJ.subgroupOf NN).Normal := hJn'
    let z : ↥NN ⧸ JJ.subgroupOf NN :=
      QuotientGroup.mk' (JJ.subgroupOf NN) (⟨Θ c, hkN⟩ : ↥NN)
    have hz : z = QuotientGroup.mk (⟨Θ c, hkN⟩ : ↥NN) := rfl
    have hzp : z ^ p = 1 := by
      rw [hz, ← QuotientGroup.mk_pow]
      have hordN : orderOf (⟨Θ c, hkN⟩ : ↥NN) = p := by
        rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hkord]
      rw [← hordN]
      exact congrArg QuotientGroup.mk (pow_orderOf_eq_one _)
    obtain ⟨m, hm⟩ := hquot z
    have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have h2 : orderOf z ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    have hcop : Nat.Coprime p (2 ^ m) :=
      Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have h3 : orderOf z = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff, hz, QuotientGroup.eq_one_iff] at h3
    exact Subgroup.mem_subgroupOf.1 h3
  have hpJ' : p ∣ Nat.card ↥JJ := by
    have h1 : orderOf (⟨Θ c, hkcJ⟩ : ↥JJ) = p := by
      rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hkord]
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hpos : 0 < s := by have := hCM.1.2.1; omega
  let q₀ : TauCeti.PrimePower := ⟨ℓ, s, h.1.1, hpos⟩
  have hq₀ : q₀.card = ℓ ^ s := PrimePower.card_def q₀
  have hq0pow : q₀.card ^ p = q.card := by
    rw [hq₀, ← pow_mul, mul_comm s p, hq]
  have hn3 : 3 ≤ n := h.1.2.2.1
  have hℓ2 : ℓ ≠ 2 := h.1.2.2.2
  have hv₀ : (TauCeti.LieTypeIndex.B n q₀).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨le_trans (by norm_num) hn3, ?_⟩, ?_⟩
    · rintro ⟨h1, -⟩
      omega
    · rintro ⟨h1, -⟩
      omega
  have hcent : ↥JJ ⧸ Subgroup.center ↥JJ ≃* ↥JJ :=
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hJnab).2).trans
      QuotientGroup.quotientBot)
  have hSCsub : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadOdd n kk))
      .POmegaOdd n ℓ s :=
    ⟨hCM.1, kk, inferInstance, inferInstance, hcardk,
      ⟨(coordinateOddWitnessEquiv kk
        (MulEquiv.refl (StatedProj (StatedOmega (StatedQuadOdd n kk))))).symm⟩⟩
  obtain ⟨eM⟩ := exists_mulEquiv_catalogue_pomegaOdd h.1.1 hpos hv₀ hn3 hℓ2 hSCsub
  have hi : ∃ i : TauCeti.CFSGIndex, Nonempty (↥JJ ⧸ Subgroup.center ↥JJ ≃* i.Group) ∧
      subRelC p (.B n q) i := by
    refine ⟨.lie ⟨.B n q₀, hv₀⟩, ⟨hcent.trans
      ((inclEquiv kk (coordinateQuadOdd_isExtension kk n) hd).symm.trans eM)⟩, ?_⟩
    simp only [subRelC, subRel, sameShape, fieldSize]
    exact Or.inl ⟨trivial, hq0pow⟩
  exact idxCoreAt_of_mulEquiv Θ hΘa hN hJN' hJn' hJq hpJ' hi

theorem idxCoreAt_pomegaPlus_of_mem_image {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] [Finite G] (h : StatedClassicalModel G .POmegaPlus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f)
    {a : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (haE : a ∈ matrixProjectiveImage (coordinateQuadPlus n K))
    (haD : a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range)
    (hap : orderOf a = p)
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K))) :
    IdxCoreAt p (.D n q) a := by
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hn4 : 4 ≤ n := h.1.2.2
  have hd : 0 < 2 * n := by omega
  have hinj : Function.Injective (MulAut.conj :
      matrixProjectiveDerived (coordinateQuadPlus n K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))) :=
    conj_injective_matrixProjectiveDerived _ hd hnd hT
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p h hp hp2 K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT'⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  obtain ⟨s, rfl⟩ := hpf
  rw [Nat.mul_div_cancel_left s hp.pos] at hcard hCM
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ s := by
    rw [hUr]; exact hcard
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hK' : Nat.card K = ℓ ^ (s * p) := by rw [mul_comm]; exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  let kk : Subfield K := semilinearFixedSubfield U.val.right
  have hcardk : Nat.card kk = ℓ ^ s := hcard'
  have hσkk : ∀ x, x ∈ kk ↔ U.val.right x = x := hσk
  obtain ⟨-, hconc⟩ :=
    CFSG.LieType.SeitzGeneration.orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd
      .POmegaPlus (Or.inr (Or.inl rfl)) n ℓ s p hCM.1 hp hp2 hpℓ K kk hcardk hK'
        U.val.right hord' hσkk
  obtain ⟨⟨-, hJsimple, hJnab⟩, -, hfix, hJN, hJn, hquot, -, -, -, -⟩ := hconc
  clear hFFD
  have hg' : g' = fieldPair (coordinateQuadPlus n K) U.val.right
      (coordinateQuadPlus_fieldAut n U.val.right) :=
    Subtype.ext (SemidirectProduct.ext hg'l hg'r)
  have hδ : matrixProjectiveConjugationHom (coordinateQuadPlus n K) g' =
      fieldAutT (coordinateQuadPlus n K) U.val.right
        (coordinateQuadPlus_fieldAut n U.val.right) := by
    rw [hg']; rfl
  have hΘa : MulAut.congr Θ a = matrixProjectiveConjugationHom (coordinateQuadPlus n K) g' := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
    rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]
  let NN : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    subfieldFixedGroup kk (coordinateQuadPlus n kk) (coordinateQuadPlus n K)
  let JJ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    subfieldDerivedImage kk (coordinateQuadPlus_isExtension kk n)
  have hN : ∀ t, matrixProjectiveConjugationHom (coordinateQuadPlus n K) g' t = t ↔ t ∈ NN := by
    intro t
    rw [hδ]
    exact hfix t
  have hJN' : JJ ≤ NN := hJN
  have hJn' : (JJ.subgroupOf NN).Normal := hJn
  have hI : IsSimpleGroup ↥JJ := hJsimple
  haveI := hI
  have hJq : CFSG.IsQuasisimple JJ :=
    isQuasisimple_of_simple_nonabelian (fun hc => by
      obtain ⟨x, y, hxy⟩ := hJnab
      exact hxy (hc x y))
  have hap' : a ^ p = 1 := by rw [← hap]; exact pow_orderOf_eq_one a
  obtain ⟨y, hy, hy1, hyp, hcomm⟩ := exists_innerAut_orderOf_prime_commute hp hinj hap' hpdvd
  obtain ⟨c, hkfix, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj (δ := a) (x := a)
    (h := 1) (by group) hy hy1 hyp hcomm
  have hkδ : matrixProjectiveConjugationHom (coordinateQuadPlus n K) g' (Θ c) = Θ c := by
    have h1 : (MulAut.congr Θ a) (Θ c) = Θ (a c) := by simp [MulAut.congr_apply]
    rw [← hΘa, h1, hkfix]
  have hkN : Θ c ∈ NN := (hN (Θ c)).1 hkδ
  have hkcJ : Θ c ∈ JJ := by
    haveI : (JJ.subgroupOf NN).Normal := hJn'
    let z : ↥NN ⧸ JJ.subgroupOf NN :=
      QuotientGroup.mk' (JJ.subgroupOf NN) (⟨Θ c, hkN⟩ : ↥NN)
    have hz : z = QuotientGroup.mk (⟨Θ c, hkN⟩ : ↥NN) := rfl
    have hzp : z ^ p = 1 := by
      rw [hz, ← QuotientGroup.mk_pow]
      have hordN : orderOf (⟨Θ c, hkN⟩ : ↥NN) = p := by
        rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hkord]
      rw [← hordN]
      exact congrArg QuotientGroup.mk (pow_orderOf_eq_one _)
    obtain ⟨m, hm⟩ := hquot z
    have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have h2 : orderOf z ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    have hcop : Nat.Coprime p (2 ^ m) :=
      Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have h3 : orderOf z = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff, hz, QuotientGroup.eq_one_iff] at h3
    exact Subgroup.mem_subgroupOf.1 h3
  have hpJ' : p ∣ Nat.card ↥JJ := by
    have h1 : orderOf (⟨Θ c, hkcJ⟩ : ↥JJ) = p := by
      rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hkord]
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hpos : 0 < s := by have := hCM.1.2.1; omega
  let q₀ : TauCeti.PrimePower := ⟨ℓ, s, h.1.1, hpos⟩
  have hq₀ : q₀.card = ℓ ^ s := PrimePower.card_def q₀
  have hq0pow : q₀.card ^ p = q.card := by
    rw [hq₀, ← pow_mul, mul_comm s p, hq]
  have hv₀ : (TauCeti.LieTypeIndex.D n q₀).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_trans (by norm_num) hn4, not_false⟩
  have hcent : ↥JJ ⧸ Subgroup.center ↥JJ ≃* ↥JJ :=
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hJnab).2).trans
      QuotientGroup.quotientBot)
  have hSCsub : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n kk))
      .POmegaPlus n ℓ s :=
    ⟨hCM.1, kk, inferInstance, inferInstance, hcardk,
      ⟨(coordinatePlusWitnessEquiv kk
        (MulEquiv.refl (StatedProj (StatedOmega (StatedQuadPlus n kk))))).symm⟩⟩
  obtain ⟨eM⟩ := exists_mulEquiv_catalogue_pomegaPlus h.1.1 hpos hv₀ hn4 hSCsub
  have hi : ∃ i : TauCeti.CFSGIndex, Nonempty (↥JJ ⧸ Subgroup.center ↥JJ ≃* i.Group) ∧
      subRelC p (.D n q) i := by
    refine ⟨.lie ⟨.D n q₀, hv₀⟩, ⟨hcent.trans
      ((inclEquiv kk (coordinateQuadPlus_isExtension kk n) hd).symm.trans eM)⟩, ?_⟩
    simp only [subRelC, subRel, sameShape, fieldSize]
    exact Or.inl ⟨trivial, hq0pow⟩
  exact idxCoreAt_of_mulEquiv Θ hΘa hN hJN' hJn' hJq hpJ' hi

theorem idxCoreAt_pomegaMinus_of_mem_image {n ℓ f p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] {G : Type} [Group G] [Finite G]
    (h : StatedClassicalModel G .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f)
    {a : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))}
    (haE : a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn b c))
    (haD : a ∉ (linearConjugationHom (coordinateQuadMinus n K hn b c)).range)
    (hap : orderOf a = p)
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) :
    IdxCoreAt p (.twistedD n q) a := by
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hn4 : 4 ≤ n := h.1.2.2
  have hd : 0 < 2 * n := by omega
  have hinj : Function.Injective (MulAut.conj :
      matrixProjectiveDerived (coordinateQuadMinus n K hn b c) →*
        MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) :=
    conj_injective_matrixProjectiveDerived _ hd hnd hT
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p h hp hp2 hn K hK b c hirr e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT'⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  obtain ⟨s, rfl⟩ := hpf
  rw [Nat.mul_div_cancel_left s hp.pos] at hcard hCM
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ s := by
    rw [hUr]; exact hcard
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hK' : Nat.card K = ℓ ^ (s * p) := by rw [mul_comm]; exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  let kk : Subfield K := semilinearFixedSubfield U.val.right
  have hcardk : Nat.card kk = ℓ ^ s := hcard'
  have hσkk : ∀ x, x ∈ kk ↔ U.val.right x = x := hσk
  obtain ⟨-, hconc⟩ :=
    CFSG.LieType.SeitzGeneration.orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd
      .POmegaMinus (Or.inr (Or.inr rfl)) n ℓ s p hCM.1 hp hp2 hpℓ hn K kk hcardk hK'
        U.val.right hord' hσkk b' c' hirr'
  obtain ⟨⟨-, hJsimple, hJnab⟩, -, hfix, hJN, hJn, hquot, -, -, -, -⟩ := hconc
  clear hFFD
  have hg' : g' = fieldPair (coordinateQuadMinus n K hn (b' : K) (c' : K)) U.val.right
      (coordinateQuadMinus_fieldAut kk n hn hσkk b' c') :=
    Subtype.ext (SemidirectProduct.ext hg'l hg'r)
  have hδ : matrixProjectiveConjugationHom (coordinateQuadMinus n K hn (b' : K) (c' : K)) g' =
      fieldAutT (coordinateQuadMinus n K hn (b' : K) (c' : K)) U.val.right
        (coordinateQuadMinus_fieldAut kk n hn hσkk b' c') := by
    rw [hg']; rfl
  have hΘa : MulAut.congr Θ a =
      matrixProjectiveConjugationHom (coordinateQuadMinus n K hn (b' : K) (c' : K)) g' := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
    rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]
  let NN : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn (b' : K) (c' : K))) :=
    subfieldFixedGroup kk (coordinateQuadMinus n kk hn b' c')
      (coordinateQuadMinus n K hn (b' : K) (c' : K))
  let JJ : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn (b' : K) (c' : K))) :=
    subfieldDerivedImage kk (coordinateQuadMinus_isExtension kk n hn b' c')
  have hN : ∀ t, matrixProjectiveConjugationHom
      (coordinateQuadMinus n K hn (b' : K) (c' : K)) g' t = t ↔ t ∈ NN := by
    intro t
    rw [hδ]
    exact hfix t
  have hJN' : JJ ≤ NN := hJN
  have hJn' : (JJ.subgroupOf NN).Normal := hJn
  have hI : IsSimpleGroup ↥JJ := hJsimple
  haveI := hI
  have hJq : CFSG.IsQuasisimple JJ :=
    isQuasisimple_of_simple_nonabelian (fun hc => by
      obtain ⟨x, y, hxy⟩ := hJnab
      exact hxy (hc x y))
  have hap' : a ^ p = 1 := by rw [← hap]; exact pow_orderOf_eq_one a
  obtain ⟨y, hy, hy1, hyp, hcomm⟩ := exists_innerAut_orderOf_prime_commute hp hinj hap' hpdvd
  obtain ⟨c₀, hkfix, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj (δ := a) (x := a)
    (h := 1) (by group) hy hy1 hyp hcomm
  have hkδ : matrixProjectiveConjugationHom
      (coordinateQuadMinus n K hn (b' : K) (c' : K)) g' (Θ c₀) = Θ c₀ := by
    have h1 : (MulAut.congr Θ a) (Θ c₀) = Θ (a c₀) := by simp [MulAut.congr_apply]
    rw [← hΘa, h1, hkfix]
  have hkN : Θ c₀ ∈ NN := (hN (Θ c₀)).1 hkδ
  have hkcJ : Θ c₀ ∈ JJ := by
    haveI : (JJ.subgroupOf NN).Normal := hJn'
    let z : ↥NN ⧸ JJ.subgroupOf NN :=
      QuotientGroup.mk' (JJ.subgroupOf NN) (⟨Θ c₀, hkN⟩ : ↥NN)
    have hz : z = QuotientGroup.mk (⟨Θ c₀, hkN⟩ : ↥NN) := rfl
    have hzp : z ^ p = 1 := by
      rw [hz, ← QuotientGroup.mk_pow]
      have hordN : orderOf (⟨Θ c₀, hkN⟩ : ↥NN) = p := by
        rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hkord]
      rw [← hordN]
      exact congrArg QuotientGroup.mk (pow_orderOf_eq_one _)
    obtain ⟨m, hm⟩ := hquot z
    have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have h2 : orderOf z ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    have hcop : Nat.Coprime p (2 ^ m) :=
      Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have h3 : orderOf z = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff, hz, QuotientGroup.eq_one_iff] at h3
    exact Subgroup.mem_subgroupOf.1 h3
  have hpJ' : p ∣ Nat.card ↥JJ := by
    have h1 : orderOf (⟨Θ c₀, hkcJ⟩ : ↥JJ) = p := by
      rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hkord]
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hpos : 0 < s := by have := hCM.1.2.1; omega
  let q₀ : TauCeti.PrimePower := ⟨ℓ, s, h.1.1, hpos⟩
  have hq₀ : q₀.card = ℓ ^ s := PrimePower.card_def q₀
  have hq0pow : q₀.card ^ p = q.card := by
    rw [hq₀, ← pow_mul, mul_comm s p, hq]
  have hv₀ : (TauCeti.LieTypeIndex.twistedD n q₀).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_trans (by norm_num) hn4, not_false⟩
  have hcent : ↥JJ ⧸ Subgroup.center ↥JJ ≃* ↥JJ :=
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hJnab).2).trans
      QuotientGroup.quotientBot)
  have hSCsub : StatedClassicalModel
      (matrixProjectiveDerived (coordinateQuadMinus n kk hn b' c')) .POmegaMinus n ℓ s :=
    ⟨hCM.1, kk, inferInstance, inferInstance, hcardk, b', c', hirr',
      ⟨(coordinateMinusWitnessEquiv kk hn b' c'
        (MulEquiv.refl (StatedProj (StatedOmega (StatedQuadMinus n kk b' c'))))).symm⟩⟩
  obtain ⟨eM⟩ := exists_mulEquiv_catalogue_pomegaMinus (k := kk) hn (b := b') (c := c')
    hirr' h.1.1 hpos hv₀ hn4 hSCsub
  have hi : ∃ i : TauCeti.CFSGIndex, Nonempty (↥JJ ⧸ Subgroup.center ↥JJ ≃* i.Group) ∧
      subRelC p (.twistedD n q) i := by
    refine ⟨.lie ⟨.twistedD n q₀, hv₀⟩, ⟨hcent.trans
      ((inclEquiv kk (coordinateQuadMinus_isExtension kk n hn b' c') hd).symm.trans eM)⟩, ?_⟩
    simp only [subRelC, subRel, sameShape, fieldSize]
    exact Or.inl ⟨trivial, hq0pow⟩
  exact idxCoreAt_of_mulEquiv Θ hΘa hN hJN' hJn' hJq hpJ' hi

theorem idxCoreAt_pomegaOdd_of_outer {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] [Finite G] (h : StatedClassicalModel G .POmegaOdd n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f)
    {x : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))} (hxp : x ^ p = 1)
    (hxo : x ∉ innAutDerived (matrixProjectiveDerived (coordinateQuadOdd n K)))
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadOdd n K))) :
    IdxCoreAt p (.B n q) x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have haH : x ∉ inner (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    fun hmem => hxo (inner_le_innAutDerived _ hmem)
  obtain ⟨haE, haD⟩ := pomegaOdd_mem_image_not_linear h hp hp2 hpℓ hK e hxp haH
  have hx1 : x ≠ 1 := fun h1 => haH (h1 ▸ one_mem _)
  exact idxCoreAt_pomegaOdd_of_mem_image h hp hp2 hpℓ hK e hq haE haD
    (orderOf_eq_prime hxp hx1) hpdvd

theorem idxCoreAt_pomegaPlus_of_outer {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] [Finite G] (h : StatedClassicalModel G .POmegaPlus n ℓ f)
    (hn : 5 ≤ n ∨ 3 < p) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f)
    {x : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hxp : x ^ p = 1)
    (hxo : x ∉ innAutDerived (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K))) :
    IdxCoreAt p (.D n q) x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have haH : x ∉ inner (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    fun hmem => hxo (inner_le_innAutDerived _ hmem)
  obtain ⟨haE, haD⟩ := pomegaPlus_mem_image_not_linear h hn hp hp2 hpℓ hK e hxp haH
  have hx1 : x ≠ 1 := fun h1 => haH (h1 ▸ one_mem _)
  exact idxCoreAt_pomegaPlus_of_mem_image h hp hp2 hpℓ hK e hq haE haD
    (orderOf_eq_prime hxp hx1) hpdvd

theorem idxCoreAt_pomegaMinus_of_outer {n ℓ f p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] {G : Type} [Group G] [Finite G]
    (h : StatedClassicalModel G .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f)
    {x : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))} (hxp : x ^ p = 1)
    (hxo : x ∉ innAutDerived (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)))
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) :
    IdxCoreAt p (.twistedD n q) x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have haH : x ∉ inner (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
    fun hmem => hxo (inner_le_innAutDerived _ hmem)
  obtain ⟨haE, haD⟩ := pomegaMinus_mem_image_not_linear hn h hp hp2 hpℓ hK b c hirr e hxp haH
  have hx1 : x ≠ 1 := fun h1 => haH (h1 ▸ one_mem _)
  exact idxCoreAt_pomegaMinus_of_mem_image hn h hp hp2 hpℓ hK b c hirr e hq haE haD
    (orderOf_eq_prime hxp hx1) hpdvd

theorem outerIdxAt_pomegaOdd {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.StatedClassicalModel G .POmegaOdd n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpdvd : p ∣ Nat.card G)
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f) (hv : (TauCeti.LieTypeIndex.B n q).Valid) :
    OuterIdxAt p (.B n q) G := by
  have hmodel := h
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  letI := hfield
  letI := hfinite
  haveI : Finite (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    Finite.of_equiv G (coordinateOddWitnessEquiv K e).toEquiv
  have hpdvdM : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
    rw [← Nat.card_congr (coordinateOddWitnessEquiv K e).toEquiv]
    exact hpdvd
  have hcoord : OuterIdxAt p (.B n q) (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
    refine outerIdxAt_of_idxCoreAt hp ?_
    intro x hxp hxo
    exact idxCoreAt_pomegaOdd_of_outer hmodel hp hp2 hpℓ hK e hq hxp hxo hpdvdM
  exact outerIdxAt_of_mulEquiv hp (coordinateOddWitnessEquiv K e).symm hcoord

theorem outerIdxAt_pomegaPlus {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.StatedClassicalModel G .POmegaPlus n ℓ f) (hn : 5 ≤ n ∨ 3 < p)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpdvd : p ∣ Nat.card G)
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f) (hv : (TauCeti.LieTypeIndex.D n q).Valid) :
    OuterIdxAt p (.D n q) G := by
  have hmodel := h
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  letI := hfield
  letI := hfinite
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv G (coordinatePlusWitnessEquiv K e).toEquiv
  have hpdvdM : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rw [← Nat.card_congr (coordinatePlusWitnessEquiv K e).toEquiv]
    exact hpdvd
  have hcoord : OuterIdxAt p (.D n q) (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    refine outerIdxAt_of_idxCoreAt hp ?_
    intro x hxp hxo
    exact idxCoreAt_pomegaPlus_of_outer hmodel hn hp hp2 hpℓ hK e hq hxp hxo hpdvdM
  exact outerIdxAt_of_mulEquiv hp (coordinatePlusWitnessEquiv K e).symm hcoord

theorem outerIdxAt_pomegaMinus {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.StatedClassicalModel G .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpdvd : p ∣ Nat.card G)
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f)
    (hv : (TauCeti.LieTypeIndex.twistedD n q).Valid) :
    OuterIdxAt p (.twistedD n q) G := by
  have hmodel := h
  have hn : 1 ≤ n := by have := h.1.2.2; omega
  obtain ⟨-, K, hfield, hfinite, hK, b, c, hirr, ⟨e⟩⟩ := h
  letI := hfield
  letI := hfinite
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
    Finite.of_equiv G (coordinateMinusWitnessEquiv K hn b c e).toEquiv
  have hpdvdM : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) := by
    rw [← Nat.card_congr (coordinateMinusWitnessEquiv K hn b c e).toEquiv]
    exact hpdvd
  have hcoord : OuterIdxAt p (.twistedD n q)
      (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) := by
    refine outerIdxAt_of_idxCoreAt hp ?_
    intro x hxp hxo
    exact idxCoreAt_pomegaMinus_of_outer hn hmodel hp hp2 hpℓ hK b c hirr e hq hxp hxo hpdvdM
  exact outerIdxAt_of_mulEquiv hp (coordinateMinusWitnessEquiv K hn b c e).symm hcoord

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
