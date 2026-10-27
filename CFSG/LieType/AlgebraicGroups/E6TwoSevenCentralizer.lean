module

public import CFSG.LieType.SeitzGeneration.ExcTorusE6Three
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Roots
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6OddLemmas
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoSevenSylow
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenTorus
public import CFSG.LieType.SeitzGeneration.SpBlockPlanes
public import CFSG.LieType.SeitzGeneration.ExcParabolicModel
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
public import CFSG.LocalAnalysis.StandardType.GGFinModelEps
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNTorus

public section

namespace CFSG.LieType.AlgebraicGroups.E6TwoSeven

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.RootSpace
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
open CFSG.RankThree.Lattice
open CFSG.HardMathSupport.Timmesfeld.Torality

theorem odd_card_familyStabilizerSubgroup_of_familyKernel_empty
    {τ : Tag} {L : Type} [Field L] {m : ℕ} (hm : Odd m) {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) (ha : ∀ s i, a s i ^ m = 1)
    (hKer : familyKernel a = ∅) :
    Odd (Nat.card ↥(familyStabilizerSubgroup a)) := by
  classical
  refine Nat.not_even_iff_odd.1 ?_
  intro heven
  have hdvd : 2 ∣ Nat.card ↥(familyStabilizerSubgroup a) := even_iff_two_dvd.1 heven
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(familyStabilizerSubgroup a)) 2 hdvd
  have hw2sub : w ^ 2 = 1 := by
    rw [← hw]
    exact pow_orderOf_eq_one w
  have hw2 : ((w : WeylGroup τ) ^ 2) = 1 := by
    simpa using congrArg Subtype.val hw2sub
  obtain ⟨βs, hlen, hroots, hpair, hprod, hspan, hcomm, hnil⟩ :=
    exceptional_Lang_Weyl_involution_orthogonal_reflections τ (w : WeylGroup τ) hw2
  have hne : βs ≠ [] := by
    rintro rfl
    have hw1 : (w : WeylGroup τ) = 1 := by simpa using hprod
    have hw1' : w = 1 := Subtype.ext hw1
    rw [hw1', orderOf_one] at hw
    omega
  obtain ⟨β, hβmem⟩ := List.exists_mem_of_ne_nil βs hne
  have hβroot : IsRoot τ β := hroots β hβmem
  have hβspan : (ofLattice β : RootSpace τ) ∈
      (Submodule.span ℝ (ofLattice '' {β | β ∈ βs}) : Set (RootSpace τ)) :=
    Submodule.subset_span (Set.mem_image_of_mem _ hβmem)
  rw [hspan] at hβspan
  have hwβR : weylAct τ (w : WeylGroup τ) (ofLattice β) = -ofLattice β := hβspan
  have hwβ : (w : WeylGroup τ) • β = -β := by
    apply ofLattice_injective
    rw [← weylAct_ofLattice, hwβR, ofLattice_neg]
  have hχ : ∀ s, rootChar (a s) β = rootChar (a s) (-β) := by
    intro s
    have hwS : ∀ i, (w : WeylGroup τ) ∈ rootCharStabilizerSubgroup (a i) := by
      have h := w.2
      change (w : WeylGroup τ) ∈ ⨅ i, rootCharStabilizerSubgroup (a i) at h
      rwa [Subgroup.mem_iInf] at h
    have h := (hwS s) β
    rw [hwβ] at h
    exact h.symm
  have hχinv : ∀ s, rootChar (a s) β = (rootChar (a s) β)⁻¹ := by
    intro s
    calc rootChar (a s) β = rootChar (a s) (-β) := hχ s
      _ = (rootChar (a s) β)⁻¹ := by
        rw [show -β = (-1 : ℤ) • β by simp, rootChar_zsmul, zpow_neg_one]
  have hχsq : ∀ s, rootChar (a s) β ^ 2 = 1 := by
    intro s
    have h := congrArg (fun u : Lˣ => u * rootChar (a s) β) (hχinv s)
    simpa [pow_two, mul_assoc] using h
  have hχm : ∀ s, rootChar (a s) β ^ m = 1 := by
    intro s
    rw [rootChar, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha s i, one_zpow]
  have hχ1 : ∀ s, rootChar (a s) β = 1 := by
    intro s
    have hord : orderOf (rootChar (a s) β) ∣ Nat.gcd 2 m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hχsq s)) (orderOf_dvd_of_pow_eq_one (hχm s))
    have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact hord
  have hβker : β ∈ familyKernel a := ⟨hβroot, hχ1⟩
  rw [hKer] at hβker
  exact hβker

theorem isSolvable_familyCentralizer_of_familyKernel_empty_of_odd
    {τ : Tag} {L : Type} [Field L] {m : ℕ} (hm : Odd m) {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) (ha : ∀ s i, a s i ^ m = 1)
    (hKer : familyKernel a = ∅) :
    Group.IsSolvable ↥(familyCentralizer τ L a) := by
  classical
  haveI : Finite (WeylGroup τ) :=
    (exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.1
  haveI hHs : Group.IsSolvable ↥(familyStabilizerSubgroup a) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _
      (odd_card_familyStabilizerSubgroup_of_familyKernel_empty hm a ha hKer)
  have hgroup : familyGroup (K := L) a = torusGroup τ L := by
    rw [familyGroup, hKer, rootSpan]
    simp
  have hmono : ∀ g : ↥(familyCentralizer τ L a),
      ∃ w ∈ familyStabilizerSubgroup a, ∃ m ∈ torusGroup τ L,
        (g : ModGL τ L) = m * canonicalRep (coxeterSystem τ) L w := by
    intro g
    obtain ⟨w, hw, m, hm, hmg⟩ := familyCentralizer_le_mul τ L a g.2
    rw [hgroup] at hm
    exact ⟨w, mem_familyStabilizerSubgroup.2 hw, m, hm, hmg⟩
  have hmem : ∀ g : ↥(familyCentralizer τ L a),
      (g : ModGL τ L) ∈ monomialSubgroup τ L := by
    intro g
    obtain ⟨w, -, m, hm, hmg⟩ := hmono g
    rw [hmg]
    exact mul_mem (Subgroup.mem_sup_left hm) (canonicalRep_mem_monomialSubgroup' (K := L) w)
  let ψ : ↥(familyCentralizer τ L a) →* monomialSubgroup τ L :=
    MonoidHom.codRestrict (Subgroup.subtype _) _ hmem
  have hψ : Function.Injective ψ := by
    intro g g' h
    exact Subtype.ext (congrArg (fun x : monomialSubgroup τ L => (x : ModGL τ L)) h)
  obtain ⟨ρ, hρmaps, hsolv⟩ :=
    isSolvable_comap_weylQuotient τ L (familyStabilizerSubgroup a)
  have hρψ : ∀ g, ρ (ψ g) ∈ familyStabilizerSubgroup a := by
    intro g
    obtain ⟨w, hw, m, hm, hmg⟩ := hmono g
    have h1 : MapsRootLines (ψ g : (Module.End L (RootModule τ L))ˣ) (1 * w) := by
      have e : (ψ g : (Module.End L (RootModule τ L))ˣ) =
          m * canonicalRep (coxeterSystem τ) L w := hmg
      rw [e]
      exact (mapsRootLines_of_mem_torusGroup hm).mul (mapsRootLines_canonicalRep w)
    rw [(hρmaps (ψ g)).unique h1, one_mul]
    exact hw
  let ψ' : ↥(familyCentralizer τ L a) →*
      ↥((familyStabilizerSubgroup a).comap ρ) :=
    ψ.codRestrict ((familyStabilizerSubgroup a).comap ρ) hρψ
  haveI := hsolv
  refine Group.isSolvable_of_isSolvable_injective (f := ψ') ?_
  intro g g' h
  exact hψ (congrArg Subtype.val h)

end CFSG.LieType.AlgebraicGroups.E6TwoSeven

namespace CFSG.LieType.AlgebraicGroups.E6TwoSeven

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE.CTTorus
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.KGCentE6
open scoped Matrix

variable {L : Type} [Field L]

def e6ThreeEigBasis : Matrix (Fin Tag.E6.rank) (Fin 3) ℤ :=
  Matrix.of ![![5, 0, 4], ![2, 2, 0], ![6, 4, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

def e6ThreeEigBasisMod : Matrix (Fin Tag.E6.rank) (Fin 3) (ZMod 7) :=
  e6ThreeEigBasis.map (Int.castRingHom (ZMod 7))

def e6ThreeEigColumn (j : Fin 3) : Fin Tag.E6.rank → ZMod 7 :=
  fun i => e6ThreeEigBasisMod i j

theorem e6ThreeEigBasisMod_mulVec_single (j : Fin 3) :
    e6ThreeEigBasisMod *ᵥ (Pi.single j 1 : Fin 3 → ZMod 7) = e6ThreeEigColumn j := by
  ext i
  simp [e6ThreeEigBasisMod, e6ThreeEigColumn, Matrix.mulVec, Pi.single_apply, Matrix.map_apply]

theorem e6ThreeEigColumn_mem (j : Fin 3) :
    (modMat 7 (toMat Tag.E6.rank e6ThreeMat))ᵀ *ᵥ e6ThreeEigColumn j =
      (2 : ZMod 7) • e6ThreeEigColumn j := by
  revert j
  decide +kernel

def e6ThreeFamily (ζ : Lˣ) (c : Fin 3 → ZMod 7) : Fin Tag.E6.rank → Lˣ :=
  expTuple ζ (e6ThreeEigBasisMod *ᵥ c)

theorem e6ThreeFamily_pow_eq_one {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 7)
    (c : Fin 3 → ZMod 7) (i : Fin Tag.E6.rank) :
    (e6ThreeFamily ζ c i) ^ 7 = 1 := by
  simp only [e6ThreeFamily, expTuple]
  rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem e6ThreeEigBasisMod_mem :
    (modMat 7 (toMat Tag.E6.rank e6ThreeMat))ᵀ * e6ThreeEigBasisMod =
      (2 : ZMod 7) • e6ThreeEigBasisMod := by
  ext i j
  have h := congrFun (e6ThreeEigColumn_mem j) i
  simpa [e6ThreeEigColumn, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct] using h

theorem e6ThreeFamily_mem_eig (c : Fin 3 → ZMod 7) :
    (modMat 7 (toMat Tag.E6.rank e6ThreeMat))ᵀ *ᵥ (e6ThreeEigBasisMod *ᵥ c) =
      (2 : ZMod 7) • (e6ThreeEigBasisMod *ᵥ c) := by
  rw [Matrix.mulVec_mulVec, e6ThreeEigBasisMod_mem, Matrix.smul_mulVec]

theorem e6ThreeFamily_mem_fixedCharTuples
    {L : Type} [Field L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ 2) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 7)
    (c : Fin 3 → ZMod 7) :
    e6ThreeFamily ζ c ∈ fixedCharTuples (toMat Tag.E6.rank e6ThreeMat) Fr := by
  change expTuple ζ (e6ThreeEigBasisMod *ᵥ c) ∈
    fixedCharTuples (toMat Tag.E6.rank e6ThreeMat) Fr
  rw [expTuple_mem_fixedCharTuples_iff hζ (toMat Tag.E6.rank e6ThreeMat) Fr hFr]
  exact e6ThreeFamily_mem_eig c

def e6ThreeRootCheck : Bool :=
  roots72.all fun α =>
    (List.finRange 3).any fun j =>
      decide (((∑ i, ((e6ThreeEigColumn j i).val : ℤ) * α i : ℤ) : ZMod 7) ≠ 0)

theorem e6ThreeRootCheck_eq_true : e6ThreeRootCheck = true := by
  decide +kernel

theorem e6ThreeEigColumn_root_nonorthogonal {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ roots72) :
    ∃ j : Fin 3, (((∑ i, ((e6ThreeEigColumn j i).val : ℤ) * α i : ℤ) : ZMod 7) ≠ 0) := by
  have h := List.all_eq_true.1 e6ThreeRootCheck_eq_true α hα
  obtain ⟨j, -, hj⟩ := List.any_eq_true.1 h
  exact ⟨j, of_decide_eq_true hj⟩

theorem e6ThreeFamily_familyKernel_empty {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 7) :
    familyKernel (e6ThreeFamily (L := L) ζ) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro α ⟨hroot, hχ⟩
  obtain ⟨j, hj⟩ := e6ThreeEigColumn_root_nonorthogonal (mem_roots72_of_isRoot hroot)
  have h1 : rootChar (e6ThreeFamily ζ (Pi.single j 1)) α = 1 := hχ (Pi.single j 1)
  rw [e6ThreeFamily, e6ThreeEigBasisMod_mulVec_single, rootChar_expTuple] at h1
  have hdvd : (7 : ℤ) ∣ ∑ i, ((e6ThreeEigColumn j i).val : ℤ) * α i :=
    (hζ.zpow_eq_one_iff_dvd _).1 h1
  have hzero : (((∑ i, ((e6ThreeEigColumn j i).val : ℤ) * α i : ℤ) : ZMod 7)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 hdvd
  exact hj hzero

theorem e6TwoSeven_familyCentralizer_solvable
    {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 7) :
    Group.IsSolvable ↥(familyCentralizer Tag.E6 L (e6ThreeFamily (L := L) ζ)) := by
  exact isSolvable_familyCentralizer_of_familyKernel_empty_of_odd (m := 7) (by norm_num)
    (e6ThreeFamily (L := L) ζ) (fun c i => e6ThreeFamily_pow_eq_one hζ c i)
    (e6ThreeFamily_familyKernel_empty hζ)

end CFSG.LieType.AlgebraicGroups.E6TwoSeven

namespace CFSG.LieType.AlgebraicGroups.E6TwoSeven

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootSpace
open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
open CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
open scoped Matrix

theorem e6ThreeMat_isWeyl :
    IsWeylMatrix Tag.E6 (toMat Tag.E6.rank e6ThreeMat) := by
  rw [← e6Three_wordMat]
  exact IsWeylMatrix.of_word Tag.E6 e6ThreeWord

theorem e6ThreeFamily_mem_twistedTorus
    {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L)
    (hFr2 : ∀ c, Fr c = c ^ 2)
    (w : WeylGroup Tag.E6) (hw : ∀ u, w • u = toMat Tag.E6.rank e6ThreeMat *ᵥ u)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 7) (c : Fin 3 → ZMod 7) :
    rootDiagUnit Tag.E6 (e6ThreeFamily ζ c) ∈
      twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) L w)
        (Units.map (entrywiseHom Fr)) := by
  rw [twistedTorusOf_eq_map_fixedCharTuples Fr w hw]
  exact Subgroup.mem_map_of_mem _ (e6ThreeFamily_mem_fixedCharTuples Fr hFr2 hζ c)

theorem e6TwoSeven_phi3_family_lang_conjugate
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ 7) :
    ∃ g ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
      ∀ c : Fin 3 → ZMod 7,
        g * rootDiagUnit Tag.E6 (e6ThreeFamily (L := AlgebraicClosure K) ζ c) * g⁻¹ ∈
          (adjointGroup Tag.E6 K).map
            (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  classical
  let L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hfcard⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP L (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K L).injective _
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hfcard
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := by
    intro c
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  have hFr2 : ∀ c, Fr c = c ^ 2 := by
    intro c
    rw [hFr c, hK]
  let Φ : ModGL Tag.E6 L →* ModGL Tag.E6 L := Units.map (entrywiseHom Fr)
  obtain ⟨w, hw⟩ := e6ThreeMat_isWeyl
  let n : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L w
  obtain ⟨g0, hg0C, hg0⟩ :=
    lang_conjugator (τ := Tag.E6) K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
  have hg0' : Φ g0 = g0 * n := hg0
  let cg : ModGL Tag.E6 L →* ModGL Tag.E6 L := (MulAut.conj g0).toMonoidHom
  have hcg_apply : ∀ x, cg x = g0 * x * g0⁻¹ := fun _ => rfl
  let X : Subgroup (ModGL Tag.E6 L) :=
    (twistedTorusOf n Φ).map cg
  have hXfin : Finite X := by
    have hT0fin : Finite (twistedTorusOf n Φ) := by
      refine finite_twistedTorusOf_gen (e := 3) Fr w hw hFr (by norm_num) ?_
      simpa [e6Three_wordMat] using e6Three_pow
    exact Finite.of_surjective (cg.subgroupMap (twistedTorusOf n Φ))
      (cg.subgroupMap_surjective (twistedTorusOf n Φ))
  have hXC : X ≤ adjointGroup Tag.E6 L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (twistedTorusOf_le_adjointGroup n Φ hx)) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Φ x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix := (mem_twistedTorusOf.1 hx).2
    rw [hcg_apply, map_mul, map_mul, map_inv, hg0']
    calc g0 * n * Φ x * (g0 * n)⁻¹ = g0 * (n * Φ x * n⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  let Fset : Set (ModGL Tag.E6 L) :=
    Set.range fun c : Fin 3 → ZMod 7 =>
      rootDiagUnit Tag.E6 (e6ThreeFamily (L := L) ζ c)
  let P0 : Subgroup (ModGL Tag.E6 L) := Subgroup.closure Fset
  let P : Subgroup (ModGL Tag.E6 L) := P0.map cg
  have hFset_sub : Fset ⊆ twistedTorusOf n Φ := by
    rintro _ ⟨c, rfl⟩
    exact e6ThreeFamily_mem_twistedTorus Fr hFr2 w hw hζ c
  have hP0_le : P0 ≤ twistedTorusOf n Φ :=
    (Subgroup.closure_le (twistedTorusOf n Φ)).2 hFset_sub
  have hPX : P ≤ X := Subgroup.map_mono hP0_le
  have hFcomm : ∀ x ∈ Fset, ∀ y ∈ Fset, Commute x y := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact torusGroup_comm (rootDiagUnit_mem_torusGroup (e6ThreeFamily ζ a))
      (rootDiagUnit_mem_torusGroup (e6ThreeFamily ζ b))
  have hFpow : ∀ x ∈ Fset, x ^ 7 = 1 := by
    rintro _ ⟨a, rfl⟩
    have ha7 : (e6ThreeFamily ζ a) ^ 7 = 1 := by
      funext i
      simpa [Pi.pow_apply] using e6ThreeFamily_pow_eq_one hζ a i
    change rootDiagUnit Tag.E6 (e6ThreeFamily ζ a) ^ 7 = 1
    rw [rootDiagUnit_pow, ha7, rootDiagUnit_one]
  have hP0elem : IsElemAbelian 7 P0 := isElemAbelian_closure_of_comm hFcomm hFpow
  have hPelem : IsElemAbelian 7 P := by
    refine ⟨isMulCommutative_map cg hP0elem.1, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [← map_pow, hP0elem.2 p hp, map_one]
  have hPp : IsPGroup 7 P := isPGroup_of_isElemAbelian hPelem
  have hPleK : P ≤ (adjointGroup Tag.E6 K).map
      (baseChangeGL (algebraMap K L)) := by
    refine (finite_fixed_subgroup_rational (τ := Tag.E6) (K := K) (L := L) 3
      (Or.inl ⟨rfl, rfl⟩) Fr hFr X hXC hXF).2 7 Nat.prime_seven (by norm_num) P hPX hPp
  refine ⟨g0, hg0C, ?_⟩
  intro c
  have hgen : cg (rootDiagUnit Tag.E6 (e6ThreeFamily (L := L) ζ c)) ∈ P :=
    Subgroup.mem_map_of_mem cg (Subgroup.subset_closure ⟨c, rfl⟩)
  have := hPleK hgen
  simpa [cg, MulAut.conj_apply] using this

end CFSG.LieType.AlgebraicGroups.E6TwoSeven

namespace CFSG.LieType.AlgebraicGroups.E6TwoSeven

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Torality
open scoped Matrix

theorem e6TwoSeven_family_finite_centralizer_solvable
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ 7) :
    ∃ Pfin : Subgroup (adjointGroup Tag.E6 K),
      IsElemAbelian 7 Pfin ∧
      Group.IsSolvable ↥(Subgroup.centralizer (Pfin : Set (adjointGroup Tag.E6 K))) := by
  classical
  let L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  obtain ⟨g0, hg0C, hconj⟩ :=
    e6TwoSeven_phi3_family_lang_conjugate (K := K) hK ζ hζ
  let ι : adjointGroup Tag.E6 K →* ModGL Tag.E6 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.E6 K).subtype
  have hι_inj : Function.Injective ι :=
    (baseChangeGL_injective (algebraMap K L)).comp (Subgroup.subtype_injective _)
  have hrange : ι.range = (adjointGroup Tag.E6 K).map
      (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp
      (adjointGroup Tag.E6 K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let cg : ModGL Tag.E6 L →* ModGL Tag.E6 L := (MulAut.conj g0).toMonoidHom
  let Fset : Set (ModGL Tag.E6 L) :=
    Set.range fun c : Fin 3 → ZMod 7 =>
      rootDiagUnit Tag.E6 (e6ThreeFamily (L := L) ζ c)
  let P0 : Subgroup (ModGL Tag.E6 L) := Subgroup.closure Fset
  let P : Subgroup (ModGL Tag.E6 L) := P0.map cg
  have hFcomm : ∀ x ∈ Fset, ∀ y ∈ Fset, Commute x y := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact torusGroup_comm (rootDiagUnit_mem_torusGroup (e6ThreeFamily ζ a))
      (rootDiagUnit_mem_torusGroup (e6ThreeFamily ζ b))
  have hFpow : ∀ x ∈ Fset, x ^ 7 = 1 := by
    rintro _ ⟨a, rfl⟩
    have ha7 : (e6ThreeFamily ζ a) ^ 7 = 1 := by
      funext i
      simpa [Pi.pow_apply] using e6ThreeFamily_pow_eq_one hζ a i
    change rootDiagUnit Tag.E6 (e6ThreeFamily ζ a) ^ 7 = 1
    rw [rootDiagUnit_pow, ha7, rootDiagUnit_one]
  have hP0elem : IsElemAbelian 7 P0 := isElemAbelian_closure_of_comm hFcomm hFpow
  have hPelem : IsElemAbelian 7 P := by
    refine ⟨isMulCommutative_map cg hP0elem.1, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [← map_pow, hP0elem.2 p hp, map_one]
  have hPle : P ≤ ι.range := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le (ι.range.comap cg)).2 ?_
    rintro _ ⟨c, rfl⟩
    simpa [ι, cg, MulAut.conj_apply] using hconj c
  let Pfin : Subgroup (adjointGroup Tag.E6 K) := P.comap ι
  have hPfin_map : Pfin.map ι = P := Subgroup.map_comap_eq_self hPle
  have hPfin_elem : IsElemAbelian 7 Pfin :=
    isElemAbelian_comap_of_injective ι hι_inj hPelem
  refine ⟨Pfin, hPfin_elem, ?_⟩
  let ψ : ↥(Subgroup.centralizer (Pfin : Set (adjointGroup Tag.E6 K))) →*
      ↥(familyCentralizer Tag.E6 L (e6ThreeFamily (L := L) ζ)) :=
  { toFun := fun x =>
      ⟨g0⁻¹ * ι x.1 * g0, by
        refine mem_familyCentralizer.2 ⟨?_, fun c => ?_⟩
        · exact mul_mem (mul_mem (inv_mem hg0C)
            (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K L)
              x.1.2)) hg0C
        · have hgen : cg (rootDiagUnit Tag.E6 (e6ThreeFamily ζ c)) ∈ P :=
            Subgroup.mem_map_of_mem cg (Subgroup.subset_closure ⟨c, rfl⟩)
          have hgen' : cg (rootDiagUnit Tag.E6 (e6ThreeFamily ζ c)) ∈ Pfin.map ι := by
            rw [hPfin_map]
            exact hgen
          obtain ⟨p, hpPfin, hpι⟩ := Subgroup.mem_map.1 hgen'
          have hpx : p * x.1 = x.1 * p :=
            Subgroup.mem_centralizer_iff.1 x.2 p hpPfin
          have hιcomm : Commute (ι x.1) (ι p) := by
            change ι x.1 * ι p = ι p * ι x.1
            rw [← map_mul, ← map_mul, hpx.symm]
          have hcommP : Commute (ι x.1) (cg (rootDiagUnit Tag.E6 (e6ThreeFamily ζ c))) := by
            rwa [hpι] at hιcomm
          have hycomm : Commute (g0⁻¹ * ι x.1 * g0)
              (rootDiagUnit Tag.E6 (e6ThreeFamily ζ c)) :=
            (Commute.conj_iff g0).1 (by
              simpa [cg, MulAut.conj_apply, mul_assoc] using hcommP)
          exact hycomm.symm.mul_inv_cancel
      ⟩
    map_one' := by
      ext
      simp
    map_mul' := by
      intro x y
      ext
      simp only [Submonoid.coe_mul, Subgroup.coe_mul, map_mul]
      group }
  have hψ : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    apply hι_inj
    have h' : g0⁻¹ * ι x.1 * g0 = g0⁻¹ * ι y.1 * g0 := congrArg Subtype.val h
    have h'' : ι x.1 = ι y.1 := by
      have := congrArg (fun z => g0 * z * g0⁻¹) h'
      simpa [mul_assoc] using this
    exact h''
  haveI hfam : Group.IsSolvable ↥(familyCentralizer Tag.E6 L
      (e6ThreeFamily (L := L) ζ)) := e6TwoSeven_familyCentralizer_solvable hζ
  exact Group.isSolvable_of_isSolvable_injective (f := ψ) hψ

end CFSG.LieType.AlgebraicGroups.E6TwoSeven

namespace CFSG.LieType.AlgebraicGroups.E6TwoSeven

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.SeitzGeneration CFSG.StandardType
open CFSG.RankThree.PartOne.KE

theorem isSolvable_centralizer_of_map_conj_eq
    {G : Type} [Group G] {H K : Subgroup G} {g : G}
    (hmap : H.map (MulAut.conj g).toMonoidHom = K)
    (hK : Group.IsSolvable ↥(Subgroup.centralizer (K : Set G))) :
    Group.IsSolvable ↥(Subgroup.centralizer (H : Set G)) := by
  classical
  let ψ : ↥(Subgroup.centralizer (H : Set G)) →*
      ↥(Subgroup.centralizer (K : Set G)) :=
  { toFun := fun x =>
      ⟨g * x.1 * g⁻¹, by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        rw [← hmap] at hk
        obtain ⟨h0, hh0, rfl⟩ := Subgroup.mem_map.1 hk
        have hx : h0 * x.1 = x.1 * h0 :=
          Subgroup.mem_centralizer_iff.1 x.2 h0 hh0
        calc g * h0 * g⁻¹ * (g * x.1 * g⁻¹) = g * (h0 * x.1) * g⁻¹ := by group
          _ = g * (x.1 * h0) * g⁻¹ := by rw [hx]
          _ = g * x.1 * g⁻¹ * (g * h0 * g⁻¹) := by group⟩
    map_one' := by ext; simp
    map_mul' := by
      intro x y
      ext
      simp only [Submonoid.coe_mul, Subgroup.coe_mul, map_mul]
      group }
  have hψ : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    have h' : g * x.1 * g⁻¹ = g * y.1 * g⁻¹ := congrArg Subtype.val h
    have := congrArg (fun z => g⁻¹ * z * g) h'
    simpa [mul_assoc] using this
  exact Group.isSolvable_of_isSolvable_injective (f := ψ) hψ

theorem e6_two_seven_full_centralizer_solvable
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (E : Subgroup (adjointGroup Tag.E6 K))
    (hE : IsElemAbelian 7 E) (hcard : 7 ^ 3 ≤ Nat.card E) :
    Group.IsSolvable ↥(Subgroup.centralizer (E : Set (adjointGroup Tag.E6 K))) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  have hK2 : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  haveI : CharP K 2 := charP_of_ne_zero (R := K) 2 hK2 (by
    intro i hi hzero
    interval_cases i
    · rfl
    · exact ((one_ne_zero : (1 : K) ≠ 0) (by simpa using hzero)).elim)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ζ, hζo⟩ := CFSG.StandardType.GGFinModel.exists_zeta
    (AlgebraicClosure K) Nat.prime_seven (by norm_num)
  have hζ : IsPrimitiveRoot ζ 7 := IsPrimitiveRoot.iff_orderOf.mpr hζo
  obtain ⟨Pfin, hPfinElem, hPfinSolv⟩ :=
    e6TwoSeven_family_finite_centralizer_solvable (K := K) hK ζ hζ
  obtain ⟨T, E0, -, hconj, -, hE0tors, -, hE0card⟩ :=
    (sylowTorus_adjoint_E6_two_seven hK).exists_torus
  haveI : Finite E0 := Nat.finite_of_card_ne_zero (by rw [hE0card]; norm_num)
  obtain ⟨g, hg⟩ := hconj Pfin (isPGroup_of_isElemAbelian hPfinElem)
  have hPE0 : Pfin.map (MulAut.conj g⁻¹).toMonoidHom ≤ E0 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨t, ht, hpt⟩ := hg hp
    refine hE0tors _ ?_ ?_
    · rw [← hpt]
      have hcomp : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom t) = t := by
        show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t
        group
      rw [hcomp]
      exact ht
    · rw [← map_pow, hPfinElem.2 p hp, map_one]
  let E1 : Subgroup (adjointGroup Tag.E6 K) := E0.map (MulAut.conj g).toMonoidHom
  have hPfinE1 : Pfin ≤ E1 := by
    intro p hp
    have hx : (MulAut.conj g⁻¹) p ∈ E0 :=
      hPE0 (Subgroup.mem_map_of_mem _ hp)
    have hcomp : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom p) = p := by
      show g * (g⁻¹ * p * g) * g⁻¹ = p
      group
    rw [← hcomp]
    exact Subgroup.mem_map_of_mem _ hx
  have hcent_le : Subgroup.centralizer (E1 : Set (adjointGroup Tag.E6 K)) ≤
      Subgroup.centralizer (Pfin : Set (adjointGroup Tag.E6 K)) :=
    Subgroup.centralizer_le (fun x hx => hPfinE1 hx)
  haveI : Group.IsSolvable ↥(Subgroup.centralizer
      (Pfin : Set (adjointGroup Tag.E6 K))) := hPfinSolv
  have hE1solv : Group.IsSolvable ↥(Subgroup.centralizer
      (E1 : Set (adjointGroup Tag.E6 K))) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hcent_le)
      (Subgroup.inclusion_injective hcent_le)
  have hE0solv : Group.IsSolvable ↥(Subgroup.centralizer
      (E0 : Set (adjointGroup Tag.E6 K))) :=
    isSolvable_centralizer_of_map_conj_eq (H := E0) (K := E1) (g := g) rfl hE1solv
  have hEcard : Nat.card E = 7 ^ 3 := by
    apply le_antisymm
    · exact (sylowTorus_adjoint_E6_two_seven hK).rank_le Nat.prime_seven hE
    · exact hcard
  obtain ⟨gE, hgE⟩ := hconj E (isPGroup_of_isElemAbelian hE)
  have hEsub : E.map (MulAut.conj gE⁻¹).toMonoidHom ≤ E0 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨t, ht, het⟩ := hgE he
    refine hE0tors _ ?_ ?_
    · rw [← het]
      have hcomp : (MulAut.conj gE⁻¹).toMonoidHom ((MulAut.conj gE).toMonoidHom t) = t := by
        show gE⁻¹ * (gE * t * gE⁻¹) * gE⁻¹⁻¹ = t
        group
      rw [hcomp]
      exact ht
    · rw [← map_pow, hE.2 e he, map_one]
  have hEeq : E.map (MulAut.conj gE⁻¹).toMonoidHom = E0 := by
    refine Subgroup.eq_of_le_of_card_ge hEsub ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj gE⁻¹).injective, hEcard, hE0card]
  exact isSolvable_centralizer_of_map_conj_eq (H := E) (K := E0) (g := gE⁻¹) hEeq hE0solv

end CFSG.LieType.AlgebraicGroups.E6TwoSeven
