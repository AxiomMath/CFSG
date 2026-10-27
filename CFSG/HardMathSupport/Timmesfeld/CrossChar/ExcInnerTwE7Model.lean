module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KE.CTLangData

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice

section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem prod_zpow_eq_zpow_sum'' {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, ξ ^ f i = ξ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add, ih]

theorem rootDiagUnit_mem_torusGroup_of_adjugate
    [IsAlgClosed L] {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    {N : ℕ} (hN : 0 < N) (hB : B * τ.cartan = (N : ℤ) • 1) (a : Fin τ.rank → Lˣ) :
    rootDiagUnit τ a ∈ torusGroup τ L := by
  classical
  have hroot : ∀ x : Lˣ, ∃ y : Lˣ, y ^ N = x := fun x => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : L) hN
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hN.ne'] at hz
      exact x.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩
  choose s hs using fun l => hroot (a l)
  set c : Fin τ.rank → Lˣ := fun j => ∏ m, s m ^ B m j with hcdef
  have hc : cartanChar c = a := by
    funext l
    have h1 : ∀ j, (∏ m, s m ^ B m j) ^ τ.cartan j l = ∏ m, s m ^ (B m j * τ.cartan j l) := by
      intro j
      rw [← Finset.prod_zpow]
      exact Finset.prod_congr rfl fun m _ => (zpow_mul _ _ _).symm
    simp only [cartanChar, hcdef, h1]
    rw [Finset.prod_comm]
    have h2 : ∀ m, ∏ j, s m ^ (B m j * τ.cartan j l) = s m ^ ((N : ℤ) • (1 : Matrix
        (Fin τ.rank) (Fin τ.rank) ℤ)) m l := fun m => by
      rw [prod_zpow_eq_zpow_sum'', ← hB, Matrix.mul_apply]
    simp only [h2, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.prod_eq_single l (fun m _ hm => by simp [hm])
      (fun h => absurd (Finset.mem_univ l) h)]
    simp [hs l]
  rw [← hc, ← list_prod_torusElt_eq_rootDiagUnit]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_torusGroup i _

theorem coroot_mem_twistedTorus
    (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L) {w : WeylGroup τ}
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {ζ : Lˣ} (hζ : ζ ^ (q + 1) = 1) (v : WeylGroup τ) (k : Fin τ.rank) :
    canonicalRep (coxeterSystem τ) L v * torusElt τ L k ζ *
        (canonicalRep (coxeterSystem τ) L v)⁻¹ ∈
      twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr := by
  refine (mem_twistedTorus_of_neg htorL hw hFr).2 ?_
  refine ⟨weylTuple v fun j => ζ ^ τ.cartan k j, ?_, fun i => ?_⟩
  · rw [torusElt_eq_rootDiagUnit, canonicalRep_conj_rootDiagUnit]
  · refine CTTorus.rootChar_pow_eq_one (fun j => ?_) _
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]

end Torus

section Lang


theorem exists_lang_data (τ : Tag) (K : Type) [Field K] [Finite K] (w : WeylGroup τ) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ g0 ∈ adjointGroup τ (AlgebraicClosure K), Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := ringChar K) (f := f) f.pos
    (AlgebraicClosure K) w
  refine ⟨iterateFrobenius (AlgebraicClosure K) (ringChar K) f, fun c => ?_, g0, hg0C, hg0⟩
  rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]

end Lang

section E7

@[expose] def e7NegWord : List (Fin Tag.E7.rank) :=
  (List.replicate 9 [0, 1, 2, 3, 4, 5, 6]).flatten

theorem wordMat_e7NegWord : wordMat Tag.E7 e7NegWord = -1 := by decide +kernel

@[expose] def e7Neg : WeylGroup Tag.E7 := (coxeterSystem Tag.E7).wordProd e7NegWord

theorem e7Neg_smul
    (u : Fin Tag.E7.rank → ℤ) : e7Neg • u = -u := by
  rw [e7Neg, wordProd_smul_eq_wordMat_mulVec, wordMat_e7NegWord, Matrix.neg_mulVec,
    Matrix.one_mulVec]

theorem exists_mul_cartan_E7 : ∃ B : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ,
    B * Tag.E7.cartan = ((2 : ℕ) : ℤ) • 1 :=
  ⟨!![4, 4, 6, 8, 6, 4, 2; 4, 7, 8, 12, 9, 6, 3; 6, 8, 12, 16, 12, 8, 4;
    8, 12, 16, 24, 18, 12, 6; 6, 9, 12, 18, 15, 10, 5; 4, 6, 8, 12, 10, 8, 4;
    2, 3, 4, 6, 5, 4, 3], by decide +kernel⟩

theorem rootDiagUnit_mem_torusGroup_E7
    {L : Type} [Field L] [IsAlgClosed L]
    (a : Fin Tag.E7.rank → Lˣ) : rootDiagUnit Tag.E7 a ∈ torusGroup Tag.E7 L :=
  rootDiagUnit_mem_torusGroup_of_adjugate (by norm_num) exists_mul_cartan_E7.choose_spec a

end E7

section Model

variable (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]

@[expose] noncomputable def e7Model
    (g0 : ModGL Tag.E7 L) : Subgroup (ModGL Tag.E7 L) :=
  ((adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L))).map
    (MulAut.conj g0⁻¹).toMonoidHom


noncomputable def e7ModelEquiv (g0 : ModGL Tag.E7 L) :
    adjointGroup Tag.E7 K ≃* e7Model K L g0 :=
  ((adjointGroup Tag.E7 K).equivMapOfInjective _ (baseChangeGL_injective _)).trans
    ((MulAut.conj g0⁻¹).subgroupMap _)

theorem finite_e7Model [Finite K] (g0 : ModGL Tag.E7 L) : Finite (e7Model K L g0) := by
  have : Finite (ModGL Tag.E7 K) := finite_modGL
  exact Finite.of_equiv _ (e7ModelEquiv K L g0).toEquiv

theorem e7Model_le_adjointGroup {g0 : ModGL Tag.E7 L} (hg0C : g0 ∈ adjointGroup Tag.E7 L) :
    e7Model K L g0 ≤ adjointGroup Tag.E7 L := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact (adjointGroup Tag.E7 L).mul_mem ((adjointGroup Tag.E7 L).mul_mem
    ((adjointGroup Tag.E7 L).inv_mem hg0C) (baseChangeGL_mem_adjointGroup _ hy)) (by
      simpa using hg0C)

theorem e7Model_le_twModel [Finite K] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E7 L} (hg0C : g0 ∈ adjointGroup Tag.E7 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E7) L e7Neg) :
    e7Model K L g0 ≤ twModel (canonicalRep (coxeterSystem Tag.E7) L e7Neg) Fr := by
  have h1 := map_conj_twModel hg0C hg0
  rintro _ ⟨x, hx, rfl⟩
  have hxF : x ∈ adjointGroup Tag.E7 L ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨baseChangeGL_mem_adjointGroup _ hy,
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr y⟩
  rw [← h1] at hxF
  obtain ⟨z, hz, hzx⟩ := hxF
  have : (MulAut.conj g0⁻¹).toMonoidHom x = z := by
    rw [← hzx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [this]
  exact hz


theorem le_e7Model_of_le_twModel [Finite K] [IsAlgClosure K L] {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g0 : ModGL Tag.E7 L} (hg0C : g0 ∈ adjointGroup Tag.E7 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E7) L e7Neg)
    {P : Subgroup (ModGL Tag.E7 L)} [Finite P]
    (hPM : P ≤ twModel (canonicalRep (coxeterSystem Tag.E7) L e7Neg) Fr) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hPp : IsPGroup p P) : P ≤ e7Model K L g0 := by
  classical
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set X := P.map (MulAut.conj g0).toMonoidHom with hX
  have : Finite X := Finite.of_surjective ((MulAut.conj g0).toMonoidHom.subgroupMap P)
    ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective P)
  have hXF : X ≤ adjointGroup Tag.E7 L ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rw [← map_conj_twModel hg0C hg0]
    exact Subgroup.map_mono hPM
  have hdesc := finite_fixed_subgroup_rational_perfect 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) Fr hFr X
    (fun x hx => (hXF hx).1) (fun x hx => (hXF hx).2)
  have hXC := hdesc.2.1 p hp hp3 X le_rfl (hPp.map _)
  intro x hx
  refine ⟨(MulAut.conj g0).toMonoidHom x, hXC ⟨x, hx, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end Model

end CFSG.HardMathSupport.Timmesfeld.CrossChar
