module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice

section LangModel

variable (τ : Tag) (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]

@[expose] noncomputable def langModel
    (g0 : ModGL τ L) : Subgroup (ModGL τ L) :=
  ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).map (MulAut.conj g0⁻¹).toMonoidHom


noncomputable def langModelEquiv (g0 : ModGL τ L) : adjointGroup τ K ≃* langModel τ K L g0 :=
  ((adjointGroup τ K).equivMapOfInjective _ (baseChangeGL_injective _)).trans
    ((MulAut.conj g0⁻¹).subgroupMap _)

theorem finite_langModel [Finite K] (g0 : ModGL τ L) : Finite (langModel τ K L g0) := by
  have : Finite (ModGL τ K) := finite_modGL
  exact Finite.of_equiv _ (langModelEquiv τ K L g0).toEquiv

theorem langModel_le_adjointGroup {g0 : ModGL τ L} (hg0C : g0 ∈ adjointGroup τ L) :
    langModel τ K L g0 ≤ adjointGroup τ L := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact (adjointGroup τ L).mul_mem ((adjointGroup τ L).mul_mem
    ((adjointGroup τ L).inv_mem hg0C) (baseChangeGL_mem_adjointGroup _ hy)) (by
      simpa using hg0C)

theorem langModel_le_twModel [Finite K] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {n g0 : ModGL τ L} (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * n) : langModel τ K L g0 ≤ twModel n Fr := by
  have h1 := map_conj_twModel hg0C hg0
  rintro _ ⟨x, hx, rfl⟩
  have hxF : x ∈ adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
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

end LangModel

section E8

@[expose] def e8NegWord : List (Fin Tag.E8.rank) :=
  (List.replicate 15 [0, 1, 2, 3, 4, 5, 6, 7]).flatten

theorem wordMat_e8NegWord : wordMat Tag.E8 e8NegWord = -1 := by decide +kernel

@[expose] def e8Neg : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd e8NegWord

theorem e8Neg_smul
    (u : Fin Tag.E8.rank → ℤ) : e8Neg • u = -u := by
  rw [e8Neg, wordProd_smul_eq_wordMat_mulVec, wordMat_e8NegWord, Matrix.neg_mulVec,
    Matrix.one_mulVec]

theorem exists_mul_cartan_E8 : ∃ B : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ,
    B * Tag.E8.cartan = 1 :=
  ⟨!![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2], by decide +kernel⟩

theorem rootDiagUnit_mem_torusGroup_E8
    {L : Type} [Field L] (a : Fin Tag.E8.rank → Lˣ) :
    rootDiagUnit Tag.E8 a ∈ torusGroup Tag.E8 L :=
  rootDiagUnit_mem_torusGroup_of_unimodular exists_mul_cartan_E8.choose_spec a

end E8

section ModelE8

variable (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]


theorem le_langModel_E8_of_le_twModel {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {n g0 : ModGL Tag.E8 L} (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * n) {P : Subgroup (ModGL Tag.E8 L)} [Finite P]
    (hPM : P ≤ twModel n Fr) : P ≤ langModel Tag.E8 K L g0 := by
  classical
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set X := P.map (MulAut.conj g0).toMonoidHom with hX
  have : Finite X := Finite.of_surjective ((MulAut.conj g0).toMonoidHom.subgroupMap P)
    ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective P)
  have hXF : X ≤ adjointGroup Tag.E8 L ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rw [← map_conj_twModel hg0C hg0]
    exact Subgroup.map_mono hPM
  have hdesc := finite_fixed_subgroup_rational_perfect 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X
    (fun x hx => (hXF hx).1) (fun x hx => (hXF hx).2)
  have hXC : X ≤ (adjointGroup Tag.E8 K).map (baseChangeGL (algebraMap K L)) :=
    Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1 hdesc.1)
  intro x hx
  refine ⟨(MulAut.conj g0).toMonoidHom x, hXC ⟨x, hx, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem exists_twistedTorus_le_langModel_E8 {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E8 L} (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem Tag.E8) L e8Neg)
    {N : ℕ} (hN : N ∣ Nat.card K + 1) :
    ∃ H₀ : Subgroup (ModGL Tag.E8 L),
      H₀ ≤ twistedTorus (canonicalRep (coxeterSystem Tag.E8) L e8Neg) Fr ∧
        H₀ ≤ langModel Tag.E8 K L g0 ∧ Nat.card H₀ = N ^ 8 := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨ζ, hζord, hζq⟩ := exists_orderOf_eq_of_dvd_add_one K (L := L) hN
  obtain ⟨H₀, hH₀T, hH₀card⟩ := exists_le_twistedTorus_card (L := L)
    rootDiagUnit_mem_torusGroup_E8 e8Neg_smul hFr hζq
  rw [hζord] at hH₀card
  have hN0 : N ≠ 0 := fun h0 => by
    rw [h0] at hN
    exact absurd (Nat.eq_zero_of_zero_dvd hN) (by omega)
  have : Finite H₀ := Nat.finite_of_card_ne_zero (by rw [hH₀card]; exact pow_ne_zero _ hN0)
  exact ⟨H₀, hH₀T, le_langModel_E8_of_le_twModel K L hFr hg0C hg0
    (hH₀T.trans (twistedTorus_le_twModel _ Fr)), hH₀card⟩

theorem coroot_mem_langModel_E8 {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E8 L} (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem Tag.E8) L e8Neg)
    {ζ : Lˣ} (hζ : ζ ^ (Nat.card K + 1) = 1) (v : WeylGroup Tag.E8) (k : Fin Tag.E8.rank) :
    canonicalRep (coxeterSystem Tag.E8) L v * torusElt Tag.E8 L k ζ *
        (canonicalRep (coxeterSystem Tag.E8) L v)⁻¹ ∈ langModel Tag.E8 K L g0 := by
  set x := canonicalRep (coxeterSystem Tag.E8) L v * torusElt Tag.E8 L k ζ *
    (canonicalRep (coxeterSystem Tag.E8) L v)⁻¹ with hx
  have hxT : x ∈ twistedTorus (canonicalRep (coxeterSystem Tag.E8) L e8Neg) Fr :=
    coroot_mem_twistedTorus rootDiagUnit_mem_torusGroup_E8 e8Neg_smul hFr hζ v k
  have hxq : x ^ (Nat.card K + 1) = 1 := by
    obtain ⟨a, hxa, ha⟩ := (mem_twistedTorus_of_neg rootDiagUnit_mem_torusGroup_E8 e8Neg_smul
      hFr).1 hxT
    have h1 : rootDiagUnit Tag.E8 (a ^ (Nat.card K + 1)) =
        rootDiagUnit Tag.E8 a ^ (Nat.card K + 1) := map_pow (rootDiagUnitHom Tag.E8 L) a _
    rw [hxa, ← h1, show a ^ (Nat.card K + 1) = 1 from funext ha, rootDiagUnit_one]
  have : Finite (Subgroup.zpowers x) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨_, by omega, hxq⟩)).ne')
  exact le_langModel_E8_of_le_twModel K L hFr hg0C hg0
    ((Subgroup.zpowers_le).2 (twistedTorus_le_twModel _ Fr hxT)) (Subgroup.mem_zpowers x)

end ModelE8

end CFSG.HardMathSupport.Timmesfeld.CrossChar
