module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.RankThree.PartOne.KE.CTTorus
public import CFSG.RankThree.PartOne.KE.CTStatement
public import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice

section Neg

variable {τ : Tag} {L : Type} [Field L]

theorem weylTuple_eq_inv_of_neg {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (b : Fin τ.rank → Lˣ) : weylTuple w b = b⁻¹ := by
  funext i
  have h1 : w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1 := by
    have h := hw (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))
    rw [smul_inv_smul] at h
    calc w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) = -(-(w⁻¹ • Pi.single i 1)) := (neg_neg _).symm
      _ = -Pi.single i 1 := by rw [← h]
  simp only [weylTuple, h1, Pi.inv_apply]
  rw [show (-Pi.single i 1 : Fin τ.rank → ℤ) = (-1 : ℤ) • Pi.single i 1 by simp, rootChar_zsmul,
    CTTorus.rootChar_single, zpow_neg_one]

theorem mem_twistedFixedTuples_of_neg {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {a : Fin τ.rank → Lˣ} :
    a ∈ twistedFixedTuples w Fr ↔ ∀ i, a i ^ (q + 1) = 1 := by
  change weylTuple w (fun i => Units.map Fr.toMonoidHom (a i)) = a ↔ _
  rw [weylTuple_eq_inv_of_neg hw]
  simp only [CTTorus.map_units_eq_pow hFr]
  constructor
  · intro h i
    have h1 := congrFun h i
    simp only [Pi.inv_apply] at h1
    calc a i ^ (q + 1) = a i ^ q * a i := pow_succ _ _
      _ = a i ^ q * (a i ^ q)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  · intro h
    funext i
    simp only [Pi.inv_apply]
    rw [inv_eq_iff_mul_eq_one, ← pow_succ, h i]


theorem rootDiagUnit_mem_torusGroup_of_unimodular {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hB : B * τ.cartan = 1) (a : Fin τ.rank → Lˣ) : rootDiagUnit τ a ∈ torusGroup τ L := by
  rw [rootDiagUnit_eq_list_prod_torusElt hB a]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_torusGroup i _

theorem mem_twistedTorus_of_neg (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {x : ModGL τ L} :
    x ∈ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr ↔
      ∃ a : Fin τ.rank → Lˣ, x = rootDiagUnit τ a ∧ ∀ i, a i ^ (q + 1) = 1 := by
  rw [mem_twistedTorus]
  constructor
  · rintro ⟨hxT, hfix⟩
    obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hxT
    exact ⟨a, rfl, (mem_twistedFixedTuples_of_neg hw hFr).1
      (mem_twistedFixedTuples_iff_conj.2 hfix)⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨htorL a, mem_twistedFixedTuples_iff_conj.1 ((mem_twistedFixedTuples_of_neg hw hFr).2 ha)⟩

theorem exists_le_twistedTorus_card
    (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L) {w : WeylGroup τ}
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Lˣ} (hζ : ζ ^ (q + 1) = 1) :
    ∃ H₀ : Subgroup (ModGL τ L),
      H₀ ≤ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr ∧
        Nat.card H₀ = orderOf ζ ^ τ.rank := by
  classical
  let ψ : (Fin τ.rank → Subgroup.zpowers ζ) →* ModGL τ L :=
    (rootDiagUnitHom τ L).comp ((Subgroup.zpowers ζ).subtype.compLeft (Fin τ.rank))
  have hψ : ∀ a, ψ a = rootDiagUnit τ (fun i => (a i : Lˣ)) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    intro a b hab
    rw [hψ, hψ] at hab
    funext i
    exact Subtype.ext (congrFun (rootDiagUnit_injective hab) i)
  refine ⟨ψ.range, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    refine (mem_twistedTorus_of_neg htorL hw hFr).2 ⟨fun i => (a i : Lˣ), hψ a, fun i => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (a i).2
    show ((a i : Lˣ)) ^ (q + 1) = 1
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun, Nat.card_zpowers,
      Nat.card_eq_fintype_card, Fintype.card_fin]

end Neg

section Model

variable {τ : Tag} {L : Type} [Field L]

@[expose] noncomputable def twModel (n : ModGL τ L) (Fr : L →+* L) : Subgroup (ModGL τ L) :=
  adjointGroup τ L ⊓
    ((MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom Fr))).eqLocus (MonoidHom.id _)

theorem mem_twModel {n : ModGL τ L} {Fr : L →+* L} {y : ModGL τ L} :
    y ∈ twModel n Fr ↔
      y ∈ adjointGroup τ L ∧ n * Units.map (entrywiseHom Fr) y * n⁻¹ = y :=
  Iff.rfl

theorem twistedTorus_le_twModel
    (n : ModGL τ L) (Fr : L →+* L) : twistedTorus n Fr ≤ twModel n Fr := fun _ hx =>
  ⟨twistedTorusOf_le_adjointGroup n _ hx, (mem_twistedTorus.1 hx).2⟩

theorem map_conj_twModel {n g0 : ModGL τ L} {Fr : L →+* L} (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * n) :
    (twModel n Fr).map (MulAut.conj g0).toMonoidHom =
      adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
  set F : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hFdef
  have hginv : F g0⁻¹ = n⁻¹ * g0⁻¹ := by rw [map_inv, hg0, mul_inv_rev]
  ext x
  constructor
  · rintro ⟨y, ⟨hyC, hyF⟩, rfl⟩
    have hyF' : n * F y * n⁻¹ = y := hyF
    have hyC' : y ∈ adjointGroup τ L := hyC
    refine ⟨(adjointGroup τ L).mul_mem ((adjointGroup τ L).mul_mem hg0C hyC')
      ((adjointGroup τ L).inv_mem hg0C), ?_⟩
    change F (g0 * y * g0⁻¹) = g0 * y * g0⁻¹
    calc F (g0 * y * g0⁻¹) = g0 * (n * F y * n⁻¹) * g0⁻¹ := by
          rw [map_mul, map_mul, hg0, hginv]
          group
      _ = g0 * y * g0⁻¹ := by rw [hyF']
  · rintro ⟨hxC, hxF⟩
    have hxF' : F x = x := hxF
    have hxC' : x ∈ adjointGroup τ L := hxC
    refine ⟨g0⁻¹ * x * g0, ⟨(adjointGroup τ L).mul_mem ((adjointGroup τ L).mul_mem
      ((adjointGroup τ L).inv_mem hg0C) hxC') hg0C, ?_⟩, ?_⟩
    · change n * F (g0⁻¹ * x * g0) * n⁻¹ = g0⁻¹ * x * g0
      rw [map_mul, map_mul, hginv, hxF', hg0]
      group
    · change g0 * (g0⁻¹ * x * g0) * g0⁻¹ = x
      group

end Model

section F4

@[expose] def f4NegWord : List (Fin Tag.F4.rank) := (List.replicate 6 [0, 1, 2, 3]).flatten

theorem wordMat_f4NegWord : wordMat Tag.F4 f4NegWord = -1 := by decide +kernel

@[expose] def f4Neg : WeylGroup Tag.F4 := (coxeterSystem Tag.F4).wordProd f4NegWord

theorem f4Neg_smul
    (u : Fin Tag.F4.rank → ℤ) : f4Neg • u = -u := by
  rw [f4Neg, wordProd_smul_eq_wordMat_mulVec, wordMat_f4NegWord, Matrix.neg_mulVec,
    Matrix.one_mulVec]

theorem exists_mul_cartan_F4 : ∃ B : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ,
    B * Tag.F4.cartan = 1 :=
  ⟨!![2, 3, 2, 1; 3, 6, 4, 2; 4, 8, 6, 3; 2, 4, 3, 2], by decide⟩

end F4

end CFSG.HardMathSupport.Timmesfeld.CrossChar
