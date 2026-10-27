
module

public import CFSG.LieType.Chevalley.C2E6StdMatrixModelBase
import all CFSG.LieType.Chevalley.C2E6StdMatrixModelBase

public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.Monster.B.Classical.E6AdjointTable
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Blueprint.Catalog
public import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix
public import CFSG.LieType.Chevalley.C2E6StdMatrixVec
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
public import CFSG.LieType.Chevalley.C2E6StdMatrixModelInputs
public import Certificates.Certificate10004
public meta import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix
public meta import CFSG.LieType.Chevalley.C2E6StdMatrixData
public meta import CFSG.Monster.B.Classical.E6AdjointTable
import CFSG.Monster.B.Classical.E6AdjointGroup
import CFSG.Monster.B.E6.StdF4LeviRank
import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
import CFSG.LieType.Chevalley.C2E6FirstResidueLevi
import CFSG.LieType.Chevalley.FoldedWeylIdentification
import CFSG.LieType.Chevalley.C2E6FirstResidueGeometry
import CFSG.LieType.Chevalley.TwistedE6FieldTwoCyclicKernel
import all CFSG.Fischer.F4
public import Certificates.Certificate10004Base

public section

namespace CFSG.LieType.Chevalley.C2E6Std.MatrixModel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.Monster.B.Classical.E6Adjoint

section SLP

variable {M N : Type*} [Monoid M] [Monoid N]

end SLP

open C2E6Std
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

noncomputable def letters :
    Array (ModGL Tag.E6 K) :=
  #[xL (fa 0) 1, xL (fa 0) (pc (fa 0) card_orbit_zero ω),
    xL (fa 0) (pc (fa 0) card_orbit_zero (ω ^ 2)), xL (fa 1) 1,
    xL (fa 1) (pc (fa 1) card_orbit_one ω), xL (fa 1) (pc (fa 1) card_orbit_one (ω ^ 2)),
    xL (fa 2) 1, xL (fa 3) 1, nL (fa 0), nL (fa 1), nL (fa 2), nL (fa 3)]

theorem letters_mem :
    ∀ x ∈ letters, x ∈ stdGroup := by
  intro x hx
  simp only [letters, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    first | exact xL_mem _ _ | exact nL_mem _


theorem stdGroup_le_of_letters
    {H : Subgroup (ModGL Tag.E6 K)}
    (h : ∀ j < 12, letters.getD j 1 ∈ H) : stdGroup ≤ H := by
  refine stdGroup_le_of (fun a c => ?_) (fun a => ?_)
  · obtain ⟨i, rfl⟩ := exists_fa a
    obtain ⟨c, hc⟩ := c
    rcases K_cases c with rfl | rfl | rfl | rfl
    · rw [xL_zero]
      exact H.one_mem
    · fin_cases i
      · exact h 0 (by decide)
      · exact h 3 (by decide)
      · exact h 6 (by decide)
      · exact h 7 (by decide)
    · fin_cases i
      · exact h 1 (by decide)
      · exact h 4 (by decide)
      · exact absurd ((mem_orbitField_iff_of_card_eq_one card_orbit_two).1 hc) bar_omega_ne
      · exact absurd ((mem_orbitField_iff_of_card_eq_one card_orbit_three).1 hc) bar_omega_ne
    · fin_cases i
      · exact h 2 (by decide)
      · exact h 5 (by decide)
      · exact absurd ((mem_orbitField_iff_of_card_eq_one card_orbit_two).1 hc) bar_omega_sq_ne
      · exact absurd ((mem_orbitField_iff_of_card_eq_one card_orbit_three).1 hc)
          bar_omega_sq_ne
  · obtain ⟨i, rfl⟩ := exists_fa a
    fin_cases i
    · exact h 8 (by decide)
    · exact h 9 (by decide)
    · exact h 10 (by decide)
    · exact h 11 (by decide)

noncomputable def genA :
    ModGL Tag.E6 K := (slpRunG letters fwdProg).getD idxA 1

noncomputable def genB :
    ModGL Tag.E6 K := (slpRunG letters fwdProg).getD idxB 1

theorem genA_mem :
    genA ∈ stdGroup :=
  getD_mem _ (slpRunG_mem _ letters_mem fwdProg) idxA

theorem genB_mem :
    genB ∈ stdGroup :=
  getD_mem _ (slpRunG_mem _ letters_mem fwdProg) idxB

noncomputable def stdA :
    stdGroup := ⟨genA, genA_mem⟩

noncomputable def stdB :
    stdGroup := ⟨genB, genB_mem⟩

theorem img2_stdA_stdB :
    (fun i => ((img2 stdA stdB i : stdGroup) : ModGL Tag.E6 K)) =
    img2 genA genB := by
  funext i
  unfold img2
  split_ifs <;> rfl

noncomputable def labBasis :
    Module.Basis (Fin 78) K (RootModule Tag.E6 K) :=
  Finsupp.basisSingleOne.reindex (Equiv.ofBijective lab CFSG.Monster.B.E6.StdF4.lab_bijective).symm

theorem labBasis_apply
    (k : Fin 78) : labBasis k = Finsupp.single (lab k) 1 := by
  simp [labBasis]

theorem labBasis_repr
    (x : RootModule Tag.E6 K) (k : Fin 78) : labBasis.repr x k = x (lab k) := by
  simp [labBasis]

noncomputable def matOf :
    Module.End K (RootModule Tag.E6 K) ≃ₐ[K] Matrix (Fin 78) (Fin 78) K :=
  LinearMap.toMatrixAlgEquiv labBasis

theorem matOf_apply
    (f : Module.End K (RootModule Tag.E6 K)) (k l : Fin 78) :
    matOf f k l = f (Finsupp.single (lab l) 1) (lab k) := by
  rw [matOf, LinearMap.toMatrixAlgEquiv_apply, labBasis_apply, labBasis_repr]

@[expose] noncomputable def glMat :
    ModGL Tag.E6 K →* Matrix (Fin 78) (Fin 78) K where
  toFun g := matOf (g : Module.End K (RootModule Tag.E6 K))
  map_one' := by rw [Units.val_one, map_one]
  map_mul' g h := by rw [Units.val_mul, map_mul]

theorem glMat_apply (g : ModGL Tag.E6 K) :
    glMat g = matOf (g : Module.End K (RootModule Tag.E6 K)) := rfl

theorem glMat_injective : Function.Injective glMat := fun _ _ h =>
  Units.ext (matOf.injective h)

theorem matOf_rootOp
    (r : Fin 78) (c0 c1 : Bool) :
    matOf (1 + ofBits c0 c1 • ad K (Finsupp.single (lab r) 1) +
      ofBits c0 c1 ^ 2 • formTensor K (Finsupp.single (lab r) 1)) =
      toMat (Native.rootMat bracketCodes formBits r c0 c1) := by
  ext k l
  rw [matOf_apply, rootOp_apply, bracket_lab, form_lab, Native.rootMat, toMat_ofFn,
    Native.rootCol]
  have hc : Native.maskOf (Native.code bracketCodes r l) = brMask r l := rfl
  have hf : Native.fbit formBits r l = fbit r l := rfl
  rw [hc, hf]
  have h1 : (1 <<< (l : ℕ)).testBit k = decide ((l : ℕ) = k) := by
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  have h2 : (1 <<< (r : ℕ)).testBit k = decide ((r : ℕ) = k) := by
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, CFSG.Monster.B.E6.StdF4.toVec_apply_lab, single_lab_apply,
    single_lab_apply, vecOf_vadd, vecOf_vadd, Pi.add_apply, Pi.add_apply, vecOf_vsmul,
    Pi.smul_apply, vecOf_mask, vecOf_mask, h1, ← ofBits_sq]
  cases fbit r l
  · simp [vecOf_zero]
  · simp only [↓reduceIte, vecOf_vsmul, Pi.smul_apply, vecOf_mask, h2]
    simp

theorem matOf_xOp
    (i : Fin Tag.E6.rank) (c0 c1 : Bool) :
    matOf (xOp Tag.E6 K i (ofBits c0 c1)) = toMat (Native.xMat bracketCodes formBits i c0 c1) := by
  rw [xOp_eq, CFSG.Monster.B.E6.StdF4.rootVec_single]
  exact matOf_rootOp ⟨6 + i, CFSG.Monster.B.E6.StdF4.six_add_lt i⟩ c0 c1

theorem matOf_yOp
    (i : Fin Tag.E6.rank) :
    matOf (yOp Tag.E6 K i 1) = toMat (Native.yMat bracketCodes formBits i) := by
  rw [yOp_eq, rootVec_neg_single, ← ofBits_true_false]
  exact matOf_rootOp ⟨12 + 2 * i, twelve_add_lt i⟩ true false

theorem toMat_xMat
    (j : ℕ) (hj : j < Tag.E6.rank) (c0 c1 : Bool) :
    toMat (Native.xMat bracketCodes formBits j c0 c1) =
      matOf (xOp Tag.E6 K ⟨j, hj⟩ (ofBits c0 c1)) :=
  (matOf_xOp ⟨j, hj⟩ c0 c1).symm

theorem toMat_nMat
    (j : ℕ) (hj : j < Tag.E6.rank) :
    toMat (Native.nMat bracketCodes formBits j) =
      matOf (xOp Tag.E6 K ⟨j, hj⟩ 1) * matOf (yOp Tag.E6 K ⟨j, hj⟩ 1) *
        matOf (xOp Tag.E6 K ⟨j, hj⟩ 1) := by
  rw [Native.nMat, toMat_mul, toMat_mul, toMat_xMat j hj, ← matOf_yOp ⟨j, hj⟩, ofBits_true_false]

theorem glMat_xUnit
    (i : Fin Tag.E6.rank) (c : K) :
    glMat (xUnit Tag.E6 K i c) = matOf (xOp Tag.E6 K i c) := rfl

theorem glMat_weylElt
    (i : Fin Tag.E6.rank) :
    glMat (weylElt Tag.E6 K i 1) =
      matOf (xOp Tag.E6 K i 1) * matOf (yOp Tag.E6 K i 1) * matOf (xOp Tag.E6 K i 1) := by
  rw [glMat_apply, coe_weylElt, inv_one, Units.val_one, neg_K, map_mul, map_mul]

theorem glMat_xL_pair
    {a : Fin TwistTag.E6.foldedTag.rank} (ha : (TwistTag.E6.orbit a).card = 2)
    {i j : Fin TwistTag.E6.tag.rank} (hi : (TwistTag.E6.perm ^ 0) (TwistTag.E6.orbitMin a) = i)
    (hj : (TwistTag.E6.perm ^ 1) (TwistTag.E6.orbitMin a) = j)
    (c : orbitField TwistTag.E6 K barHom a) :
    glMat (xL a c) = matOf (xOp Tag.E6 K i c) * matOf (xOp Tag.E6 K j (bar c)) := by
  rw [xL, coe_orbitX, ha, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil, mul_one, hi, hj]
  simp only [pow_zero, pow_one, RingHom.coe_one, id_eq, barHom_apply]
  exact map_mul glMat _ _

theorem glMat_xL_single
    {a : Fin TwistTag.E6.foldedTag.rank} (ha : (TwistTag.E6.orbit a).card = 1)
    {i : Fin TwistTag.E6.tag.rank} (hi : (TwistTag.E6.perm ^ 0) (TwistTag.E6.orbitMin a) = i)
    (c : orbitField TwistTag.E6 K barHom a) : glMat (xL a c) = matOf (xOp Tag.E6 K i c) := by
  rw [xL, coe_orbitX, ha, show List.range 1 = [0] from rfl, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, hi]
  simp only [pow_zero, RingHom.coe_one, id_eq]
  rfl

theorem glMat_nL
    {a : Fin TwistTag.E6.foldedTag.rank} {w : List (Fin Tag.E6.rank)}
    (h : TwistTag.E6.orbitWord a = w) :
    glMat (nL a) = (w.map fun i => glMat (weylElt Tag.E6 K i 1)).prod := by
  have e2 : nL a = canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).wordProd w) := by
    unfold nL TwistTag.orbitReflection
    rw [h]
    rfl
  rw [e2, canonicalRep_wordProd_charTwo, map_list_prod, List.map_map]
  rfl

private theorem glMat_letter0 :
    glMat (xL (fa 0) 1) =
    toMat (Native.mul (Native.xMat bracketCodes formBits 0 true false)
      (Native.xMat bracketCodes formBits 5 true false)) := by
  rw [glMat_xL_pair card_orbit_zero (i := ⟨0, by decide⟩) (j := ⟨5, by decide⟩) (by decide)
    (by decide), toMat_mul, toMat_xMat 0 (by decide), toMat_xMat 5 (by decide)]
  congr 3

private theorem glMat_letter1 :
    glMat (xL (fa 0) (pc (fa 0) card_orbit_zero ω)) =
    toMat (Native.mul (Native.xMat bracketCodes formBits 0 false true)
      (Native.xMat bracketCodes formBits 5 true true)) := by
  rw [glMat_xL_pair card_orbit_zero (i := ⟨0, by decide⟩) (j := ⟨5, by decide⟩) (by decide)
    (by decide), toMat_mul, toMat_xMat 0 (by decide), toMat_xMat 5 (by decide)]
  congr 3

private theorem glMat_letter2 :
    glMat (xL (fa 0) (pc (fa 0) card_orbit_zero (ω ^ 2))) =
    toMat (Native.mul (Native.xMat bracketCodes formBits 0 true true)
      (Native.xMat bracketCodes formBits 5 false true)) := by
  rw [glMat_xL_pair card_orbit_zero (i := ⟨0, by decide⟩) (j := ⟨5, by decide⟩) (by decide)
    (by decide), toMat_mul, toMat_xMat 0 (by decide), toMat_xMat 5 (by decide)]
  congr 3

private theorem glMat_letter3 :
    glMat (xL (fa 1) 1) =
    toMat (Native.mul (Native.xMat bracketCodes formBits 2 true false)
      (Native.xMat bracketCodes formBits 4 true false)) := by
  rw [glMat_xL_pair card_orbit_one (i := ⟨2, by decide⟩) (j := ⟨4, by decide⟩) (by decide)
    (by decide), toMat_mul, toMat_xMat 2 (by decide), toMat_xMat 4 (by decide)]
  congr 3

private theorem glMat_letter4 :
    glMat (xL (fa 1) (pc (fa 1) card_orbit_one ω)) =
    toMat (Native.mul (Native.xMat bracketCodes formBits 2 false true)
      (Native.xMat bracketCodes formBits 4 true true)) := by
  rw [glMat_xL_pair card_orbit_one (i := ⟨2, by decide⟩) (j := ⟨4, by decide⟩) (by decide)
    (by decide), toMat_mul, toMat_xMat 2 (by decide), toMat_xMat 4 (by decide)]
  congr 3

private theorem glMat_letter5 :
    glMat (xL (fa 1) (pc (fa 1) card_orbit_one (ω ^ 2))) =
    toMat (Native.mul (Native.xMat bracketCodes formBits 2 true true)
      (Native.xMat bracketCodes formBits 4 false true)) := by
  rw [glMat_xL_pair card_orbit_one (i := ⟨2, by decide⟩) (j := ⟨4, by decide⟩) (by decide)
    (by decide), toMat_mul, toMat_xMat 2 (by decide), toMat_xMat 4 (by decide)]
  congr 3

private theorem glMat_letter6 :
    glMat (xL (fa 2) 1) = toMat (Native.xMat bracketCodes formBits 3 true false) := by
  rw [glMat_xL_single card_orbit_two (i := ⟨3, by decide⟩) (by decide),
    toMat_xMat 3 (by decide), c_one]
  rfl

private theorem glMat_letter7 :
    glMat (xL (fa 3) 1) = toMat (Native.xMat bracketCodes formBits 1 true false) := by
  rw [glMat_xL_single card_orbit_three (i := ⟨1, by decide⟩) (by decide),
    toMat_xMat 1 (by decide), c_one]
  rfl

private theorem glMat_letter8 :
    glMat (nL (fa 0)) = toMat (Native.mul
    (Native.nMat bracketCodes formBits 0) (Native.nMat bracketCodes formBits 5)) := by
  rw [glMat_nL (w := [⟨0, by decide⟩, ⟨5, by decide⟩]) orbitWord_fa0, toMat_mul,
    toMat_nMat 0 (by decide), toMat_nMat 5 (by decide), List.map_cons, List.map_cons,
    List.map_nil, prod_two, glMat_weylElt, glMat_weylElt]

private theorem glMat_letter9 :
    glMat (nL (fa 1)) = toMat (Native.mul
    (Native.nMat bracketCodes formBits 2) (Native.nMat bracketCodes formBits 4)) := by
  rw [glMat_nL (w := [⟨2, by decide⟩, ⟨4, by decide⟩]) orbitWord_fa1, toMat_mul,
    toMat_nMat 2 (by decide), toMat_nMat 4 (by decide), List.map_cons, List.map_cons,
    List.map_nil, prod_two, glMat_weylElt, glMat_weylElt]

private theorem glMat_letter10 :
    glMat (nL (fa 2)) = toMat (Native.nMat bracketCodes formBits 3) := by
  rw [glMat_nL (w := [⟨3, by decide⟩]) orbitWord_fa2, toMat_nMat 3 (by decide), List.map_cons,
    List.map_nil, prod_one, glMat_weylElt]

private theorem glMat_letter11 :
    glMat (nL (fa 3)) = toMat (Native.nMat bracketCodes formBits 1) := by
  rw [glMat_nL (w := [⟨1, by decide⟩]) orbitWord_fa3, toMat_nMat 1 (by decide), List.map_cons,
    List.map_nil, prod_one, glMat_weylElt]

theorem letters_map_glMat :
    letters.map glMat = (Native.letters bracketCodes formBits).map toMat := by
  simp only [letters, Native.letters, List.map_toArray, List.map_cons, List.map_nil]
  rw [glMat_letter0, glMat_letter1, glMat_letter2, glMat_letter3, glMat_letter4, glMat_letter5,
    glMat_letter6, glMat_letter7, glMat_letter8, glMat_letter9, glMat_letter10, glMat_letter11]

theorem glMat_getD
    {arr : Array (ModGL Tag.E6 K)} {arr' : Array Native.Mat}
    (h : arr.map glMat = arr'.map toMat) (i : ℕ) :
    glMat (arr.getD i 1) = toMat (arr'.getD i Native.one) := by
  have e1 := getD_map glMat arr i 1
  have e2 := getD_map toMat arr' i Native.one
  rw [← e1, map_one, h, ← toMat_one, e2]

theorem glMat_slpRunG_letters
    (prog : List (List ℕ)) :
    (slpRunG letters prog).map glMat =
      (Native.slpRun (Native.letters bracketCodes formBits) prog).map toMat := by
  rw [map_slpRunG, letters_map_glMat, toMat_slpRun]

theorem glMat_genA :
    glMat genA = matA :=
  glMat_getD (glMat_slpRunG_letters fwdProg) idxA

theorem glMat_genB :
    glMat genB = matB :=
  glMat_getD (glMat_slpRunG_letters fwdProg) idxB

theorem eq_of_glMat
    {g : ModGL Tag.E6 K} {P : Native.Mat} (hg : glMat g = toMat P)
    (h : Native.eqM P Native.one = true) : g = 1 :=
  glMat_injective (by rw [hg, toMat_eq_of_eqM h, toMat_one, map_one])

theorem orderOf_eq_of_ordP
    {g : ModGL Tag.E6 K} {P : Native.Mat} (hg : glMat g = toMat P)
    {p : ℕ} [Fact p.Prime] (h : Native.ordP P p = true) : orderOf g = p := by
  simp only [Native.ordP, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine orderOf_eq_prime (eq_of_glMat (by rw [map_pow, hg, toMat_pow]) h.1) fun h1 => ?_
  have e := eqM_of_toMat_eq (P := P) (Q := Native.one) (by rw [← hg, h1, map_one, toMat_one])
  rw [h.2] at e
  exact Bool.false_ne_true e

theorem glMat_genA_mul_genB :
    glMat (genA * genB) = toMat (Native.mul nativeAB.1 nativeAB.2) := by
  rw [map_mul, glMat_genA, glMat_genB, matA, matB, toMat_mul]

private theorem glMat_signed
    (hA : genA * genA = 1) (hB : genB * genB * genB = 1)
    (l : ℕ × Bool) :
    glMat (if l.2 then img2 genA genB l.1 else (img2 genA genB l.1)⁻¹) =
      toMat (Native.signedMat nativeAB.1 nativeAB.2 l) := by
  have hAi : genA⁻¹ = genA := inv_eq_of_mul_eq_one_right hA
  have hBi : genB⁻¹ = genB * genB := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hB])
  obtain ⟨i, b⟩ := l
  by_cases hi : i = 0
  · subst hi
    cases b <;> simp [img2, Native.signedMat, hAi, glMat_genA, matA]
  · cases b <;> simp [img2, hi, Native.signedMat, hBi, glMat_genB, matB, toMat_mul]

theorem glMat_wordProd
    (hA : genA * genA = 1) (hB : genB * genB * genB = 1)
    (v : List (ℕ × Bool)) :
    glMat (wordProd (img2 genA genB) v) = toMat (Native.wordMat nativeAB.1 nativeAB.2 v) := by
  have key : ∀ acc : Native.Mat, toMat (v.foldl (fun acc l =>
      Native.mul acc (Native.signedMat nativeAB.1 nativeAB.2 l)) acc) =
        toMat acc * glMat (wordProd (img2 genA genB) v) := by
    induction v with
    | nil => intro acc; simp [wordProd]
    | cons l v ih =>
      intro acc
      rw [List.foldl_cons, ih, toMat_mul, wordProd_cons, map_mul, glMat_signed hA hB, mul_assoc]
  rw [Native.wordMat, key, toMat_one, one_mul]

theorem genA_mul_genA_of_relCheck
    {ws : List (List (ℕ × Bool))}
    (h : Native.relCheck bracketCodes formBits fwdProg idxA idxB ws = true) :
    genA * genA = 1 ∧ genB * genB * genB = 1 ∧
      ∀ v ∈ ws, Native.eqM (Native.wordMat nativeAB.1 nativeAB.2 v) Native.one = true := by
  simp only [Native.relCheck, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨eq_of_glMat ?_ h.1.1, eq_of_glMat ?_ h.1.2, h.2⟩
  · rw [map_mul, glMat_genA, matA, toMat_mul]
    rfl
  · rw [map_mul, map_mul, glMat_genB, matB, toMat_mul, toMat_mul]
    rfl

theorem relators_hold
    (ws : List (List (ℕ × Bool)))
    (h : Native.relCheck bracketCodes formBits fwdProg idxA idxB ws = true) :
    ∀ v ∈ ws, wordProd (img2 genA genB) v = 1 := by
  obtain ⟨hA, hB, hw⟩ := genA_mul_genA_of_relCheck h
  exact fun v hv => eq_of_glMat (glMat_wordProd hA hB v) (hw v hv)

theorem relators_hold_std
    (ws : List (List (ℕ × Bool)))
    (h : Native.relCheck bracketCodes formBits fwdProg idxA idxB ws = true) :
    ∀ v ∈ ws, wordProd (img2 stdA stdB) v = 1 := fun v hv =>
  Subtype.ext (by rw [coe_wordProd, img2_stdA_stdB, relators_hold ws h v hv]; rfl)

theorem check_eq_true :
    Native.check bracketCodes formBits fwdProg idxA idxB bwdProg letterIdx = true :=
  Certificates.certificate10004.1

private theorem check_parts :
    (∀ j < 12, Native.eqM ((Native.slpRun #[nativeAB.1, nativeAB.2] bwdProg).getD
      (letterIdx.getD j 0) Native.one) ((Native.letters bracketCodes formBits).getD j Native.one) =
        true) ∧
      Native.ordP nativeAB.1 2 = true ∧ Native.ordP nativeAB.2 3 = true ∧
        Native.ordP (Native.mul nativeAB.1 nativeAB.2) 19 = true := by
  have h := check_eq_true
  simp only [Native.check, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem orderOf_genA :
    orderOf genA = 2 :=
  orderOf_eq_of_ordP glMat_genA check_parts.2.1

theorem orderOf_genB :
    orderOf genB = 3 :=
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  orderOf_eq_of_ordP glMat_genB check_parts.2.2.1

theorem orderOf_genA_mul_genB :
    orderOf (genA * genB) = 19 :=
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  orderOf_eq_of_ordP glMat_genA_mul_genB check_parts.2.2.2

theorem closure_genA_genB :
    Subgroup.closure {genA, genB} = stdGroup := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) (stdGroup_le_of_letters fun j hj => ?_)
  · rintro _ (rfl | rfl)
    exacts [genA_mem, genB_mem]
  · set H := Subgroup.closure ({genA, genB} : Set (ModGL Tag.E6 K))
    have hAB : (#[genA, genB] : Array (ModGL Tag.E6 K)).map glMat =
        (#[nativeAB.1, nativeAB.2] : Array Native.Mat).map toMat := by
      simp only [List.map_toArray, List.map_cons, List.map_nil, glMat_genA, glMat_genB, matA, matB]
    have hv := glMat_getD (by rw [map_slpRunG, hAB, toMat_slpRun]) (letterIdx.getD j 0)
      (arr := slpRunG #[genA, genB] bwdProg)
      (arr' := Native.slpRun #[nativeAB.1, nativeAB.2] bwdProg)
    have hl := glMat_getD letters_map_glMat j
    have e : letters.getD j 1 = (slpRunG #[genA, genB] bwdProg).getD (letterIdx.getD j 0) 1 :=
      glMat_injective (by rw [hl, hv, toMat_eq_of_eqM (check_parts.1 j hj)])
    rw [e]
    refine getD_mem _ (slpRunG_mem _ (fun x hx => ?_) _) _
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)]

theorem twistedE6_two_standard_generators :
    genA ∈ stdGroup ∧ genB ∈ stdGroup ∧ Subgroup.closure {genA, genB} = stdGroup ∧
      orderOf genA = 2 ∧ orderOf genB = 3 ∧ orderOf (genA * genB) = 19 :=
  ⟨genA_mem, genB_mem, closure_genA_genB, orderOf_genA, orderOf_genB, orderOf_genA_mul_genB⟩

open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

theorem orderOf_wordProd
    (v : List (ℕ × Bool)) {p : ℕ} [Fact p.Prime]
    (h : Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 v) p = true) :
    orderOf (wordProd (img2 genA genB) v) = p := by
  have hA : genA * genA = 1 := by rw [← pow_two, ← orderOf_genA, pow_orderOf_eq_one]
  have hB : genB * genB * genB = 1 := by rw [← pow_three', ← orderOf_genB, pow_orderOf_eq_one]
  exact orderOf_eq_of_ordP (glMat_wordProd hA hB v) h

theorem orderOf_ababb :
    orderOf (wordProd (img2 genA genB) [(0, true), (1, true), (0, true), (1, true), (1, true)]) =
      5 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_wordProd _ Certificates.certificate10004.2

theorem closure_stdA_stdB :
    Subgroup.closure {stdA, stdB} = (⊤ : Subgroup stdGroup) := by
  apply Subgroup.map_injective stdGroup.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Set.image_pair]
  exact closure_genA_genB

theorem orderOf_stdA :
    orderOf stdA = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_genA

theorem orderOf_stdB :
    orderOf stdB = 3 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_genB

theorem orderOf_stdA_mul_stdB :
    orderOf (stdA * stdB) = 19 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_genA_mul_genB

end CFSG.LieType.Chevalley.C2E6Std.MatrixModel
