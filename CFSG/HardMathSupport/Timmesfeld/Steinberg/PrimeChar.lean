module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
public import Certificates.Data.CFSGNative.Timmesfeld.PrimeStein

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag} {p : ℕ}

@[expose] def Zp (p : ℕ) : Type := Multiplicative (ZMod p)

instance (p : ℕ) : CommGroup (Zp p) := inferInstanceAs (CommGroup (Multiplicative (ZMod p)))

@[expose] def Zp.ofAdd (x : ZMod p) : Zp p := Multiplicative.ofAdd x

@[expose] def Zp.toAdd (x : Zp p) : ZMod p := Multiplicative.toAdd x

theorem Zp.ofAdd_add (x y : ZMod p) : Zp.ofAdd (x + y) = Zp.ofAdd x * Zp.ofAdd y := rfl

theorem Zp.ofAdd_zero : Zp.ofAdd (0 : ZMod p) = 1 := rfl

theorem Zp.ofAdd_toAdd (x : Zp p) : Zp.ofAdd (Zp.toAdd x) = x := rfl

theorem Zp.ofAdd_eq_ofAdd_iff {x y : ZMod p} : Zp.ofAdd x = Zp.ofAdd y ↔ x = y :=
  ⟨fun h => Multiplicative.ofAdd.injective h, fun h => by rw [h]⟩

theorem Zp.ofAdd_eq_one {x : ZMod p} : Zp.ofAdd x = 1 ↔ x = 0 :=
  ⟨fun h => Multiplicative.ofAdd.injective h, fun h => by rw [h]; rfl⟩

@[expose] def pPairing (b : Fin τ.rank → ZMod p) (v : Fin τ.rank → ℤ) : ZMod p :=
  ∑ j, b j * ((v j : ℤ) : ZMod p)

theorem pPairing_add (b : Fin τ.rank → ZMod p) (u v : Fin τ.rank → ℤ) :
    pPairing b (u + v) = pPairing b u + pPairing b v := by
  simp only [pPairing, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]

theorem pPairing_zero (b : Fin τ.rank → ZMod p) : pPairing b 0 = 0 := by
  simp [pPairing]

theorem pPairing_zsmul_single (b : Fin τ.rank → ZMod p) (c : ℤ) (k : Fin τ.rank) :
    pPairing b (c • (Pi.single k 1 : Fin τ.rank → ℤ)) = b k * (c : ZMod p) := by
  rw [pPairing, Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
  simp

@[expose] def pChar (b : Fin τ.rank → ZMod p) :
    Multiplicative (Fin τ.rank → ℤ) →* Zp p where
  toFun v := Zp.ofAdd (pPairing b (Multiplicative.toAdd v))
  map_one' := by simp [pPairing_zero, Zp.ofAdd_zero]
  map_mul' u v := by simp [pPairing_add, Zp.ofAdd_add]

theorem pChar_apply (b : Fin τ.rank → ZMod p) (v : Fin τ.rank → ℤ) :
    pChar b (Multiplicative.ofAdd v) = Zp.ofAdd (pPairing b v) :=
  rfl

theorem eq_pChar (χ : Multiplicative (Fin τ.rank → ℤ) →* Zp p) :
    χ = pChar fun j => Zp.toAdd (χ (Multiplicative.ofAdd (Pi.single j 1))) := by
  refine lattice_hom_ext fun j => ?_
  rw [pChar_apply]
  have h := pPairing_zsmul_single
    (fun k => Zp.toAdd (χ (Multiplicative.ofAdd (Pi.single k 1)))) 1 j
  rw [one_smul] at h
  rw [h]
  simp [Zp.ofAdd_toAdd]

theorem mem_kernelRoots_pChar {b : Fin τ.rank → ZMod p} {α : Fin τ.rank → ℤ} :
    α ∈ kernelRoots (pChar b) ↔ IsRoot τ α ∧ pPairing b α = 0 := by
  refine Iff.trans Iff.rfl (and_congr_right fun _ => ?_)
  rw [pChar_apply, Zp.ofAdd_eq_one]

@[expose] def pReflect (i : Fin τ.rank) (b : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  fun j => b j - (τ.cartan i j : ZMod p) * b i

theorem pChar_pReflect
    (i : Fin τ.rank) (b : Fin τ.rank → ZMod p) (v : Fin τ.rank → ℤ) :
    pChar (pReflect i b) (Multiplicative.ofAdd v) =
      pChar b (Multiplicative.ofAdd (simple τ i • v)) := by
  rw [← charComp_apply]
  refine congrArg (fun f => f (Multiplicative.ofAdd v)) (lattice_hom_ext
    (f := pChar (pReflect i b)) (g := charComp (pChar b) (simple τ i)) fun j => ?_)
  rw [charComp_apply, simple_smul, pChar_apply, pChar_apply]
  have hs : ∑ k, τ.cartan i k * (Pi.single j 1 : Fin τ.rank → ℤ) k = τ.cartan i j := by
    simp [Pi.single_apply]
  have hr : reflect τ i (Pi.single j 1) = (1 : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ) +
      (-τ.cartan i j) • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    rw [reflect, hs, one_smul, neg_smul, ← sub_eq_add_neg]
  have h1 : pPairing (pReflect i b) (Pi.single j 1) = pReflect i b j := by
    have := pPairing_zsmul_single (pReflect i b) 1 j
    rwa [one_smul, Int.cast_one, mul_one] at this
  rw [h1, hr, pPairing_add, pPairing_zsmul_single, pPairing_zsmul_single]
  congr 1
  simp only [pReflect, Int.cast_one, mul_one, Int.cast_neg]
  ring

@[expose] def pAct (ω : List (Fin τ.rank)) (b : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  ω.foldr pReflect b

theorem pChar_pAct
    (ω : List (Fin τ.rank)) (b : Fin τ.rank → ZMod p) (v : Fin τ.rank → ℤ) :
    pChar (pAct ω b) (Multiplicative.ofAdd v) =
      pChar b (Multiplicative.ofAdd (((coxeterSystem τ).wordProd ω)⁻¹ • v)) := by
  induction ω generalizing v with
  | nil => simp [pAct]
  | cons i ω ih =>
    change pChar (pReflect i (pAct ω b)) (Multiplicative.ofAdd v) = _
    rw [pChar_pReflect, ih, CoxeterSystem.wordProd_cons, _root_.mul_inv_rev, mul_smul,
      (coxeterSystem τ).inv_simple]

@[expose] def vecP (p : ℕ) (l : List ℕ) : Fin τ.rank → ZMod p :=
  fun j => ((l.getD j 0 : ℕ) : ZMod p)

@[expose] def negCartanRowP (τ : Tag) (p : ℕ) (i : ℕ) : List ℕ :=
  (List.finRange τ.rank).map fun j =>
    if h : i < τ.rank then ((-(τ.cartan ⟨i, h⟩ j)) % (p : ℤ)).toNat else 0

@[expose] def negCartanRowsP (τ : Tag) (p : ℕ) : List (List ℕ) :=
  (List.range τ.rank).map (negCartanRowP τ p)

theorem length_negCartanRowP (τ : Tag) (p i : ℕ) : (negCartanRowP τ p i).length = τ.rank := by
  simp [negCartanRowP]

theorem negCartanRowsP_getD {i : ℕ} (hi : i < τ.rank) :
    (negCartanRowsP τ p).getD i [] = negCartanRowP τ p i := getD_range_map' _ _ hi

theorem length_reflLP {i : ℕ} (hi : i < τ.rank) {b : List ℕ} (hb : b.length = τ.rank) :
    (PrimeSteinNative.reflL p (negCartanRowsP τ p) i b).length = τ.rank := by
  rw [PrimeSteinNative.reflL, PrimeSteinNative.reflAux, List.length_zipWith, negCartanRowsP_getD hi, length_negCartanRowP, hb,
    min_self]

theorem length_actLP {word : List ℕ} (hw : ∀ i ∈ word, i < τ.rank) {b : List ℕ}
    (hb : b.length = τ.rank) : (PrimeSteinNative.actL p (negCartanRowsP τ p) word b).length = τ.rank := by
  induction word with
  | nil => simpa [PrimeSteinNative.actL] using hb
  | cons i w ih =>
    have hi : i < τ.rank := hw i (by simp)
    have := ih (fun k hk => hw k (by simp [hk]))
    simpa [PrimeSteinNative.actL] using length_reflLP hi (by simpa [PrimeSteinNative.actL] using this)

theorem zmodP_aux [NeZero p] (A : ℤ) (x y : ℕ) :
    ((((x + ((-A) % (p : ℤ)).toNat * y) % p : ℕ)) : ZMod p) =
      (x : ZMod p) - (A : ZMod p) * (y : ZMod p) := by
  have hmod : (((-A) % (p : ℤ) : ℤ) : ZMod p) = -((A : ℤ) : ZMod p) := by
    have := ZMod.intCast_mod (-A) p
    rw [Int.cast_neg] at this
    exact this
  have key : ((((-A) % (p : ℤ)).toNat : ℕ) : ZMod p) = -((A : ℤ) : ZMod p) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne p)),
      hmod]
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, key]
  exact aux_ring (R := ZMod p) _ _ _

theorem vecP_reflL [NeZero p] (i : Fin τ.rank) {b : List ℕ} (hb : b.length = τ.rank) :
    vecP (τ := τ) p (PrimeSteinNative.reflL p (negCartanRowsP τ p) i b) = pReflect i (vecP (τ := τ) p b) := by
  funext j
  simp only [vecP, pReflect, PrimeSteinNative.reflL, PrimeSteinNative.reflAux, negCartanRowsP_getD i.2]
  have hj : (j : ℕ) < (negCartanRowP τ p i).length := by
    rw [length_negCartanRowP]; exact j.2
  have hj' : (j : ℕ) < b.length := by rw [hb]; exact j.2
  rw [List.getD_eq_getElem _ _ (by simp [hj, hj']), List.getElem_zipWith,
    ← List.getD_eq_getElem _ 0 hj', ← List.getD_eq_getElem _ 0 hj]
  have hneg : (negCartanRowP τ p i).getD j 0 = ((-(τ.cartan i j)) % (p : ℤ)).toNat := by
    simp only [negCartanRowP]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
    simp [i.2]
  rw [hneg]
  exact zmodP_aux (τ.cartan i j) _ _

theorem vecP_actL [NeZero p] {word : List ℕ} (hw : ∀ i ∈ word, i < τ.rank) {b : List ℕ}
    (hb : b.length = τ.rank) :
    vecP (τ := τ) p (PrimeSteinNative.actL p (negCartanRowsP τ p) word b) =
      pAct (toFinWord3 word) (vecP (τ := τ) p b) := by
  induction word with
  | nil => simp [PrimeSteinNative.actL, toFinWord3, pAct]
  | cons i w ih =>
    have hi : i < τ.rank := hw i (by simp)
    have hw' : ∀ k ∈ w, k < τ.rank := fun k hk => hw k (by simp [hk])
    have h1 := ih hw'
    have hlen := length_actLP (p := p) hw' hb
    simp only [PrimeSteinNative.actL, List.foldr_cons] at *
    rw [vecP_reflL ⟨i, hi⟩ hlen, h1]
    simp [toFinWord3, hi, pAct]

open RootCertificate

end CFSG.HardMathSupport.Timmesfeld.Steinberg
