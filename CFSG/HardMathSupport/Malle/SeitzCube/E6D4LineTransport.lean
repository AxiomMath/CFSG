module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6D4LineData
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeKernel
public import CFSG.RankThree.PartOne.KE6.Phi3Lattice
public import CFSG.RankThree.PartOne.KE6.Phi3Torus

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus)
open CFSG.RankThree.PartOne.KE6 (phi3N)
open CFSG.RankThree.Classical2 (torusRootKernel torusRootKernel_rootDiagUnit)
open scoped Matrix

section Weyl

variable {L : Type} [Field L]

theorem rootChar_weyl_smul (a : Fin Tag.E6.rank → Lˣ) (w : WeylGroup Tag.E6)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar a (w • v) = ∏ i, rootChar a (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ^ v i := by
  have hv : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := by
    rw [← weylMatrix_mulVec]
    ext k
    simp [Matrix.mulVec, dotProduct, weylMatrix_apply, Finset.sum_apply, mul_comm]
  have hsum : ∀ s : Finset (Fin Tag.E6.rank), rootChar a
      (∑ i ∈ s, v i • (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) =
        ∏ i ∈ s, rootChar a (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ^ v i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [rootChar_zero]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, rootChar_add, rootChar_zsmul, ih]
  rw [hv, hsum]

theorem exists_rootChar_weyl (a : Fin Tag.E6.rank → Lˣ) (w : WeylGroup Tag.E6) :
    ∃ a' : Fin Tag.E6.rank → Lˣ, ∀ v, rootChar a' v = rootChar a (w • v) :=
  ⟨fun i => rootChar a (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)), fun v =>
    (rootChar_weyl_smul a w v).symm ▸ rfl⟩

theorem rootChar_weyl_smul_pow (a : Fin Tag.E6.rank → Lˣ) (w : WeylGroup Tag.E6) (q : ℕ)
    (h : ∀ i, rootChar a (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
      rootChar a (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ^ q) (v : Fin Tag.E6.rank → ℤ) :
    rootChar a (w • v) = rootChar a v ^ q := by
  have h1 := rootChar_weyl_smul a 1 v
  rw [one_smul] at h1
  rw [rootChar_weyl_smul, h1]
  simp only [one_smul, h, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

end Weyl

section Main

set_option linter.unusedSectionVars false

variable {Ω : Type} [Field Ω]

@[expose] def e6D4m : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word e6D4M)

@[expose] def e6D4wp : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word e6D4Wp)

@[expose] def e6D4w (s : Fin 3) : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd (e6Word (e6D4Ws s))

theorem e6D4_comm_words : ∀ j : Fin 6,
    (e6D4M ++ e6D4Wp).foldr (reflect Tag.E6) (Pi.single j 1) =
      ((List.replicate 4 [0, 1, 2, 3, 4, 5]).flatten ++ e6D4M).foldr (reflect Tag.E6)
        (Pi.single j 1) := by
  decide +kernel

theorem e6D4m_mul_wp : e6D4m * e6D4wp = CFSG.RankThree.Lattice.e6T3W * e6D4m := by
  have h4 : CFSG.RankThree.Lattice.e6T3W = (coxeterSystem Tag.E6).wordProd
      (e6Word (List.replicate 4 [0, 1, 2, 3, 4, 5]).flatten) := by
    rw [CFSG.RankThree.Lattice.e6T3W_eq_wordProd]
    rfl
  have e1 : e6D4m * e6D4wp = (coxeterSystem Tag.E6).wordProd (e6Word (e6D4M ++ e6D4Wp)) :=
    (CoxeterSystem.wordProd_append _ _ _).symm
  have e2 : (coxeterSystem Tag.E6).wordProd (e6Word (List.replicate 4 [0, 1, 2, 3, 4, 5]).flatten) *
      e6D4m = (coxeterSystem Tag.E6).wordProd (e6Word
        ((List.replicate 4 [0, 1, 2, 3, 4, 5]).flatten ++ e6D4M)) :=
    (CoxeterSystem.wordProd_append _ _ _).symm
  rw [h4, e1, e2]
  refine eq_of_smul_single_eq fun j => ?_
  rw [wordProd_e6Word_smul, wordProd_e6Word_smul]
  exact e6D4_comm_words j

theorem exists_conj_rootDiagUnit (a : Fin Tag.E6.rank → Ωˣ) (w : WeylGroup Tag.E6) :
    ∃ a' : Fin Tag.E6.rank → Ωˣ,
      rootDiagUnit Tag.E6 a' = canonicalRep (coxeterSystem Tag.E6) Ω w * rootDiagUnit Tag.E6 a *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ ∧
      ∀ v, rootChar a' v = rootChar a (w⁻¹ • v) := by
  obtain ⟨a', ha'⟩ := exists_rootChar_weyl a w⁻¹
  exact ⟨a', (rootDiagUnit_eq_conj_canonicalRep_iff a' a w).2 fun v => by
    rw [ha', inv_smul_smul], ha'⟩

theorem rootCharKernel_of_rootChar {a a' : Fin Tag.E6.rank → Ωˣ} (w : WeylGroup Tag.E6)
    (h : ∀ v, rootChar a' v = rootChar a (w⁻¹ • v)) :
    rootCharKernel a' = (w • ·) '' rootCharKernel a := by
  ext v
  constructor
  · rintro ⟨hr, h1⟩
    refine ⟨w⁻¹ • v, ⟨IsRoot.smul hr w⁻¹, ?_⟩, smul_inv_smul w v⟩
    rwa [← h]
  · rintro ⟨u, ⟨hu, h1⟩, rfl⟩
    refine ⟨IsRoot.smul hu w, ?_⟩
    rw [h, inv_smul_smul]
    exact h1


theorem e6D4_rootChar_twist {ζ : Ωˣ} {p q x y : ℕ} (hζ : orderOf ζ = p) (hq : p ∣ q ^ 2 + q + 1)
    (i : Fin Tag.E6.rank) :
    rootChar (e6KerChar ζ q x y) (e6D4wp • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
      rootChar (e6KerChar ζ q x y) (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ^ q := by
  rw [rootChar_e6KerChar, rootChar_e6KerChar]
  have hw : e6D4wp • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
      e6D4Wp.foldr (reflect Tag.E6) (Pi.single i 1) := wordProd_e6Word_smul _ _
  rw [hw]
  obtain ⟨h0P, h0Q⟩ := e6D4_twist 0 (by decide) i
  obtain ⟨h1P, h1Q⟩ := e6D4_twist 1 (by decide) i
  have hdvd : (orderOf ζ : ℤ) ∣ e6KerExp (q : ℤ) x y (e6D4Wp.foldr (reflect Tag.E6) (Pi.single i 1)) -
      e6KerExp (q : ℤ) x y (Pi.single i 1) * q := by
    have h : (p : ℤ) ∣ (q : ℤ) ^ 2 + q + 1 := by exact_mod_cast hq
    have e : e6KerExp (q : ℤ) x y (e6D4Wp.foldr (reflect Tag.E6) (Pi.single i 1)) -
        e6KerExp (q : ℤ) x y (Pi.single i 1) * q =
        ((q : ℤ) ^ 2 + q + 1) * (-((x : ℤ) * e6KerQ 0 (Pi.single i 1) +
          (y : ℤ) * e6KerQ 1 (Pi.single i 1))) := by
      unfold e6KerExp
      rw [h0P, h0Q, h1P, h1Q]
      ring
    rw [e, hζ]
    exact Dvd.dvd.mul_right h _
  have h1 := orderOf_dvd_iff_zpow_eq_one.1 hdvd
  rw [zpow_sub, mul_inv_eq_one] at h1
  rw [← zpow_natCast, ← zpow_mul]
  exact h1

theorem coe_e6D4RootsF : (↑e6D4RootsF : Set (Fin Tag.E6.rank → ℤ)) =
    parabolicRoots Tag.E6 d4Support := by
  ext v
  simp only [e6D4RootsF, Finset.coe_filter, Set.mem_ofPred_eq, mem_rootFinset, parabolicRoots,
    d4Support]
  constructor
  · rintro ⟨hr, h0, h5⟩
    refine ⟨hr, fun i hi => ?_⟩
    simp only [not_and_or, not_not] at hi
    rcases hi with rfl | rfl
    exacts [h0, h5]
  · rintro ⟨hr, h⟩
    exact ⟨hr, h 0 (by simp), h 5 (by simp)⟩

theorem e6D4_smul_smul (s : Fin 3) (v : Fin Tag.E6.rank → ℤ) :
    e6D4w s • (e6D4m • v) = (e6Word (e6D4Ws s ++ e6D4M)).foldr (reflect Tag.E6) v := by
  show _ = (e6Word (e6D4Ws s) ++ e6Word e6D4M).foldr (reflect Tag.E6) v
  rw [List.foldr_append, e6D4w, e6D4m, wordProd_e6Word_smul, wordProd_e6Word_smul]

theorem e6D4Line_transport [IsAlgClosed Ω] {Fr : Ω →+* Ω} {p q x y : ℕ} {ζ : Ωˣ} {s : Fin 3}
    (hFr : ∀ c, Fr c = c ^ q) (hp : p.Prime) (hp3 : p ≠ 3) (hζ : orderOf ζ = p)
    (hq : p ∣ q ^ 2 + q + 1) (hx : ¬ p ∣ x)
    (hs : (y : ZMod p) = (x : ZMod p) * (q : ZMod p) ^ (s : ℕ)) :
    canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * rootDiagUnit Tag.E6 (e6KerChar ζ q x y) *
        (canonicalRep (coxeterSystem Tag.E6) Ω e6D4m)⁻¹ ∈ twistedTorus (phi3N Ω) Fr ∧
    (e6D4w s • ·) '' torusRootKernel (canonicalRep (coxeterSystem Tag.E6) Ω e6D4m *
        rootDiagUnit Tag.E6 (e6KerChar ζ q x y) *
        (canonicalRep (coxeterSystem Tag.E6) Ω e6D4m)⁻¹) = parabolicRoots Tag.E6 d4Support := by
  obtain ⟨a', hconj, hchi⟩ := exists_conj_rootDiagUnit (Ω := Ω) (e6KerChar ζ q x y) e6D4m
  rw [← hconj]
  constructor
  · rw [CFSG.RankThree.PartOne.KE6.mem_twistedTorus_rootDiagUnit_iff3 hFr,
      CFSG.RankThree.PartOne.KE6.mem_ker_monomialHom_iff_forall]
    intro μ
    rw [CFSG.RankThree.PartOne.KE6.rootChar_phi3Matrix_mulVec, hchi, hchi]
    have hum : CFSG.RankThree.Lattice.e6T3W * e6D4m = e6D4m * e6D4wp := e6D4m_mul_wp.symm
    have hcomm : e6D4m⁻¹ * CFSG.RankThree.Lattice.e6T3W = e6D4wp * e6D4m⁻¹ :=
      calc e6D4m⁻¹ * CFSG.RankThree.Lattice.e6T3W
          = e6D4m⁻¹ * (CFSG.RankThree.Lattice.e6T3W * e6D4m) * e6D4m⁻¹ := by group
        _ = e6D4wp * e6D4m⁻¹ := by rw [hum]; group
    rw [← mul_smul, hcomm, mul_smul,
      rootChar_weyl_smul_pow _ e6D4wp q (e6D4_rootChar_twist hζ hq)]
    exact mul_inv_cancel _
  · rw [torusRootKernel_rootDiagUnit, rootCharKernel_of_rootChar e6D4m hchi,
      rootCharKernel_e6KerChar_mixed hp hp3 hζ hq hx hs, Set.image_image]
    simp only [e6D4_smul_smul]
    have hU : e6BlockRoots 2 ∪ e6MixedRoots s = ↑(e6BlockRootsF 2 ∪ e6MixedRootsF s) := by
      simp [e6BlockRoots, e6MixedRoots]
    rw [hU, ← Finset.coe_image, show (fun v => (e6Word (e6D4Ws s ++ e6D4M)).foldr (reflect Tag.E6) v) =
      fun v => (e6D4Ws s ++ e6D4M).foldr (reflect Tag.E6) v from rfl, e6D4_image, coe_e6D4RootsF]

end Main

end CFSG.HardMathSupport.Malle.SeitzCube
