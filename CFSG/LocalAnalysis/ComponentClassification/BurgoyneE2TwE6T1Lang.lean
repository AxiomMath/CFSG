module

public import CFSG.LieType.AlgebraicGroups.E6RationalGraphCoset
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionFixedComponents

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Signs

variable {τ : Tag} {L : Type} [Field L]

@[expose] def signOfBits (b : Fin τ.rank → Bool) : Fin τ.rank → Lˣ :=
  fun j => if b j then -1 else 1

variable (τ) in
@[expose] def bitsStep (i : Fin τ.rank) (b : Fin τ.rank → Bool) : Fin τ.rank → Bool :=
  fun j => xor (b j) (b i && decide (τ.cartan i j % 2 ≠ 0))

theorem signOfBits_zpow (b : Fin τ.rank → Bool) (i : Fin τ.rank) (n : ℤ) :
    (signOfBits (L := L) b i) ^ n = if b i && decide (n % 2 ≠ 0) then -1 else 1 := by
  unfold signOfBits
  cases b i
  · simp
  · rcases Int.even_or_odd n with h | h
    · have h2 : n % 2 = 0 := Int.even_iff.1 h
      simp [h.neg_one_zpow, h2]
    · have h2 : n % 2 = 1 := Int.odd_iff.1 h
      simp [h.neg_one_zpow, h2]

theorem weylElt_conj_signOfBits
    (i : Fin τ.rank)
    (b : Fin τ.rank → Bool) :
    weylElt τ L i 1 * rootDiagUnit τ (signOfBits b) * (weylElt τ L i 1)⁻¹ =
      rootDiagUnit τ (signOfBits (bitsStep τ i b)) := by
  rw [weylElt_conj_rootDiagUnit]
  congr 1
  funext j
  rw [signOfBits_zpow]
  have hpar : (-τ.cartan i j) % 2 = 0 ↔ τ.cartan i j % 2 = 0 := by omega
  unfold signOfBits bitsStep
  by_cases hA : τ.cartan i j % 2 = 0
  · have hA' : (-τ.cartan i j) % 2 = 0 := hpar.2 hA
    cases b j <;> cases b i <;> simp [hA, hA']
  · cases b j <;> cases b i <;> simp [hA]

theorem wordWeylMatrix_conj_signOfBits
    (l : List (Fin τ.rank)) (b : Fin τ.rank → Bool) :
    wordWeylMatrix τ L l * rootDiagUnit τ (signOfBits b) * (wordWeylMatrix τ L l)⁻¹ =
      rootDiagUnit τ (signOfBits (l.foldl (fun b i => bitsStep τ i b) b)) := by
  induction l generalizing b with
  | nil => simp [wordWeylMatrix]
  | cons i l ih =>
    have e : wordWeylMatrix τ L (i :: l) = wordWeylMatrix τ L l * weylElt τ L i 1 := by
      simp [wordWeylMatrix, List.reverse_cons, List.map_append, List.prod_append]
    rw [e, List.foldl_cons, ← ih (bitsStep τ i b), ← weylElt_conj_signOfBits]
    group

theorem signMaskTuple_eq_signOfBits (m : ℕ) :
    signMaskTuple τ L m = signOfBits (fun j => decide (m / 2 ^ (j : ℕ) % 2 = 1)) := by
  funext j
  unfold signMaskTuple signOfBits
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ (j : ℕ)) with h | h <;> simp [h]

end Signs

@[expose] def e6W0Word : List (Fin TwistTag.E6.tag.rank) :=
  ([0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1,
    5, 4, 3, 2, 0] : List (Fin 6))

@[expose] def e6Bits20 : Fin TwistTag.E6.tag.rank → Bool :=
  fun j => decide (20 / 2 ^ (j : ℕ) % 2 = 1)

theorem e6W0_bits :
    e6W0Word.foldl (fun b i => bitsStep TwistTag.E6.tag i b) e6Bits20 = e6Bits20 := by
  decide +kernel

theorem e6Bits20_perm (i : Fin TwistTag.E6.tag.rank) :
    e6Bits20 (TwistTag.E6.perm.symm i) = e6Bits20 i := by
  revert i
  decide +kernel


theorem e6W0_root_check : ∀ j : Fin TwistTag.E6.tag.rank, List.ofFn (e6Certificate.root
    (applyWordIdx e6Certificate e6W0Word (TwistTag.E6.perm j))) =
      List.ofFn (-Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
  decide +kernel

theorem thetaMap_e6W0
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    thetaMap (ToralSign.wordElt TwistTag.E6.tag e6W0Word) TwistTag.E6.perm v = -v := by
  have hs : ∀ i : Fin TwistTag.E6.tag.rank,
      thetaMap (ToralSign.wordElt TwistTag.E6.tag e6W0Word) TwistTag.E6.perm (Pi.single i 1) =
        -Pi.single i 1 := by
    intro i
    obtain ⟨hl, hr⟩ := root_fin e6Certificate_check (TwistTag.E6.perm i)
    obtain ⟨-, he⟩ := applyWordIdx_spec e6Certificate_check e6W0Word hl
    have hr' : (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        e6Certificate.root (TwistTag.E6.perm i) := hr.symm
    rw [thetaMap, permLattice_single, hr']
    exact (he.symm.trans (List.ofFn_injective (e6W0_root_check i)) :)
  let φ : (Fin TwistTag.E6.tag.rank → ℤ) →+ (Fin TwistTag.E6.tag.rank → ℤ) :=
    { toFun := thetaMap (ToralSign.wordElt TwistTag.E6.tag e6W0Word) TwistTag.E6.perm
      map_zero' := by
        have h := thetaMap_zsmul (ω := ToralSign.wordElt TwistTag.E6.tag e6W0Word)
          (ρ := TwistTag.E6.perm) 0 0
        simpa using h
      map_add' := thetaMap_add }
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  change φ v = -v
  conv_lhs => rw [hv]
  rw [map_sum]
  conv_rhs => rw [hv]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  change v i • thetaMap _ _ (Pi.single i 1) = _
  rw [hs i, smul_neg]

section Lang

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [CharP L p]

theorem d20_eq_signOfBits :
    rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) =
      rootDiagUnit TwistTag.E6.tag (signOfBits e6Bits20) := by
  rw [signCharTuple_signMaskChar, signMaskTuple_eq_signOfBits]
  rfl

theorem wordWeylMatrix_e6W0_conj_d20 :
    wordWeylMatrix TwistTag.E6.tag L e6W0Word *
        rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) *
        (wordWeylMatrix TwistTag.E6.tag L e6W0Word)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) := by
  rw [d20_eq_signOfBits, wordWeylMatrix_conj_signOfBits, e6W0_bits]

theorem diagramMap_conj_d20 :
    diagramMap TwistTag.E6 L *
        rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) *
        (diagramMap TwistTag.E6 L)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) := by
  rw [d20_eq_signOfBits, diagramMap_mul_rootDiagUnit, mul_inv_cancel_right]
  congr 1
  funext i
  unfold signOfBits
  rw [e6Bits20_perm]

theorem frobTwistGL_d20 (e : ℕ) :
    frobTwistGL TwistTag.E6.tag L p e (diagramMap TwistTag.E6 L)
        (rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20))) =
      rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) := by
  rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit p e (signCharTuple_sign _),
    diagramMap_conj_d20]


theorem frobTwistGL_mem_toralCentralizer_d20 [IsAlgClosed L] (e : ℕ)
    {g : ModGL TwistTag.E6.tag L}
    (hg : g ∈ toralCentralizer TwistTag.E6.tag L
      (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20))) :
    frobTwistGL TwistTag.E6.tag L p e (diagramMap TwistTag.E6 L) g ∈ toralCentralizer
      TwistTag.E6.tag L (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) := by
  obtain ⟨hgG, hgc⟩ := mem_toralCentralizer.1 hg
  refine mem_toralCentralizer.2 ⟨?_, ?_⟩
  · have h := frobTwistGL_diagramMap_pow_mem_adjointGroup (p := p) e 1 hgG
    rwa [pow_one] at h
  · rw [← frobTwistGL_d20 (p := p) e, ← map_inv, ← map_mul, ← map_mul, hgc]

theorem exists_e6_untwist [IsAlgClosed L] (hp2 : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e) :
    ∃ g₁ ∈ toralCentralizer TwistTag.E6.tag L
        (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)),
      g₁ * (frobTwistGL TwistTag.E6.tag L p e (diagramMap TwistTag.E6 L) g₁)⁻¹ =
        wordWeylMatrix TwistTag.E6.tag L e6W0Word := by
  obtain ⟨⟨hM, -, hsm, -⟩, -⟩ := connected_exceptional_toral_centralizer_Lang p hp2 L
    TwistTag.E6.tag (Or.inr (Or.inr (Or.inl rfl)))
    (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) (signCharTuple_sign _)
  have hN : wordWeylMatrix TwistTag.E6.tag L e6W0Word ∈ toralCentralizer TwistTag.E6.tag L
      (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) := by
    refine mem_toralCentralizer.2 ⟨wordWeylMatrix_mem_adjointGroup _, ?_⟩
    have h := wordWeylMatrix_e6W0_conj_d20 (L := L)
    set N := wordWeylMatrix TwistTag.E6.tag L e6W0Word
    set d := rootDiagUnit TwistTag.E6.tag
      (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20))
    calc d * N * d⁻¹ = (N * d * N⁻¹) * N * d⁻¹ := by rw [h]
      _ = N := by group
  obtain ⟨z, hz, hzN⟩ := exists_eq_inv_mul_frobTwistGL p he (diagramMap TwistTag.E6 L) hM hsm
    (fun g hg => frobTwistGL_mem_toralCentralizer_d20 e hg) hN
  refine ⟨z⁻¹, inv_mem hz, ?_⟩
  rw [map_inv, inv_inv, hzN]

end Lang

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
