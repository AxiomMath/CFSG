module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Stage2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Model
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Stage1

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix Module CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem sum_single_apply (I : Finset (Fin 18)) (a : I → ZMod 2) (k : Fin 18) :
    (∑ i : I, a i • (Pi.single (i : Fin 18) 1 : Fin 18 → ZMod 2)) k =
      if h : k ∈ I then a ⟨k, h⟩ else 0 := by
  rw [Finset.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩]
    · simp
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_eq_of_ne', smul_zero]
      intro e; exact hb (Subtype.ext e)
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [Pi.smul_apply, Pi.single_eq_of_ne', smul_zero]
    intro e; exact h (e ▸ b.2)

theorem coord_zero_of_card (S : Submodule (ZMod 2) (Fin 18 → ZMod 2)) (I : Finset (Fin 18))
    (hI : ∀ i ∈ I, (Pi.single i 1 : Fin 18 → ZMod 2) ∈ S) (hcard : Nat.card S ≤ 2 ^ I.card) :
    ∀ v ∈ S, ∀ c ∉ I, v c = 0 := by
  intro v hv c hc
  by_contra hvc
  have hv1 : v c = 1 := by
    rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (v c) with h | h
    · exact absurd h hvc
    · exact h
  let φ : (I → ZMod 2) × ZMod 2 → S := fun p =>
    ⟨∑ i : I, p.1 i • (Pi.single (i : Fin 18) 1 : Fin 18 → ZMod 2) + p.2 • v,
      add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hI i i.2))
        (Submodule.smul_mem _ _ hv)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hp
    have hp' := congrArg Subtype.val hp
    have hc' := congrFun hp' c
    simp only [Pi.add_apply, Pi.smul_apply, sum_single_apply, hc, dite_false, zero_add, hv1,
      smul_eq_mul, mul_one, φ] at hc'
    subst hc'
    have ha : a = a' := by
      funext i
      have := congrFun hp' i
      simp only [Pi.add_apply, sum_single_apply, i.2, dite_true, φ] at this
      exact add_right_cancel this
    rw [ha]
  have h1 := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := I),
    Fintype.card_coe] at h1
  have : 2 ^ I.card * 2 ≤ 2 ^ I.card := h1.trans hcard
  have h2 : 0 < 2 ^ I.card := Nat.two_pow_pos _
  omega

theorem mem_of_supp {S : Submodule (ZMod 2) (Fin 18 → ZMod 2)} {I : Finset (Fin 18)}
    (hI : ∀ i ∈ I, (Pi.single i 1 : Fin 18 → ZMod 2) ∈ S) {v : Fin 18 → ZMod 2}
    (hv : ∀ c ∉ I, v c = 0) : v ∈ S := by
  have : v = ∑ i ∈ I, v i • (Pi.single i 1 : Fin 18 → ZMod 2) := by
    ext c
    rw [Finset.sum_apply]
    by_cases hc : c ∈ I
    · rw [Finset.sum_eq_single c (fun b _ hb => by simp [Pi.single_eq_of_ne' hb])
        (fun h => absurd hc h)]
      simp
    · rw [hv c hc, Finset.sum_eq_zero fun b hb => by
        simp [Pi.single_eq_of_ne' (fun h : b = c => hc (h ▸ hb))]]
  rw [this]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hI i hi)

@[expose] def I0 : Finset (Fin 18) := Finset.univ.filter fun c => clsN c ≤ 1

@[expose] def IV : Finset (Fin 18) := Finset.univ.filter fun c => clsN c = 0

theorem card_I0 : I0.card = 10 := by decide

theorem card_IV : IV.card = 2 := by decide

theorem mem_I0 (c : Fin 18) : c ∈ I0 ↔ clsN c ≤ 1 := by simp [I0]

theorem mem_IV (c : Fin 18) : c ∈ IV ↔ clsN c = 0 := by simp [IV]

theorem tMN_eq_tauM : tMN 9 = tauM := by
  ext r c
  refine Fin.addCases (fun i => ?_) (fun i => ?_) r <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) c
  · rw [tMN, blkN_cc, tauM, one_apply_eq_bz, toMat_apply]; congr 1; revert i j; decide
  · rw [tMN, blkN_cn, tauM, one_apply_eq_bz, toMat_apply]; congr 1; revert i j; decide
  · rw [tMN, blkN_nc, tauM, toMat_apply]
    have : ∀ i j : Fin 9, (tauBits.getD (Fin.natAdd 9 i) 0).testBit (Fin.castAdd 9 j) = false := by
      decide
    rw [this, bz_false]
  · rw [tMN, blkN_nn, tauM, one_apply_eq_bz, toMat_apply]; congr 1; revert i j; decide

theorem toMat_bd9_self (A : Array ℕ) : toMat 18 18 (bd9Bits A A) = rhoN (toMat 9 9 A) := by
  rw [toMat_bd9Bits, bdN_self]

theorem rhoN_genA_eM (m : ℕ) : rhoN (genA (Fin.ofNat 12 m)) = eM m := by
  rw [eM, eBits18, toMat_bd9_self]; rfl

theorem rhoN_genA_vM (j : ℕ) : rhoN (genA (nuS j)) = vM j := by
  rw [vM, vBits, toMat_bd9_self]; rfl

section Shapes

theorem shapeCheck_spec :
    presV1B tauBits = true ∧ bdiagB tauBits = true ∧ bmul 18 18 tauBits tauBits = id18 ∧
    subBits w0pC w0pC tauBits = t2Bits ∧ subBits w1C w1C tauBits = t2Bits ∧
    (∀ m < 4, fixV1B (eBits18 m) = true ∧ flagB (eBits18 m) = true ∧
      blk1Bits (eBits18 m) = aBits2 m) ∧
    (∀ j < 4, fixV1B (vBits j) = true ∧ triB (vBits j) = true ∧
      bmul 18 18 (vBits j) (vBits j) = id18 ∧ subBits w0pC w0pC (vBits j) = n0Bits2 j ∧
      subBits w1C w1C (vBits j) = n1Bits2 j) ∧
    (∀ z < 4, ∀ m < 4, lay1B (yBits z m) = true ∧ blk1Bits (yBits z m) = candBlock z m) := by
  have h := shapeCheck_eq_true
  simp only [shapeCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, fun m hm => ⟨(h6 m hm).1.1, (h6 m hm).1.2, (h6 m hm).2⟩,
    fun j hj => ⟨(h7 j hj).1.1.1.1, (h7 j hj).1.1.1.2, (h7 j hj).1.1.2, (h7 j hj).1.2,
      (h7 j hj).2⟩, fun z hz m hm => ⟨(h8 z hz m hm).1, (h8 z hz m hm).2⟩⟩

theorem tauM_mul_self : tauM * tauM = 1 := by
  rw [tauM, ← toMat_bmul, shapeCheck_spec.2.2.1, toMat_id18]

theorem tauM_tri (r c : Fin 18) (h : clsN c < clsN r) : tauM r c = 0 :=
  bdiagB_apply shapeCheck_spec.2.1 r c (by omega)

theorem presV1_tauM : PresV1 tauM := presV1_of shapeCheck_spec.1

theorem sub0M_tauM : sub0M tauM = tM2 := by
  rw [tauM, sub0M_toMat, shapeCheck_spec.2.2.2.1]; rfl

theorem sub1M_tauM : sub1M tauM = tM2 := by
  rw [tauM, sub1M_toMat, shapeCheck_spec.2.2.2.2.1]; rfl

theorem blk1M_eM {m : ℕ} (hm : m < 4) : blk1M (eM m) = aM2 m := by
  rw [eM, blk1M_toMat, (shapeCheck_spec.2.2.2.2.2.1 m hm).2.2]; rfl

theorem vM_tri {j : ℕ} (hj : j < 4) (r c : Fin 18) (h : clsN c < clsN r) : vM j r c = 0 :=
  triB_apply (shapeCheck_spec.2.2.2.2.2.2.1 j hj).2.1 r c h

theorem vM_mul_self {j : ℕ} (hj : j < 4) : vM j * vM j = 1 := by
  rw [vM, ← toMat_bmul, (shapeCheck_spec.2.2.2.2.2.2.1 j hj).2.2.1, toMat_id18]

theorem sub0M_vM {j : ℕ} (hj : j < 4) : sub0M (vM j) = n0M2 j := by
  rw [vM, sub0M_toMat, (shapeCheck_spec.2.2.2.2.2.2.1 j hj).2.2.2.1]; rfl

theorem sub1M_vM {j : ℕ} (hj : j < 4) : sub1M (vM j) = n1M2 j := by
  rw [vM, sub1M_toMat, (shapeCheck_spec.2.2.2.2.2.2.1 j hj).2.2.2.2]; rfl

theorem lay1_yM {z m : ℕ} (hz : z < 4) (hm : m < 4) (r c : Fin 18)
    (h : ¬ (clsN r = 1 ∧ clsN c = 2)) : yM z m r c = (1 : Mat18) r c :=
  lay1B_apply (shapeCheck_spec.2.2.2.2.2.2.2 z hz m hm).1 r c h

theorem fixV1_yM {z m : ℕ} (hz : z < 4) (hm : m < 4) : FixV1 (yM z m) :=
  fixV1_of_lay1B (shapeCheck_spec.2.2.2.2.2.2.2 z hz m hm).1

theorem blk1M_yM {z m : ℕ} (hz : z < 4) (hm : m < 4) : blk1M (yM z m) = candM z m := by
  rw [yM, blk1M_toMat, (shapeCheck_spec.2.2.2.2.2.2.2 z hz m hm).2]; rfl

end Shapes

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
