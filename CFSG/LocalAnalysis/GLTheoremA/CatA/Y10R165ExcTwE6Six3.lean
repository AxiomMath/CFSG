module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

@[expose] def tw6SixZ3 (p q : ℕ) : Fin Tag.E6.rank → ZMod p :=
  ![-((q : ZMod p)), -1, (q : ZMod p) - 1, 1, 0, 0]

theorem tw6SixZ3_mulVec {p q : ℕ} (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    (dualMatrix (ZMod p) e6T3W) *ᵥ tw6SixZ3 p q = (-(q : ZMod p)) • tw6SixZ3 p q := by
  rw [dualMatrix_e6T3W]
  change ((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec (tw6SixZ3 p q)
    = (-(q : ZMod p)) • (tw6SixZ3 p q)
  funext i
  revert i
  change ∀ i : Fin 6,
    (((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec (tw6SixZ3 p q)) i
      = ((-(q : ZMod p)) • (tw6SixZ3 p q)) i
  intro i
  fin_cases i <;>
    change (((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec (tw6SixZ3 p q)) _
      = (-(q : ZMod p)) * tw6SixZ3 p q _ <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, e6T3Matrix6, tw6SixZ3]
  all_goals (first | rfl | ring)
  · linear_combination -hq
  · linear_combination hq

abbrev Tw6SixEigen (p q : ℕ) : Type :=
  {z : Fin Tag.E6.rank → ZMod p // (dualMatrix (ZMod p) e6T3W) *ᵥ z = (-(q : ZMod p)) • z}

private theorem tw6Six_eigen_add {p q : ℕ} {u v : Fin Tag.E6.rank → ZMod p}
    (hu : (dualMatrix (ZMod p) e6T3W) *ᵥ u = (-(q : ZMod p)) • u)
    (hv : (dualMatrix (ZMod p) e6T3W) *ᵥ v = (-(q : ZMod p)) • v) :
    (dualMatrix (ZMod p) e6T3W) *ᵥ (u + v) = (-(q : ZMod p)) • (u + v) := by
  rw [Matrix.mulVec_add, hu, hv, smul_add]

private theorem tw6Six_eigen_smul {p q : ℕ} (c : ZMod p) {u : Fin Tag.E6.rank → ZMod p}
    (hu : (dualMatrix (ZMod p) e6T3W) *ᵥ u = (-(q : ZMod p)) • u) :
    (dualMatrix (ZMod p) e6T3W) *ᵥ (c • u) = (-(q : ZMod p)) • (c • u) := by
  rw [Matrix.mulVec_smul, hu, smul_comm]

private theorem tw6Six_eigen_lin {p q : ℕ} (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0)
    (v : Fin 3 → ZMod p) :
    (dualMatrix (ZMod p) e6T3W) *ᵥ
        (v 0 • tw6SixZ3 p q + v 1 • tw6SixZx p q + v 2 • tw6SixZy p q)
      = (-(q : ZMod p)) •
        (v 0 • tw6SixZ3 p q + v 1 • tw6SixZx p q + v 2 • tw6SixZy p q) :=
  tw6Six_eigen_add
    (tw6Six_eigen_add (tw6Six_eigen_smul _ (tw6SixZ3_mulVec hq))
      (tw6Six_eigen_smul _ (tw6SixZx_mulVec p q hq)))
    (tw6Six_eigen_smul _ (tw6SixZy_mulVec p q hq))

private theorem tw6Six_lin_three {p q : ℕ} (v : Fin 3 → ZMod p) :
    (v 0 • tw6SixZ3 p q + v 1 • tw6SixZx p q + v 2 • tw6SixZy p q) 3 = v 0 := by
  change v 0 * tw6SixZ3 p q 3 + v 1 * tw6SixZx p q 3 + v 2 * tw6SixZy p q 3 = v 0
  simp [tw6SixZx, tw6SixZy, tw6SixZ3]

private theorem tw6Six_lin_four {p q : ℕ} (v : Fin 3 → ZMod p) :
    (v 0 • tw6SixZ3 p q + v 1 • tw6SixZx p q + v 2 • tw6SixZy p q) 4 = v 1 := by
  change v 0 * tw6SixZ3 p q 4 + v 1 * tw6SixZx p q 4 + v 2 * tw6SixZy p q 4 = v 1
  simp [tw6SixZx, tw6SixZy, tw6SixZ3]

private theorem tw6Six_lin_five {p q : ℕ} (v : Fin 3 → ZMod p) :
    (v 0 • tw6SixZ3 p q + v 1 • tw6SixZx p q + v 2 • tw6SixZy p q) 5 = v 2 := by
  change v 0 * tw6SixZ3 p q 5 + v 1 * tw6SixZx p q 5 + v 2 * tw6SixZy p q 5 = v 2
  simp [tw6SixZx, tw6SixZy, tw6SixZ3]

private theorem tw6Six_mulVec_zero (p : ℕ) (z : Fin Tag.E6.rank → ZMod p) :
    ((dualMatrix (ZMod p) e6T3W) *ᵥ z) 0 = z 1 + z 2 + z 3 + z 4 + z 5 := by
  rw [dualMatrix_e6T3W]
  change ((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec z 0
    = z 1 + z 2 + z 3 + z 4 + z 5
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, e6T3Matrix6]
  first | rfl | ring

private theorem tw6Six_mulVec_two (p : ℕ) (z : Fin Tag.E6.rank → ZMod p) :
    ((dualMatrix (ZMod p) e6T3W) *ᵥ z) 2 = z 3 := by
  rw [dualMatrix_e6T3W]
  change ((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec z 2 = z 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, e6T3Matrix6]
  first | rfl | ring

private theorem tw6Six_mulVec_one (p : ℕ) (z : Fin Tag.E6.rank → ZMod p) :
    ((dualMatrix (ZMod p) e6T3W) *ᵥ z) 1 = z 2 + z 3 + z 4 := by
  rw [dualMatrix_e6T3W]
  change ((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec z 1 = z 2 + z 3 + z 4
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, e6T3Matrix6]
  first | rfl | ring

private theorem tw6Six_mulVec_four (p : ℕ) (z : Fin Tag.E6.rank → ZMod p) :
    ((dualMatrix (ZMod p) e6T3W) *ᵥ z) 4 = -z 1 + -z 3 + -z 4 := by
  rw [dualMatrix_e6T3W]
  change ((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec z 4
    = -z 1 + -z 3 + -z 4
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, e6T3Matrix6]
  first | rfl | ring

private theorem tw6Six_eigen_eq_zero {p q : ℕ} [Fact p.Prime] [NeZero p]
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0)
    {z : Fin Tag.E6.rank → ZMod p}
    (hz : (dualMatrix (ZMod p) e6T3W) *ᵥ z = (-(q : ZMod p)) • z)
    (h3 : z 3 = 0) (h4 : z 4 = 0) (h5 : z 5 = 0) : z = 0 := by
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    rw [h] at hq
    have h1 : (1 : ZMod p) = 0 := by simpa using hq
    exact one_ne_zero h1
  have h2 : z 3 = (-(q : ZMod p)) * z 2 := by
    have h := congrFun hz 2
    rw [tw6Six_mulVec_two] at h
    change z 3 = (-(q : ZMod p)) * z 2 at h
    exact h
  have h4' : -z 1 + -z 3 + -z 4 = (-(q : ZMod p)) * z 4 := by
    have h := congrFun hz 4
    rw [tw6Six_mulVec_four] at h
    change -z 1 + -z 3 + -z 4 = (-(q : ZMod p)) * z 4 at h
    exact h
  have h0' : z 1 + z 2 + z 3 + z 4 + z 5 = (-(q : ZMod p)) * z 0 := by
    have h := congrFun hz 0
    rw [tw6Six_mulVec_zero] at h
    change z 1 + z 2 + z 3 + z 4 + z 5 = (-(q : ZMod p)) * z 0 at h
    exact h
  have hz2 : z 2 = 0 := by
    have h : (-(q : ZMod p)) * z 2 = 0 := by
      rw [h3] at h2
      exact h2.symm
    exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr hq0)
  have hz1 : z 1 = 0 := by
    have h := congrFun hz 1
    rw [tw6Six_mulVec_one] at h
    change z 2 + z 3 + z 4 = (-(q : ZMod p)) * z 1 at h
    rw [hz2, h3, h4] at h
    have h' : (-(q : ZMod p)) * z 1 = 0 := by
      simpa only [zero_add, add_zero] using h.symm
    exact (mul_eq_zero.mp h').resolve_left (neg_ne_zero.mpr hq0)
  have hz0 : z 0 = 0 := by
    have h := h0'
    rw [hz1, hz2, h3, h4, h5] at h
    have h' : (-(q : ZMod p)) * z 0 = 0 := by
      simpa only [zero_add, add_zero] using h.symm
    exact (mul_eq_zero.mp h').resolve_left (neg_ne_zero.mpr hq0)
  funext i
  fin_cases i <;> assumption

theorem tw6Six_charSpace_card {p q : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    Nat.card {z : Fin Tag.E6.rank → ZMod p //
      (dualMatrix (ZMod p) e6T3W) *ᵥ z = (-(q : ZMod p)) • z} = p ^ 3 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hle1 : Nat.card {z : Fin Tag.E6.rank → ZMod p //
      (dualMatrix (ZMod p) e6T3W) *ᵥ z = (-(q : ZMod p)) • z}
      ≤ Nat.card (Fin 3 → ZMod p) := by
    refine Nat.card_le_card_of_injective
      (fun z : Tw6SixEigen p q => (![z.1 3, z.1 4, z.1 5] : Fin 3 → ZMod p)) ?_
    intro z w hzw
    have h3 : z.1 3 = w.1 3 := by simpa using congrFun hzw 0
    have h4 : z.1 4 = w.1 4 := by simpa using congrFun hzw 1
    have h5 : z.1 5 = w.1 5 := by simpa using congrFun hzw 2
    have hsub : (dualMatrix (ZMod p) e6T3W) *ᵥ (z.1 - w.1) = (-(q : ZMod p)) • (z.1 - w.1) := by
      rw [Matrix.mulVec_sub, z.2, w.2, smul_sub]
    have hzero : z.1 - w.1 = 0 := by
      refine tw6Six_eigen_eq_zero hq hsub ?_ ?_ ?_
      · simp [Pi.sub_apply, h3]
      · simp [Pi.sub_apply, h4]
      · simp [Pi.sub_apply, h5]
    exact Subtype.ext (sub_eq_zero.mp hzero)
  have hle2 : Nat.card (Fin 3 → ZMod p) ≤ Nat.card {z : Fin Tag.E6.rank → ZMod p //
      (dualMatrix (ZMod p) e6T3W) *ᵥ z = (-(q : ZMod p)) • z} := by
    refine Nat.card_le_card_of_injective
      (fun v : Fin 3 → ZMod p =>
        (⟨v 0 • tw6SixZ3 p q + v 1 • tw6SixZx p q + v 2 • tw6SixZy p q,
          tw6Six_eigen_lin hq v⟩ : Tw6SixEigen p q)) ?_
    intro v w hvw
    have h3 : v 0 = w 0 := by
      have h := congrFun (congrArg Subtype.val hvw) 3
      simp only [Subtype.coe_mk] at h
      rwa [tw6Six_lin_three, tw6Six_lin_three] at h
    have h4 : v 1 = w 1 := by
      have h := congrFun (congrArg Subtype.val hvw) 4
      simp only [Subtype.coe_mk] at h
      rwa [tw6Six_lin_four, tw6Six_lin_four] at h
    have h5 : v 2 = w 2 := by
      have h := congrFun (congrArg Subtype.val hvw) 5
      simp only [Subtype.coe_mk] at h
      rwa [tw6Six_lin_five, tw6Six_lin_five] at h
    funext i
    fin_cases i <;> assumption
  have hcard : Nat.card {z : Fin Tag.E6.rank → ZMod p //
      (dualMatrix (ZMod p) e6T3W) *ᵥ z = (-(q : ZMod p)) • z} = Nat.card (Fin 3 → ZMod p) :=
    le_antisymm hle1 hle2
  rw [hcard, Nat.card_fun]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem tw6Six_eigen_points_mem {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L}
    {q p : ℕ} [Fact p.Prime] [NeZero p] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (hFr : ∀ c, Fr c = c ^ q) (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) (hp5 : 5 < p)
    {A : Subgroup (ModGL Tag.E6 L)} (hAe : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hAT : A ≤ twistedTorusOf (tw6N L) (twistE6 L Fr)) :
    rootDiagUnit Tag.E6 (fun i => ζ ^ (tw6SixZx p q i).val) ∈ A ∧
      rootDiagUnit Tag.E6 (fun i => ζ ^ (tw6SixZy p q i).val) ∈ A := by
  have hparam : ∀ a : ↥A, ∃ z : Tw6SixEigen p q,
      a.1 = rootDiagUnit Tag.E6 (fun i => ζ ^ (z.1 i).val) := by
    intro a
    obtain ⟨z, hz, hzeig, -, -⟩ :=
      exists_column_of_tw6Torus (L := L) hFr hζ (hAT a.2) (hAe.2 a.1 a.2)
    exact ⟨⟨z, hzeig⟩, hz⟩
  let g : ↥A → Tw6SixEigen p q := fun a => Classical.choose (hparam a)
  have hg : ∀ a, a.1 = rootDiagUnit Tag.E6 (fun i => ζ ^ ((g a).1 i).val) := fun a =>
    Classical.choose_spec (hparam a)
  have hginj : Function.Injective g := by
    intro a b hab
    refine Subtype.ext ?_
    rw [hg a, hg b, hab]
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hAcard]; positivity)
  have hVcard : Nat.card (Tw6SixEigen p q) = p ^ 3 := tw6Six_charSpace_card hp5 hq
  have hsurj : Function.Surjective g := by
    have hrange : (Set.range g).ncard = Nat.card ↥A := Set.ncard_range_of_injective hginj
    have huniv : (Set.univ : Set (Tw6SixEigen p q)).ncard = p ^ 3 := by
      rw [Set.ncard_univ, hVcard]
    have heq : Set.range g = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
      rw [huniv, hrange, hAcard]
    intro v
    have hv : v ∈ Set.range g := by rw [heq]; exact Set.mem_univ v
    exact hv
  have hx : rootDiagUnit Tag.E6 (fun i => ζ ^ (tw6SixZx p q i).val) ∈ A := by
    obtain ⟨a, ha⟩ := hsurj ⟨tw6SixZx p q, tw6SixZx_mulVec p q hq⟩
    have hga : (g a).1 = tw6SixZx p q := congrArg Subtype.val ha
    have h := hg a
    rw [hga] at h
    rw [← h]
    exact a.2
  have hy : rootDiagUnit Tag.E6 (fun i => ζ ^ (tw6SixZy p q i).val) ∈ A := by
    obtain ⟨a, ha⟩ := hsurj ⟨tw6SixZy p q, tw6SixZy_mulVec p q hq⟩
    have hga : (g a).1 = tw6SixZy p q := congrArg Subtype.val ha
    have h := hg a
    rw [hga] at h
    rw [← h]
    exact a.2
  exact ⟨hx, hy⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
