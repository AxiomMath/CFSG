module

public import CFSG.Monster.GMS.LeechOddSetup
public import CFSG.Sporadic.Co1Block.Co1Equiv
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeFinal
public import Certificates.Certificate17597

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.Module.Odd
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.OddNative CFSG.HardMathSupport.Dickson.I271.TabCo1
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native CFSG.Blueprint Matrix

attribute [local irreducible] rr regsRows

section Counts


theorem fix_counts :
    fixCount [transposeRows 24 (c0Rows ())] = 4096 ∧
      fixCount [transposeRows 24 (rootRows 0)] = 64 ∧
      fixCount [transposeRows 24 (rootRows 2)] = 256 ∧
      fixCount [transposeRows 24 (threeARows ())] = 1 := by
  have h := (Certificates.certificate17597 : threeAFix () = [4096, 64, 256, 1])
  simpa only [threeAFix, List.cons.injEq, and_true] using h

end Counts

section Element


@[expose] noncomputable def c0 : NativeSporadic.Co1 := rho3 * sRep 0

theorem sRep_zero : sRep 0 = reg 70 := rfl

theorem mat_c0 : mat c0 = rowsMatrix 24 (c0Rows ()) := by
  have h1 : mat rho3 = rowsMatrix 24 (rr 27) := mat_reg 27
  have h2 : mat (sRep 0) = rowsMatrix 24 (rr 70) := by
    rw [sRep_zero]
    exact mat_reg 70
  rw [c0, map_mul, h1, h2]
  unfold c0Rows
  exact (rowsMatrix_mulRows 24 (rr 27) (rr 70)).symm

theorem mrep_c0 : MRep (c0Rows ()) ((co1MatEquiv c0 : GA) : GL24) := by
  unfold MRep
  rw [co1MatEquiv_val]
  exact mat_c0.symm

theorem ncard_fix_of_mrep {y : NativeSporadic.Co1} {R : Rows}
    (hy : MRep R ((co1MatEquiv y : GA) : GL24)) :
    {v : Fin 24 → ZMod 2 | co1Act y v = v}.ncard = fixCount [transposeRows 24 R] := by
  have hmat : mat y = rowsMatrix 24 R := by
    unfold MRep at hy
    rw [co1MatEquiv_val] at hy
    exact hy.symm
  have h2 := ncard_fixedSet [R]
  have h3 : {v : Fin 24 → ZMod 2 | co1Act y v = v} =
      {v : Fin 24 → ZMod 2 | ∀ M ∈ [R], rowsMatrix 24 M *ᵥ v = v} := by
    ext v
    simp only [Set.mem_setOf_eq, List.mem_singleton, forall_eq, Odd.co1Act_eq_mulVec, hmat]
  rw [h3, h2]
  rfl

section Order


theorem orderOf_c0 : orderOf c0 = 3 := order_rho3_sRep.1

end Order

end Element

section Class


theorem ncard_fix_c0 : {v : Fin 24 → ZMod 2 | co1Act c0 v = v}.ncard = 2 ^ 12 := by
  rw [ncard_fix_of_mrep mrep_c0, fix_counts.1]
  norm_num

theorem ncard_fix_threeB {y : NativeSporadic.Co1} (hy : IsConj c0 y) :
    {v : Fin 24 → ZMod 2 | co1Act y v = v}.ncard = 2 ^ 12 := by
  obtain ⟨u, hu⟩ := isConj_iff.1 hy
  rw [← hu, CFSG.Sporadic.Co1.Module.ncard_fix_conj]
  exact ncard_fix_c0

end Class

section Root


theorem exists_conj_root :
    ∃ u x : NativeSporadic.Co1, c0 = u * x * u⁻¹ ∧
      MRep (rootRows 1) ((co1MatEquiv x : GA) : GL24) := by
  have hs : orderOf (co1MatEquiv c0) = 3 := by
    rw [orderOf_co1MatEquiv]
    exact orderOf_c0
  obtain ⟨g, x, hx, hcases⟩ := tabCo1_census_three (co1MatEquiv c0) hs
  have hc0 : c0 = co1MatEquiv.symm g * co1MatEquiv.symm x * (co1MatEquiv.symm g)⁻¹ := by
    apply co1MatEquiv.injective
    rw [hx]
    simp
  have hrep : ∀ {R : Rows}, MRep R (x : GL24) →
      MRep R ((co1MatEquiv (co1MatEquiv.symm x) : GA) : GL24) := by
    intro R h
    rw [MulEquiv.apply_symm_apply]
    exact h
  have hcount : ∀ {R : Rows}, MRep R (x : GL24) → fixCount [transposeRows 24 R] = 4096 := by
    intro R h
    rw [← ncard_fix_of_mrep (hrep h),
      ← CFSG.Sporadic.Co1.Module.ncard_fix_conj (co1MatEquiv.symm g), ← hc0, ncard_fix_c0]
    norm_num
  obtain ⟨-, h3C, h3D, h3A⟩ := fix_counts
  have h3A' : fixCount [transposeRows 24 (mul (mul (aRows 1) (aRows 4)) (aRows 5))] = 1 := h3A
  rcases hcases with h | h | h | h
  · exact absurd (hcount h) (by rw [h3C]; norm_num)
  · exact ⟨co1MatEquiv.symm g, co1MatEquiv.symm x, hc0, hrep h⟩
  · exact absurd (hcount h) (by rw [h3D]; norm_num)
  · exact absurd (hcount h) (by rw [h3A']; norm_num)

section Cent


theorem card_centralizer_threeB_le {y : NativeSporadic.Co1} (hy : IsConj c0 y) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set NativeSporadic.Co1)) ≤ 58786560 := by
  obtain ⟨v, hv⟩ := isConj_iff.1 hy
  obtain ⟨u, x, hu, hx⟩ := exists_conj_root
  have hyx : y = v * u * x * (v * u)⁻¹ := by
    rw [← hv, hu]
    group
  rw [hyx, card_centralizer_conj, card_centralizer_co1]
  exact card_cent_threeB_le (co1MatEquiv x) hx

end Cent

end Root

end CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic
  CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

section Leech


theorem card_centralizer_inf_le_of_threeA (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    {α β t : G} (hα : IsConj a α) (hβ : β ∈ typeSet a z₀ α .threeA)
    (ht : t ∈ Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({β} : Set G))
    (htB : IsConj z₀ t) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({α * β} : Set G)) ≤
      3 * 160526499840 := by
  obtain ⟨⟨hβa, hβne, hodd, -⟩, hk⟩ := hβ
  have hY : IsOddPair a t α β := IsOddPair.of_mem_inf hα hβa hβne.symm hodd ht
  have hty : LeechOddType t α β 0 := hk t ht htB
  obtain ⟨L⟩ := S365.exists_leechSystem_of_isConj hG htB
  have hyp := LeechOdd.oddPairHyp I hG htB hY L
  have hot := LeechOdd.oddType I hG htB hY L hty
  obtain ⟨g, hgr, hgs⟩ := CFSG.Sporadic.Co1.Module.Odd.exists_conj_base hyp.twoA hyp.conj
    hyp.ne hyp.four hot
  have hαβ : α * β ∈ Subgroup.centralizer ({t} : Set G) := mul_mem hY.1 hY.2.1
  have hφ : L.φ ⟨α * β, hαβ⟩ = L.φ ⟨α, hY.1⟩ * L.φ ⟨β, hY.2.1⟩ := by
    rw [← map_mul]
    rfl
  have hconj : IsConj c0 (L.φ ⟨α * β, hαβ⟩) := by
    rw [hφ]
    refine isConj_iff.2 ⟨g, ?_⟩
    rw [← hgr, ← hgs]
    unfold c0
    group
  have h1 := (L.involution_bounds hαβ).1
  have h2 : (co1Fix (L.φ ⟨α * β, hαβ⟩)).ncard = 2 ^ 12 := ncard_fix_threeB hconj
  have h3 := card_centralizer_threeB_le hconj
  rw [h2] at h1
  calc _ ≤ 2 * (2 ^ 12 * Nat.card ↥(Subgroup.centralizer
          ({L.φ ⟨α * β, hαβ⟩} : Set Co1))) := h1
    _ ≤ 2 * (2 ^ 12 * 58786560) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    _ = 3 * 160526499840 := by norm_num

end Leech

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
