module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcCore
public import CFSG.LargeExtraspecial.DWRtUntwisted
public import CFSG.LieType.Chevalley.RankOneFaithful
public import CFSG.LargeExtraspecial.Setting

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LargeExtraspecial Matrix

section SL2

variable {K : Type} [Field K]

@[expose] def cThree : SL2 K := ⟨!![0, -1; 1, -1], by simp [det_fin_two]⟩

theorem coe_cThree : ((cThree : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, -1] := rfl

theorem cThree_pow_three : (cThree : SL2 K) ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [SpecialLinearGroup.coe_mul, coe_cThree, Matrix.mul_apply, Fin.sum_univ_two]

theorem cThree_mul_u_ne : (cThree : SL2 K) * uSL 1 ≠ uSL 1 * cThree := by
  intro h
  have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [SpecialLinearGroup.coe_mul, coe_cThree, coe_uSL, Matrix.mul_apply,
    Fin.sum_univ_two] at this

theorem u_mul_v_ne : (uSL 1 : SL2 K) * vSL 1 ≠ vSL 1 * uSL 1 := by
  intro h
  have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem HSL_neg_one_sq : (HSL (-1 : Kˣ) : SL2 K) * HSL (-1) = 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [SpecialLinearGroup.coe_mul, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem cThree_comm_HSL : (cThree : SL2 K) * HSL (-1) = HSL (-1) * cThree := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [SpecialLinearGroup.coe_mul, coe_cThree, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two]

end SL2

section Even

variable {τ : Tag} {K : Type} [Field K]

theorem threeTwoWitness_adjointQuotient_even
    [Finite K] [CharP K 2] (hr : 2 ≤ τ.rank) : ThreeTwoWitness (AdjointQuotient τ K) := by
  have hfin : Finite (ModGL τ K) := finite_modGL
  let A := adjointGroup τ K
  let i : Fin τ.rank := ⟨0, by omega⟩
  let j : Fin τ.rank := ⟨1, by omega⟩
  let J : Set (Fin τ.rank) := {i}
  have hjJ : j ∉ J := by
    intro h
    rw [Set.mem_singleton_iff] at h
    have := congrArg Fin.val h
    simp [i, j] at this
  have hRadA : parabolicRadical τ K J ≤ A :=
    (parabolic_root_radical_Levi_factors τ K J).1.trans (parabolicSubgroup_le_adjointGroup τ K J)
  obtain ⟨ρ, hu, hrange, hinj⟩ := DW.exists_rankOne_injective (τ := τ) (K := K) i
  have hρA : ∀ g, ρ g ∈ A := fun g => by
    have : ρ g ∈ ρ.range := ⟨g, rfl⟩
    rw [hrange] at this
    exact DW.closure_xUnit_yUnit_le_adjointGroup i this
  have hρN : ∀ g, ρ g ∈ Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
    fun g => by
    have : ρ g ∈ ρ.range := ⟨g, rfl⟩
    rw [hrange] at this
    exact parabolicSubgroup_le_normalizer_parabolicRadical J
      (parabolicLevi_le_parabolicSubgroup J (DW.closure_xUnit_yUnit_le_parabolicLevi i this))
  let g0 : A := ⟨ρ cThree, hρA _⟩
  refine threeTwoWitness_quotient_center ((parabolicRadical τ K J).subgroupOf A) ?_ ?_ g0 ?_ ?_ ?_
  ·
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have hcardQ : Nat.card ((parabolicRadical τ K J).subgroupOf A) =
        Nat.card K ^ (parabolicRadicalRoots τ J).ncard := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRadA).toEquiv]
      exact card_parabolicRadical J
    refine IsPGroup.of_card (n := (n : ℕ) * (parabolicRadicalRoots τ J).ncard) ?_
    rw [hcardQ, Nat.card_eq_fintype_card, hn, ← pow_mul]
  ·
    intro hle
    obtain ⟨ρj, huj, hrj, hinjj⟩ := DW.exists_rankOne_injective (τ := τ) (K := K) j
    have hρjA : ∀ g, ρj g ∈ A := fun g => by
      have : ρj g ∈ ρj.range := ⟨g, rfl⟩
      rw [hrj] at this
      exact DW.closure_xUnit_yUnit_le_adjointGroup j this
    have hα : (Pi.single j 1 : Fin τ.rank → ℤ) ∈ parabolicRadicalRoots τ J :=
      mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ j, by rw [height_single]; exact one_pos,
        j, hjJ, by simp⟩
    have hx : ρj (uSL 1) ∈ parabolicRadical τ K J := by
      rw [huj, ← pinnedX_single]
      exact pinnedX_mem_rootSpan hα 1
    have hxQ : (⟨ρj (uSL 1), hρjA _⟩ : A) ∈ (parabolicRadical τ K J).subgroupOf A := hx
    have hcen := Subgroup.mem_center_iff.1 (hle hxQ) ⟨ρj (vSL 1), hρjA _⟩
    have h1 : ρj (vSL 1) * ρj (uSL 1) = ρj (uSL 1) * ρj (vSL 1) := congrArg Subtype.val hcen
    rw [← map_mul, ← map_mul] at h1
    exact u_mul_v_ne (hinjj h1).symm
  · intro q hq
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hρN cThree)) (q : ModGL τ K)
    exact (this.1 hq)
  · refine Subtype.ext ?_
    show (ρ cThree) ^ 3 = 1
    rw [← map_pow, cThree_pow_three, map_one]
  · intro hc
    have hcen := Subgroup.mem_center_iff.1 hc ⟨ρ (uSL 1), hρA _⟩
    have h1 : ρ (uSL 1) * ρ cThree = ρ cThree * ρ (uSL 1) := congrArg Subtype.val hcen
    rw [← map_mul, ← map_mul] at h1
    exact cThree_mul_u_ne (hinj h1).symm

end Even

section Odd

variable {τ : Tag} {K : Type} [Field K]

theorem threeTwoWitness_adjointQuotient_odd
    [Finite K] (hK : ringChar K ≠ 2) (hr : 1 ≤ τ.rank) :
    ThreeTwoWitness (AdjointQuotient τ K) := by
  have hfin : Finite (ModGL τ K) := finite_modGL
  let A := adjointGroup τ K
  let i : Fin τ.rank := ⟨0, by omega⟩
  obtain ⟨ρ, hu, hv, hH, hW, hrange, hker, -, -⟩ :=
    exceptional_ordinary_rank_one_central_image τ K i
  have hinj : Function.Injective ρ := (odd_Chevalley_simple_root_SL2_faithful τ K hK i).1 ρ hu hv
  have hρA : ∀ g, ρ g ∈ A := fun g => by
    have : ρ g ∈ ρ.range := ⟨g, rfl⟩
    rw [hrange] at this
    exact DW.closure_xUnit_yUnit_le_adjointGroup i this
  let g0 : A := ⟨ρ (HSL (-1)), hρA _⟩
  let gc : A := ⟨ρ cThree, hρA _⟩
  have hg0sq : g0 ^ 2 = 1 := by
    refine Subtype.ext ?_
    show (ρ (HSL (-1))) ^ 2 = 1
    rw [← map_pow, pow_two, HSL_neg_one_sq, map_one]
  have hcomm : Commute gc g0 := by
    refine Subtype.ext ?_
    show ρ cThree * ρ (HSL (-1)) = ρ (HSL (-1)) * ρ cThree
    rw [← map_mul, ← map_mul, cThree_comm_HSL]
  refine threeTwoWitness_quotient_center (Subgroup.zpowers g0) ?_ ?_ gc ?_ ?_ ?_
  · intro z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, ?_⟩
    refine Subtype.ext ?_
    show (z : A) ^ 2 ^ 1 = 1
    rw [← hn, pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, hg0sq, _root_.one_zpow]
  · intro hle
    obtain ⟨j, hj⟩ := exists_cartan_odd τ i
    have hcen := Subgroup.mem_center_iff.1 (hle (Subgroup.mem_zpowers g0))
      ⟨xUnit τ K j 1, xUnit_mem_adjointGroup j 1⟩
    have h1 : xUnit τ K j 1 * ρ (HSL (-1)) = ρ (HSL (-1)) * xUnit τ K j 1 :=
      congrArg Subtype.val hcen
    rw [hH] at h1
    have hc := (simple_torus_root_conjugation τ K i j (-1) 1).1
    have hodd : Odd (τ.cartan i j) := by rcases hj with hj | hj <;> rw [hj] <;> decide
    rw [hodd.neg_one_zpow, Units.val_neg, Units.val_one, mul_one, ← h1, mul_inv_cancel_right] at hc
    have h1' : (1 : K) = -1 := xOp_injective j (by rw [← coe_xUnit, ← coe_xUnit, hc])
    exact hK (neg_one_eq_one_iff.1 h1'.symm)
  · intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    have : gc * g0 ^ n * gc⁻¹ = g0 ^ n := by
      rw [(hcomm.zpow_right n).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g0) n
  · refine Subtype.ext ?_
    show (ρ cThree) ^ 3 = 1
    rw [← map_pow, cThree_pow_three, map_one]
  · intro hc
    have hcen := Subgroup.mem_center_iff.1 hc ⟨ρ (uSL 1), hρA _⟩
    have h1 : ρ (uSL 1) * ρ cThree = ρ cThree * ρ (uSL 1) := congrArg Subtype.val hcen
    rw [← map_mul, ← map_mul] at h1
    exact cThree_mul_u_ne (hinj h1).symm

end Odd

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
