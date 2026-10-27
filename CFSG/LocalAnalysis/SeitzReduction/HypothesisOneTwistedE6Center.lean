module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Inner
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInnerBasic

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

variable {K : Type} [Field K]


theorem commutator_pinnedX_single_mem_and_rootCoord [Finite K] [CharP K 2] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ' : Fin τ.rank → ℤ}
    (hγ' : IsRoot τ γ' ∧ 0 < height γ') (j : Fin τ.rank) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (hδpos : 0 < height δ) (hht : height γ' ≤ height δ + 1) (c d : K) :
    ⁅pinnedX τ K δ c, pinnedX τ K (Pi.single j 1) d⁆ ∈ heightSeries τ K (height γ') ∧
      rootCoord hγ' ⁅pinnedX τ K δ c, pinnedX τ K (Pi.single j 1) d⁆ =
        if δ + Pi.single j 1 = γ' then c * d else 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hej := isRoot_single τ j
  have hmem : ⁅pinnedX τ K δ c, pinnedX τ K (Pi.single j 1) d⁆ ∈ heightSeries τ K (height γ') := by
    have h1 : ⁅pinnedX τ K δ c, pinnedX τ K (Pi.single j 1) d⁆ ∈
        heightSeries τ K (height δ + 1) := by
      rw [← commutatorElement_inv]
      exact inv_mem (commutator_posUnipotent_heightSeries_le _ (commutator_mem_commutator
        (pinnedX_single_mem_posUnipotent j d)
        (pinnedX_mem_rootSpan (S := {β | IsRoot τ β ∧ 0 < height β ∧ height δ ≤ height β})
          ⟨hδ, hδpos, le_rfl⟩ c)))
    exact (iSup₂_le fun α hα => le_iSup₂_of_le α ⟨hα.1, hα.2.1, hht.trans hα.2.2⟩ le_rfl :
      heightSeries τ K (height δ + 1) ≤ heightSeries τ K (height γ')) h1
  refine ⟨hmem, ?_⟩
  by_cases hδj : δ = Pi.single j 1
  · subst hδj
    have hne : Pi.single j 1 + Pi.single j 1 ≠ γ' := by
      intro h
      have e : γ' = (2 : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ) := by rw [← h, two_zsmul]
      rcases hγ'.1.eq_one_or_neg_one_of_eq_smul e with h1 | h1 <;> omega
    rw [ite_eq_right hne, commutatorElement_eq_one_iff_mul_comm.2
      (by rw [← pinnedX_add, ← pinnedX_add, add_comm]), rootCoord_one]
  have hδj' : δ ≠ -Pi.single j 1 := by
    intro h
    have : height δ = -1 := by rw [h, height_neg, height_single]
    omega
  obtain ⟨hroot, hnroot⟩ := simply_laced_root_commutator_unit τ (Or.inr hτ) hδ hej hδj hδj'
  by_cases hsum : IsRoot τ (δ + Pi.single j 1)
  · obtain ⟨hε, hcomm⟩ := hroot hsum
    have hε1 : (commConst τ δ (Pi.single j 1) (1, 1) : K) = 1 := by
      refine eq_one_of_mul_self_eq_one_of_two_eq_zero h2 ?_
      rcases hε with h | h <;> simp [h]
    rw [hcomm K c d, hε1, one_mul]
    by_cases hδγ : δ + Pi.single j 1 = γ'
    · rw [ite_eq_left_iff.2 fun h => absurd hδγ h]
      subst hδγ
      exact rootCoord_self hγ' _
    · rw [ite_eq_right hδγ]
      refine rootCoord_pinnedX_of_ne hγ' ⟨hsum, by rw [height_add, height_single]; omega⟩
        (by rw [height_add, height_single]; exact hht) hδγ _
  · have hc := hnroot hsum K _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc.eq, rootCoord_one,
      ite_eq_right (by rintro rfl; exact hsum hγ'.1)]

theorem mem_rootSubgroup_e6HighestRoot_of_commute [Finite K] [CharP K 2] {σ : K →+* K}
    {d₀ : K} (hd₀ : σ d₀ ≠ d₀) {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ posUnipotent TwistTag.E6.tag K)
    (hc1 : ∀ j : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm j = j →
      z * pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 =
        pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 * z)
    (hc2 : ∀ j : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm j ≠ j → ∀ d : K,
      z * (pinnedX TwistTag.E6.tag K (Pi.single j 1) d *
          pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm j) 1) (σ d)) =
        (pinnedX TwistTag.E6.tag K (Pi.single j 1) d *
          pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm j) 1) (σ d)) * z) :
    z ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot := by
  classical
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hτ : TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨ TwistTag.E6.tag = .E8 := Or.inl rfl
  obtain ⟨α, hα, hrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos (τ := TwistTag.E6.tag)
    (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β}) fun β hβ => hβ)
  have hpos : ∀ l, IsRoot TwistTag.E6.tag (α l) ∧ 0 < height (α l) := fun l => by
    have h : α l ∈ Set.range α := ⟨l, rfl⟩
    rwa [hrange] at h
  obtain ⟨c, -, hcz⟩ := ((positive_root_collection TwistTag.E6.tag K).2 α hα hrange).2.2 hz
  have hcz' : (List.ofFn fun l => pinnedX TwistTag.E6.tag K (α l) (c l)).prod = z := hcz
  have key : ∀ n : ℕ, ∀ l, height (α l) ≤ n → α l ≠ e6HighestRoot → c l = 0 := by
    intro n
    induction n with
    | zero =>
      intro l hl _
      have := (hpos l).2
      push_cast at hl
      omega
    | succ n ih =>
      intro i hi hir
      by_cases hle : height (α i) ≤ n
      · exact ih i hle hir
      obtain ⟨j, hj, hγ'⟩ := exists_isRoot_add_single hτ (hpos i).1 (hpos i).2 hir
      have hht' : height (α i + Pi.single j 1) = height (α i) + 1 := by
        rw [height_add, height_single]
      have hγ'p : IsRoot TwistTag.E6.tag (α i + Pi.single j 1) ∧
          0 < height (α i + Pi.single j 1) := ⟨hγ', by have := (hpos i).2; omega⟩
      have hlow : ∀ l, height (α l) < height (α i) → c l = 0 := fun l hl => ih l (by
        push_cast at hi
        omega) fun h => by
          have h1 : height (α i + Pi.single j 1) ≤ height e6HighestRoot :=
            height_le_height_highRoot hγ'
          rw [← h] at h1
          omega
      have hfac : ∀ (j' : Fin TwistTag.E6.tag.rank) (d : K) (l : Fin _),
          ⁅pinnedX TwistTag.E6.tag K (α l) (c l), pinnedX TwistTag.E6.tag K (Pi.single j' 1) d⁆ ∈
              heightSeries TwistTag.E6.tag K (height (α i + Pi.single j 1)) ∧
            rootCoord hγ'p ⁅pinnedX TwistTag.E6.tag K (α l) (c l),
                pinnedX TwistTag.E6.tag K (Pi.single j' 1) d⁆ =
              if α l + Pi.single j' 1 = α i + Pi.single j 1 then c l * d else 0 := by
        intro j' d l
        by_cases hl : height (α l) < height (α i)
        · rw [hlow l hl, pinnedX_zero, commutatorElement_one_left, rootCoord_one, zero_mul,
            ite_self]
          exact ⟨one_mem _, rfl⟩
        · exact commutator_pinnedX_single_mem_and_rootCoord hτ hγ'p j' (hpos l).1 (hpos l).2
            (by rw [hht']; omega) (c l) d
      have hsum : ∀ ws : List (Fin TwistTag.E6.tag.rank × K),
          z * (ws.map fun p => pinnedX TwistTag.E6.tag K (Pi.single p.1 1) p.2).prod =
            (ws.map fun p => pinnedX TwistTag.E6.tag K (Pi.single p.1 1) p.2).prod * z →
          ∑ l, (ws.map fun p => if α l + Pi.single p.1 1 = α i + Pi.single j 1 then
            c l * p.2 else 0).sum = 0 := by
        intro ws hws
        obtain ⟨-, hπ⟩ := commutator_prod_mem_and_coord (U := posUnipotent TwistTag.E6.tag K)
          (M := heightSeries TwistTag.E6.tag K (height (α i + Pi.single j 1)))
          (heightSeries_le_normalizer K _) (rootCoord hγ'p)
          (fun x hx y hy => rootCoord_mul hγ'p hx hy) (fun g hg x hx => rootCoord_conj hγ'p hg hx)
          (List.ofFn fun l => pinnedX TwistTag.E6.tag K (α l) (c l))
          (ws.map fun p => pinnedX TwistTag.E6.tag K (Pi.single p.1 1) p.2)
          (fun x hx => by
            obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
            exact rootSubgroup_le_posUnipotent_of_height_pos (hpos l).1 (hpos l).2
              (mem_rootSubgroup.2 ⟨_, rfl⟩))
          (fun y hy => by
            obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
            exact pinnedX_single_mem_posUnipotent p.1 p.2)
          (fun x hx y hy => by
            obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
            obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
            exact (hfac p.1 p.2 l).1)
        rw [hcz', commutatorElement_eq_one_iff_mul_comm.2 hws, rootCoord_one, List.map_ofFn,
          List.sum_ofFn] at hπ
        refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) hπ.symm
        simp only [Function.comp_apply, List.map_map]
        congr 1
        refine List.map_congr_left fun p _ => ?_
        exact ((hfac p.1 p.2 l).2).symm
      have hsplit : ∀ (j' : Fin TwistTag.E6.tag.rank) (d : K),
          (∑ l, if α l + Pi.single j' 1 = α i + Pi.single j 1 then c l * d else 0) =
            (∑ l, if α l + Pi.single j' 1 = α i + Pi.single j 1 then c l else 0) * d := by
        intro j' d
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by rw [ite_mul, zero_mul]
      have hself : (∑ l, if α l + Pi.single j 1 = α i + Pi.single j 1 then c l else 0) = c i := by
        rw [Finset.sum_eq_single i (fun l _ hl => by
          rw [ite_eq_right_iff]
          intro h
          exact absurd (hα (add_right_cancel h)) hl) (fun h => absurd (Finset.mem_univ i) h),
          ite_eq_left_iff.2 fun h => absurd rfl h]
      by_cases hjρ : TwistTag.E6.perm j = j
      · have h1 := hsum [(j, 1)] (by simpa using hc1 j hjρ)
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1
        rw [hsplit, hself, mul_one] at h1
        exact h1
      · have hd : ∀ d : K, c i * d +
            (∑ l, if α l + Pi.single (TwistTag.E6.perm j) 1 = α i + Pi.single j 1 then c l
              else 0) * σ d = 0 := by
          intro d
          have h1 := hsum [(j, d), (TwistTag.E6.perm j, σ d)] (by simpa using hc2 j hjρ d)
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            Finset.sum_add_distrib] at h1
          rw [hsplit, hsplit, hself] at h1
          exact h1
        set C := ∑ l, if α l + Pi.single (TwistTag.E6.perm j) 1 = α i + Pi.single j 1 then c l
          else 0
        have h1 := hd 1
        rw [mul_one, map_one, mul_one] at h1
        have hC : C = c i := by linear_combination h1 - c i * h2
        have h3 := hd d₀
        rw [hC] at h3
        have h4 : c i * (σ d₀ - d₀) = 0 := by linear_combination h3 - c i * d₀ * h2
        exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hd₀)
  rw [← hcz']
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
  by_cases hl : α l = e6HighestRoot
  · rw [hl]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  · rw [key (height (α l)).toNat l (Int.self_le_toNat _) hl, pinnedX_zero]
    exact one_mem _

theorem pinnedX_mul_pinnedX_perm_mem [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    (j : Fin TwistTag.E6.tag.rank) (hj : TwistTag.E6.perm j ≠ j) (d : K) :
    pinnedX TwistTag.E6.tag K (Pi.single j 1) d *
        pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm j) 1) (σ d) ∈
      graphFixedPosUnipotent TwistTag.E6 K σ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hρρ : TwistTag.E6.perm (TwistTag.E6.perm j) = j := by
    revert j
    decide
  have hcomm : Commute (pinnedX TwistTag.E6.tag K (Pi.single j 1) d)
      (pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm j) 1) (σ d)) :=
    commute_pinnedX_of_rootForm_eq_zero K (isRoot_single _ _) (isRoot_single _ _)
      (TwistTag.E6.rootForm_single_single_eq_zero (TwistTag.E6.mem_orbit_orbitIndex j)
        (TwistTag.E6.perm_mem_orbit (TwistTag.E6.mem_orbit_orbitIndex j)) hj.symm) d (σ d)
  refine Subgroup.mem_inf.2 ⟨mul_mem (pinnedX_single_mem_posUnipotent _ _)
    (pinnedX_single_mem_posUnipotent _ _), (mem_twistedFixedGroup_iff_twistHom _ _ _).2
    ⟨mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _), ?_⟩⟩
  rw [map_mul, twistHom_pinnedX_eq_of_charTwo h2 σ (isRoot_single _ _),
    twistHom_pinnedX_eq_of_charTwo h2 σ (isRoot_single _ _), permLattice_single,
    permLattice_single, hρρ, hσσ]
  exact hcomm.eq.symm

theorem mem_rootSubgroup_e6HighestRoot_of_mem_center [Finite K] [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {d₀ : K} (hd₀ : σ d₀ ≠ d₀) {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ graphFixedPosUnipotent TwistTag.E6 K σ)
    (hc : ∀ u ∈ graphFixedPosUnipotent TwistTag.E6 K σ, z * u = u * z) :
    z ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot :=
  mem_rootSubgroup_e6HighestRoot_of_commute hd₀ (Subgroup.mem_inf.1 hz).1
    (fun j hj => hc _ (pinnedX_mem_graphFixedPosUnipotent σ (isRoot_single _ j)
      (by rw [height_single]; omega) (by rw [permLattice_single, hj]) (map_one σ)))
    (fun j hj d => hc _ (pinnedX_mul_pinnedX_perm_mem hσσ j hj d))

theorem exists_twistedE6_sigma_ne {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ d : K, σ d ≠ d := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hK] at hζ
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  refine ⟨ζ, fun h => ?_⟩
  rw [hσ] at h
  have h1 : ζ ^ (2 ^ f - 1) = 1 := by
    refine Units.ext ?_
    have e : (ζ : K) ^ (2 ^ f - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, h]
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_right_cancel₀ ζ.ne_zero e
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hζ] at h2
  have h3 := Nat.le_of_dvd (by omega) h2
  have h4 : 2 ^ f < (2 ^ f) ^ 2 := by nlinarith
  omega

theorem innerCentralizerCriterion_twistedE6_of_posUnipotent_le [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hodd : ∀ u : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (u : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom →
        u ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
          c * t = t * c ∧ Odd (orderOf c)}) :
    InnerCentralizerCriterion t := by
  have hσ2 := twistedE6_sigma_pow_order hK hσ
  have hσσ : ∀ x, σ.toRingHom (σ.toRingHom x) = x := fun x => by
    have h := congrArg (fun g : K ≃+* K => g x) hσ2
    simpa [TwistTag.order, pow_two] using h
  obtain ⟨d₀, hd₀⟩ := exists_twistedE6_sigma_ne hf hK hσ
  have hA : (RootWeightDatum.fixed TwistTag.E6 σ hσ2).actors = ⊤ :=
    EvenExceptionalActorCoverage.fixedDiagonalFieldActors_E6_eq_top hf hK σ hσ
  have hJ : (∅ : Set (Fin (RootWeightDatum.fixed (K := K) TwistTag.E6 σ hσ2).rank)) ≠
      Set.univ := by
    intro h
    have := Set.mem_univ (⟨0, (RootWeightDatum.fixed (K := K) TwistTag.E6 σ hσ2).rank_pos⟩ :
      Fin (RootWeightDatum.fixed (K := K) TwistTag.E6 σ hσ2).rank)
    rw [← h] at this
    exact this
  refine innerCentralizerCriterion_of_conj_radical_of_actors_eq_top
    (RootWeightDatum.fixed TwistTag.E6 σ hσ2) hA hJ 1 (t := t)
    (fun u hu => hodd u (mem_map_radicalIn_empty_iff_fixed.1 hu)) ?_
  intro z hz hzc _
  have hmem := mem_rootSubgroup_e6HighestRoot_of_mem_center (σ := σ.toRingHom) hσσ hd₀
    (mem_map_radicalIn_empty_iff_fixed.1 hz) fun u hu => congrArg Subtype.val
      (hzc ⟨u, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hu⟩
        (mem_map_radicalIn_empty_iff_fixed.2 hu))
  obtain ⟨c, hcz⟩ := mem_rootSubgroup.1 hmem
  have hsq : pinnedX TwistTag.E6.tag K e6HighestRoot c *
      pinnedX TwistTag.E6.tag K e6HighestRoot c = 1 := by
    rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  refine Subtype.ext ?_
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, sq]
  have key : (z : ModGL (RootWeightDatum.fixed TwistTag.E6 σ hσ2).tag K) =
      pinnedX TwistTag.E6.tag K e6HighestRoot c := hcz.symm
  rw [key]
  exact hsq

end CFSG.SeitzReduction
