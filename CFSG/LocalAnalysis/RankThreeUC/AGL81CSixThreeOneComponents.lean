module

public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
public import CFSG.Open.StatedDefs
import CFSG.ClassicalInvolution.Basic
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.RepresentationTheory.QuaternionKernelOrbit
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

variable {X : Type*} [Group X] [Finite X]

theorem exists_isComponent_of_fittingSubgroup_le_center
    (hF : CFSG.fittingSubgroup X ≤ Subgroup.center X)
    (hX : ∃ a b : X, a * b ≠ b * a) :
    ∃ L : Subgroup X, CFSG.IsComponent L := by
  by_contra h
  have hlayer : CFSG.layer X = ⊥ := by
    rw [CFSG.layer.eq_sSup]
    exact sSup_eq_bot.mpr fun K hK => (h ⟨K, hK⟩).elim
  have hgen : CFSG.generalizedFitting X = CFSG.fittingSubgroup X := by
    rw [CFSG.generalizedFitting.eq_sup, hlayer, sup_bot_eq]
  have htop : (⊤ : Subgroup X) ≤ Subgroup.center X := by
    intro x _
    have hx : x ∈ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_center_iff.mp (hF (hgen ▸ hy)) x).symm
    exact hF (hgen ▸ CFSG.centralizer_generalizedFitting_le X hx)
  obtain ⟨a, b, hab⟩ := hX
  exact hab (Subgroup.mem_center_iff.mp (htop (Subgroup.mem_top a)) b).symm

theorem pow_sixty_le_card_iSup_of_pairwise_distinct_components {ι : Type*} [Fintype ι]
    {L : ι → Subgroup X} (hL : ∀ i, CFSG.IsComponent (L i))
    (hne : ∀ i j, i ≠ j → L i ≠ L j) :
    60 ^ Fintype.card ι ≤ Nat.card ↥(⨆ i, L i) := by
  classical
  suffices h : ∀ s : Finset ι, 60 ^ s.card ≤ Nat.card ↥(s.sup L) by
    simpa [Finset.sup_eq_iSup] using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha, Finset.sup_insert, pow_succ']
      have hcomm : ∀ x ∈ L a, ∀ y ∈ s.sup L, x * y = y * x := by
        intro x hx y hy
        have hle : s.sup L ≤ Subgroup.centralizer (L a : Set X) := by
          refine Finset.sup_le fun b hb => ?_
          have hba : b ≠ a := fun h => ha (h ▸ hb)
          rcases CFSG.LocalCores.distinct_components_commute (hL b) (hL a) with heq | hcom
          · exact absurd heq (hne b a hba)
          · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcom
        exact Subgroup.mem_centralizer_iff.mp (hle hy) x hx
      let S : Subgroup X := L a ⊔ s.sup L
      have hA : CFSG.IsQuasisimple ↥((L a).subgroupOf S) :=
        (CFSG.LocalCores.component_overgroup (hL a) (le_sup_left : L a ≤ S)).1
      obtain ⟨-, -, -, -, -, hbound⟩ :=
        CFSG.GroupTheory.quasisimple_commuting_product_centralizer_order_bound
          ((L a).subgroupOf S) hA
      have hBcomm : (s.sup L).subgroupOf S ≤
          Subgroup.centralizer ((L a).subgroupOf S : Set ↥S) := by
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        apply Subtype.ext
        exact hcomm (z : X) (Subgroup.mem_subgroupOf.mp hz) (y : X)
          (Subgroup.mem_subgroupOf.mp hy)
      have hBbound := hbound ((s.sup L).subgroupOf S) hBcomm
      have hcard : Nat.card ↥((s.sup L).subgroupOf S) = Nat.card ↥(s.sup L) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (le_sup_right : s.sup L ≤ S)).toEquiv
      rw [hcard] at hBbound
      exact (Nat.mul_le_mul_left 60 ih).trans hBbound

theorem conj_mem_of_isComponent {p : ℕ} (hp : p.Prime) (hX : Nat.card X < 60 ^ p)
    {L : Subgroup X} (hL : CFSG.IsComponent L) {x : X} (hx : x ^ p = 1) :
    ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
  classical
  by_cases hxN : x ∈ Subgroup.normalizer (L : Set X)
  · intro l hl
    exact (Subgroup.mem_normalizer_iff.mp hxN l).mp hl
  · exfalso
    let Li : Fin p → Subgroup X := fun i => L.map (MulAut.conj (x ^ (i : ℕ))).toMonoidHom
    have hcomp : ∀ i, CFSG.IsComponent (Li i) := fun i =>
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (x ^ (i : ℕ))) hL
    have hdistinct : ∀ i j : Fin p, i ≠ j → Li i ≠ Li j := by
      intro i j hij heq
      have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      rcases lt_or_gt_of_ne hval with hlt | hlt
      · have hmem : x ^ ((j : ℕ) - (i : ℕ)) ∈ Subgroup.normalizer (L : Set X) := by
          have h := (CFSG.ClassicalInvolution.map_conj_eq_map_conj_iff
            (J := L) (g := x ^ (i : ℕ)) (h := x ^ (j : ℕ))).mp heq
          have hpow : (x ^ (j : ℕ))⁻¹ * x ^ (i : ℕ) =
              (x ^ ((j : ℕ) - (i : ℕ)))⁻¹ := by
            rw [← pow_sub_mul_pow x hlt.le]
            group
          rw [hpow] at h
          simpa using Subgroup.inv_mem _ h
        exact hxN (CFSG.RepresentationTheory.pow_mem_normalizer_of_prime hp
          (by omega) (by omega) hx hmem)
      · have hmem : x ^ ((i : ℕ) - (j : ℕ)) ∈ Subgroup.normalizer (L : Set X) := by
          have h := (CFSG.ClassicalInvolution.map_conj_eq_map_conj_iff
            (J := L) (g := x ^ (j : ℕ)) (h := x ^ (i : ℕ))).mp heq.symm
          have hpow : (x ^ (i : ℕ))⁻¹ * x ^ (j : ℕ) =
              (x ^ ((i : ℕ) - (j : ℕ)))⁻¹ := by
            rw [← pow_sub_mul_pow x hlt.le]
            group
          rw [hpow] at h
          simpa using Subgroup.inv_mem _ h
        exact hxN (CFSG.RepresentationTheory.pow_mem_normalizer_of_prime hp
          (by omega) (by omega) hx hmem)
    have hbound : 60 ^ p ≤ Nat.card ↥(⨆ i, Li i) := by
      simpa using pow_sixty_le_card_iSup_of_pairwise_distinct_components hcomp hdistinct
    have hle : Nat.card ↥(⨆ i, Li i) ≤ Nat.card X := by
      have h := Subgroup.card_le_of_le (G := X) (H := ⨆ i, Li i) (K := ⊤) le_top
      rwa [Subgroup.card_top] at h
    exact absurd hX (not_lt.mpr (hbound.trans hle))

private theorem pow_ten_lt_sixty_pow {p : ℕ} (hp : 5 ≤ p) : p ^ 10 < 60 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hstep : (k + 1) ^ 10 < 60 * k ^ 10 := by
        have h5 : 5 * (k + 1) ≤ 6 * k := by omega
        have hpow : 5 ^ 10 * (k + 1) ^ 10 ≤ 6 ^ 10 * k ^ 10 := by
          simpa only [Nat.mul_pow] using Nat.pow_le_pow_left h5 10
        have h6 : 6 ^ 10 < 60 * 5 ^ 10 := by norm_num
        have h6k : 6 ^ 10 * k ^ 10 < (60 * 5 ^ 10) * k ^ 10 :=
          Nat.mul_lt_mul_of_pos_right h6 (by positivity)
        have hcomb : 5 ^ 10 * (k + 1) ^ 10 < 60 * 5 ^ 10 * k ^ 10 :=
          lt_of_le_of_lt hpow h6k
        have hrew : 60 * 5 ^ 10 * k ^ 10 = 5 ^ 10 * (60 * k ^ 10) := by ring
        rw [hrew] at hcomb
        exact Nat.lt_of_mul_lt_mul_left hcomb
      calc (k + 1) ^ 10 < 60 * k ^ 10 := hstep
        _ < 60 * 60 ^ k := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 60 ^ (k + 1) := by rw [pow_succ']

theorem card_statedSp_lt_sixty_pow {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    Nat.card ↥(CFSG.Open.StatedSp 2 (ZMod p)) < 60 ^ p := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, Nat.card_zmod]
  have hp2 : 0 < p ^ 2 := by positivity
  have hp4 : 0 < p ^ 4 := by positivity
  have h1 : p ^ 2 - 1 < p ^ 2 := Nat.sub_lt hp2 (by norm_num)
  have h2 : p ^ 4 - 1 < p ^ 4 := Nat.sub_lt hp4 (by norm_num)
  have h3 : (p ^ 2 - 1) * (p ^ 4 - 1) < p ^ 2 * p ^ 4 := Nat.mul_lt_mul'' h1 h2
  have h4 : p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) < p ^ 4 * (p ^ 2 * p ^ 4) :=
    Nat.mul_lt_mul_of_pos_left h3 hp4
  have h5 : p ^ 4 * (p ^ 2 * p ^ 4) = p ^ 10 := by ring
  rw [h5] at h4
  exact h4.trans (pow_ten_lt_sixty_pow hp5)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
