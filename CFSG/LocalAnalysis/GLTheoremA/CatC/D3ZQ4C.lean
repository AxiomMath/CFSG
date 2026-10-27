module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ4CRoots
public import CFSG.LieType.Chevalley.RootCommutator
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate43

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement
open CFSG.LieType.SeitzGeneration.ExcWideThree (d4F2Theta)


local instance : NeZero Tag.D4.rank := ⟨by decide⟩

local notation "Rd4J" => parabolicRadicalRoots Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank))

theorem mem_of_ofFn_prod_mem {G : Type*} [Group G] (M : Subgroup G) :
    ∀ (m : ℕ) (f : Fin m → G) (i : Fin m), (∀ j, j ≠ i → f j ∈ M) →
      (List.ofFn f).prod ∈ M → f i ∈ M
  | 0, _, i, _, _ => i.elim0
  | m + 1, f, i, hother, hprod => by
    rw [List.ofFn_succ, List.prod_cons] at hprod
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · have htail : (List.ofFn fun j : Fin m => f j.succ).prod ∈ M := by
        refine Subgroup.list_prod_mem _ fun x hx => ?_
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        exact hother j.succ (Fin.succ_ne_zero j)
      simpa using M.mul_mem hprod (M.inv_mem htail)
    · have hf0 : f 0 ∈ M := hother 0 (Fin.succ_ne_zero k).symm
      have htail : (List.ofFn fun j : Fin m => f j.succ).prod ∈ M := by
        simpa using M.mul_mem (M.inv_mem hf0) hprod
      exact mem_of_ofFn_prod_mem M m (fun j : Fin m => f j.succ) k
        (fun j hj => hother j.succ fun h => hj (Fin.succ_injective _ h)) htail

theorem d3Q013Center_holds :
    ∀ (K : Type) [Field K] (x : ModGL Tag.D4 K),
      x ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)) →
      (∀ y ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)), x * y = y * x) →
      x ∈ degSeries Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)) 2 := by
  intro K _ x hxQ hxc
  unfold parabolicRadical at hxQ
  have hS : ∀ α ∈ Rd4J, IsRoot Tag.D4 α ∧ 0 < height α := fun α hα =>
    ⟨(mem_parabolicRadicalRoots_iff.1 hα).1, (mem_parabolicRadicalRoots_iff.1 hα).2.1⟩
  have hclosed : ∀ α ∈ Rd4J, ∀ β ∈ Rd4J, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot Tag.D4 (a • α + b • β) → a • α + b • β ∈ Rd4J :=
    fun α hα β hβ a b ha hb hr => add_mem_parabolicRadicalRoots (hS α hα) hβ ha hb hr
  have hfin : Set.Finite Rd4J :=
    (finite_setOf_isRoot Tag.D4).subset fun α hα => (hS α hα).1
  obtain ⟨m, α, hαinj, hαrange⟩ : ∃ (m : ℕ) (α : Fin m → Fin Tag.D4.rank → ℤ),
      Function.Injective α ∧ Set.range α = Rd4J := by
    classical
    haveI := hfin.fintype
    refine ⟨Fintype.card ↥Rd4J, fun i => ((Fintype.equivFin ↥Rd4J).symm i).1, ?_, ?_⟩
    · intro i j h
      exact (Fintype.equivFin ↥Rd4J).symm.injective (Subtype.ext h)
    · ext v
      constructor
      · rintro ⟨i, rfl⟩
        exact ((Fintype.equivFin ↥Rd4J).symm i).2
      · intro hv
        exact ⟨Fintype.equivFin ↥Rd4J ⟨v, hv⟩, by simp⟩
  have hbij := bijOn_prod_pinnedX (τ := Tag.D4) K hS hclosed α hαinj hαrange
  obtain ⟨c, -, hc⟩ := hbij.surjOn hxQ
  dsimp only at hc
  have hδdeg : d4F2Theta ∈ degSet Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) 2 :=
    ⟨mem_radical_d4F2Theta, by rw [parabolicDegree_d4J]; exact le_of_eq rfl⟩
  have key : ∀ i : Fin m, α i ≠ d4F2Theta → c i = 0 := by
    intro i hi
    have hγS : α i ∈ Rd4J := by rw [← hαrange]; exact Set.mem_range_self i
    obtain ⟨hγr, hγp⟩ := hS _ hγS
    have hγ2 : α i 2 = 1 := by
      have h1 := one_le_coord_two_of_mem_radical hγS
      have h2 := coord_two_le_of_isRoot hγr
      by_contra hne
      exact hi (eq_d4F2Theta_of_coord_two hγr (by omega))
    obtain ⟨β, hβdef⟩ : ∃ β : Fin Tag.D4.rank → ℤ, β = d4F2Theta - α i := ⟨_, rfl⟩
    have hβ2 : β 2 = 1 := by
      have e2 : d4F2Theta 2 = 2 := rfl
      rw [hβdef]
      show d4F2Theta 2 - α i 2 = 1
      omega
    have hβr : IsRoot Tag.D4 β := by
      rw [hβdef]; exact isRoot_d4F2Theta_sub hγr hγ2
    have hβpos : 0 < height β := by
      rw [IsRoot.height_pos_iff hβr]
      rcases hβr.nonneg_or_nonpos with h | h
      · exact h
      · have := h 2
        omega
    have hβS : β ∈ Rd4J :=
      mem_radical_iff_d4J.2 ⟨hβr, hβpos, by rw [hβ2]; norm_num⟩
    have hsum : α i + β = d4F2Theta := by rw [hβdef]; abel
    have hγβ : IsRoot Tag.D4 (α i + β) := by rw [hsum]; exact isRoot_d4F2Theta
    have hne1 : α i ≠ β := by
      intro h
      have e0 : β 0 = 1 - α i 0 := by rw [hβdef]; rfl
      have h0 := congrFun h 0
      omega
    have hne2 : α i ≠ -β := by
      intro h
      have := congrArg height h
      rw [height_neg] at this
      linarith
    have hy : pinnedX Tag.D4 K β 1 ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)) :=
      pinnedX_mem_rootSpan hβS 1
    have hcomm := hxc _ hy
    obtain ⟨M, hM⟩ : ∃ M : Subgroup (Module.End K (RootModule Tag.D4 K))ˣ,
        M = Subgroup.centralizer ({pinnedX Tag.D4 K β 1} : Set (Module.End K (RootModule Tag.D4 K))ˣ) :=
      ⟨_, rfl⟩
    have memM : ∀ g, g ∈ M ↔ pinnedX Tag.D4 K β 1 * g = g * pinnedX Tag.D4 K β 1 := by
      intro g
      rw [hM, Subgroup.mem_centralizer_iff]
      constructor
      · intro h
        exact h _ (Set.mem_singleton _)
      · intro h e he
        rw [Set.mem_singleton_iff] at he
        subst he
        exact h
    have hother : ∀ j, j ≠ i → pinnedX Tag.D4 K (α j) (c j) ∈ M := by
      intro j hj
      rw [memM]
      by_cases hjβ : α j = β
      · have h1 : pinnedX Tag.D4 K (α j) (c j) ∈ rootSubgroup Tag.D4 K β := by
          rw [hjβ]
          exact mem_rootSubgroup.2 ⟨c j, rfl⟩
        have h2 : pinnedX Tag.D4 K β 1 ∈ rootSubgroup Tag.D4 K β := mem_rootSubgroup.2 ⟨1, rfl⟩
        exact rootSubgroup_mul_comm K h2 h1
      · have hjS : α j ∈ Rd4J := by rw [← hαrange]; exact Set.mem_range_self j
        obtain ⟨hjr, hjp⟩ := hS _ hjS
        have hjne : α j ≠ -β := by
          intro h
          have := congrArg height h
          rw [height_neg] at this
          linarith
        have hnr : ¬ IsRoot Tag.D4 (α j + β) := by
          intro hr
          have h2 := coord_two_le_of_isRoot hr
          have hcoord : (α j + β) 2 = α j 2 + 1 := by
            show α j 2 + β 2 = α j 2 + 1
            rw [hβ2]
          have hj1 := one_le_coord_two_of_mem_radical hjS
          have hjeq : α j 2 = 1 := by omega
          have hsum' : α j + β = d4F2Theta :=
            eq_d4F2Theta_of_coord_two hr (by rw [hcoord, hjeq]; norm_num)
          have hαji : α j = α i := by
            calc α j = (α j + β) - β := by abel
              _ = d4F2Theta - β := by rw [hsum']
              _ = α i := by rw [hβdef]; abel
          exact hj (hαinj hαji)
        exact ((simply_laced_root_commutator_unit Tag.D4 (Or.inl rfl) hjr hβr hjβ hjne).2 hnr K
          _ (mem_rootSubgroup.2 ⟨c j, rfl⟩) _ (mem_rootSubgroup.2 ⟨1, rfl⟩)).symm
    have hxM : (List.ofFn fun j => pinnedX Tag.D4 K (α j) (c j)).prod ∈ M := by
      rw [hc, memM]
      exact hcomm.symm
    have hfi := mem_of_ofFn_prod_mem M m (fun j => pinnedX Tag.D4 K (α j) (c j)) i hother hxM
    have hcomm1 : ⁅pinnedX Tag.D4 K (α i) (c i), pinnedX Tag.D4 K β 1⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact ((memM _).1 hfi).symm
    have hsl := (simply_laced_root_commutator_unit Tag.D4 (Or.inl rfl) hγr hβr hne1 hne2).1 hγβ
    obtain ⟨hε, hform⟩ := hsl
    have hform' := hform K (c i) 1
    rw [hcomm1, hsum] at hform'
    have h0 : pinnedX Tag.D4 K d4F2Theta
        ((commConst Tag.D4 (α i) β (1, 1) : K) * c i * 1) = pinnedX Tag.D4 K d4F2Theta 0 := by
      rw [pinnedX_zero]
      exact hform'.symm
    have hz := pinnedX_injective Tag.D4 K d4F2Theta h0
    have hε0 : ((commConst Tag.D4 (α i) β (1, 1) : ℤ) : K) ≠ 0 := by
      rcases hε with h | h <;> rw [h] <;> norm_num
    rw [mul_one, mul_eq_zero] at hz
    exact hz.resolve_left hε0
  rw [← hc]
  unfold degSeries
  refine Subgroup.list_prod_mem _ ?_
  intro g hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
  by_cases hj : α j = d4F2Theta
  · rw [hj]
    exact pinnedX_mem_rootSpan hδdeg (c j)
  · rw [key j hj, pinnedX_zero]
    exact Subgroup.one_mem _

end CFSG.LocalAnalysis.GLTheoremA
