module

public import CFSG.LieType.SeitzGeneration.OuterSpPair

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCSpComm CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne (card_semilinearFixedSubfield proj_injective_sp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section Center

variable {r : ℕ} {k : Type} [Field k] [Finite k]

theorem isSimpleGroup_statedProj_statedSp_of_two_le (hr : 2 ≤ r)
    (hk : ¬ (r = 2 ∧ Nat.card k = 2)) : IsSimpleGroup (StatedProj (StatedSp r k)) := by
  refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r (by omega) ?_
  by_cases h4 : 4 ≤ Nat.card k
  · exact Or.inl (Or.inr h4)
  · have h1 : 1 < Nat.card k := Finite.one_lt_card
    have h23 : Nat.card k = 2 ∨ Nat.card k = 3 := by omega
    rcases h23 with h2 | h3
    · exact Or.inr (Or.inr ⟨h2, by
        by_contra hr3
        exact hk ⟨by omega, h2⟩⟩)
    · exact Or.inr (Or.inl ⟨h3, hr⟩)

theorem isPerfect_statedProj_statedSp_of_two_le (hr : 2 ≤ r)
    (hk : ¬ (r = 2 ∧ Nat.card k = 2)) : Group.IsPerfect (StatedProj (StatedSp r k)) := by
  have hP : Group.IsPerfect (StatedSp r k) := by
    have : Group.IsPerfect (TauCeti.GLSymplecticFin r k) :=
      CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin k r (by
        by_cases h4 : 4 ≤ Nat.card k
        · exact Or.inl (Or.inr h4)
        · have h1 : 1 < Nat.card k := Finite.one_lt_card
          have h23 : Nat.card k = 2 ∨ Nat.card k = 3 := by omega
          rcases h23 with h2 | h3
          · exact Or.inr (Or.inr ⟨h2, by
              by_contra hr3
              exact hk ⟨by omega, h2⟩⟩)
          · exact Or.inr (Or.inl ⟨h3, hr⟩))
    let e : TauCeti.GLSymplecticFin r k ≃* StatedSp r k :=
      (TauCeti.GLSymplecticFin.mulEquivGLSymplectic r k).trans
        (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
          (n := r) (K := k)).symm)
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.ofSurjective (f := proj r k) proj_surjective

theorem center_statedProj_statedSp_eq_bot (hr : 2 ≤ r) :
    Subgroup.center (StatedProj (StatedSp r k)) = ⊥ := by
  have : NeZero r := ⟨by omega⟩
  by_cases hk : r = 2 ∧ Nat.card k = 2
  ·
    have hchar : CharP k 2 := by
      have := charP_two_of_card (K := k) (f := 1) (by rw [hk.2]; rfl)
      exact this
    have hinj : Function.Injective (proj r k) :=
      proj_injective_sp (f := 1) (by rw [hk.2]; rfl) le_rfl NeZero.one_le
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨g, rfl⟩ := proj_surjective x
    have hg : g ∈ Subgroup.center (StatedSp r k) := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply hinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hx (proj r k h)
    rw [eq_one_of_central_statedSp hg, map_one]
  · have hsimple := isSimpleGroup_statedProj_statedSp_of_two_le hr hk
    have hperf := isPerfect_statedProj_statedSp_of_two_le hr hk
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedProj (StatedSp r k)))
      with h | h
    · exact h
    · exfalso
      have h1 := (commutator_eq_bot_iff_center_eq_top (StatedProj (StatedSp r k))).2 h
      rw [Group.IsPerfect.commutator_eq_top] at h1
      have : Nontrivial (StatedProj (StatedSp r k)) :=
        (CFSG.LieType.Classical.symplectic_projective_nontrivial k r (by omega)).1
      exact top_ne_bot h1

end Center

section Data

theorem fieldAutData_projectiveSp_odd (hpair : SubfieldPairSpOdd) {r : ℕ} (hr : 2 ≤ r)
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) :
    FieldAutData (StatedProj (StatedSp r K)) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero r := ⟨by omega⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card hℓ hf hK
  have O : SpOuter ℓ f r K := spOuter hℓ hf hr hK
  refine fieldAutData_of_standard (spLinearAutGroup r K)
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = fieldAut r K σ} ?_ ?_ ?_ ?_ ?_
  ·
    intro E hE hEc
    by_cases hEH : E ≤ inner (StatedProj (StatedSp r K))
    · obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
        rw [hbot, Subgroup.card_bot] at hEc
        have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
        omega
      obtain ⟨g, rfl⟩ := hEH haE
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (map_one _)
    · have hcard := card_inf_inner_eq_prime O hr hp hp2 hcyc hEc hEH
      have h1 : (E ⊓ inner (StatedProj (StatedSp r K)) :
          Subgroup (MulAut (StatedProj (StatedSp r K)))) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hcard]
        exact hp.one_lt
      obtain ⟨⟨a, haE, haI⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
      obtain ⟨g, rfl⟩ := haI
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (Subtype.ext (map_one _))
  ·
    intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    have hαE : α ∈ spSemilinearAutGroup r K :=
      mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd (hord ▸ hpodd)
    have hαD : α ∉ spLinearAutGroup r K := fun hD => by
      have := inner_normal (StatedProj (StatedSp r K))
      obtain ⟨g, hg⟩ := mem_of_pow_eq_one_of_relIndex_dvd_two
        (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hp hp2 hD hαp
      exact hout g hg.symm
    obtain ⟨-, σ, hσord, h, hhD, hαh⟩ := O.descent p hp α hαE hαD hord
    exact ⟨h, hhD, fieldAut r K σ, ⟨σ, hσord, rfl⟩, hαh⟩
  ·
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
    have hτp : τ ^ p = 1 := hτ ▸ pow_orderOf_eq_one τ
    have hfield : descentField σ = descentField τ := fixedField_eq_of_orderOf hℓ hf hK hσ hτ
    rw [fixedSubgroup_fieldAut_eq_range_sp hpodd hσp, fixedSubgroup_fieldAut_eq_range_sp hpodd hτp,
      range_subfieldProj_eq_map, range_subfieldProj_eq_map, hfield]
  ·
    rintro _ ⟨σ, hσ, rfl⟩ _ x hx hcomm
    have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
    have hcardk : Finite (descentField σ) := inferInstance
    rw [fixedSubgroup_fieldAut_eq_range_sp hpodd hσp, ← range_subfieldInj] at hx hcomm
    obtain ⟨y, rfl⟩ := hx
    have hy : y ∈ Subgroup.center (StatedProj (StatedSp r (descentField σ))) := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply subfieldInj_injective (r := r) σ
      rw [map_mul, map_mul]
      exact (hcomm (subfieldInj σ z) ⟨z, rfl⟩).symm
    rw [center_statedProj_statedSp_eq_bot hr, Subgroup.mem_bot] at hy
    rw [hy, map_one]
  ·
    rintro _ ⟨σ, hσ, rfl⟩ d hd hne
    left
    obtain ⟨A, rfl⟩ := mem_spLinearAutGroup_iff.mp hd
    have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
    rw [fixedSubgroup_fieldAut_eq_range_sp hpodd hσp, range_subfieldProj_eq_map] at hne ⊢
    set k := descentField σ with hk
    have hpf : p ∣ f ∧ Nat.card k = ℓ ^ (f / p) := card_semilinearFixedSubfield hℓ hf hK hσ
    have hcardK : Nat.card K = Nat.card k ^ p := by
      rw [hK, hpf.2, ← pow_mul, Nat.div_mul_cancel hpf.1]
    have hne' : (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k := by
      intro h
      apply hne
      rw [map_conjAut_map_proj, h]
    have hgen := hpair K k p hp hp2 hcardK r hr A hne'
    have h4 := congrArg (Subgroup.map (proj r K)) hgen
    rw [map_closure_union, Subgroup.map_top_of_surjective _ proj_surjective] at h4
    rw [map_conjAut_map_proj]
    exact h4

end Data

end CFSG.LieType.SeitzGeneration
