module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerData
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm

private lemma conjNormal_mem_a11TwoSetStab (τ : Equiv.Perm (Fin 11)) {i j : Fin 11}
    {y : alternatingGroup (Fin 11)} (hy : y ∈ a11TwoSetStab i j) :
    (MulAut.conjNormal (H := alternatingGroup (Fin 11)) τ) y ∈
      a11TwoSetStab (τ i) (τ j) := by
  rcases hy with ⟨hyi, hyj⟩ | ⟨hyi, hyj⟩
  · refine Or.inl ⟨?_, ?_⟩ <;>
      rw [MulAut.conjNormal_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] <;>
      simp [hyi, hyj]
  · refine Or.inr ⟨?_, ?_⟩ <;>
      rw [MulAut.conjNormal_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] <;>
      simp [hyi, hyj]

private lemma map_conjNormal_a11TwoSetStab (τ : Equiv.Perm (Fin 11)) {i j : Fin 11} :
    (a11TwoSetStab i j).map
        (MulAut.conjNormal (H := alternatingGroup (Fin 11)) τ).toMonoidHom =
      a11TwoSetStab (τ i) (τ j) := by
  ext σ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact conjNormal_mem_a11TwoSetStab τ hy
  · intro hσ
    refine ⟨(MulAut.conjNormal (H := alternatingGroup (Fin 11)) τ⁻¹) σ, ?_, ?_⟩
    · simpa using
        conjNormal_mem_a11TwoSetStab (τ := τ⁻¹) (i := τ i) (j := τ j) hσ
    · change ((MulAut.conjNormal (H := alternatingGroup (Fin 11)) τ) *
        (MulAut.conjNormal (H := alternatingGroup (Fin 11)) τ⁻¹)) σ = σ
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl

theorem exists_mulAut_map_a11TwoSetStab {i j : Fin 11} (hij : i ≠ j) :
    ∃ c : MulAut (alternatingGroup (Fin 11)),
      (a11TwoSetStab i j).map c.toMonoidHom = a11TwoSetStab 9 10 := by
  classical
  let a : Equiv.Perm (Fin 11) := Equiv.swap i 9
  let b : Equiv.Perm (Fin 11) := Equiv.swap (a j) 10
  let τ : Equiv.Perm (Fin 11) := b * a
  have haj9 : a j ≠ 9 := by
    intro h
    have h' : j = i := by simpa [a] using congrArg a h
    exact hij h'.symm
  have hτi : τ i = 9 := by
    have h9aj : (9 : Fin 11) ≠ a j := haj9.symm
    simp only [τ, b, a, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne h9aj (by norm_num)
  have hτj : τ j = 10 := by
    by_cases h : a j = 10 <;> simp [τ, b, h]
  refine ⟨MulAut.conjNormal (H := alternatingGroup (Fin 11)) τ, ?_⟩
  rw [map_conjNormal_a11TwoSetStab τ, hτi, hτj]

private def a11CycleThree : alternatingGroup (Fin 11) :=
  ⟨c[0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def a11CycleThree' : alternatingGroup (Fin 11) :=
  ⟨c[3, 4, 5], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def a11CycleFive : alternatingGroup (Fin 11) :=
  ⟨c[3, 4, 5, 6, 7], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private lemma a11CycleThree_pow_three : a11CycleThree ^ 3 = 1 := by
  apply Subtype.ext
  decide

private lemma a11CycleThree'_pow_three : a11CycleThree' ^ 3 = 1 := by
  apply Subtype.ext
  decide

private lemma a11CycleFive_pow_five : a11CycleFive ^ 5 = 1 := by
  apply Subtype.ext
  decide

private lemma a11CycleThree_ne_one : a11CycleThree ≠ 1 := by
  intro h
  have h0 : ((a11CycleThree : Equiv.Perm (Fin 11)) 0) = 0 :=
    congrArg (fun z : alternatingGroup (Fin 11) =>
      (z : Equiv.Perm (Fin 11)) 0) h
  have h1 : ((a11CycleThree : Equiv.Perm (Fin 11)) 0) ≠ 0 := by decide
  exact h1 h0

private lemma a11CycleFive_ne_one : a11CycleFive ≠ 1 := by
  intro h
  have h0 : ((a11CycleFive : Equiv.Perm (Fin 11)) 3) = 3 :=
    congrArg (fun z : alternatingGroup (Fin 11) =>
      (z : Equiv.Perm (Fin 11)) 3) h
  have h1 : ((a11CycleFive : Equiv.Perm (Fin 11)) 3) ≠ 3 := by decide
  exact h1 h0

private lemma a11CycleThree_orderOf : orderOf a11CycleThree = 3 := by
  exact orderOf_eq_prime a11CycleThree_pow_three a11CycleThree_ne_one

private lemma a11CycleThree'_orderOf : orderOf a11CycleThree' = 3 := by
  refine orderOf_eq_prime a11CycleThree'_pow_three ?_
  intro h
  have h3 : ((a11CycleThree' : Equiv.Perm (Fin 11)) 3) = 3 :=
    congrArg (fun z : alternatingGroup (Fin 11) =>
      (z : Equiv.Perm (Fin 11)) 3) h
  have h4 : ((a11CycleThree' : Equiv.Perm (Fin 11)) 3) ≠ 3 := by decide
  exact h4 h3

private lemma a11CycleFive_orderOf : orderOf a11CycleFive = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime a11CycleFive_pow_five a11CycleFive_ne_one

private lemma a11CycleThree_mem : a11CycleThree ∈ a11TwoSetStab 9 10 := by
  change (((a11CycleThree : Equiv.Perm (Fin 11)) 9 = 9 ∧
      (a11CycleThree : Equiv.Perm (Fin 11)) 10 = 10) ∨
    ((a11CycleThree : Equiv.Perm (Fin 11)) 9 = 10 ∧
      (a11CycleThree : Equiv.Perm (Fin 11)) 10 = 9))
  decide

private lemma a11CycleThree'_mem : a11CycleThree' ∈ a11TwoSetStab 9 10 := by
  change (((a11CycleThree' : Equiv.Perm (Fin 11)) 9 = 9 ∧
      (a11CycleThree' : Equiv.Perm (Fin 11)) 10 = 10) ∨
    ((a11CycleThree' : Equiv.Perm (Fin 11)) 9 = 10 ∧
      (a11CycleThree' : Equiv.Perm (Fin 11)) 10 = 9))
  decide

private lemma a11CycleFive_mem : a11CycleFive ∈ a11TwoSetStab 9 10 := by
  change (((a11CycleFive : Equiv.Perm (Fin 11)) 9 = 9 ∧
      (a11CycleFive : Equiv.Perm (Fin 11)) 10 = 10) ∨
    ((a11CycleFive : Equiv.Perm (Fin 11)) 9 = 10 ∧
      (a11CycleFive : Equiv.Perm (Fin 11)) 10 = 9))
  decide

private lemma a11CycleThree_commute : Commute a11CycleThree a11CycleThree' := by
  apply Subtype.ext
  decide

private lemma a11CycleThree_commute_five : Commute a11CycleThree a11CycleFive := by
  apply Subtype.ext
  decide

private lemma a11CycleThree'_notMem_zpowers :
    a11CycleThree' ∉ Subgroup.zpowers a11CycleThree := by
  intro h
  have hle : Subgroup.zpowers a11CycleThree ≤
      MulAction.stabilizer (alternatingGroup (Fin 11)) (3 : Fin 11) :=
    Subgroup.zpowers_le.mpr (by
      rw [MulAction.mem_stabilizer_iff]
      change ((a11CycleThree : Equiv.Perm (Fin 11)) 3) = 3
      decide)
  have hfix := hle h
  rw [MulAction.mem_stabilizer_iff] at hfix
  have hnot : ((a11CycleThree' : Equiv.Perm (Fin 11)) 3) ≠ 3 := by decide
  exact hnot hfix

private def finFiveToEleven : Fin 5 ↪ Fin 11 where
  toFun k := ⟨6 + k.1, by have := k.2; omega⟩
  inj' := by
    intro a b h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)

private noncomputable def a11LiftA5 : alternatingGroup (Fin 5) →* alternatingGroup (Fin 11) :=
  ((Equiv.Perm.viaEmbeddingHom finFiveToEleven).comp
      (alternatingGroup (Fin 5)).subtype).codRestrict (alternatingGroup (Fin 11)) fun σ => by
    rw [Equiv.Perm.mem_alternatingGroup]
    have hσ : Equiv.Perm.sign (σ : Equiv.Perm (Fin 5)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp σ.2
    rw [MonoidHom.comp_apply, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding,
      Equiv.Perm.sign_extendDomain]
    exact hσ

private lemma a11LiftA5_injective : Function.Injective a11LiftA5 := by
  intro x y h
  have h' := congrArg (fun z : alternatingGroup (Fin 11) =>
    (z : Equiv.Perm (Fin 11))) h
  have h'' : (Equiv.Perm.viaEmbeddingHom finFiveToEleven) (x : Equiv.Perm (Fin 5)) =
      (Equiv.Perm.viaEmbeddingHom finFiveToEleven) (y : Equiv.Perm (Fin 5)) := by
    simpa [a11LiftA5] using h'
  exact Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective finFiveToEleven h'')

private lemma a11LiftA5_apply_of_notMem (x : alternatingGroup (Fin 5)) {k : Fin 11}
    (hk : k ∉ Set.range finFiveToEleven) :
    (a11LiftA5 x : Equiv.Perm (Fin 11)) k = k := by
  change (Equiv.Perm.viaEmbeddingHom finFiveToEleven) (x : Equiv.Perm (Fin 5)) k = k
  exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk

private lemma a11LiftA5_apply_range (x : alternatingGroup (Fin 5)) (j : Fin 5) :
    (a11LiftA5 x : Equiv.Perm (Fin 11)) (finFiveToEleven j) =
      finFiveToEleven ((x : Equiv.Perm (Fin 5)) j) := by
  change (Equiv.Perm.viaEmbeddingHom finFiveToEleven) (x : Equiv.Perm (Fin 5))
    (finFiveToEleven j) = finFiveToEleven ((x : Equiv.Perm (Fin 5)) j)
  exact Equiv.Perm.viaEmbedding_apply _ _ _

private lemma mem_range_finFiveToEleven {k : Fin 11} :
    k ∈ Set.range finFiveToEleven ↔ 6 ≤ k.val := by
  constructor
  · rintro ⟨j, rfl⟩
    change 6 ≤ 6 + j.val
    omega
  · intro hk
    refine ⟨⟨k.val - 6, by omega⟩, ?_⟩
    apply Fin.ext
    change 6 + (k.val - 6) = k.val
    omega

private lemma a11CycleThree_fix_range (j : Fin 5) :
    (a11CycleThree : Equiv.Perm (Fin 11)) (finFiveToEleven j) = finFiveToEleven j := by
  fin_cases j <;> decide

private lemma a11CycleThree'_fix_range (j : Fin 5) :
    (a11CycleThree' : Equiv.Perm (Fin 11)) (finFiveToEleven j) = finFiveToEleven j := by
  fin_cases j <;> decide

private lemma a11CycleThree_lt_six {k : Fin 11} (hk : k.val < 6) :
    ((a11CycleThree : Equiv.Perm (Fin 11)) k).val < 6 := by
  revert hk
  fin_cases k <;> decide

private lemma a11CycleThree'_lt_six {k : Fin 11} (hk : k.val < 6) :
    ((a11CycleThree' : Equiv.Perm (Fin 11)) k).val < 6 := by
  revert hk
  fin_cases k <;> decide

private lemma a11LiftA5_commute_three (x : alternatingGroup (Fin 5)) :
    Commute (a11LiftA5 x) a11CycleThree := by
  apply Subtype.ext
  ext k
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
  by_cases hk : k ∈ Set.range finFiveToEleven
  · obtain ⟨j, rfl⟩ := hk
    rw [a11CycleThree_fix_range j, a11LiftA5_apply_range, a11CycleThree_fix_range]
  · have hklt : k.val < 6 := by
      by_contra h
      exact hk ((mem_range_finFiveToEleven).mpr (by omega))
    have hkσ' : (a11CycleThree : Equiv.Perm (Fin 11)) k ∉ Set.range finFiveToEleven := by
      rw [mem_range_finFiveToEleven]
      exact not_le.mpr (a11CycleThree_lt_six hklt)
    rw [a11LiftA5_apply_of_notMem x hkσ',
      a11LiftA5_apply_of_notMem x hk]

private lemma a11LiftA5_commute_three' (x : alternatingGroup (Fin 5)) :
    Commute (a11LiftA5 x) a11CycleThree' := by
  apply Subtype.ext
  ext k
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
  by_cases hk : k ∈ Set.range finFiveToEleven
  · obtain ⟨j, rfl⟩ := hk
    rw [a11CycleThree'_fix_range j, a11LiftA5_apply_range, a11CycleThree'_fix_range]
  · have hklt : k.val < 6 := by
      by_contra h
      exact hk ((mem_range_finFiveToEleven).mpr (by omega))
    have hkσ' : (a11CycleThree' : Equiv.Perm (Fin 11)) k ∉ Set.range finFiveToEleven := by
      rw [mem_range_finFiveToEleven]
      exact not_le.mpr (a11CycleThree'_lt_six hklt)
    rw [a11LiftA5_apply_of_notMem x hkσ',
      a11LiftA5_apply_of_notMem x hk]

private lemma not_isPSolvable_centralizer_cycles :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(Subgroup.centralizer ({a11CycleThree, a11CycleThree'} :
        Set (alternatingGroup (Fin 11)))) := by
  have hcard5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hnot : ¬ CFSG.HallHigman.IsPSolvable 3 (alternatingGroup (Fin 5)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer.not_isPSolvable_of_simple
      alternatingGroup.isSimpleGroup_five
      (by
        rw [alternatingGroup.isMulCommutative_iff_card_le_three, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        norm_num)
      (by rw [hcard5]; norm_num)
  intro hsolv
  have hrange : a11LiftA5.range ≤
      Subgroup.centralizer ({a11CycleThree, a11CycleThree'} :
        Set (alternatingGroup (Fin 11))) := by
    rintro y ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases hz with rfl | rfl
    · exact (a11LiftA5_commute_three x).symm
    · exact (a11LiftA5_commute_three' x).symm
  have hsolvRange : CFSG.HallHigman.IsPSolvable 3 ↥(a11LiftA5.range) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
      hsolv hrange
  have e : alternatingGroup (Fin 5) ≃* ↥(a11LiftA5.range) :=
    MonoidHom.ofInjective a11LiftA5_injective
  exact hnot
    (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      e.symm hsolvRange)

private lemma exists_sylow_stab_contains_cycles :
    ∃ P₀ : Sylow 3 (a11TwoSetStab 9 10),
      (⟨a11CycleThree, a11CycleThree_mem⟩ : a11TwoSetStab 9 10) ∈ (P₀ : Subgroup _) ∧
      (⟨a11CycleThree', a11CycleThree'_mem⟩ : a11TwoSetStab 9 10) ∈
        (P₀ : Subgroup _) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup (alternatingGroup (Fin 11)) := a11TwoSetStab 9 10
  have hσ1S : a11CycleThree ∈ S := a11CycleThree_mem
  have hσ2S : a11CycleThree' ∈ S := a11CycleThree'_mem
  let E : Subgroup (alternatingGroup (Fin 11)) :=
    Subgroup.zpowers a11CycleThree ⊔ Subgroup.zpowers a11CycleThree'
  have hES : E ≤ S :=
    sup_le (Subgroup.zpowers_le.mpr hσ1S) (Subgroup.zpowers_le.mpr hσ2S)
  have hcardz : Nat.card (Subgroup.zpowers a11CycleThree) = 3 := by
    rw [Nat.card_zpowers, a11CycleThree_orderOf]
  have hcomm : ∀ a ∈ Subgroup.zpowers a11CycleThree,
      a * a11CycleThree' = a11CycleThree' * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (a11CycleThree_commute.zpow_left n).eq
  have hEea : CFSG.Open.IsElemAbelian 3 E :=
    (CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3) hcardz
      a11CycleThree'_orderOf a11CycleThree'_notMem_zpowers hcomm).1
  have hEp : IsPGroup 3 ↥E := CFSG.Open.IsElemAbelian.isPGroup hEea
  have hEsubP : IsPGroup 3 ↥(E.subgroupOf S) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hES).symm
  obtain ⟨P₀, hP₀⟩ := hEsubP.exists_le_sylow
  exact ⟨P₀,
    hP₀ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))),
    hP₀ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))⟩

private lemma exists_conj_mem_sylow (T : Sylow 3 (alternatingGroup (Fin 11)))
    (hT : (T : Subgroup (alternatingGroup (Fin 11))) ≤ a11TwoSetStab 9 10) :
    ∃ g : alternatingGroup (Fin 11), g ∈ a11TwoSetStab 9 10 ∧
      (MulAut.conj g) a11CycleThree ∈ (T : Subgroup (alternatingGroup (Fin 11))) ∧
      (MulAut.conj g) a11CycleThree' ∈ (T : Subgroup (alternatingGroup (Fin 11))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup (alternatingGroup (Fin 11)) := a11TwoSetStab 9 10
  obtain ⟨P₀, hσ1P₀, hσ2P₀⟩ := exists_sylow_stab_contains_cycles
  let Tsub : Sylow 3 S := T.subtype hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P₀ Tsub
  have hgS : (g : alternatingGroup (Fin 11)) ∈ S := g.2
  have hs1S : (MulAut.conj (g : alternatingGroup (Fin 11))) a11CycleThree ∈ S := by
    rw [MulAut.conj_apply]
    exact S.mul_mem (S.mul_mem hgS a11CycleThree_mem) (S.inv_mem hgS)
  have hs2S : (MulAut.conj (g : alternatingGroup (Fin 11))) a11CycleThree' ∈ S := by
    rw [MulAut.conj_apply]
    exact S.mul_mem (S.mul_mem hgS a11CycleThree'_mem) (S.inv_mem hgS)
  refine ⟨(g : alternatingGroup (Fin 11)), hgS, ?_, ?_⟩
  · have hmem : (⟨(MulAut.conj (g : alternatingGroup (Fin 11))) a11CycleThree,
        hs1S⟩ : S) ∈ (Tsub : Subgroup S) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨⟨a11CycleThree, a11CycleThree_mem⟩, hσ1P₀, rfl⟩
    have hTmem := hmem
    rw [Sylow.coe_subtype] at hTmem
    simpa using Subgroup.mem_subgroupOf.mp hTmem
  · have hmem : (⟨(MulAut.conj (g : alternatingGroup (Fin 11))) a11CycleThree',
        hs2S⟩ : S) ∈ (Tsub : Subgroup S) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨⟨a11CycleThree', a11CycleThree'_mem⟩, hσ2P₀, rfl⟩
    have hTmem := hmem
    rw [Sylow.coe_subtype] at hTmem
    simpa using Subgroup.mem_subgroupOf.mp hTmem

private lemma conj_cycles_basic (g : alternatingGroup (Fin 11)) :
    ((MulAut.conj g) a11CycleThree) ^ 3 = 1 ∧
      ((MulAut.conj g) a11CycleThree') ^ 3 = 1 ∧
      (MulAut.conj g) a11CycleThree ≠ 1 ∧
      Commute ((MulAut.conj g) a11CycleThree) ((MulAut.conj g) a11CycleThree') ∧
      (MulAut.conj g) a11CycleThree' ∉
        Subgroup.zpowers ((MulAut.conj g) a11CycleThree) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, a11CycleThree_pow_three, map_one]
  · rw [← map_pow, a11CycleThree'_pow_three, map_one]
  · simpa using (MulAut.conj g).injective.ne a11CycleThree_ne_one
  · exact a11CycleThree_commute.map (MulAut.conj g)
  · intro hmem
    apply a11CycleThree'_notMem_zpowers
    have hmap : (Subgroup.zpowers ((MulAut.conj g) a11CycleThree)).map
        (MulAut.conj g).symm.toMonoidHom = Subgroup.zpowers a11CycleThree := by
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers ((MulAut.conj g).symm_apply_apply a11CycleThree)
    have himg : a11CycleThree' ∈
        (Subgroup.zpowers ((MulAut.conj g) a11CycleThree)).map
          (MulAut.conj g).symm.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨(MulAut.conj g) a11CycleThree', hmem,
        (MulAut.conj g).symm_apply_apply a11CycleThree'⟩
    rwa [hmap] at himg

private lemma conj_cycles_not_isPSolvable (g : alternatingGroup (Fin 11)) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(Subgroup.centralizer ({(MulAut.conj g) a11CycleThree,
        (MulAut.conj g) a11CycleThree'} : Set (alternatingGroup (Fin 11)))) := by
  intro hsolv
  have hmap : (Subgroup.centralizer ({(MulAut.conj g) a11CycleThree,
        (MulAut.conj g) a11CycleThree'} : Set (alternatingGroup (Fin 11)))).map
        (MulAut.conj g).symm.toMonoidHom =
      Subgroup.centralizer ({a11CycleThree, a11CycleThree'} :
        Set (alternatingGroup (Fin 11))) := by
    have h := CFSG.Glauberman.map_centralizer_eq_of_equiv
      (e := (MulAut.conj g).symm)
      (P := Subgroup.closure ({(MulAut.conj g) a11CycleThree,
        (MulAut.conj g) a11CycleThree'} : Set (alternatingGroup (Fin 11))))
    rw [Subgroup.centralizer_closure, MonoidHom.map_closure,
      Subgroup.centralizer_closure, Set.image_pair] at h
    convert h using 2
    change {a11CycleThree, a11CycleThree'} =
      {((MulAut.conj g).symm) ((MulAut.conj g) a11CycleThree),
        ((MulAut.conj g).symm) ((MulAut.conj g) a11CycleThree')}
    rw [(MulAut.conj g).symm_apply_apply, (MulAut.conj g).symm_apply_apply]
  have hsolv' :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      (MulAut.conj g).symm.toMonoidHom hsolv
  rw [hmap] at hsolv'
  exact not_isPSolvable_centralizer_cycles hsolv'

private lemma conj_five_spec (g : alternatingGroup (Fin 11))
    (hg : g ∈ a11TwoSetStab 9 10) :
    (MulAut.conj g) a11CycleFive ∈ a11TwoSetStab 9 10 ∧
      orderOf ((MulAut.conj g) a11CycleFive) = 5 ∧
      Commute ((MulAut.conj g) a11CycleThree) ((MulAut.conj g) a11CycleFive) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [MulAut.conj_apply]
    exact (a11TwoSetStab 9 10).mul_mem
      ((a11TwoSetStab 9 10).mul_mem hg a11CycleFive_mem)
      ((a11TwoSetStab 9 10).inv_mem hg)
  · rw [(MulAut.conj g).orderOf_eq, a11CycleFive_orderOf]
  · exact a11CycleThree_commute_five.map (MulAut.conj g)

private lemma exists_conj_spec (T : Sylow 3 (alternatingGroup (Fin 11)))
    (g : alternatingGroup (Fin 11)) (hg : g ∈ a11TwoSetStab 9 10)
    (h1 : (MulAut.conj g) a11CycleThree ∈ (T : Subgroup (alternatingGroup (Fin 11))))
    (h2 : (MulAut.conj g) a11CycleThree' ∈ (T : Subgroup (alternatingGroup (Fin 11)))) :
    ∃ s₁ s₂ t : alternatingGroup (Fin 11),
      s₁ ∈ (T : Subgroup (alternatingGroup (Fin 11))) ∧
      s₂ ∈ (T : Subgroup (alternatingGroup (Fin 11))) ∧
      s₁ ^ 3 = 1 ∧ s₂ ^ 3 = 1 ∧ s₁ ≠ 1 ∧ Commute s₁ s₂ ∧
      s₂ ∉ Subgroup.zpowers s₁ ∧
      ¬ CFSG.HallHigman.IsPSolvable 3
          ↥(Subgroup.centralizer ({s₁, s₂} : Set (alternatingGroup (Fin 11)))) ∧
      t ∈ a11TwoSetStab 9 10 ∧ orderOf t = 5 ∧ Commute s₁ t := by
  obtain ⟨hpow1, hpow2, hne, hcomm, hnotz⟩ := conj_cycles_basic g
  have hnotC := conj_cycles_not_isPSolvable g
  obtain ⟨htm, htord, hcommt⟩ := conj_five_spec g hg
  exact ⟨(MulAut.conj g) a11CycleThree, (MulAut.conj g) a11CycleThree',
    (MulAut.conj g) a11CycleFive, h1, h2, hpow1, hpow2, hne, hcomm, hnotz, hnotC,
    htm, htord, hcommt⟩

theorem exists_caseTwo_perms (T : Sylow 3 (alternatingGroup (Fin 11)))
    (hT : (T : Subgroup (alternatingGroup (Fin 11))) ≤ a11TwoSetStab 9 10) :
    ∃ s₁ s₂ t : alternatingGroup (Fin 11),
      s₁ ∈ (T : Subgroup (alternatingGroup (Fin 11))) ∧
      s₂ ∈ (T : Subgroup (alternatingGroup (Fin 11))) ∧
      s₁ ^ 3 = 1 ∧ s₂ ^ 3 = 1 ∧ s₁ ≠ 1 ∧ Commute s₁ s₂ ∧
      s₂ ∉ Subgroup.zpowers s₁ ∧
      ¬ CFSG.HallHigman.IsPSolvable 3
          ↥(Subgroup.centralizer ({s₁, s₂} : Set (alternatingGroup (Fin 11)))) ∧
      t ∈ a11TwoSetStab 9 10 ∧ orderOf t = 5 ∧ Commute s₁ t := by
  obtain ⟨g, hg, h1, h2⟩ := exists_conj_mem_sylow T hT
  exact exists_conj_spec T g hg h1 h2

private lemma not_pow_three_dvd_factorial_eleven {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 3 ∣ Nat.factorial 11 := by
  intro h
  have hp11 : p ≤ 11 :=
    (hp.dvd_factorial).1 ((dvd_pow_self p (by norm_num)).trans h)
  have key : ∀ p < 12, p.Prime → 5 ≤ p → ¬ p ^ 3 ∣ Nat.factorial 11 := by decide
  exact key p (by omega) hp hp5 h

private lemma eq_five_of_pow_two_dvd_factorial_eleven {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ Nat.factorial 11) : p = 5 := by
  have hp11 : p ≤ 11 :=
    (hp.dvd_factorial).1 ((dvd_pow_self p (by norm_num)).trans h)
  have key : ∀ p < 12, p.Prime → 5 ≤ p → p ^ 2 ∣ Nat.factorial 11 → p = 5 := by decide
  exact key p (by omega) hp hp5 h

theorem pRank_top_le_two_of_card_dvd_factorial {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hY : Nat.card Y ∣ Nat.factorial 11) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 ∧
      (2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) → p = 5) := by
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup Y)
  have hdvd : p ^ CFSG.Open.pRank p (⊤ : Subgroup Y) ∣ Nat.factorial 11 := by
    rw [← hEcard]
    exact (Subgroup.card_subgroup_dvd_card E).trans hY
  constructor
  · by_contra hle
    have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by omega
    exact not_pow_three_dvd_factorial_eleven hp hp5 ((pow_dvd_pow p h3).trans hdvd)
  · intro h2
    exact eq_five_of_pow_two_dvd_factorial_eleven hp hp5
      ((pow_dvd_pow p h2).trans hdvd)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
