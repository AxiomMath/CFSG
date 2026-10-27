module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueTab
public import Certificates.Certificate25230
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJSyl

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.F3.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native
open CFSG.EvenSporadicStandard.TwoFi22.FrameJ (card_D_slvl_le)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section


@[expose] noncomputable def uqG0 (k : ℕ) : J := treeG TS[0]! (pairG sylG) k

@[expose] noncomputable def uqG1 (k : ℕ) : J := treeG TS[1]! (pairG sylG) k

theorem tabS0_size : (tabS 0).size = 1024 := by
  rw [tabS_size, TS_size (l := 0) rfl]

theorem tabS1_size : (tabS 1).size = 128 := by
  rw [tabS_size, TS_size (l := 1) rfl]

theorem uqG0_rep : ∀ k < (tabS 0).size, Rep 3510 (tabS 0)[k]! (uqG0 k) := fun k hk =>
  rep_tabS (i := 0) (by rw [sylBase_size]; norm_num) (by rwa [tabS_size] at hk)

theorem uqG1_rep : ∀ k < (tabS 1).size, Rep 3510 (tabS 1)[k]! (uqG1 k) := fun k hk =>
  rep_tabS (i := 1) (by rw [sylBase_size]; norm_num) (by rwa [tabS_size] at hk)

theorem uqG0_mem {k : ℕ} (hk : k < 1024) : uqG0 k ∈ slvl 0 :=
  (syl_facts.1 0 (by rw [sylBase_size]; norm_num)).treeG_mem
    (by rw [TS_size (l := 0) rfl]; exact hk)

theorem uqG1_mem {k : ℕ} (hk : k < 128) : uqG1 k ∈ slvl 0 :=
  levelGroup_anti (letters := LS) (base := sylBase) (pairG sylG) (Nat.zero_le 1)
    ((syl_facts.1 1 (by rw [sylBase_size]; norm_num)).treeG_mem
      (by rw [TS_size (l := 1) rfl]; exact hk))

theorem exists_uqG_mul {s : J} (hs : s ∈ slvl 0) :
    ∃ k₀ < 1024, ∃ k₁ < 128, s = uqG0 k₀ * uqG1 k₁ := by
  obtain ⟨k0, hk0, h, hh, rfl⟩ :=
    exists_tree_mul (i := 0) (by rw [sylBase_size]; norm_num) hs
  obtain ⟨k1, hk1, h', hh', rfl⟩ :=
    exists_tree_mul (i := 1) (by rw [sylBase_size]; norm_num) hh
  have hh'' : h' ∈ slvl 2 := hh'
  rw [slvl_two, Subgroup.mem_bot] at hh''
  subst hh''
  refine ⟨k0, ?_, k1, ?_, ?_⟩
  · rwa [TS_size (l := 0) rfl] at hk0
  · rwa [TS_size (l := 1) rfl] at hk1
  · rw [mul_one]
    rfl

theorem uqTabFacts :
    TabFacts uqG0 uqG1 1024 128 uqDp uqBas uqW (uqCols uqW uqSg0) (uqCols uqW uqSg1) := by
  have h : uqTabCheckT orb.alpha (tabS 0) (tabS 1) uqDp uqBas uqW uqSg0 uqSg1 = true :=
    Certificates.certificate25230
  have := uqTabCheckT_sound uqG0_rep uqG1_rep h
  rwa [tabS0_size, tabS1_size] at this

theorem cp_of_fc
    (hfc : fcSpec (uqCols uqW uqSg0) (uqCols uqW uqSg1))
    {A : Subgroup J} (hA : A ≤ slvl 0) (hsq : ∀ a ∈ A, a ^ 2 = 1) (hcard : 2 ^ 10 ≤ Nat.card A)
    (hE : Nat.card (Subgroup.closure {x : J | x ∈ D ∧ x ∈ slvl 0}) = 2 ^ 10) :
    A ≤ Subgroup.closure {x : J | x ∈ D ∧ x ∈ slvl 0} := by
  have hT := uqTabFacts
  have hδS : ∀ j < 22, uqDelta uqG0 uqG1 uqDp j ∈ slvl 0 := fun j hj => by
    obtain ⟨h1, h2⟩ := hT.pair_lt j hj
    exact (slvl 0).mul_mem (uqG0_mem h1) (uqG1_mem h2)
  have hbS : ∀ i < 10, uqB uqG0 uqG1 uqDp uqBas i ∈ slvl 0 := fun i hi =>
    hδS _ (hT.bas_lt i hi)
  have hbD : ∀ i < 10, uqB uqG0 uqG1 uqDp uqBas i ∈ D := fun i hi =>
    hT.delta_D _ (hT.bas_lt i hi)
  have hbsq : ∀ i < 10, uqB uqG0 uqG1 uqDp uqBas i * uqB uqG0 uqG1 uqDp uqBas i = 1 :=
    fun i hi => by
      rw [← pow_two]
      have := pow_orderOf_eq_one (uqB uqG0 uqG1 uqDp uqBas i)
      rwa [orderOf_of_mem_D (hbD i hi)] at this
  have hsurj : ∀ x : J, x ∈ D → x ∈ slvl 0 → ∃ j < 22, uqDelta uqG0 uqG1 uqDp j = x := by
    let f : Fin 22 → {x : J // x ∈ D ∧ x ∈ slvl 0} := fun j =>
      ⟨uqDelta uqG0 uqG1 uqDp j, hT.delta_D j j.2, hδS j j.2⟩
    have hinj : ∀ i j : Fin 22, uqDelta uqG0 uqG1 uqDp i = uqDelta uqG0 uqG1 uqDp j → i = j :=
      fun i j h => Fin.ext (hT.delta_inj i i.2 j j.2 h)
    have hf : Function.Injective f := by
      intro i j h
      have h' : (f i).1 = (f j).1 := by rw [h]
      exact hinj i j h'
    have h22 : Nat.card (Fin 22) = 22 := by simp
    have hcardle : Nat.card {x : J // x ∈ D ∧ x ∈ slvl 0} ≤ Nat.card (Fin 22) :=
      card_D_slvl_le.trans_eq h22.symm
    have hb := hf.bijective_of_nat_card_le hcardle
    intro x hxD hxS
    obtain ⟨j, hj⟩ := hb.2 ⟨x, hxD, hxS⟩
    have hj' : (f j).1 = x := by rw [hj]
    exact ⟨j, j.2, hj'⟩
  have hcl : Subgroup.closure {x : J | x ∈ D ∧ x ∈ slvl 0} =
      Subgroup.closure (uqB uqG0 uqG1 uqDp uqBas '' Set.Iio 10) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x ⟨hxD, hxS⟩
      obtain ⟨j, hj, rfl⟩ := hsurj x hxD hxS
      rw [hT.delta_phi j hj]
      exact phi_mem _
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      exact Subgroup.subset_closure ⟨hbD i hi, hbS i hi⟩
  have hAbs : AbsData J (slvl 0) (uqB uqG0 uqG1 uqDp uqBas) uqG0 uqG1 (uqCols uqW uqSg0)
      (uqCols uqW uqSg1) :=
    { card_S := by rw [card_slvl_zero]; norm_num
      b_mem := hbS
      b_sq := hbsq
      b_comm := hT.b_comm
      card_E := hcl ▸ hE
      gen := fun s hs => by
        obtain ⟨k0, h0, k1, h1, rfl⟩ := exists_uqG_mul hs
        exact ⟨k0, by rw [hT.cu_size]; exact h0, k1, by rw [hT.cw_size]; exact h1, rfl⟩
      u_mem := fun k hk => uqG0_mem (by rwa [hT.cu_size] at hk)
      w_mem := fun k hk => uqG1_mem (by rwa [hT.cw_size] at hk)
      cu_lt := fun k hk i hi => hT.cu_lt k (by rwa [hT.cu_size] at hk) i hi
      cw_lt := fun k hk i hi => hT.cw_lt k (by rwa [hT.cw_size] at hk) i hi
      act_u := fun k hk i hi => hT.act0 k (by rwa [hT.cu_size] at hk) i hi
      act_w := fun k hk i hi => hT.act1 k (by rwa [hT.cw_size] at hk) i hi
      fc := hfc }
  rw [hcl]
  exact hAbs.le_of_card hA hsq hcard

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81
