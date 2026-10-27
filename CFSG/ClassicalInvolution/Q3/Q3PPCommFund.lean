module

public import CFSG.ClassicalInvolution.Q3.Q3URTransfer
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3OFStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3OF
open scoped MatrixGroups

section Conj

theorem commutes_map_conj_pair {G : Type} [Group G] {A B : Subgroup G} (h : Commutes A B) (g : G) :
    Commutes (A.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h a ha b hb]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem commutes_map_pair {G H : Type} [Group G] [Group H] {A B : Subgroup G} (h : Commutes A B)
    (f : G →* H) : Commutes (A.map f) (B.map f) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, h a ha b hb]

end Conj

section Models

theorem commFund_psl {m : ℕ} (hm : 3 ≤ m) :
    ∀ R ∈ (CompData.model .PSL (m + 1)).fund,
      ∃ S ∈ (CompData.model .PSL (m + 1)).fund, Commutes R S := by
  intro R hR
  have hn : 2 ≤ m + 1 := by omega
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨g, hg⟩ := (Models.mem_longRootSet_iff hn).mp (fundamentalSubgroups_psl_subset hn hR)
  let T₀ : Models.Pair (m + 1) :=
    ⟨{⟨0, by omega⟩, ⟨0 + 1, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  let T₁ : Models.Pair (m + 1) :=
    ⟨{⟨2, by omega⟩, ⟨3, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  have hroot : Models.rootSL2 (GaloisField 3 1) hn = Models.Lc (GaloisField 3 1) T₀ := by
    rw [Models.rootSL2_eq_longRootGroup h2 hn, Models.negBlock_eq_zMat (by omega : 0 + 2 ≤ m + 1)]
    rfl
  have hd : Disjoint T₀.1 T₁.1 := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [T₀, T₁, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;>
      · have := congrArg Fin.val h
        simp only at this
        omega
  have hcomm := Models.commutes_Lc_of_disjoint h2 hd
  have hS : (Models.Lc (GaloisField 3 1) T₁).map (MulAut.conj g).toMonoidHom ∈
      Models.longRootSet hn :=
    Models.longRootSet_conjInvariant hn g _ (Models.Lc_mem_longRootSet h2 hn T₁)
  have hfund := Exotic.fundamentalSubgroups_psl_eq (p := 3) (f := 1) (m := m) (by omega)
  refine ⟨(Models.Lc (GaloisField 3 1) T₁).map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · have : (Models.Lc (GaloisField 3 1) T₁).map (MulAut.conj g).toMonoidHom ∈
        fundamentalSubgroups .PSL (modelUniv .PSL (m + 1) 3 1 Fact.out).D := by
      rw [hfund]
      exact hS
    exact this
  · rw [hg, hroot]
    exact commutes_map_conj_pair hcomm g

theorem commFund_psu {n : ℕ} (hadm : StatedLieAdmissible .PSU n 3 1) (hn4 : 4 ≤ n) :
    ∀ R ∈ (CompData.model .PSU n).fund,
      ∃ S ∈ (CompData.model .PSU n).fund, Commutes R S := by
  intro R hR
  have hn : 2 ≤ n := by omega
  have h2 : (2 : GaloisField 3 2) ≠ 0 := two_ne_zero_gf9
  obtain ⟨e, he⟩ := psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  obtain ⟨g, hg⟩ := (Models.mem_longRootSetU_iff hn).mp ((he R).mp hR)
  let T₀ : Models.Pair n :=
    ⟨{⟨0, by omega⟩, ⟨0 + 1, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  let T₁ : Models.Pair n :=
    ⟨{⟨2, by omega⟩, ⟨3, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  have hroot : Models.rootSU2 (GaloisField 3 2) 3 1 hn = Models.LcU (GaloisField 3 2) 3 1 T₀ := by
    rw [Models.rootSU2_eq_longRootGroupSU h2 hn,
      Models.negBlock_eq_zMat (by omega : 0 + 2 ≤ n)]
    rfl
  have hd : Disjoint T₀.1 T₁.1 := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [T₀, T₁, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;>
      · have := congrArg Fin.val h
        simp only at this
        omega
  have hcomm := Models.commutes_LcU_of_disjoint (p := 3) (f := 1) h2 hd
  have hS' : (Models.LcU (GaloisField 3 2) 3 1 T₁).map (MulAut.conj g).toMonoidHom ∈
      Models.longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) hn :=
    Models.longRootSetU_conjInvariant hn g _ (Models.LcU_mem_longRootSetU h2 hn T₁)
  have hid : ∀ A : Subgroup (modelUniv .PSU n 3 1 Fact.out).K,
      (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
    intro A
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  have hid' : ∀ B : Subgroup (Phan.Su (GaloisField 3 2) 3 1 n),
      (B.map e.symm.toMonoidHom).map e.toMonoidHom = B := by
    intro B
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  refine ⟨((Models.LcU (GaloisField 3 2) 3 1 T₁).map (MulAut.conj g).toMonoidHom).map
    e.symm.toMonoidHom, ?_, ?_⟩
  · refine (he _).mpr ?_
    rw [hid']
    exact hS'
  · rw [← hid R, hg, hroot]
    exact commutes_map_pair (commutes_map_conj_pair hcomm g) e.symm.toMonoidHom

theorem commFund_psp {m : ℕ} (hadm : StatedLieAdmissible .PSp m 3 1) :
    ∀ R ∈ (CompData.model .PSp m).fund,
      ∃ S ∈ (CompData.model .PSp m).fund, Commutes R S := by
  intro R hR
  have hm : 2 ≤ m := hadm.2.2.1
  obtain ⟨P, hP, rfl⟩ := (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  let k₀ : Fin m := ⟨0, by omega⟩
  let k₁ : Fin m := ⟨1, by omega⟩
  obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP k₀
  obtain ⟨P', hP', hP'g⟩ := Models.SymplecticPairs.exists_planeGroup_eq_map_conj_longBlock g k₁
  refine ⟨Models.SymplecticPairs.planeGroup P',
    (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadm _).mpr ⟨P', hP', rfl⟩, ?_⟩
  rw [hg, ← hP'g]
  refine commutes_map_conj_pair ?_ g
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact (Models.SymplecticPairs.commute_longBlock_longBlock (by simp [k₀, k₁, Fin.ext_iff]) A B).eq

end Models

end CFSG.ClassicalInvolution.Q3.Q3PP
